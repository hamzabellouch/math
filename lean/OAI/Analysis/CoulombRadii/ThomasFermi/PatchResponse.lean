import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.TFOscillation

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
noncomputable section
namespace Coulomb

def tfScalarDensity (v : ℝ) : ℝ :=
  (max v 0/(thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)

lemma tfScalarDensity_nonneg (v : ℝ) : 0≤tfScalarDensity v := by
  unfold tfScalarDensity
  have hc := thomasFermiKineticConstant_pos
  positivity

lemma tfScalarDensity_mono : Monotone tfScalarDensity := by
  intro v w hvw
  have hc := thomasFermiKineticConstant_pos
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  apply div_le_div_of_nonneg_right (max_le_max_right 0 hvw)
  exact mul_nonneg thomasFermiKineticConstant_pos.le (by norm_num)

lemma localTFDensity_euler {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W=ᵐ[volume.restrict Ω] Φ) :
    ∀ᵐ x, x∈Ω → localTFDensity hΩ W x=
      tfScalarDensity (Φ x-tfPotential (localTFMinimizer hΩ W) x) := by
  have HE := tfEuler_equation hΩ thomasFermiKineticConstant_pos W
    (localTFMinimizer_nonneg hΩ W) (fun f hf => localTFMinimizer_minimizes hΩ W hf)
  filter_upwards [(ae_restrict_iff' hΩ).mp HE,(ae_restrict_iff' hΩ).mp hW,
    tfDensity_ae_tfExtend hΩ (localTFMinimizer_nonneg hΩ W)] with x he hw hd
  intro hx
  change tfDensity Ω (localTFMinimizer hΩ W) x=_
  rw [hd,tfExtend,indicator_of_mem hx,(he hx).1,hw hx]
  rfl

lemma localTFDensity_test_enclosure {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W=ᵐ[volume.restrict Ω] Φ)
    (χ : Space → ℝ) (hχm : Measurable χ) (hχi : Integrable χ)
    (hχp : ∀ x, 0≤χ x) (B : ℝ) (hB : ∀ x, |χ x|≤B)
    (hs : ∀ x, χ x≠0 → x∈Ω) (u d : ℝ)
    (hosc : ∀ x, χ x≠0 → |(Φ x-tfPotential (localTFMinimizer hΩ W) x)-u|≤d) :
    tfScalarDensity (u-d)*(∫ x, χ x)≤∫ x, localTFDensity hΩ W x*χ x ∧
    (∫ x, localTFDensity hΩ W x*χ x)≤tfScalarDensity (u+d)*(∫ x, χ x) := by
  have hρi : Integrable (localTFDensity hΩ W) :=
    (tfExtend_integrable hΩ (localTFMinimizer hΩ W)).congr
      (tfDensity_ae_tfExtend hΩ (localTFMinimizer_nonneg hΩ W)).symm
  have hi : Integrable (fun x => localTFDensity hΩ W x*χ x) :=
    hρi.mul_bdd hχm.aestronglyMeasurable (Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using hB x))
  have H := localTFDensity_euler hΩ Φ W hW
  have hh : ∀ᵐ x, tfScalarDensity (u-d)*χ x≤localTFDensity hΩ W x*χ x ∧
      localTFDensity hΩ W x*χ x≤tfScalarDensity (u+d)*χ x := by
    filter_upwards [H] with x hx
    by_cases hz : χ x=0
    · simp [hz]
    rw [hx (hs x hz)]
    have hr := abs_le.mp (hosc x hz)
    exact ⟨mul_le_mul_of_nonneg_right (tfScalarDensity_mono (by linarith : u-d≤_)) (hχp x),
      mul_le_mul_of_nonneg_right (tfScalarDensity_mono (by linarith : _≤u+d)) (hχp x)⟩
  have hl := integral_mono_ae (hχi.const_mul _) hi (hh.mono (fun _ h => h.1))
  have hu := integral_mono_ae hi (hχi.const_mul _) (hh.mono (fun _ h => h.2))
  simpa only [integral_const_mul] using And.intro hl hu

theorem exists_patch_tested_reaction_enclosure :
    ∃ C : ℝ, 0<C ∧ ∀ {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t r : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space),
    SpatiallySupported u {z | t≤‖z-y‖} →
    ∀ (hn : ∀ j, 20*a≤‖S.position j-y‖), 0≤r → r≤a →
    ∀ (χ : Space → ℝ), Measurable χ → Integrable χ →
    (∀ z, 0≤χ z) → ∀ B : ℝ, (∀ z, |χ z|≤B) →
    (∀ z, χ z≠0 → ‖z-y‖≤r) →
    let W := coreTFField S u measurableSet_ball ha
      (patch_nucleus_separation S ha hb ht.2 y hn)
    let v := patchTFScreenedField S u ha hb ht.2 y hn y
    let d := C*(r/a)*((a^4)⁻¹+max (-v) 0)
    tfScalarDensity (v-d)*(∫ z, χ z)≤∫ z, localTFDensity measurableSet_ball W z*χ z ∧
    (∫ z, localTFDensity measurableSet_ball W z*χ z)≤tfScalarDensity (v+d)*(∫ z, χ z) := by
  obtain ⟨C,hC,H⟩ := exists_patch_TF_oscillation
  refine ⟨C,hC,?_⟩
  intro J k S u a b t r ha hb hsmall ht y hu hn hr hra χ hχm hχi hχp B hB hs
  dsimp only
  apply localTFDensity_test_enclosure measurableSet_ball (coreScreenedField S u) _
    (coreTFField_coe S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn))
    χ hχm hχi hχp B hB
  · intro z hz
    have HZ := hs z hz
    rw [Metric.mem_ball,dist_eq_norm]
    linarith [ht.1]
  · intro z hz
    have hz' : z∈Metric.closedBall y a := by
      rw [Metric.mem_closedBall,dist_eq_norm]
      exact (hs z hz).trans hra
    have hh := H S u ha hb hsmall ht y hu hn z hz'
    rw [Real.norm_eq_abs] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hs z hz) ha.le) hC.le

end Coulomb
end

end
end

end OAI
