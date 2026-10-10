import Mathlib
import OAI.Analysis.CoulombRadii.Screening.ScaledTest

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff
noncomputable section
namespace Coulomb

lemma rawTFBregman_nonneg {ρ σ : Space → ℝ}
    (hρ : ∀ᵐ x, 0≤ρ x) (hσ : ∀ᵐ x, 0≤σ x) : 0≤rawTFBregman ρ σ := by
  apply mul_nonneg thomasFermiKineticConstant_pos.le
  apply integral_nonneg_of_ae
  filter_upwards [hρ,hσ] with x hx hy
  exact tf_power_tangent hx hy

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

include hΩ in
lemma raw_coulomb_nonneg {σ : Space → ℝ}
    (hσ : MemLp σ TFExponent (volume.restrict Ω)) (hs : ∀ x∉Ω, σ x=0) :
    0≤coulombBilinear σ σ := by
  have he := tfExtend_toLp hΩ hσ hs
  have H := tfCoulomb_self_nonneg hΩ (hσ.toLp σ)
  rwa [show tfCoulomb Ω (hσ.toLp σ) (hσ.toLp σ)=coulombBilinear σ σ from
    coulombBilinear_congr_ae he he] at H

lemma rawTF_gap_coulomb (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {σ : Space → ℝ} (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hp : ∀ᵐ x, 0≤σ x) (hs : ∀ x∉Ω, σ x=0) :
    coulombBilinear (fun x => σ x-localTFDensity hΩ W x)
      (fun x => σ x-localTFDensity hΩ W x) ≤
      2*(rawThomasFermiEnergy Φ σ-rawThomasFermiEnergy Φ (localTFDensity hΩ W)) := by
  have H := raw_localTF_gap_density hΩ Φ W hW hσ (ae_restrict_of_ae hp) hs
  have HB := rawTFBregman_nonneg (ρ := localTFDensity hΩ W) (Eventually.of_forall (tfDensity_nonneg (localTFMinimizer hΩ W))) hp
  linarith

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma integrable_mul_countTest {f : Space → ℝ} (hf : Integrable f) (y : Space) (a : ℝ) :
    Integrable (fun x => f x*countTest y a x) :=
  hf.mul_bdd (countTest_smooth y a).continuous.aestronglyMeasurable
    (Eventually.of_forall (fun x => by rw [Real.norm_of_nonneg (countTest_nonneg y a x)]; exact countTest_le_one y a x))

lemma rawTF_count_test (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {σ : Space → ℝ} (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hp : ∀ᵐ x, 0≤σ x) (hs : ∀ x∉Ω, σ x=0)
    (y : Space) {a : ℝ} (ha : 0<a) (hb : Metric.closedBall y (2*a)⊆Ω) :
    (∫ x, σ x*countTest y a x)^2 ≤
      2*(∫ x, localTFDensity hΩ W x*countTest y a x)^2+
      4*a*(max countTestEnergy 0)*(rawThomasFermiEnergy Φ σ-
        rawThomasFermiEnergy Φ (localTFDensity hΩ W)) := by
  let ρ := localTFDensity hΩ W
  have hρ : MemLp ρ TFExponent volume := tfDensity_memLp hΩ (localTFMinimizer_nonneg hΩ W)
  have hρs (x : Space) (hx : x∉Ω) : ρ x=0 := tfDensity_eq_zero _ hx
  have hd := hσ.sub (hρ.restrict (s := Ω))
  have hds : ∀ x∉Ω, σ x-ρ x=0 := fun x hx => by rw [hs x hx,hρs x hx,sub_self]
  have H := raw_coulomb_smooth_test hΩ (countTest_smooth y a) (countTest_compact y ha)
    ((countTest_support y ha).trans hb) hd hds
  rw [countTest_energy y ha] at H
  have hQ := raw_coulomb_nonneg hΩ hd hds
  have Hgap := rawTF_gap_coulomb hΩ Φ W hW hσ hp hs
  have He := mul_le_mul_of_nonneg_left (le_max_left countTestEnergy 0) (mul_nonneg ha.le hQ)
  have Hg := mul_le_mul_of_nonneg_right Hgap (mul_nonneg ha.le (le_max_right countTestEnergy 0))
  have hiσ : Integrable σ := (tfExtend_integrable hΩ (hσ.toLp σ)).congr (tfExtend_toLp hΩ hσ hs)
  have hiρ : Integrable ρ := (tfExtend_integrable hΩ (localTFMinimizer hΩ W)).congr
    (tfDensity_ae_tfExtend hΩ (localTFMinimizer_nonneg hΩ W)).symm
  have hiσχ := integrable_mul_countTest hiσ y a
  have hiρχ := integrable_mul_countTest hiρ y a
  have he : (∫ x, (σ x-ρ x)*countTest y a x)=(∫ x, σ x*countTest y a x)-
      (∫ x, ρ x*countTest y a x) := by
    simp_rw [sub_mul]; exact integral_sub hiσχ hiρχ
  simp only [Pi.sub_apply,Pi.sub_def] at H hQ He
  rw [he] at H
  dsimp only [ρ] at H hQ He hiρχ
  nlinarith only [H,He,Hg,sq_nonneg ((∫ x, σ x*countTest y a x)-2*(∫ x, localTFDensity hΩ W x*countTest y a x))]

include hΩ in
lemma tfDensity_test_bound {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (y : Space) {a B : ℝ} (ha : 0<a) (hB : 0≤B)
    (hbound : ∀ᵐ x ∂volume.restrict (Metric.closedBall y (2*a)), tfDensity Ω f x≤B) :
    (∫ x, tfDensity Ω f x*countTest y a x)≤B*((2*a)^3*(Real.pi*4/3)) := by
  have hi := integrable_mul_countTest ((tfExtend_integrable hΩ f).congr
    (tfDensity_ae_tfExtend hΩ hf).symm) y a
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall y (2*a))) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall y (2*a)).measure_lt_top.ne
  have hj : Integrable (Metric.closedBall y (2*a) |>.indicator (fun _ => B)) := by
    apply integrable_indicator_iff measurableSet_closedBall |>.mpr
    exact integrable_const B
  have H : (∫ x, tfDensity Ω f x*countTest y a x)≤
      ∫ x in Metric.closedBall y (2*a), B := by
    rw [←integral_indicator measurableSet_closedBall]
    apply integral_mono_ae hi hj
    filter_upwards [(ae_restrict_iff' measurableSet_closedBall).mp hbound] with x hx
    by_cases h : x∈Metric.closedBall y (2*a)
    · rw [indicator_of_mem h]
      calc
        _≤B*countTest y a x := mul_le_mul_of_nonneg_right (hx h) (countTest_nonneg y a x)
        _≤B := mul_le_of_le_one_right hB (countTest_le_one y a x)
    · rw [indicator_of_notMem h,countTest_zero y ha (le_of_lt (by simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using h)),mul_zero]
  apply H.trans_eq
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,EuclideanSpace.volume_closedBall_fin_three,
    ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal (by positivity : 0≤2*a),
    ENNReal.toReal_ofReal (by positivity : 0≤Real.pi*4/3),smul_eq_mul]
  ring

end Coulomb
end

end
end

end OAI
