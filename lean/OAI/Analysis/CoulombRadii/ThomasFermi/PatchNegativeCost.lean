import Mathlib
import OAI.Analysis.CoulombRadii.Screening.PatchComparison
import OAI.Analysis.CoulombRadii.ThomasFermi.TFOscillation
import OAI.Analysis.CoulombRadii.ThomasFermi.TFNegativeGap
import OAI.Analysis.CoulombRadii.Screening.NegativeCost

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

include hΩ in
lemma tf_negative_cost_integrable (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {f : TFLp (volume.restrict Ω)} {σ : Space → ℝ}
    (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hp : ∀ᵐ x, 0 ≤ σ x) (hs : ∀ x ∉ Ω, σ x=0) :
    Integrable (fun x => max (tfPotential f x-Φ x) 0*σ x) := by
  have : ENNReal.HolderConjugate TFFieldExponent TFExponent :=
    coulomb_holder_exponents.ennrealOfReal
  have H : IntegrableOn (fun x => (tfPotential f x-Φ x)*σ x) Ω :=
    ((tfPotential_memLp hΩ f).sub ((memLp_congr_ae hW).mp (Lp.memLp W))).integrable_mul hσ
  have Hi : Integrable (fun x => (tfPotential f x-Φ x)*σ x) := by
    apply (H.integrable_indicator hΩ).congr
    filter_upwards [] with x
    by_cases hx : x∈Ω
    · simp [hx]
    · simp [hx,hs x hx]
  apply Hi.pos_part.congr
  filter_upwards [hp] with x hx
  rw [max_mul_of_nonneg _ _ hx,zero_mul]

lemma rawTF_negativeError_le_gap (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {σ : Space → ℝ} (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hp : ∀ᵐ x, 0 ≤ σ x) (hs : ∀ x ∉ Ω, σ x=0) :
    rawTFNegativeError Φ (localTFDensity hΩ W) σ ≤
      rawThomasFermiEnergy Φ σ-rawThomasFermiEnergy Φ (localTFDensity hΩ W) := by
  have H := raw_localTF_refined_gap_density hΩ Φ W hW hσ (ae_restrict_of_ae hp) hs
  have hρ : MemLp (localTFDensity hΩ W) TFExponent volume :=
    tfDensity_memLp hΩ (localTFMinimizer_nonneg hΩ W)
  have hpQ := raw_coulomb_nonneg hΩ (hσ.sub (hρ.restrict (s := Ω)))
    (fun x hx => by change σ x-localTFDensity hΩ W x=0; rw [hs x hx,show localTFDensity hΩ W x=0 from tfDensity_eq_zero _ hx,sub_self])
  change 0 ≤ coulombBilinear (fun x => σ x-localTFDensity hΩ W x)
    (fun x => σ x-localTFDensity hΩ W x) at hpQ
  linarith

lemma tf_negative_center_le_gap (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {σ : Space → ℝ} (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hp : ∀ᵐ x, 0 ≤ σ x) (hs : ∀ x ∉ Ω, σ x=0)
    (χ : Space → ℝ) (y : Space) (θ B K m : ℝ)
    (hθ : 0 ≤ θ) (hθh : θ ≤ 1/2) (hB : 0 ≤ B) (hK : 0 ≤ K) (hm : 0 < m)
    (hχ : ∀ᵐ x, 0 ≤ χ x ∧ χ x ≤ K) (hi : Integrable (fun x => σ x*χ x))
    (hmass : m ≤ ∫ x, σ x*χ x)
    (hosc : ∀ᵐ x, χ x≠0 →
      ‖(Φ x-tfPotential (localTFMinimizer hΩ W) x)-
        (Φ y-tfPotential (localTFMinimizer hΩ W) y)‖ ≤
        θ*(B+max (-(Φ y-tfPotential (localTFMinimizer hΩ W) y)) 0)) :
    max (-(Φ y-tfPotential (localTFMinimizer hΩ W) y)) 0 ≤
      (2*K/m)*(rawThomasFermiEnergy Φ σ-rawThomasFermiEnergy Φ (localTFDensity hΩ W))+2*θ*B := by
  have hc := tf_negative_cost_integrable hΩ Φ W hW (f := localTFMinimizer hΩ W) hσ hp hs
  have he : (∫ x, max (-(Φ x-tfPotential (localTFMinimizer hΩ W) x)) 0*σ x)=
      rawTFNegativeError Φ (localTFDensity hΩ W) σ := by
    rw [tfPotential_eq_density hΩ (localTFMinimizer_nonneg hΩ W)]
    simp only [neg_sub,NeutralAtom.potentialOf,rawTFNegativeError,localTFDensity,NeutralAtom.coulombKernel,coulombKernel]
  have H := NeutralAtom.negative_center_of_test_mass
    (fun x => Φ x-tfPotential (localTFMinimizer hΩ W) x) σ χ
    (Φ y-tfPotential (localTFMinimizer hΩ W) y) θ B K m hθ hθh hB hK hm hp hχ hi
    (by simpa only [neg_sub] using hc) hmass hosc
  rw [he] at H
  have Hg := mul_le_mul_of_nonneg_left (rawTF_negativeError_le_gap hΩ Φ W hW hσ hp hs)
    (show 0 ≤ 2*K/m by positivity)
  linarith

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in

theorem exists_patch_negative_center_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {J k n : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t r : ℝ} (ha : 0 < a) (hb : 0 < b) (hsmall : 18*b ≤ a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space),
    SpatiallySupported u {z | t ≤ ‖z-y‖} →
    ∀ (hn : ∀ j, 20*a ≤ ‖S.position j-y‖), 0 ≤ r → r ≤ a → C*(r/a) ≤ 1/2 →
    ∀ (x : Configuration n) (χ : Space → ℝ) (K m : ℝ), 0 ≤ K → 0 < m →
    (∀ᵐ z, 0 ≤ χ z ∧ χ z ≤ K) →
    Integrable (fun z => retainedFineDensity b (patchRetained y t b x) (position x) z*χ z) →
    (∀ z, χ z≠0 → ‖z-y‖ ≤ r) →
    m ≤ ∫ z, retainedFineDensity b (patchRetained y t b x) (position x) z*χ z →
    max (-patchTFScreenedField S u ha hb ht.2 y hn y) 0 ≤
      (2*K/m)*(rawThomasFermiEnergy (coreScreenedField S u)
        (retainedFineDensity b (patchRetained y t b x) (position x))-
        rawThomasFermiEnergy (coreScreenedField S u)
          (localTFDensity measurableSet_ball (coreTFField S u measurableSet_ball ha
            (patch_nucleus_separation S ha hb ht.2 y hn))))+2*(C*(r/a))*((a^4)⁻¹) := by
  obtain ⟨C,hC,H⟩ := exists_patch_TF_oscillation
  refine ⟨C,hC,?_⟩
  intro J k n S u a b t r ha hb hsmall ht y hu hn hr hra hθ x χ K m hK hm hχ hi hs hmass
  let W := coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn)
  apply tf_negative_center_le_gap measurableSet_ball (coreScreenedField S u) W
    (coreTFField_coe S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn))
    (retainedFineDensity_memLp hb _ _) (Eventually.of_forall (fun _ => retainedFineDensity_nonneg ..))
    (retainedFineDensity_patch_support hb y t x) χ y (C*(r/a)) ((a^4)⁻¹) K m
    (by positivity) hθ (by positivity) hK hm hχ hi hmass
  filter_upwards [] with z
  intro hz
  have hzr := hs z hz
  have hza : z∈Metric.closedBall y a := by simpa [Metric.mem_closedBall,dist_eq_norm] using hzr.trans hra
  have hosc := H S u ha hb hsmall ht y hu hn z hza
  apply hosc.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hzr ha.le) hC.le) (by positivity)

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

def patchSliceTFGap {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖) (s : Spins m) (x : Configuration m) : ℝ :=
  rawThomasFermiEnergy (coreScreenedField S (u.coreSlice s x).normalized)
    (retainedFineDensity b (patchRetained y t b x) (position x))-
  rawThomasFermiEnergy (coreScreenedField S (u.coreSlice s x).normalized)
    (localTFDensity measurableSet_ball (coreTFField S (u.coreSlice s x).normalized
      measurableSet_ball ha (patch_nucleus_separation S ha hb ht y hn)))

lemma patchSliceTFGap_nonneg {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖) (s : Spins m) (x : Configuration m) :
    0≤patchSliceTFGap S u ha hb ht y hn s x := by
  have H := rawTF_negativeError_le_gap measurableSet_ball
    (coreScreenedField S (u.coreSlice s x).normalized) _
    (coreTFField_coe S _ measurableSet_ball ha (patch_nucleus_separation S ha hb ht y hn))
    (retainedFineDensity_memLp hb (patchRetained y t b x) (position x))
    (Eventually.of_forall (fun z => retainedFineDensity_nonneg b _ _ z))
    (retainedFineDensity_patch_support hb y t x)
  apply le_trans _ H
  exact integral_nonneg (fun z => mul_nonneg (le_max_right _ _)
    (retainedFineDensity_nonneg b _ _ z))

lemma patchSliceTFGap_weight_integrable {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖) (s : Spins m)
    (hcs : ∀ᵐ x, SpatiallySupported (u.coreSlice s x).normalized {z | t≤‖z-y‖}) :
    Integrable (fun x => mass (u.coreSlice s x)*patchSliceTFGap S u ha hb ht y hn s x) := by
  have hT := (coreTF_conditional_integrable measurableSet_ball S u s ha
    (patch_nucleus_separation S ha hb ht y hn) (show 0<12*a by positivity)
    (patch_diameter ha hb ht y) (fun _ => totalCharge S/a)
    (Eventually.of_forall (fun _ => div_nonneg (totalCharge_nonneg S) ha.le))
    ((mass_coreSlice_integrable u s).mul_const ((totalCharge S/a)^2))
    (show ∀ᵐ x, ∀ z∈Metric.ball y (t-4*b),
      coreScreenedField S (u.coreSlice s x).normalized z≤totalCharge S/a from ?_)).2
  · have hF : Integrable (fun x => mass (u.coreSlice s x)*
        rawThomasFermiEnergy (coreScreenedField S (u.coreSlice s x).normalized)
          (retainedFineDensity b (patchRetained y t b x) (position x))) := by
      apply (discreteFineTF_weight_integrable S u hb (patchRetained y t b)
        (patchRetained_measurable y t b) s).congr
      filter_upwards [hcs] with x hx
      rw [discreteFineTF_eq_raw S u hb (patchRetained y t b) s x hx ?_
        (patch_retained_separated ha hb y x)]
      intro j i hi
      have hret := (patchRetained_mem ..).mp hi
      have H := norm_sub_le_norm_sub_add_norm_sub (S.position j) (position x i) y
      have hs : Real.sqrt 3≤2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
      nlinarith [hn j]
    apply (hF.sub hT).congr
    filter_upwards [] with x
    simp only [patchSliceTFGap,Pi.sub_apply,mul_sub]
  · filter_upwards [] with x
    intro z hz
    apply (sub_le_self _ (coreCoulombPotential_nonneg _ z)).trans
    exact attraction_le_totalCharge_div S ha z
      (fun j => patch_nucleus_separation S ha hb ht y hn j z hz)

end Coulomb

end

end OAI
