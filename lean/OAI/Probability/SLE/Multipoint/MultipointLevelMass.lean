import OAI.Probability.SLE.Multipoint.MultipointLevelWeights
import OAI.Probability.SLE.Multipoint.MultipointMomentIntegration
import OAI.Probability.SLE.Loewner.CanonicalRadiusKernel

namespace OAI

/-! Jointly measurable actual level masses and the tensor identity used
to integrate the multipoint estimate. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SLEExactGauge.Multipoint

local instance : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

lemma actual_stoppedGreen_joint_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω)) :
    Measurable (fun q : Ω × ℂ => stoppedGreen κ (fun t => Real.sqrt κ*B t q.1)
      (γ q.1) (G q.1) q.2 u) := by
  have hp : Measurable (sourceDriverPath B hBc) := source_path_measurable _ hm
  have h : Measurable (fun q : Ω × ℂ =>
      canonicalStoppedGreen κ (u, q.2, sourceDriverPath B hBc q.1)) :=
    (canonicalStoppedGreen_measurable κ).comp
    (measurable_const.prodMk (measurable_snd.prodMk (hp.comp measurable_fst)))
  convert h using 1
  funext q
  exact (canonicalStoppedGreen_eq κ (sourceDriverPath B hBc q.1) (hw q.1) u hu q.2).symm

def levelMass {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (K : Set ℂ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ z in K, ENNReal.ofReal (stoppedGreen κ (fun t => Real.sqrt κ*B t ω)
    (γ ω) (G ω) z u)

lemma levelMass_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (K : Set ℂ) : Measurable (levelMass κ B γ G u K) :=
  (actual_stoppedGreen_joint_measurable hm hBc κ u hu γ G F hw).ennreal_ofReal.lintegral_prod_right'

theorem levelMass_moment_identity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SigmaFinite P]
    {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (K : Set ℂ) (m : ℕ) :
    (∫⁻ ω, levelMass κ B γ G u K ω ^ m ∂P) =
      ∫⁻ z : Fin m → ℂ, ∫⁻ ω, ENNReal.ofReal (∏ i, stoppedGreen κ
        (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (z i) u) ∂P
        ∂Measure.pi (fun _ : Fin m => volume.restrict K) := by
  have h := lintegral_mass_pow_eq P (volume.restrict K)
    (fun ω z => ENNReal.ofReal (stoppedGreen κ (fun t => Real.sqrt κ*B t ω)
      (γ ω) (G ω) z u))
    (actual_stoppedGreen_joint_measurable hm hBc κ u hu γ G F hw).ennreal_ofReal m
  change (∫⁻ ω, (∫⁻ z in K, ENNReal.ofReal (stoppedGreen κ
    (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) z u)) ^ m ∂P) = _
  rw [h]
  apply lintegral_congr
  intro z
  apply lintegral_congr
  intro ω
  exact (ENNReal.ofReal_prod_of_nonneg
    (fun i _ => stoppedGreen_nonneg (hw ω) κ _ _)).symm

lemma common_level_log_target (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) :
    Real.log (2*z.im/(2*z.im*Real.exp (-u))) = u := by
  have hratio : 2*z.im/(2*z.im*Real.exp (-u)) = Real.exp u := by
    rw [Real.exp_neg]
    field_simp [(show z.im ≠ 0 from ne_of_gt hz),(Real.exp_pos u).ne']
  rw [hratio,Real.log_exp]

theorem stoppedGreen_common_level_product_bound
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (z : ι → ℂ) (hz : ∀ i, z i ∈ upperHalfPlane) (hne : Function.Injective z)
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) (hbR : ∀ i, b i ≤ 2*(z i).im)
    (hsep : ∀ i j, i ≠ j → b i ≤ dist (z i) (z j)) (u : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (∏ i, stoppedGreen κ (fun t => Real.sqrt κ*B t ω)
      (γ ω) (G ω) (z i) u) ∂P) ≤
      ENNReal.ofReal ((3 : ℝ)^(Fintype.card ι) *
        Real.exp (uniformDiscountBudget κ (sourceBeta κ) (Finset.univ : Finset ι)) *
        ∏ i, (b i)^(-codimension κ)) := by
  have h := stoppedGreen_product_expectation_bound hB hm hBm hBc hB0 hκ hκ8 γ G F hw
    hgrowth z hz hne b (fun i => 2*(z i).im*Real.exp (-u))
    (fun i => mul_pos (mul_pos (by norm_num) (hz i)) (Real.exp_pos _)) hb hbR hsep
  simpa only [common_level_log_target _ (hz _) u] using h

end SLEExactGauge.Multipoint

end

end OAI
