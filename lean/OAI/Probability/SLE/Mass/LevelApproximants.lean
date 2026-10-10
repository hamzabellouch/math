import OAI.Probability.SLE.Multipoint.MultipointLevelMass

namespace OAI

/-! The actual finite-level random measures used to construct canonical
trace mass. Time truncation retains precisely levels already attained. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SLEExactGauge.Multipoint

local instance : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

lemma actual_radiusLevel_joint_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω)) :
    Measurable (fun q : Ω × ℂ => radiusLevelTime (γ q.1) (G q.1) q.2 u) := by
  have hp : Measurable (sourceDriverPath B hBc) := source_path_measurable _ hm
  have h : Measurable (fun q : Ω × ℂ =>
      canonicalRadiusLevel κ (u,q.2,sourceDriverPath B hBc q.1)) :=
    (canonicalRadiusLevel_measurable κ).comp
      (measurable_const.prodMk (measurable_snd.prodMk (hp.comp measurable_fst)))
  convert h using 1
  funext q
  exact (canonicalRadiusLevel_eq κ (sourceDriverPath B hBc q.1) (hw q.1) u hu q.2).symm

def levelApproximationDensity {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (t : ℝ≥0∞) (ω : Ω) (z : ℂ) : ℝ≥0∞ :=
  if radiusLevelTime (γ ω) (G ω) z u ≤ t then
    ENNReal.ofReal (stoppedGreen κ (fun s => Real.sqrt κ*B s ω) (γ ω) (G ω) z u)
  else 0

def levelApproximation {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (t : ℝ≥0∞) (ω : Ω) : Measure ℂ :=
  volume.withDensity (levelApproximationDensity κ B γ G u t ω)

lemma levelApproximationDensity_joint_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0∞) : Measurable (Function.uncurry (levelApproximationDensity κ B γ G u t)) := by
  exact Measurable.ite
    (measurableSet_le (actual_radiusLevel_joint_measurable hm hBc κ u hu γ G F hw) measurable_const)
    (actual_stoppedGreen_joint_measurable hm hBc κ u hu γ G F hw).ennreal_ofReal
    measurable_const

lemma levelApproximationDensity_mono
    {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (ω : Ω) (z : ℂ) :
    Monotone (fun t => levelApproximationDensity κ B γ G u t ω z) := by
  intro s t hst
  dsimp only [levelApproximationDensity]
  split_ifs with hs ht
  · exact le_rfl
  · exact False.elim (ht (hs.trans hst))
  · exact bot_le
  · exact le_rfl

lemma levelApproximation_mono
    {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (ω : Ω) : Monotone (fun t => levelApproximation κ B γ G u t ω) := by
  intro s t hst
  exact withDensity_mono (Filter.Eventually.of_forall (fun z =>
    levelApproximationDensity_mono κ B γ G u ω z hst))

lemma levelApproximation_apply_top
    {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (ω : Ω) {K : Set ℂ} (hK : MeasurableSet K) :
    levelApproximation κ B γ G u ∞ ω K = levelMass κ B γ G u K ω := by
  rw [levelApproximation,withDensity_apply _ hK]
  simp only [levelApproximationDensity,le_top,ite_true,levelMass]

lemma levelApproximation_apply_le
    {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (t : ℝ≥0∞) (ω : Ω) {K : Set ℂ} (hK : MeasurableSet K) :
    levelApproximation κ B γ G u t ω K ≤ levelMass κ B γ G u K ω := by
  rw [← levelApproximation_apply_top κ B γ G u ω hK]
  exact levelApproximation_mono κ B γ G u ω le_top K

lemma levelApproximation_measurable_apply
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0∞) {K : Set ℂ} (hK : MeasurableSet K) :
    Measurable (fun ω => levelApproximation κ B γ G u t ω K) := by
  simp only [levelApproximation,withDensity_apply _ hK]
  exact (levelApproximationDensity_joint_measurable hm hBc κ u hu γ G F hw t).lintegral_prod_right'

end SLEExactGauge.Multipoint

end

end OAI
