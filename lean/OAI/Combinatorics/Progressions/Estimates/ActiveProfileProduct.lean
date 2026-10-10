import OAI.Combinatorics.Progressions.Estimates.ActiveAveragedProfileComparison

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

noncomputable def unitProfileAxisMap {D G α O : Type*}
    [Fintype α] [DecidableEq α] {B : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (d : D) (sets : O → Finset α)
    (r : SamplerCoefficientSlot G B h d → ℝ)
    (x : BlockParameter (B d) (Fin (h d)) α → ℝ) (o : O) : ℝ :=
  (if sets o = ∅ then (1 / 4 : ℝ) * r (constantCoefficientSlot _ _) else 0) +
    booleanSamplerMap (F := Fin (h d))
      (fun b => 3 * unitProfilePrincipalSize (B := B) d / 2 +
        unitProfilePrincipalSize (B := B) d / 2 * r (principalCoefficientSlot h d b)) sets x o

theorem partitionedIdealMap_active_sigma {D G Z α : Type*}
    [Fintype α] [DecidableEq α] {B : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (P : D → Prop) [DecidablePred P]
    {O : {d // ¬P d} → Type*} (sets : ∀ d, O d → Finset α)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) :
    partitionedIdealMap h P sets
        (profileNoiseWithActive (Z := Z) (α := α) h P (fun _ => 0) r) =
      sigmaAxisSampler (fun d => unitProfileAxisMap h d.val (sets d) (fun e => r ⟨d, e⟩)) := by
  have hc (d : {d // ¬P d}) :
      partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B))
        (profileNoiseWithActive (Z := Z) (α := α) h P (fun _ => 0) r) d =
      fun b => 3 * unitProfilePrincipalSize (B := B) d.val / 2 +
        unitProfilePrincipalSize (B := B) d.val / 2 * r ⟨d, principalCoefficientSlot h d.val b⟩ := by
    funext b
    simp only [partitionedProfilePrincipal, profileNoiseWithActive_active]
  funext x o
  simp only [partitionedIdealMap, Pi.add_apply, booleanConstantJet,
    partitionedProfileConstant, profileNoiseWithActive_active,
    jointBooleanSampler, sigmaAxisSampler, unitProfileAxisMap, hc]

noncomputable def unitProfileAxisIdeal {D G α O : Type*}
    [Fintype α] [DecidableEq α] [Fintype O]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (d : D)
    (sets : O → Finset α) (δ : ℝ≥0) (r : SamplerCoefficientSlot G B h d → ℝ) :
    (O → ℝ) → ℝ :=
  regularizedImageDensity (blockCubeMeasure (B d) (Fin (h d)) α)
    (unitProfileAxisMap h d sets r) δ

theorem activeProfileIdeal_prod {D G Z α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
    (P : D → Prop) [DecidablePred P]
    {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)]
    (sets : ∀ d, O d → Finset α) (δ : ℝ≥0)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) (v : (Σ d, O d) → ℝ) :
    activeProfileIdeal Z h P sets δ r v =
      ∏ d, unitProfileAxisIdeal h d.val (sets d) δ (fun e => r ⟨d, e⟩) (fun o => v ⟨d, o⟩) := by
  unfold activeProfileIdeal partitionedRegularizedIdeal
  rw [partitionedIdealMap_active_sigma]
  exact regularizedImageDensity_sigma _ _ δ v

noncomputable def unitProfileAxisAveragedIdeal {D G α O : Type*}
    [Fintype D] [Fintype G] [Fintype α] [DecidableEq α] [Fintype O]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (d : D)
    (sets : O → Finset α) (δ : ℝ≥0) : (O → ℝ) → ℝ :=
  densityMixture (unitCoefficientSource (SamplerCoefficientSlot G B h d))
    (unitProfileAxisIdeal h d sets δ)

theorem activeAveragedProfileIdeal_prod {D G Z α : Type*}
    [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
    (P : D → Prop) [DecidablePred P]
    {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)]
    (sets : ∀ d, O d → Finset α) (δ : ℝ≥0) (v : (Σ d, O d) → ℝ) :
    activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ v =
      ∏ d, unitProfileAxisAveragedIdeal (G := G) (B := B) h d.val (sets d) δ
        (fun o => v ⟨d, o⟩) := by
  unfold activeAveragedProfileIdeal
  rw [unitCoefficientSource_sigma]
  unfold densityMixture
  rw [sigmaAxisMeasure_integral]
  simp_rw [activeProfileIdeal_prod]
  exact integral_fintype_prod_eq_prod
    (μ := fun d : {d // ¬P d} => unitCoefficientSource (SamplerCoefficientSlot G B h d.val))
    (fun d r => unitProfileAxisIdeal h d.val (sets d) δ r (fun o => v ⟨d, o⟩))

end Erdos3

end

end OAI
