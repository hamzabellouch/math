import OAI.Algebra.DepthFive.PairingPartition

namespace OAI

/-! The exact four-path pairing classes are disjoint.  Dropping the diagonal
inequalities enlarges each class, and therefore increases every nonnegative
weighted second-moment sum. -/

noncomputable section
open scoped BigOperators

namespace Problem335.MomentPairing

open Pairings

/-- The four edge coordinates in a layer of endpoint-fixed paths. -/
def layerLabels {γ : Type*} {L : ℕ} (endpoint : γ)
    (x : Fin L → Labels γ) (t : Fin (L + 1)) : Labels (γ × γ) :=
  zipLabels (closePaths endpoint x t.castSucc) (closePaths endpoint x t.succ)

/-- Compatibility of the four signed shifts, expressed independently in each layer. -/
def Compatible {γ : Type*} {L : ℕ} (endpoint : γ) (x : Fin L → Labels γ) : Prop :=
  ∀ t : Fin (L + 1),
    Finsupp.single (layerLabels endpoint x t).p (1 : ℤ) -
        Finsupp.single (layerLabels endpoint x t).q 1 =
      Finsupp.single (layerLabels endpoint x t).r 1 -
        Finsupp.single (layerLabels endpoint x t).s 1

instance compatibleDecidable {γ : Type*} [DecidableEq γ] {L : ℕ}
    (endpoint : γ) (x : Fin L → Labels γ) : Decidable (Compatible endpoint x) := by
  unfold Compatible
  infer_instance

/-- Assign the zero difference to the normal class; all other compatible
coordinate differences belong to the diagonal class. -/
def classifyLayer {γ : Type*} (x : Labels γ) : Kind := by
  classical
  exact if x.p = x.q then .normal else .diagonal

lemma classifyLayer_exact {γ : Type*} (x : Labels γ)
    (h : Finsupp.single x.p (1 : ℤ) - Finsupp.single x.q 1 =
      Finsupp.single x.r 1 - Finsupp.single x.s 1) :
    ExactRespects (classifyLayer x) x := by
  classical
  rcases (coordinate_difference_eq_iff_exclusive x.p x.q x.r x.s).mp h with hN | hD
  · simpa [classifyLayer, hN.1, ExactRespects] using hN
  · simpa [classifyLayer, hD.2.2, ExactRespects] using hD

lemma classifyLayer_eq_of_exact {γ : Type*} (x : Labels γ) (τ : Kind)
    (h : ExactRespects τ x) : classifyLayer x = τ := by
  classical
  cases τ
  · simp [classifyLayer, h.1]
  · simp [classifyLayer, h.2.2]

/-- The unique exact pairing word of a compatible quadruple. -/
def classifyWord {γ : Type*} {L : ℕ} (endpoint : γ)
    (x : Fin L → Labels γ) : Fin (L + 1) → Kind :=
  fun t => classifyLayer (layerLabels endpoint x t)

lemma classifyWord_exact {γ : Type*} {L : ℕ} (endpoint : γ)
    (x : Fin L → Labels γ) (hx : Compatible endpoint x) :
    ∀ t, ExactRespects (classifyWord endpoint x t) (layerLabels endpoint x t) :=
  fun t => classifyLayer_exact _ (hx t)

/-- Forgetting the noncoincidence requirement at diagonal layers embeds each
compatible quadruple into its relaxed class. -/
def toRelaxed {γ : Type*} {L : ℕ} (endpoint : γ)
    (x : {x : Fin L → Labels γ // Compatible endpoint x}) :
    RelaxedPaths γ endpoint (classifyWord endpoint x.1) :=
  ⟨x.1, fun t => (classifyWord_exact endpoint x.1 x.2 t).respects⟩

/-- This encoding preserves all four paths, not just their pairing word. -/
def relaxedEncoding {γ : Type*} {L : ℕ} (endpoint : γ) :
    {x : Fin L → Labels γ // Compatible endpoint x} →
      Σ τ : Fin (L + 1) → Kind, RelaxedPaths γ endpoint τ :=
  fun x => ⟨classifyWord endpoint x.1, toRelaxed endpoint x⟩

lemma relaxedEncoding_injective {γ : Type*} {L : ℕ} (endpoint : γ) :
    Function.Injective (relaxedEncoding (L := L) endpoint) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : Σ τ : Fin (L + 1) → Kind,
    RelaxedPaths γ endpoint τ => z.2.1) h

/-- Summing over the exact classes is bounded by summing over all relaxed
classes whenever the assigned relaxed weights are nonnegative. -/
theorem sum_exact_le_sum_relaxed {γ : Type*} [Fintype γ] [DecidableEq γ] {L : ℕ} (endpoint : γ)
    (W : (τ : Fin (L + 1) → Kind) → RelaxedPaths γ endpoint τ → ℝ)
    (hW : ∀ τ x, 0 ≤ W τ x) :
    (∑ x : {x : Fin L → Labels γ // Compatible endpoint x},
      W (classifyWord endpoint x.1) (toRelaxed endpoint x)) ≤
      ∑ τ : Fin (L + 1) → Kind, ∑ x : RelaxedPaths γ endpoint τ, W τ x := by
  classical
  let f := relaxedEncoding (L := L) endpoint
  let weight : (Σ τ : Fin (L + 1) → Kind, RelaxedPaths γ endpoint τ) → ℝ :=
    fun y => W y.1 y.2
  calc
    _ = ∑ y ∈ Finset.univ.image f, weight y := by
      rw [Finset.sum_image]
      · rfl
      · intro x _ y _ h
        exact relaxedEncoding_injective endpoint h
    _ ≤ ∑ y, weight y := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro y _ _
      exact hW y.1 y.2
    _ = _ := Fintype.sum_sigma _

/-- Normal pairings retain their coordinate-coincidence factor.  Diagonal
pairings retain the assigned constant even after their inequality is dropped. -/
def layerWeight {γ : Type*} (c : ℝ) (τ : Kind) (x : Labels γ) : ℝ := by
  classical
  exact match τ with
    | .normal => 1 + c * (if x.p = x.r then 1 else 0)
    | .diagonal => c

lemma layerWeight_nonneg {γ : Type*} {c : ℝ} (hc : 0 ≤ c)
    (τ : Kind) (x : Labels γ) : 0 ≤ layerWeight c τ x := by
  classical
  cases τ <;> simp only [layerWeight]
  · positivity
  · exact hc

/-- Product of the manuscript's normalized local geometric weights. -/
def pathWeight {γ : Type*} {L : ℕ} (isV : Fin (L + 1) → Bool)
    (α β : ℝ) (endpoint : γ) (τ : Fin (L + 1) → Kind)
    (x : Fin L → Labels γ) : ℝ :=
  ∏ t, layerWeight (if isV t then α⁻¹ else β) (τ t) (layerLabels endpoint x t)

lemma pathWeight_nonneg {γ : Type*} {L : ℕ} (isV : Fin (L + 1) → Bool)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (endpoint : γ)
    (τ : Fin (L + 1) → Kind) (x : Fin L → Labels γ) :
    0 ≤ pathWeight isV α β endpoint τ x := by
  apply Finset.prod_nonneg
  intro t _
  apply layerWeight_nonneg
  split <;> positivity

/-- The exact weighted relaxation step in the four-path second-moment proof. -/
theorem sum_compatible_pathWeight_le {γ : Type*} [Fintype γ] [DecidableEq γ] {L : ℕ}
    (isV : Fin (L + 1) → Bool) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (endpoint : γ) :
    (∑ x : {x : Fin L → Labels γ // Compatible endpoint x},
      pathWeight isV α β endpoint (classifyWord endpoint x.1) x.1) ≤
    ∑ τ : Fin (L + 1) → Kind, ∑ x : RelaxedPaths γ endpoint τ,
      pathWeight isV α β endpoint τ x.1 := by
  have hc (x : Fin L → Labels γ) : classifyWord endpoint x =
      (fun t => Pairings.classify (Pairings.layerLabels endpoint x t)) := by
    classical
    funext t
    unfold classifyWord classifyLayer Pairings.classify layerLabels Pairings.layerLabels
    split_ifs <;> rfl
  simp_rw [hc]
  exact Pairings.sum_compatiblePaths_le_sum_relaxedPaths endpoint
    (fun τ x => pathWeight isV α β endpoint τ x)
    (fun τ x => pathWeight_nonneg isV hα hβ endpoint τ x)


/-- A termwise occupation-moment bound can be summed before the pairing
inequalities are relaxed; no independence of occupations is assumed here. -/
theorem sum_occupation_bound_le_relaxed {γ : Type*} [Fintype γ] [DecidableEq γ] {L : ℕ}
    (isV : Fin (L + 1) → Bool) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (endpoint : γ) (W : (Fin L → Labels γ) → ℝ)
    (hlocal : ∀ x, Compatible endpoint x →
      W x ≤ pathWeight isV α β endpoint (classifyWord endpoint x) x) :
    (∑ x : {x : Fin L → Labels γ // Compatible endpoint x}, W x.1) ≤
    ∑ τ : Fin (L + 1) → Kind, ∑ x : RelaxedPaths γ endpoint τ,
      pathWeight isV α β endpoint τ x.1 := by
  calc
    _ ≤ ∑ x : {x : Fin L → Labels γ // Compatible endpoint x},
        pathWeight isV α β endpoint (classifyWord endpoint x.1) x.1 := by
      apply Finset.sum_le_sum
      intro x _
      exact hlocal x.1 x.2
    _ ≤ _ := sum_compatible_pathWeight_le isV hα hβ endpoint

end Problem335.MomentPairing

end

end OAI
