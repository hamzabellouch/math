import OAI.Algebra.DepthFive.SecondMomentPairing
import OAI.Algebra.DepthFive.PairingWeights

namespace OAI

noncomputable section

namespace Problem335.MomentPairing

open scoped BigOperators
open Pairings

/-- Normal pairing layers belonging to the derivative-variable group. -/
def normalVLayers {L : ℕ} (isV : Fin (L + 1) → Bool)
    (τ : Fin (L + 1) → Kind) : Finset (Fin (L + 1)) :=
  Finset.univ.filter (fun t => isV t = true ∧ τ t = .normal)

def diagonalVCount {L : ℕ} (isV : Fin (L + 1) → Bool)
    (τ : Fin (L + 1) → Kind) : ℕ :=
  (Finset.univ.filter (fun t => isV t = true ∧ τ t = .diagonal)).card

def diagonalUCount {L : ℕ} (isV : Fin (L + 1) → Bool)
    (τ : Fin (L + 1) → Kind) : ℕ :=
  (Finset.univ.filter (fun t => isV t = false ∧ τ t = .diagonal)).card

def uLayerCount {L : ℕ} (isV : Fin (L + 1) → Bool) : ℕ :=
  (Finset.univ.filter (fun t => isV t = false)).card

/-- The V correction before averaging the path labels. -/
def normalVCorrection {γ : Type*} [DecidableEq γ] {L : ℕ} (isV : Fin (L + 1) → Bool)
    (α : ℝ) (endpoint : γ) (τ : Fin (L + 1) → Kind)
    (x : Fin L → Labels γ) : ℝ :=
  ∏ t : normalVLayers isV τ,
    (1 + α⁻¹ * if (layerLabels endpoint x t).p = (layerLabels endpoint x t).r then 1 else 0)

/-- Extract all diagonal weights and bound each U coincidence factor by `1+β`. -/
theorem pathWeight_le_extracted {γ : Type*} [DecidableEq γ] {L : ℕ}
    (isV : Fin (L + 1) → Bool) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (endpoint : γ) (τ : Fin (L + 1) → Kind) (x : Fin L → Labels γ) :
    pathWeight isV α β endpoint τ x ≤
      α⁻¹ ^ diagonalVCount isV τ * β ^ diagonalUCount isV τ *
        (1 + β) ^ uLayerCount isV * normalVCorrection isV α endpoint τ x := by
  classical
  let vd (t : Fin (L + 1)) : ℝ :=
    if isV t = true ∧ τ t = .diagonal then α⁻¹ else 1
  let ud (t : Fin (L + 1)) : ℝ :=
    if isV t = false ∧ τ t = .diagonal then β else 1
  let ub (t : Fin (L + 1)) : ℝ := if isV t = false then 1 + β else 1
  let nv (t : Fin (L + 1)) : ℝ :=
    if isV t = true ∧ τ t = .normal then
      1 + α⁻¹ * if (layerLabels endpoint x t).p = (layerLabels endpoint x t).r then 1 else 0
    else 1
  have hlocal (t : Fin (L + 1)) :
      layerWeight (if isV t then α⁻¹ else β) (τ t) (layerLabels endpoint x t) ≤
        vd t * ud t * ub t * nv t := by
    cases hv : isV t <;> cases ht : τ t <;>
      by_cases he : (layerLabels endpoint x t).p = (layerLabels endpoint x t).r <;>
      simp [layerWeight, vd, ud, ub, nv, hv, ht, he] <;> nlinarith [sq_nonneg β]
  have hprod : pathWeight isV α β endpoint τ x ≤
      (∏ t, vd t) * (∏ t, ud t) * (∏ t, ub t) * (∏ t, nv t) := by
    unfold pathWeight
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro t _
      apply layerWeight_nonneg
      split <;> positivity
    · intro t _
      exact hlocal t
  have hvd : (∏ t, vd t) = α⁻¹ ^ diagonalVCount isV τ := by
    simp only [vd, ← Finset.prod_filter, Finset.prod_const, diagonalVCount]
  have hud : (∏ t, ud t) = β ^ diagonalUCount isV τ := by
    simp only [ud, ← Finset.prod_filter, Finset.prod_const, diagonalUCount]
  have hub : (∏ t, ub t) = (1 + β) ^ uLayerCount isV := by
    simp only [ub, ← Finset.prod_filter, Finset.prod_const, uLayerCount]
  have hnv : (∏ t, nv t) = normalVCorrection isV α endpoint τ x := by
    simpa [nv, normalVCorrection, normalVLayers, Finset.prod_filter] using
      (Finset.prod_coe_sort (normalVLayers isV τ) (fun t : Fin (L + 1) =>
        1 + α⁻¹ * if (layerLabels endpoint x t).p = (layerLabels endpoint x t).r
          then 1 else 0)).symm
  simpa only [hvd, hud, hub, hnv] using hprod

/-- The full weighted relaxed-quadruple bound used in the second trace. -/
theorem sum_relaxed_pathWeight_le {γ : Type*} [Fintype γ] [DecidableEq γ]
    [Nonempty γ] {L : ℕ} (isV : Fin (L + 1) → Bool)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (endpoint : γ)
    (τ : Fin (L + 1) → Kind)
    (hs : Pairwise (fun t u : normalVLayers isV τ =>
      Disjoint (internalEndpointSet t.1) (internalEndpointSet u.1))) :
    (∑ x : RelaxedPaths γ endpoint τ, pathWeight isV α β endpoint τ x.1) ≤
      α⁻¹ ^ diagonalVCount isV τ * β ^ diagonalUCount isV τ *
        (1 + β) ^ uLayerCount isV *
        ((Fintype.card γ : ℝ) ^ (2 * L - adjacentSwitches τ) *
          ∏ t : normalVLayers isV τ,
            (1 + α⁻¹ * (Fintype.card γ : ℝ)⁻¹ ^
              normalEndpointCount τ (internalEndpointSet t.1))) := by
  classical
  calc
    _ ≤ ∑ x : RelaxedPaths γ endpoint τ,
        (α⁻¹ ^ diagonalVCount isV τ * β ^ diagonalUCount isV τ *
          (1 + β) ^ uLayerCount isV) * normalVCorrection isV α endpoint τ x.1 := by
      apply Finset.sum_le_sum
      intro x _
      exact pathWeight_le_extracted isV hα hβ endpoint τ x.1
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      exact sum_relaxedPaths_layer_corrections γ endpoint τ
        (fun t : normalVLayers isV τ => t.1) hs (fun _ => α⁻¹)

/-- The normalized pairing-word summand in the second-moment reduction. -/
def relaxedWordWeight {L : ℕ} (isV : Fin (L + 1) → Bool)
    (N α β : ℝ) (τ : Fin (L + 1) → Kind) : ℝ :=
  N⁻¹ ^ adjacentSwitches τ * α⁻¹ ^ diagonalVCount isV τ * β ^ diagonalUCount isV τ *
    ∏ t : normalVLayers isV τ,
      (1 + α⁻¹ * N⁻¹ ^ normalEndpointCount τ (internalEndpointSet t.1))

/-- Separate the free two-path count from the switch penalty. -/
theorem assignmentPower_eq_normalized {L : ℕ} (τ : Fin (L + 1) → Kind)
    {N : ℝ} (hN : N ≠ 0) :
    N ^ (2 * L - adjacentSwitches τ) = N ^ (2 * L) * N⁻¹ ^ adjacentSwitches τ := by
  have hsw : adjacentSwitches τ ≤ L := by
    unfold adjacentSwitches
    simpa using Finset.card_filter_le (Finset.univ : Finset (Fin L))
      (fun i => τ i.castSucc ≠ τ i.succ)
  have hle : adjacentSwitches τ ≤ 2 * L := by omega
  have heq : N ^ (2 * L) = N ^ (2 * L - adjacentSwitches τ) *
      N ^ adjacentSwitches τ := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [heq, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hN), mul_one]

/-- Full combinatorial moment reduction, summed over all pairing words. -/
theorem sum_relaxed_pathWeight_le_wordSum {γ : Type*} [Fintype γ] [DecidableEq γ]
    [Nonempty γ] {L : ℕ} (isV : Fin (L + 1) → Bool)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (endpoint : γ)
    (hs : ∀ τ : Fin (L + 1) → Kind,
      Pairwise (fun t u : normalVLayers isV τ =>
        Disjoint (internalEndpointSet t.1) (internalEndpointSet u.1))) :
    (∑ τ : Fin (L + 1) → Kind, ∑ x : RelaxedPaths γ endpoint τ,
      pathWeight isV α β endpoint τ x.1) ≤
      (1 + β) ^ uLayerCount isV * (Fintype.card γ : ℝ) ^ (2 * L) *
        ∑ τ : Fin (L + 1) → Kind, relaxedWordWeight isV (Fintype.card γ) α β τ := by
  have hN : (Fintype.card γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ ∑ τ : Fin (L + 1) → Kind,
        (1 + β) ^ uLayerCount isV * (Fintype.card γ : ℝ) ^ (2 * L) *
          relaxedWordWeight isV (Fintype.card γ) α β τ := by
      apply Finset.sum_le_sum
      intro τ _
      have h := sum_relaxed_pathWeight_le isV hα hβ endpoint τ (hs τ)
      rw [assignmentPower_eq_normalized τ hN] at h
      apply h.trans_eq
      unfold relaxedWordWeight
      ring
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Reindex all pairing words using the canonical false-normal, true-diagonal encoding. -/
theorem sum_relaxedWordWeight_eq_bool {L : ℕ} (isV : Fin (L + 1) → Bool)
    (N α β : ℝ) :
    (∑ τ : Fin (L + 1) → Kind, relaxedWordWeight isV N α β τ) =
      ∑ w : Fin (L + 1) → Bool,
        relaxedWordWeight isV N α β (fun t => boolKindEquiv (w t)) := by
  exact (Equiv.sum_comp (Equiv.piCongrRight (fun _ : Fin (L + 1) => boolKindEquiv))
    (relaxedWordWeight isV N α β)).symm

/-- Consume a Boolean-word estimate after the full relaxed-path averaging. -/
theorem sum_relaxed_pathWeight_le_of_boolWordSum {γ : Type*} [Fintype γ]
    [DecidableEq γ] [Nonempty γ] {L : ℕ} (isV : Fin (L + 1) → Bool)
    {α β B : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (endpoint : γ)
    (hs : ∀ τ : Fin (L + 1) → Kind,
      Pairwise (fun t u : normalVLayers isV τ =>
        Disjoint (internalEndpointSet t.1) (internalEndpointSet u.1)))
    (hword : (∑ w : Fin (L + 1) → Bool,
      relaxedWordWeight isV (Fintype.card γ) α β (fun t => boolKindEquiv (w t))) ≤ B) :
    (∑ τ : Fin (L + 1) → Kind, ∑ x : RelaxedPaths γ endpoint τ,
      pathWeight isV α β endpoint τ x.1) ≤
      (1 + β) ^ uLayerCount isV * (Fintype.card γ : ℝ) ^ (2 * L) * B := by
  apply (sum_relaxed_pathWeight_le_wordSum isV hα hβ endpoint hs).trans
  rw [sum_relaxedWordWeight_eq_bool]
  exact mul_le_mul_of_nonneg_left hword (by positivity)

end Problem335.MomentPairing

end

end OAI
