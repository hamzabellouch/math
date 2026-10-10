import OAI.Algebra.DepthFive.SecondMomentPairing
import OAI.Algebra.DepthFive.LocalMomentWeights

namespace OAI

/-! Concrete normalization and reindexing of the geometric upper bound for
four-path occupation moments. -/

noncomputable section
open scoped BigOperators

namespace Problem335.MomentPairing

open Pairings

/-- The diagonal flag used by the local geometric moment table. -/
def isDiagonal : Kind → Bool
  | .normal => false
  | .diagonal => true

/-- Coordinate coincidence in the normal pairing. -/
def coincides {γ : Type*} (x : Labels γ) : Bool := by
  classical
  exact decide (x.p = x.r)

lemma localWeight_eq_layerWeight {γ : Type*} (isV : Bool)
    (α β : ℝ) (τ : Kind) (x : Labels γ) :
    LocalMomentWeights.weight isV (isDiagonal τ) (coincides x) α β =
      layerWeight (if isV then α⁻¹ else β) τ x := by
  classical
  cases τ <;> cases isV <;> by_cases h : x.p = x.r <;>
    simp [LocalMomentWeights.weight, layerWeight, isDiagonal, coincides, h]

/-- The first-moment normalization for a fixed V/U layer partition. -/
def pathMean {L : ℕ} (isV : Fin (L + 1) → Bool) (A B : ℝ) : ℝ :=
  A ^ (Finset.univ.filter (fun t => isV t = true)).card *
    (B + 1) ^ (Finset.univ.filter (fun t => isV t = false)).card

lemma pathMean_pos {L : ℕ} (isV : Fin (L + 1) → Bool) {A B : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) : 0 < pathMean isV A B := by
  unfold pathMean
  positivity

/-- The product of independent geometric local moments for a fixed pairing. -/
def pathGeometricMoment {γ : Type*} {L : ℕ} (isV : Fin (L + 1) → Bool)
    (A B : ℝ) (endpoint : γ) (τ : Fin (L + 1) → Kind)
    (x : Fin L → Labels γ) : ℝ :=
  ∏ t, LocalMomentWeights.moment (isV t) (isDiagonal (τ t))
    (coincides (layerLabels endpoint x t)) A B

/-- Local normalizations multiply to precisely the square of the first moment. -/
theorem pathGeometricMoment_eq {γ : Type*} {L : ℕ}
    (isV : Fin (L + 1) → Bool) {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (endpoint : γ) (τ : Fin (L + 1) → Kind) (x : Fin L → Labels γ) :
    pathGeometricMoment isV A B endpoint τ x =
      pathMean isV A B ^ 2 *
        pathWeight isV (A / (A + 1)) (B / (B + 1)) endpoint τ x := by
  unfold pathGeometricMoment pathMean pathWeight
  rw [LocalMomentWeights.prod_moment_eq_mu_sq_mul _ _ _ _ hA hB]
  congr 1
  apply Finset.prod_congr rfl
  intro t _
  exact localWeight_eq_layerWeight _ _ _ _ _

/-- Summing the geometric local moments over the exact compatible quadruples
is bounded by the relaxed pairing sum with its common `mu^2` normalization. -/
theorem sum_compatible_geometricMoment_le {γ : Type*} [Fintype γ] [DecidableEq γ]
    {L : ℕ} (isV : Fin (L + 1) → Bool) {A B : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (endpoint : γ) :
    (∑ x : {x : Fin L → Labels γ // Compatible endpoint x},
      pathGeometricMoment isV A B endpoint (classifyWord endpoint x.1) x.1) ≤
    pathMean isV A B ^ 2 *
      ∑ τ : Fin (L + 1) → Kind, ∑ x : RelaxedPaths γ endpoint τ,
        pathWeight isV (A / (A + 1)) (B / (B + 1)) endpoint τ x.1 := by
  simp_rw [pathGeometricMoment_eq isV hA hB]
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact sum_compatible_pathWeight_le isV (by positivity) (by positivity) endpoint

/-- After the actual occupation comparison has bounded each compatible
quadruple, all source and path sums combine with only one source-size factor. -/
theorem sum_sources_compatible_le {ι γ : Type*} [Fintype ι]
    [Fintype γ] [DecidableEq γ] {L : ℕ}
    (isV : Fin (L + 1) → Bool) {A B D : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hD : 0 ≤ D) (endpoint : γ)
    (C : ι → (Fin L → Labels γ) → ℝ)
    (hexpect : ∀ x, Compatible endpoint x →
      (∑ i, C i x) ≤ D *
        pathGeometricMoment isV A B endpoint (classifyWord endpoint x) x) :
    (∑ i, ∑ x : {x : Fin L → Labels γ // Compatible endpoint x}, C i x.1) ≤
      D * pathMean isV A B ^ 2 *
        ∑ τ : Fin (L + 1) → Kind, ∑ x : RelaxedPaths γ endpoint τ,
          pathWeight isV (A / (A + 1)) (B / (B + 1)) endpoint τ x.1 := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ x : {x : Fin L → Labels γ // Compatible endpoint x},
        D * pathGeometricMoment isV A B endpoint (classifyWord endpoint x.1) x.1 := by
      apply Finset.sum_le_sum
      intro x _
      exact hexpect x.1 x.2
    _ = D * ∑ x : {x : Fin L → Labels γ // Compatible endpoint x},
        pathGeometricMoment isV A B endpoint (classifyWord endpoint x.1) x.1 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ D * (pathMean isV A B ^ 2 *
        ∑ τ : Fin (L + 1) → Kind, ∑ x : RelaxedPaths γ endpoint τ,
          pathWeight isV (A / (A + 1)) (B / (B + 1)) endpoint τ x.1) :=
      mul_le_mul_of_nonneg_left (sum_compatible_geometricMoment_le isV hA hB endpoint) hD
    _ = _ := by ring

end Problem335.MomentPairing

end

end OAI
