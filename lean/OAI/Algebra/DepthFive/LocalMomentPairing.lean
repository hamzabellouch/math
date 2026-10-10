import OAI.Algebra.DepthFive.SecondMomentNormalization
import OAI.Algebra.DepthFive.FactorialGeometricValue

namespace OAI

/-! The actual geometric local table agrees with the canonical pairing
normalization, including coincident coordinates in the normal class. -/

noncomputable section
open scoped BigOperators

namespace Problem335.MomentPairing

open Pairings

theorem localGeometricMass_eq_moment {γ : Type*} [DecidableEq γ]
    (side : Bool) (A B : ℝ) (x : Labels γ) :
    LocalMoments.localGeometricMass side (if side then A else B) x.p x.q x.r =
      LocalMomentWeights.moment side (isDiagonal (classifyLayer x))
        (coincides x) A B := by
  classical
  cases side <;> by_cases hpq : x.p = x.q <;>
    simp [LocalMoments.localGeometricMass, LocalMoments.normalGeometricMass,
      LocalMoments.diagonalGeometricMass, LocalMomentWeights.moment,
      classifyLayer, isDiagonal, coincides, hpq]

/-- No compatibility assumption is needed for this algebraic identity: the
canonical class always chooses the normal branch precisely when `p=q`. -/
theorem prod_localGeometricMass_eq {γ : Type*} [DecidableEq γ] {L : ℕ}
    (side : Fin (L + 1) → Bool) (A B : ℝ)
    (endpoint : γ) (x : Fin L → Labels γ) :
    (∏ t, LocalMoments.localGeometricMass (side t) (if side t then A else B)
      (layerLabels endpoint x t).p (layerLabels endpoint x t).q
      (layerLabels endpoint x t).r) =
    pathGeometricMoment side A B endpoint (classifyWord endpoint x) x := by
  unfold pathGeometricMoment classifyWord
  apply Finset.prod_congr rfl
  intro t _
  exact localGeometricMass_eq_moment _ _ _ _

theorem prod_localGeometricMass_eq_normalized {γ : Type*} [DecidableEq γ] {L : ℕ}
    (side : Fin (L + 1) → Bool) {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (endpoint : γ) (x : Fin L → Labels γ) :
    (∏ t, LocalMoments.localGeometricMass (side t) (if side t then A else B)
      (layerLabels endpoint x t).p (layerLabels endpoint x t).q
      (layerLabels endpoint x t).r) =
    pathMean side A B ^ 2 * pathWeight side (A / (A + 1)) (B / (B + 1))
      endpoint (classifyWord endpoint x) x := by
  rw [prod_localGeometricMass_eq, pathGeometricMoment_eq side hA hB]

/-- Concrete input interface for occupation averaging: the geometric RHS is
the actual local polynomial table, rather than an assumed pairing weight. -/
theorem sum_sources_local_moments_le {ι γ : Type*} [Fintype ι]
    [Fintype γ] [DecidableEq γ] {L : ℕ}
    (side : Fin (L + 1) → Bool) {A B D : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hD : 0 ≤ D) (endpoint : γ)
    (C : ι → (Fin L → Labels γ) → ℝ)
    (hexpect : ∀ x, Compatible endpoint x →
      (∑ i, C i x) ≤ D *
        ∏ t, LocalMoments.localGeometricMass (side t) (if side t then A else B)
          (layerLabels endpoint x t).p (layerLabels endpoint x t).q
          (layerLabels endpoint x t).r) :
    (∑ i, ∑ x : {x : Fin L → Labels γ // Compatible endpoint x}, C i x.1) ≤
      D * pathMean side A B ^ 2 *
        ∑ τ : Fin (L + 1) → Kind, ∑ x : RelaxedPaths γ endpoint τ,
          pathWeight side (A / (A + 1)) (B / (B + 1)) endpoint τ x.1 := by
  apply sum_sources_compatible_le side hA hB hD endpoint C
  intro x hx
  simpa only [prod_localGeometricMass_eq] using hexpect x hx

end Problem335.MomentPairing

end

end OAI
