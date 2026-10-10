import OAI.NumberTheory.Ostmann.Arithmetic.MovingRoundedCellSums
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularTemplate

namespace OAI

/-! # The selected cell endpoints in the actual indexed regular template -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingCellLower (n : ℕ) (centers : List ℝ)
    (i : TreeLeafIndex n × Fin centers.length) : ℝ := centers.get i.2 - 1

theorem movingCellLower_sum (n : ℕ) (centers : List ℝ) :
    (∑ i, movingCellLower n centers i) =
      (2 ^ n : ℕ) * (centers.map (fun c => c - 1)).sum := by
  have hs : (∑ i : Fin centers.length, (centers.get i - 1)) =
      (centers.map (fun c => c - 1)).sum := by
    have he : List.ofFn (fun i : Fin centers.length => centers.get i - 1) =
        centers.map (fun c => c - 1) := by
      change List.ofFn ((fun c : ℝ => c - 1) ∘ centers.get) = _
      rw [← List.map_ofFn, List.ofFn_get]
    simpa only [List.sum_ofFn] using congrArg List.sum he
  simp only [movingCellLower, Fintype.sum_prod_type]
  change (∑ _j : TreeLeafIndex n, (∑ i : Fin centers.length, (centers.get i - 1))) = _
  simp_rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, card_treeLeafIndex, nsmul_eq_mul]

theorem movingCellLower_prime_bound (n : ℕ) (centers : List ℝ)
    (i : TreeLeafIndex n × Fin centers.length) (q : ℕ)
    (h : centers.get i.2 ≤ Real.log (q : ℝ)) (hq : 0 < q) :
    Real.exp (movingCellLower n centers i) ≤ (q : ℝ) := by
  apply (Real.le_log_iff_exp_le (by exact_mod_cast hq)).mp
  dsimp only [movingCellLower]
  linarith

end Ostmann

end OAI
