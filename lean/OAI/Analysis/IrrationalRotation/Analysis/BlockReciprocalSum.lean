import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

namespace OAI

open scoped BigOperators

namespace InvariantProjection.IndependentAngles

theorem tsum_fin_block_reciprocal {m : ℕ} (hm : 0 < m) (K : ℝ) :
    (∑' _i : Fin m, 1 / ((m : ℝ) * K)) = 1 / K := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  by_cases hK : K = 0
  · simp [hK]
  · field_simp

theorem summable_block_reciprocal (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K : ℕ → ℝ) (hK : ∀ j, 0 < K j)
    (hsum : Summable (fun j => 1 / K j)) :
    Summable (fun i : Σ j, Fin (m j) => 1 / ((m i.1 : ℝ) * K i.1)) := by
  apply (summable_sigma_of_nonneg (fun i => div_nonneg (by norm_num)
    (mul_nonneg (Nat.cast_nonneg _) (hK i.1).le))).2
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simpa only [tsum_fin_block_reciprocal (hm _) (K _)] using hsum

theorem tsum_block_reciprocal (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K : ℕ → ℝ) (hK : ∀ j, 0 < K j)
    (hsum : Summable (fun j => 1 / K j)) :
    (∑' i : Σ j, Fin (m j), 1 / ((m i.1 : ℝ) * K i.1)) = ∑' j, 1 / K j := by
  rw [(summable_block_reciprocal m hm K hK hsum).tsum_sigma' (fun _ => (hasSum_fintype _).summable)]
  simp only [tsum_fin_block_reciprocal (hm _) (K _)]

theorem enumerated_block_reciprocal {ι : Type*} (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K : ℕ → ℝ) (hK : ∀ j, 0 < K j)
    (hsum : Summable (fun j => 1 / K j)) (e : ι ≃ Σ j, Fin (m j)) :
    Summable (fun i => 1 / ((m (e i).1 : ℝ) * K (e i).1)) ∧
    (∑' i, 1 / ((m (e i).1 : ℝ) * K (e i).1)) = ∑' j, 1 / K j := by
  constructor
  · exact e.summable_iff.mpr (summable_block_reciprocal m hm K hK hsum)
  · calc
      (∑' i, 1 / ((m (e i).1 : ℝ) * K (e i).1)) =
          ∑' i : Σ j, Fin (m j), 1 / ((m i.1 : ℝ) * K i.1) := e.tsum_eq (fun i : Σ j, Fin (m j) => 1 / ((m i.1 : ℝ) * K i.1))
      _ = ∑' j, 1 / K j := tsum_block_reciprocal m hm K hK hsum

end InvariantProjection.IndependentAngles

end OAI
