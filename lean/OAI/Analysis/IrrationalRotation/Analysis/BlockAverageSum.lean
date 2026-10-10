import OAI.Analysis.IrrationalRotation.Analysis.BlockReciprocalSum

namespace OAI

open scoped BigOperators
namespace InvariantProjection.IndependentAngles

theorem tsum_fin_block_average {m : ℕ} (hm : 0 < m) (u : ℝ) :
    (∑' _i : Fin m, u / (m : ℝ)) = u := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

theorem summable_block_average (m : ℕ → ℕ) (hm : ∀ s, 0 < m s)
    (u : ℕ → ℝ) (hu : ∀ s, 0 ≤ u s) (hsum : Summable u) :
    Summable (fun i : Σ s, Fin (m s) => u i.1 / (m i.1 : ℝ)) := by
  apply (summable_sigma_of_nonneg (fun i =>
    div_nonneg (hu i.1) (Nat.cast_nonneg _))).2
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simpa only [tsum_fin_block_average (hm _)] using hsum

theorem tsum_block_average (m : ℕ → ℕ) (hm : ∀ s, 0 < m s)
    (u : ℕ → ℝ) (hu : ∀ s, 0 ≤ u s) (hsum : Summable u) :
    (∑' i : Σ s, Fin (m s), u i.1 / (m i.1 : ℝ)) = ∑' s, u s := by
  rw [(summable_block_average m hm u hu hsum).tsum_sigma'
    (fun _ => (hasSum_fintype _).summable)]
  simp only [tsum_fin_block_average (hm _)]

theorem enumerated_block_average {ι : Type*} (m : ℕ → ℕ) (hm : ∀ s, 0 < m s)
    (u : ℕ → ℝ) (hu : ∀ s, 0 ≤ u s) (hsum : Summable u)
    (e : ι ≃ Σ s, Fin (m s)) :
    Summable (fun i => u (e i).1 / (m (e i).1 : ℝ)) ∧
    (∑' i, u (e i).1 / (m (e i).1 : ℝ)) = ∑' s, u s := by
  constructor
  · exact e.summable_iff.mpr (summable_block_average m hm u hu hsum)
  · exact (e.tsum_eq _).trans (tsum_block_average m hm u hu hsum)

end InvariantProjection.IndependentAngles

end OAI
