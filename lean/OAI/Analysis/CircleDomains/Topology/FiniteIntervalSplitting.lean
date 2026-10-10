import OAI.Analysis.CircleDomains.Selection.FiniteGapIntegration

namespace OAI

/-! Splitting a line integral into its actual finite gaps and closed holes.
Only endpoint sets of zero length are ignored. -/
open Set Function MeasureTheory
namespace CircleDomainRigidity

 theorem sum_integral_gaps_and_holes (n : ℕ) (a b : Fin (n + 1) → ℝ) (h : ℝ → ℝ)
    (hia : ∀ i, IntervalIntegrable h volume (a 0) (a i))
    (hib : ∀ i, IntervalIntegrable h volume (a 0) (b i)) :
    (∑ i, ∫ x in a i..b i, h x) +
      (∑ i : Fin n, ∫ x in b i.castSucc..a i.succ, h x) =
      ∫ x in a 0..b (Fin.last n), h x := by
  let F := fun t => ∫ x in a 0..t, h x
  have heq {u v : ℝ} (hu : IntervalIntegrable h volume (a 0) u)
      (hv : IntervalIntegrable h volume (a 0) v) :
      (∫ x in u..v, h x) = F v - F u :=
    (intervalIntegral.integral_interval_sub_left hv hu).symm
  simp_rw [heq (hia _) (hib _), heq (hib _) (hia _)]
  rw [sum_gap_differences n (fun i => F (a i)) (fun i => F (b i)), add_assoc,
    ← Finset.sum_add_distrib]
  have hz : (∑ i : Fin n, ((F (b i.castSucc) - F (a i.succ)) +
      (F (a i.succ) - F (b i.castSucc)))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    ring
  rw [hz, add_zero]

end CircleDomainRigidity

end OAI
