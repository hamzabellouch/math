import OAI.Analysis.PlanarPacking.TailHeadClose
import OAI.Analysis.PlanarPacking.TailBarrier

namespace OAI

namespace SharpPlanar
lemma exact_sign_tail (a : Bool) {s : ℝ} (hs : (83:ℝ)/2 ≤ s) :
    0 ≤ (if a then 1 else -1)*exactJet a 0 s := by
  obtain ⟨n,hn,hm,hP⟩:=tail_barrier_node hs
  have hR:=exact_head_lower a hs
  have he:=abs_le.mp (tailErrorJet_bound a n hn hs hm)
  have hp : 0 ≤ P s := (mul_nonneg (by norm_num : (0:ℝ) ≤ 17/25) (sq_nonneg _)).trans hP
  have hh := mul_le_mul_of_nonneg_left hR.le hp
  rw [exactJet_split,head_rational_factor a hs]
  cases a <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hh ⊢ <;>
    nlinarith [sq_nonneg (s-(n.val:ℝ))]
lemma H₁_nonpos_tail {s : ℝ} (hs : (83:ℝ)/2 ≤ s) : H₁ s ≤ 0 := by
  have hh:=exact_sign_tail false hs
  simpa only [exactJet,exactData,Bool.false_eq_true,ite_false,ite_true,Bool.not_false,
    H₁,← cardinal_eq_cardinalSeries,neg_one_mul,neg_nonneg] using hh
lemma H₂_nonneg_tail {s : ℝ} (hs : (83:ℝ)/2 ≤ s) : 0 ≤ H₂ s := by
  have hh:=exact_sign_tail true hs
  simpa only [exactJet,exactData,ite_true,ite_false,Bool.false_eq_true,Bool.not_true,
    H₂,← cardinal_eq_cardinalSeries,one_mul] using hh
end SharpPlanar

end OAI
