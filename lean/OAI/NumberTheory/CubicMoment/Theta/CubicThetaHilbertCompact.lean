import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHilbertDiagonal

namespace OAI

/-! Compactness of a diagonal cusp operator whose compact radial blocks
tend to zero in operator norm. -/
noncomputable section
open Set
namespace CubicFirstMoment

variable {ι H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

theorem cubicThetaHilbertDiagonal_compact (T : ι → H →L[ℂ] H) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) (hc : ∀ i, IsCompactOperator (T i))
    (htail : ∀ ε : ℝ, 0<ε → ∃ s : Finset ι, ∀ i, i∉s → ‖T i‖ ≤ ε) :
    IsCompactOperator (cubicThetaHilbertDiagonal T hC hT) := by
  have hm : cubicThetaHilbertDiagonal T hC hT ∈
      closure {S : lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2 | IsCompactOperator S} := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨s,hs⟩ := htail (ε/2) (by positivity)
    refine ⟨cubicThetaHilbertFiniteDiagonal T s,cubicThetaHilbertFiniteDiagonal_compact T hc s,?_⟩
    rw [dist_eq_norm]
    exact (cubicThetaHilbertDiagonal_tail_norm T hC hT s (by positivity) hs).trans_lt (by linarith)
  rwa [isClosed_setOfPred_isCompactOperator.closure_eq] at hm

end CubicFirstMoment

end

end OAI
