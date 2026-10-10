import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.ConstantWeightStats

namespace OAI

section

noncomputable section
open scoped BigOperators
open Set
namespace SK.Analytic

theorem rawArea_bounds (l : List (ℝ × ℝ)) {a b : ℝ} (hm : ∀ p∈l,p.1∈Icc a b) :
    rawArea l∈Icc (a*rawVariance l) (b*rawVariance l) := by
  induction l with
  | nil => simp [rawArea,rawVariance]
  | cons p l ih =>
    have hp := hm p (List.mem_cons_self ..)
    have H := ih (fun z hz => hm z (List.mem_cons_of_mem _ hz))
    change p.1*p.2^2+rawArea l∈Icc (a*(p.2^2+rawVariance l)) (b*(p.2^2+rawVariance l))
    constructor
    · nlinarith [H.1,mul_le_mul_of_nonneg_right hp.1 (sq_nonneg p.2)]
    · nlinarith [H.2,mul_le_mul_of_nonneg_right hp.2 (sq_nonneg p.2)]

theorem rawPenalty_negative_bounds (l : List (ℝ × ℝ)) {a b q : ℝ}
    (hm : ∀ p∈l,p.1∈Icc a b) (hq : q+rawVariance l ≤ 0) :
    rawPenalty l q∈Icc (b*((q+rawVariance l)^2-q^2)) (a*((q+rawVariance l)^2-q^2)) := by
  induction l generalizing q with
  | nil => simp [rawPenalty,rawVariance,chainPotentialPenalty]
  | cons p l ih =>
    have hp := hm p (List.mem_cons_self ..)
    change q+(p.2^2+rawVariance l) ≤ 0 at hq
    have H := ih (fun z hz => hm z (List.mem_cons_of_mem _ hz)) (q:=q+p.2^2) (by linarith)
    have hsum : 2*q+p.2^2 ≤ 0 := by nlinarith [rawVariance_nonneg l,sq_nonneg p.2]
    have hΔ : (q+p.2^2)^2-q^2 ≤ 0 := by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg p.2) hsum]
    change p.1*((q+p.2^2)^2-q^2)+rawPenalty l (q+p.2^2)∈
      Icc (b*((q+(p.2^2+rawVariance l))^2-q^2)) (a*((q+(p.2^2+rawVariance l))^2-q^2))
    constructor
    · have H' := add_le_add (mul_le_mul_of_nonpos_right hp.2 hΔ) H.1
      convert H' using 1
      ring
    · have H' := add_le_add (mul_le_mul_of_nonpos_right hp.1 hΔ) H.2
      convert H' using 1
      ring

end SK.Analytic

end
end

end OAI
