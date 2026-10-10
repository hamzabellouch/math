import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.TimeChainSplit
import OAI.Probability.SKBarriers.SpinGlass.FinitePrefix

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def chainQuadraticPenalty : ℝ → List (ℝ × ℝ≥0) → ℝ
  | _,[] => 0
  | s,p::ps => p.1*((s+(p.2:ℝ))^2-s^2)+chainQuadraticPenalty (s+p.2) ps

theorem chainQuadraticPenalty_append (s : ℝ) (l r : List (ℝ × ℝ≥0)) :
    chainQuadraticPenalty s (l++r)=chainQuadraticPenalty s l+
      chainQuadraticPenalty (s+chainDuration l) r := by
  induction l generalizing s with
  | nil => simp [chainQuadraticPenalty,chainDuration]
  | cons p l ih =>
    simp only [List.cons_append,chainQuadraticPenalty,ih]
    rw [chainDuration_cons,NNReal.coe_add]
    simp only [add_assoc]

theorem chainQuadraticPenalty_zero (s m : ℝ) (l : List (ℝ × ℝ≥0)) :
    chainQuadraticPenalty s ((m,0)::l)=chainQuadraticPenalty s l := by simp [chainQuadraticPenalty]

theorem chainQuadraticPenalty_singleton (s m : ℝ) (t : ℝ≥0) :
    chainQuadraticPenalty s [(m,t)]=m*((s+t)^2-s^2) := by simp [chainQuadraticPenalty]

theorem chainDuration_ofFn (n : ℕ) (p : Fin n → ℝ × ℝ≥0) :
    chainDuration (List.ofFn p)=∑ i, (p i).2 := by
  simp [chainDuration,List.map_ofFn,List.sum_ofFn]

theorem finitePrefix_differences {k : ℕ} (t : Fin (k+2) → ℝ) (j : Fin (k+1)) :
    finitePrefix (fun i => t i.succ-t i.castSucc) j=t j.succ-t 0 := by
  refine Fin.induction ?_ (fun i ih => ?_) j
  · simp [finitePrefix]
  · rw [finitePrefix_succ,ih]
    simp only [Fin.castSucc_succ]
    ring

theorem finitePrefix_castSucc {n : ℕ} (v : Fin (n+1) → ℝ) (i : Fin n) :
    finitePrefix v i.castSucc=finitePrefix (fun l => v l.castSucc) i := by
  unfold finitePrefix
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.castSucc_le_castSucc_iff,
    ite_eq_right (not_le.mpr (Fin.castSucc_lt_last i)),add_zero]

theorem chainQuadraticPenalty_ofFn_zero (n : ℕ) (p : Fin (n+1) → ℝ × ℝ≥0)
    (hp : (p 0).2=0) :
    chainQuadraticPenalty 0 (List.ofFn p)=
      ∑ i : Fin n, (p i.succ).1*
        ((finitePrefix (fun l => ((p l).2:ℝ)) i.succ)^2-
         (finitePrefix (fun l => ((p l).2:ℝ)) i.castSucc)^2) := by
  induction n with
  | zero => simp [List.ofFn_succ,chainQuadraticPenalty,hp]
  | succ n ih =>
    rw [List.ofFn_succ',List.concat_eq_append,chainQuadraticPenalty_append]
    rw [ih (fun i => p i.castSucc) (by simpa using hp)]
    rw [chainQuadraticPenalty_singleton,zero_add,chainDuration_ofFn]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    simp only [← Fin.castSucc_succ,Fin.succ_last,finitePrefix_castSucc,finitePrefix_last,NNReal.coe_sum]
    congr 1
    rw [show (∑ l : Fin (n+2), ((p l).2:ℝ))=
      (∑ l : Fin (n+1), ((p l.castSucc).2:ℝ))+((p (Fin.last (n+1))).2:ℝ) from Fin.sum_univ_castSucc _]

end SK.Analytic

end
end

end OAI
