import OAI.Analysis.TreePotential.NormIdentities

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials.CostHeads

/-- The optimized square-root clipping bound. -/
theorem linear_head_tail_clipping_optimized (A : FiniteOuterHead) (x y : LinearOuter)
    (hx : linearOuterHead A.nodes A.initial x=x)
    (hy : linearOuterHead A.nodes A.initial y=0) :
    Real.sqrt (‖x‖^2+‖y‖^2/16) ≤ max ‖x+y‖ ‖x-y‖ := by
  have he := linearOuter_midpoint_sq A.nodes A.initial x y hx
  rw [hy,sub_zero] at he
  have hh := scalar_avg_sq_le (norm_nonneg (x+y)) (norm_nonneg (x-y))
    (le_max_left ‖x+y‖ ‖x-y‖) (le_max_right ‖x+y‖ ‖x-y‖)
  have hs := Real.sq_sqrt (show 0≤‖x‖^2+‖y‖^2/16 by positivity)
  have hn : 0 ≤ max ‖x+y‖ ‖x-y‖ := (norm_nonneg (x+y)).trans (le_max_left _ _)
  nlinarith [Real.sqrt_nonneg (‖x‖^2+‖y‖^2/16)]

end BoundedTreePotentials.CostHeads

namespace BoundedTreePotentials.Dyadic

section

lemma histories_length (k : ℕ) : (histories k).length=2^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [histories,List.length_flatMap,ih,pow_succ]

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def uniformVectorAverage (k : ℕ) (f : List Bool → E) : E :=
  ((2:ℝ)^k)⁻¹ • ((histories k).map f).sum

lemma uniformVectorAverage_succ (k : ℕ) (f : List Bool → E) :
    uniformVectorAverage (k+1) f=
      uniformVectorAverage k (fun w => (1/2:ℝ) • (f (false::w)+f (true::w))) := by
  have he (l : List (List Bool)) :
      ((l.flatMap (fun w => [false::w,true::w])).map f).sum =
      (2:ℝ) • ((l.map (fun w => (1/2:ℝ) • (f (false::w)+f (true::w)))).sum) := by
    induction l with
    | nil => simp
    | cons w l ih =>
      simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,
        List.map_nil,List.sum_cons,List.sum_nil,add_zero,ih]
      module
  simp only [uniformVectorAverage,histories,he,pow_succ,mul_inv_rev,smul_smul]
  congr 1
  ring

/-- An explicit average with exactly 2^k equally weighted future branches. -/
theorem conditionalMean_eq_uniform (W : List Bool → E) (k : ℕ) (w : List Bool) :
    conditionalMean W k w=
      ((2:ℝ)^k)⁻¹ • (((histories k).map (fun v => W (v++w))).sum) := by
  change conditionalMean W k w=uniformVectorAverage k (fun v => W (v++w))
  induction k generalizing W w with
  | zero => simp [uniformVectorAverage,histories,conditionalMean]
  | succ k ih =>
    rw [conditionalMean_succ_front,ih,uniformVectorAverage_succ]
    rfl

end

lemma histories_nodup (k : ℕ) : (histories k).Nodup := by
  induction k with
  | zero => simp [histories]
  | succ k ih =>
    rw [histories,List.nodup_flatMap]
    refine ⟨fun w _ => by simp,ih.imp ?_⟩
    intro a b hab
    simp [Function.onFun,List.disjoint_left,hab]
end BoundedTreePotentials.Dyadic

end

end OAI
