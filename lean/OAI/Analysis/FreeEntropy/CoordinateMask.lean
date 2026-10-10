import OAI.Analysis.FreeEntropy.GaussianBlockTail

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 def coordinateMask (m : Finset ι) (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
    WithLp.toLp 2 (fun i => if i∈m then x i else 0)
 theorem coordinateMask_sq (m : Finset ι) (x : EuclideanSpace ℝ ι) :
    ‖coordinateMask m x‖^2=∑i∈m,x i^2 := by
  classical
  simp [coordinateMask,EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]
 theorem coordinateMask_norm_le (m : Finset ι) (x : EuclideanSpace ℝ ι) :
    ‖coordinateMask m x‖≤‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [coordinateMask_sq,EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs,sq_abs]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ m) (fun i _ _ => sq_nonneg _)
 def coordinateMaskLinear (m : Finset ι) : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun := coordinateMask m
  map_add' x y := by ext i; simp only [coordinateMask,PiLp.toLp_apply,PiLp.add_apply]; split_ifs <;> simp
  map_smul' r x := by ext i; simp only [coordinateMask,PiLp.toLp_apply,PiLp.smul_apply,smul_eq_mul,RingHom.id_apply]; split_ifs <;> simp
 theorem coordinateMask_continuous (m : Finset ι) : Continuous (coordinateMask m) :=
  (coordinateMaskLinear m).continuous_of_finiteDimensional
 theorem coordinateMask_norm_sub (m : Finset ι) (x y : EuclideanSpace ℝ ι) :
    |‖coordinateMask m x‖-‖coordinateMask m y‖|≤‖x-y‖ := by
  calc
    _ ≤ ‖coordinateMask m x-coordinateMask m y‖ := abs_norm_sub_norm_le _ _
    _ = ‖coordinateMask m (x-y)‖ := by exact congrArg norm (map_sub (coordinateMaskLinear m) x y).symm
    _ ≤ _ := coordinateMask_norm_le _ _
 theorem normalLaw_coordinateMask_tail (m : Finset ι) {s r : ℝ} (hs : 0<s) (hr : 0≤r) :
    (normalLaw s) {x | r≤‖coordinateMask m x‖} ≤
      ENNReal.ofReal (Real.exp (-r^2/(4*s))*Real.sqrt 2^m.card) := by
  have he : {x : EuclideanSpace ℝ ι | r≤‖coordinateMask m x‖}={x | r^2≤∑i∈m,x i^2} := by
    ext x
    simp only [Set.mem_ofPred_eq,← coordinateMask_sq]
    exact (sq_le_sq₀ hr (norm_nonneg _)).symm
  rw [he]
  exact normalLaw_mask_tail m hs _
end FiniteEntropySeparation

end

end OAI
