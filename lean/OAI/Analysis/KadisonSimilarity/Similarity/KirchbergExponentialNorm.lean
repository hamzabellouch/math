import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

namespace OAI

/-! The exact exponential condition-number scaling used on page 61 of
Kirchberg's proof. -/

noncomputable section
namespace KadisonSimilarity

open NormedSpace
open scoped CStarAlgebra

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem exp_real_smul_eq_rpow (t : B) (ht : IsSelfAdjoint t) (s : ℝ) :
    exp (s • t) = (exp t) ^ s := by
  have hs : IsSelfAdjoint (s • t) := (IsSelfAdjoint.all s).smul ht
  rw [← CFC.real_exp_eq_normedSpace_exp hs, ← cfc_comp_const_mul s Real.exp t (by fun_prop) ht,
    ← CFC.real_exp_eq_normedSpace_exp ht,
    CFC.cfc_rpow (fun x _ => Real.exp_pos x) (by fun_prop) ht]
  congr 1
  funext x
  rw [mul_comm s x, Real.exp_mul]

theorem norm_exp_real_smul (t : B) (ht : IsSelfAdjoint t) {s : ℝ} (hs : 0 < s) :
    ‖exp (s • t)‖ = ‖exp t‖ ^ s := by
  rw [exp_real_smul_eq_rpow t ht s, CFC.norm_rpow _ hs ht.exp_nonneg]

/-- The product of the forward and inverse norms scales by the same power. -/
theorem exp_condition_real_smul (t : B) (ht : IsSelfAdjoint t) {s : ℝ} (hs : 0 < s) :
    ‖exp (s • (-t))‖ * ‖exp (s • t)‖ = (‖exp (-t)‖ * ‖exp t‖) ^ s := by
  rw [norm_exp_real_smul (-t) ht.neg hs, norm_exp_real_smul t ht hs,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]

end KadisonSimilarity

end

end OAI
