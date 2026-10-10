import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.AngularOperator

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set
open scoped ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma symbol_mul_derivative_boundND (f g : SmoothFunctionND V) (M : ℕ)
    {C D A : ℝ} (hC : 0≤C) (_hD : 0≤D) (hA : 0≤A) (w : V)
    (hf : ∀ j ≤ M, ‖iteratedFDeriv ℝ j f.1 w‖ ≤ C*A^j)
    (hg : ∀ j ≤ M, ‖iteratedFDeriv ℝ j g.1 w‖ ≤ D*A^j) :
    ‖iteratedFDeriv ℝ M (smoothMulND f g).1 w‖ ≤ C*D*(2*A)^M := by
  calc
    _ ≤ ∑ j ∈ Finset.range (M+1), (M.choose j:ℝ)*‖iteratedFDeriv ℝ j f.1 w‖*
        ‖iteratedFDeriv ℝ (M-j) g.1 w‖ :=
      norm_iteratedFDeriv_mul_le (show ContDiff ℝ ∞ f.1 from f.2) (show ContDiff ℝ ∞ g.1 from g.2) w (by exact_mod_cast (le_top : (M:ℕ∞)≤⊤))
    _ ≤ ∑ j ∈ Finset.range (M+1), (M.choose j:ℝ)*(C*A^j)*(D*A^(M-j)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hle : j≤M := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      gcongr
      · exact hf j hle
      · exact hg (M-j) (Nat.sub_le _ _)
    _ = C*D*(A+A)^M := by
      rw [add_pow,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by congr 2; ring

lemma symbol_const_mul_derivative_boundND (f : SmoothFunctionND V) (c : ℂ)
    (hc : ‖c‖≤1) (j : ℕ) (w : V) :
    ‖iteratedFDeriv ℝ j (fun w => c*f.1 w) w‖ ≤ ‖iteratedFDeriv ℝ j f.1 w‖ := by
  have he := iteratedFDeriv_const_smul_apply (a:=c) (x:=w) (i:=j)
    ((show ContDiff ℝ ∞ f.1 from f.2).contDiffAt.of_le (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤)))
  change ‖iteratedFDeriv ℝ j (c • f.1) w‖ ≤ _
  rw [he,norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) hc

end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI
