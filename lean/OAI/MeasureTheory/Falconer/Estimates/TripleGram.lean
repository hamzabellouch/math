import OAI.MeasureTheory.Falconer.Angular.GnomonicChart
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.PosDef

namespace OAI

/-! # Gram determinants for the endpoint's three original chart directions -/

namespace Falconer
variable {n : ℕ}

noncomputable def tripleGram {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c : E) : ℝ := (Matrix.gram ℝ ![a,b,c]).det

private def gramPolynomial (aa bb cc ab ac bc : ℝ) : ℝ :=
  aa*bb*cc+2*ab*ac*bc-aa*bc^2-bb*ac^2-cc*ab^2

theorem tripleGram_polynomial {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c : E) : tripleGram a b c =
      gramPolynomial (inner ℝ a a) (inner ℝ b b) (inner ℝ c c)
        (inner ℝ a b) (inner ℝ a c) (inner ℝ b c) := by
  simp only [tripleGram,Matrix.det_fin_three,Matrix.gram_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  rw [real_inner_comm b a,real_inner_comm c a,real_inner_comm c b]
  unfold gramPolynomial
  ring

theorem tripleGram_nonnegative {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c : E) : 0 ≤ tripleGram a b c :=
  (Matrix.posSemidef_gram ℝ ![a,b,c]).det_nonneg

theorem tripleGram_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c : E) (r s t : ℝ) :
    tripleGram (r • a) (s • b) (t • c) = (r*s*t)^2*tripleGram a b c := by
  rw [tripleGram_polynomial,tripleGram_polynomial]
  simp only [inner_smul_left,inner_smul_right,conj_trivial]
  unfold gramPolynomial
  ring

theorem northLift_inner (x y : Space n) :
    inner ℝ (northLift x) (northLift y) = 1+inner ℝ x y := by
  rw [PiLp.inner_apply,PiLp.inner_apply,Fin.sum_univ_succ]
  simp only [northLift_zero,northLift_succ,RCLike.inner_apply,conj_trivial,map_one,one_mul]

theorem northLift_tripleGram_identity (p q r : Space n) :
    tripleGram (northLift p) (northLift q) (northLift r) =
      tripleGram p (q-p) (r-p) + ‖q-p‖^2*‖r-p‖^2-(inner ℝ (q-p) (r-p))^2 := by
  rw [tripleGram_polynomial,tripleGram_polynomial]
  simp only [northLift_inner,← real_inner_self_eq_norm_sq,inner_sub_left,inner_sub_right,
    real_inner_comm]
  unfold gramPolynomial
  ring

theorem northLift_tripleGram_lower (p q r : Space n) :
    ‖q-p‖^2*‖r-p‖^2-(inner ℝ (q-p) (r-p))^2 ≤
      tripleGram (northLift p) (northLift q) (northLift r) := by
  rw [northLift_tripleGram_identity]
  linarith [tripleGram_nonnegative p (q-p) (r-p)]

theorem gnomonic_tripleGram (p q r : Space n) :
    tripleGram (gnomonicChart p : Space (n+1)) (gnomonicChart q : Space (n+1))
      (gnomonicChart r : Space (n+1)) =
    (‖northLift p‖⁻¹*‖northLift q‖⁻¹*‖northLift r‖⁻¹)^2*
      tripleGram (northLift p) (northLift q) (northLift r) := by
  exact tripleGram_smul _ _ _ _ _ _

end Falconer

end OAI
