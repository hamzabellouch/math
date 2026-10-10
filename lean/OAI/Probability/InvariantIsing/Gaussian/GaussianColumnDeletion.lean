import OAI.Probability.InvariantIsing.Gaussian.GaussianColumnProductLaw
import OAI.Probability.InvariantIsing.Gaussian.GaussianGramResolventEquation
import OAI.Probability.InvariantIsing.Gaussian.HermitianGaussianQuadratic

namespace OAI

/-! Deleting a column removes all dependence on that Gaussian coordinate. -/
noncomputable section
open Matrix
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing

lemma gaussianGramLeaveOneOut_congr {N m : ℕ} (g h : Fin m → Fin N → ℝ) (j : Fin m)
    (he : ∀ l, l ≠ j → g l = h l) :
    gaussianGramLeaveOneOut (gaussianColumnArray g) j =
      gaussianGramLeaveOneOut (gaussianColumnArray h) j := by
  unfold gaussianGramLeaveOneOut
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [gaussianColumnArray_column,gaussianColumnArray_column,he l (Finset.mem_erase.mp hl).1]

lemma gaussianGramLeaveOneOut_insertNth {N m : ℕ} (j : Fin (m+1))
    (x y : Fin N → ℝ) (g : Fin m → Fin N → ℝ) :
    gaussianGramLeaveOneOut (gaussianColumnArray (j.insertNth x g)) j =
      gaussianGramLeaveOneOut (gaussianColumnArray (j.insertNth y g)) j := by
  apply gaussianGramLeaveOneOut_congr
  intro l hl
  obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hl
  simp only [Fin.insertNth_apply_succAbove]

lemma gaussianGramColumnQuadratic_eq {N m : ℕ} (t : ℝ) (g : Fin m → Fin N → ℝ) (j : Fin m) :
    gaussianGramColumnQuadratic t (gaussianColumnArray g) j =
      (1/(N : ℝ))*gaussianQuadraticForm
        (gaussianGramLeaveResolvent t (gaussianColumnArray g) j) (WithLp.toLp 2 (g j)) := by
  have he : ((Real.sqrt (N : ℝ))⁻¹)^2 = 1/(N : ℝ) := by
    rw [inv_pow,Real.sq_sqrt (Nat.cast_nonneg N),one_div]
  unfold gaussianGramColumnQuadratic gaussianPatternScaledColumn
  rw [gaussianColumnArray_column,Matrix.mulVec_smul,dotProduct_smul,smul_dotProduct]
  simp only [smul_eq_mul]
  unfold gaussianQuadraticForm
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  rw [dotProduct_comm]
  change _ = (1/(N : ℝ))*((gaussianGramLeaveResolvent t (gaussianColumnArray g) j *ᵥ g j) ⬝ᵥ g j)
  calc
    _ = ((Real.sqrt (N : ℝ))⁻¹)^2*((gaussianGramLeaveResolvent t (gaussianColumnArray g) j *ᵥ g j) ⬝ᵥ g j) := by ring
    _ = _ := by rw [he]

end InvariantIsing

end

end OAI
