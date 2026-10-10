import Mathlib
import OAI.Probability.SKRatio.Matrices.LinEquiv
import OAI.Probability.SKRatio.Matrices.ClosedConvexNonempty

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
namespace SKRatioGaussian.ComplexMatrix
open Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def vectorize : Matrix ι ι ℂ →ₗ[ℝ] EuclideanSpace ℂ (ι × ι) where
  toFun M := WithLp.toLp 2 (fun p => M p.1 p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma vectorize_norm (M : Matrix ι ι ℂ) : ‖vectorize M‖ = ‖M‖ := by
  have hh : ‖vectorize M‖^2 = ‖M‖^2 := by
    rw [EuclideanSpace.norm_sq_eq,frobenius_sq]
    change (∑ p : ι × ι, ‖M p.1 p.2‖^2) = ∑ i, ∑ k, ‖M i k‖^2
    exact Fintype.sum_prod_type _
  nlinarith [norm_nonneg (vectorize M),norm_nonneg M]

noncomputable instance frobeniusInnerProduct : InnerProductSpace ℝ (Matrix ι ι ℂ) where
  inner M N := inner ℝ (vectorize M) (vectorize N)
  norm_sq_eq_re_inner M := by
    change ‖M‖^2 = inner ℝ (vectorize M) (vectorize M)
    rw [real_inner_self_eq_norm_sq,vectorize_norm]
  conj_inner_symm M N := by simp only [conj_trivial]; exact real_inner_comm _ _
  add_left M N P := by rw [map_add,inner_add_left]
  smul_left M N r := by rw [map_smul,inner_smul_left]

noncomputable def hermitianBall (R : ℝ) : Set (Matrix ι ι ℂ) :=
  {M | Mᴴ = M ∧ opNorm M ≤ R}

lemma hermitianBall_closed (R : ℝ) : IsClosed (hermitianBall (ι := ι) R) := by
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop : Continuous (fun M : Matrix ι ι ℂ => Mᴴ)) continuous_id
  · exact isClosed_le continuous_lin.norm continuous_const

lemma hermitianBall_convex (R : ℝ) : Convex ℝ (hermitianBall (ι := ι) R) := by
  intro M hM N hN a b ha hb hab
  constructor
  · simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_smul,hM.1,hN.1,star_trivial]
  · have he : lin (a • M+b • N) = a • lin M+b • lin N := by
      exact (linEquiv (ι := ι)).toLinearMap.restrictScalars ℝ |>.map_add _ _ |>.trans
        (by rw [LinearMap.map_smul,LinearMap.map_smul]; rfl)
    change ‖lin (a • M+b • N)‖ ≤ R
    rw [he]
    calc
      _ ≤ ‖a • lin M‖+‖b • lin N‖ := norm_add_le _ _
      _ = a*opNorm M+b*opNorm N := by simp [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb,opNorm]
      _ ≤ a*R+b*R := add_le_add (mul_le_mul_of_nonneg_left hM.2 ha) (mul_le_mul_of_nonneg_left hN.2 hb)
      _ = R := by rw [← add_mul,hab,one_mul]

lemma hermitianBall_good {R : ℝ} (hR : 0 ≤ R) : SKRatioGaussian.ClosedConvexNonempty (hermitianBall (ι := ι) R) where
  nonempty := ⟨0,by simp [hermitianBall,opNorm,lin,hR]⟩
  complete := (hermitianBall_closed R).isComplete
  convex := by convert hermitianBall_convex (ι := ι) R using 0

noncomputable def matrixProject (R : ℝ) (hR : 0 ≤ R) : Matrix ι ι ℂ → Matrix ι ι ℂ :=
  SKRatioGaussian.convexProject (hermitianBall_good hR)

lemma matrixProject_lipschitz (R : ℝ) (hR : 0 ≤ R) :
    LipschitzWith 1 (matrixProject (ι := ι) R hR) :=
  SKRatioGaussian.convexProject_lipschitz _

lemma matrixProject_bound (R : ℝ) (hR : 0 ≤ R) (M : Matrix ι ι ℂ) :
    (matrixProject R hR M)ᴴ = matrixProject R hR M ∧ opNorm (matrixProject R hR M) ≤ R :=
  SKRatioGaussian.convexProject_mem (hermitianBall_good (ι := ι) hR) M

lemma matrixProject_eq_self (R : ℝ) (hR : 0 ≤ R) (M : Matrix ι ι ℂ)
    (hM : Mᴴ = M) (hMR : opNorm M ≤ R) : matrixProject R hR M = M :=
  SKRatioGaussian.convexProject_eq_self _ ⟨hM,hMR⟩

end SKRatioGaussian.ComplexMatrix

end
end
end
end
end
end
end
end
end
end

end OAI
