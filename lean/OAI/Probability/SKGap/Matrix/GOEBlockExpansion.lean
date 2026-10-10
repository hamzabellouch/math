import Mathlib
import OAI.Probability.SKGap.Localization.TruncationGoodSet
import OAI.Probability.SKGap.Matrix.GOERegression
import OAI.Probability.SKGap.Matrix.GOEBilinearCov

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma symmetric_dot_mulVec (W : Matrix ι ι ℝ) (hW : Wᵀ=W) (u : ι → ℝ) (k : ι) :
    u⬝ᵥ(W*ᵥPi.single k 1)=(W*ᵥu) k := by
  rw [Matrix.mulVec_single_one]
  change (∑ i,u i*W i k)=∑ i,W k i*u i
  apply Finset.sum_congr rfl
  intro i _
  have h := congrArg (fun M : Matrix ι ι ℝ => M k i) hW
  simpa only [Matrix.transpose_apply,mul_comm] using congrArg (fun a => a*u i) h

theorem goeBlockResidual_expand (r κ ell : ℝ) (u : ι → ℝ)
    (g : MatrixCoordinates ι → ℝ) :
    goeBlockResidual r κ ell u g=goeMatrix r g+
      (κ-1) • (vecMulVec u (goeMatrix r g*ᵥu)+vecMulVec (goeMatrix r g*ᵥu) u)+
      ((ell-2*κ+1)*goeBilinear r u u g) • vecMulVec u u := by
  ext i k
  simp only [goeBlockResidual,goeBilinear,unitRow,Matrix.mulVec_add,Matrix.mulVec_smul,
    dotProduct_add,add_dotProduct,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    single_one_dotProduct,Matrix.mulVec_single_one,Matrix.add_apply,
    Matrix.smul_apply,vecMulVec_apply]
  have h := symmetric_dot_mulVec (goeMatrix r g) (goeMatrix_transpose _ _) u k
  simp only [Matrix.mulVec_single_one] at h
  rw [h]
  change _+_ = _
  dsimp only [Matrix.col, Matrix.transpose_apply]
  ring

theorem goeRegressionCoefficient_block_mean {r v c : ℝ} (hr : 0 ≤ r) (hv : 0 < v)
    {u : ι → ℝ} (hu : u⬝ᵥu=1) (z : ι → ℝ) :
    (fun i k => (goeRegressionCoefficient r v (c • u)*ᵥz) (i,k))=
      vecMulVec u ((r*c/(r*c^2+v)) • (z-(u⬝ᵥz) • u))+
      vecMulVec ((r*c/(r*c^2+v)) • (z-(u⬝ᵥz) • u)) u+
      (2*r*c/(v+2*r*c^2)*(u⬝ᵥz)) • vecMulVec u u := by
  have hs : r*c^2+v ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos (mul_nonneg hr (sq_nonneg c)) hv)
  have hS : v+2*r*c^2 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hv (by positivity))
  ext i k
  change (goeRegressionCoefficient r v (c • u)*ᵥz) (i,k)=
    u i*(r*c/(r*c^2+v)*(z k-(u⬝ᵥz)*u k))+
    (r*c/(r*c^2+v)*(z i-(u⬝ᵥz)*u i))*u k+
    (2*r*c/(v+2*r*c^2)*(u⬝ᵥz))*(u i*u k)
  rw [goeRegressionCoefficient_mulVec]
  simp only [smul_dotProduct,dotProduct_smul,smul_eq_mul,hu,mul_one,Pi.smul_apply]
  have hcc : c*c=c^2 := by ring
  rw [hcc]
  field_simp
  ring

end SKGap
end
end

end OAI
