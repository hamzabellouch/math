import Mathlib
import OAI.Probability.SKGap.Localization.SparseQuadratic

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma weighted_square_le {v z : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    (v*z)^2 ≤ v*z^2 := by
  have hh := mul_le_mul_of_nonneg_left hv1 hv
  have h := mul_le_mul_of_nonneg_right hh (sq_nonneg z)
  nlinarith only [h]

lemma weighted_square_le_small {v z η : ℝ} (hv : 0 ≤ v) (hvη : v ≤ η) :
    (v*z)^2 ≤ η*(v*z^2) := by
  have hh := mul_le_mul_of_nonneg_left hvη hv
  have h := mul_le_mul_of_nonneg_right hh (sq_nonneg z)
  nlinarith only [h]

lemma weighted_sparse_form (B : Matrix ι ι ℝ) (S : Finset ι) (v z : ι→ℝ)
    {η ε M : ℝ} (hη : 0 ≤ η) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hv : ∀ i,0 ≤ v i) (hv1 : ∀ i,v i ≤ 1) (hsmall : ∀ i,i ∉ S → v i ≤ η)
    (hB : ‖B‖ ≤ M)
    (hs : ∀ w : EuclideanSpace ℝ ι,(∀ i,i ∉ S → w i=0) →
      |⟪w,Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) B w⟫| ≤ ε*‖w‖^2) :
    |∑ i,∑ j,B i j*(v i*z i)*(v j*z j)| ≤
      (ε+M*(2*sqrt η+η))*(∑ i,v i*z i^2) := by
  let b : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i=>if i ∈ S then v i*z i else 0)
  let c : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i=>if i ∈ S then 0 else v i*z i)
  let q := ∑ i,v i*z i^2
  have hq : 0 ≤ q := Finset.sum_nonneg (fun i _=>mul_nonneg (hv i) (sq_nonneg _))
  have hb : ‖b‖^2 ≤ q := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    change (if i ∈ S then v i*z i else 0)^2 ≤ v i*z i^2
    split_ifs
    · exact weighted_square_le (hv i) (hv1 i)
    · exact (by simpa only [zero_pow (by omega : (2:ℕ) ≠ 0)] using mul_nonneg (hv i) (sq_nonneg (z i)))
  have hc : ‖c‖^2 ≤ η*q := by
    rw [EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    change (if i ∈ S then 0 else v i*z i)^2 ≤ η*(v i*z i^2)
    split_ifs with hi
    · exact (by simpa only [zero_pow (by omega : (2:ℕ) ≠ 0)] using mul_nonneg hη (mul_nonneg (hv i) (sq_nonneg (z i))))
    · exact weighted_square_le_small (hv i) (hsmall i hi)
  have hsb : |⟪b,Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) B b⟫| ≤ ε*q := by
    apply (hs b (by intro i hi;change (if i ∈ S then v i*z i else 0)=0;simp [hi])).trans
    exact mul_le_mul_of_nonneg_left hb hε
  have hh := sparse_quadratic_split (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) B) b c hq hη hM
    (by simpa only [Matrix.l2_opNorm_toEuclideanCLM] using hB) hb hc hsb
  have hbc : b+c=WithLp.toLp 2 (fun i=>v i*z i) := by
    ext i
    change (if i ∈ S then v i*z i else 0)+(if i ∈ S then 0 else v i*z i)=v i*z i
    split_ifs <;> simp
  rw [hbc,Matrix.inner_toEuclideanCLM] at hh
  have he : (WithLp.toLp 2 (fun i=>v i*z i) : EuclideanSpace ℝ ι) ⬝ᵥ
      B *ᵥ (WithLp.toLp 2 (fun i=>v i*z i) : EuclideanSpace ℝ ι)=
      ∑ i,∑ j,B i j*(v i*z i)*(v j*z j) := by
    simp only [dotProduct,Matrix.mulVec]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _;ring
  rwa [he] at hh
end SKGap

end
end

end OAI
