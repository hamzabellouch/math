import Mathlib
import OAI.Probability.SKGap.Localization.TAPVectorTaylor
import OAI.Probability.SKGap.Matrix.MatrixWhitening

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators MatrixOrder

lemma vectorNorm_sq_dot {n : ℕ} (x : Field n) : vectorNorm x^2=x⬝ᵥx := by
  rw [vectorNorm_sq]
  simp only [vectorSqNorm,dotProduct,pow_two]

lemma gram_energy {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (x : Field n) :
    x⬝ᵥ((Lᵀ*L)*ᵥx)=vectorNorm (L*ᵥx)^2 := by
  rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec,vectorNorm_sq_dot]

lemma regularizedGram_posDef {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ)
    {γ : ℝ} (hγ : 0 < γ) : (Lᵀ*L+γ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
  have hL : (Lᵀ*L).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self L
  exact Matrix.PosDef.posSemidef_add hL (Matrix.PosDef.one.smul hγ)

lemma squareRoot_energy {n : ℕ} (L R : Matrix (Fin n) (Fin n) ℝ)
    (hR : R.IsHermitian) (γ : ℝ) (hRR : R*R=Lᵀ*L+γ • 1) (x : Field n) :
    vectorNorm (R*ᵥx)^2=vectorNorm (L*ᵥx)^2+γ*vectorNorm x^2 := by
  have ht : Rᵀ=R := hR.eq
  rw [← gram_energy,ht,hRR,Matrix.add_mulVec,dotProduct_add,gram_energy,
    Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul,smul_eq_mul]
  simp only [vectorNorm_sq_dot]

theorem localGaussian_whitening {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, U.IsHermitian ∧ IsUnit U.det ∧
      U*(Lᵀ*L+γ • 1)*U=1 ∧
      (∀ g : Field n, vectorNorm (L*ᵥ(U*ᵥg)) ≤ vectorNorm g) ∧
      (∀ g : Field n, vectorNorm (U*ᵥg) ≤ vectorNorm g/sqrt γ) := by
  obtain ⟨R,hR,hRR,hu⟩ := positive_sqrt_data (regularizedGram_posDef L hγ)
  have hi : R⁻¹.IsHermitian := by
    change (R⁻¹)ᵀ=R⁻¹
    rw [Matrix.transpose_nonsing_inv,show Rᵀ=R from hR.eq]
  refine ⟨R⁻¹,hi,?_,?_,?_,?_⟩
  · rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
    exact hu.inv
  · rw [← hRR]
    simp only [← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hu,Matrix.one_mul,
      Matrix.mul_nonsing_inv _ hu]
  · intro g
    have he := squareRoot_energy L R hR γ hRR (R⁻¹*ᵥg)
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hu,Matrix.one_mulVec] at he
    exact (sq_le_sq₀ (vectorNorm_nonneg _) (vectorNorm_nonneg _)).mp
      (by nlinarith [mul_nonneg hγ.le (sq_nonneg (vectorNorm (R⁻¹*ᵥg)))])
  · intro g
    have he := squareRoot_energy L R hR γ hRR (R⁻¹*ᵥg)
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hu,Matrix.one_mulVec] at he
    apply (le_div_iff₀ (sqrt_pos.mpr hγ)).mpr
    apply (sq_le_sq₀ (mul_nonneg (vectorNorm_nonneg _) (sqrt_nonneg _)) (vectorNorm_nonneg _)).mp
    rw [mul_pow,Real.sq_sqrt hγ.le]
    nlinarith [sq_nonneg (vectorNorm (L*ᵥ(R⁻¹*ᵥg)))]

lemma symmetric_row_sq_bound {n : ℕ} {U : Matrix (Fin n) (Fin n) ℝ}
    (hU : U.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ g : Field n, vectorNorm (U*ᵥg) ≤ c*vectorNorm g) (i : Fin n) :
    ∑ k,U i k^2 ≤ c^2 := by
  let e : Field n := Pi.single i 1
  have he : vectorNorm e=1 := by
    apply (sq_eq_sq₀ (vectorNorm_nonneg _) zero_le_one).mp
    simp [vectorNorm_sq,vectorSqNorm,e,Pi.single_apply]
  have hx : U*ᵥe=fun k => U i k := by
    ext k
    simp only [e,Matrix.mulVec_single,MulOpposite.op_one,one_smul,Matrix.col_apply]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_apply] using congrFun (congrFun hU.eq i) k
  have hh := hbound e
  rw [hx,he,mul_one] at hh
  simpa only [vectorNorm_sq,vectorSqNorm] using
    (sq_le_sq₀ (vectorNorm_nonneg _) hc).mpr hh

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators
attribute [local irreducible] vectorNorm varianceAverage varianceLinear magnetizationRemainder tapField fieldJacobian magnetization

lemma vectorNorm_fourth_le {n : ℕ} (d : Field n) :
    vectorNorm d^4 ≤ (n:ℝ)*∑ i,d i^4 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin n => (1:ℝ)) (fun i => d i^2)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
    ← pow_mul] at hc
  rw [show vectorNorm d^4=(vectorNorm d^2)^2 by ring,vectorNorm_sq]
  exact hc

lemma tap_remainder_sq {n : ℕ} (hn : 0 < n) {j K : ℝ}
    (hj : 0 ≤ j) (hK : 0 ≤ K) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ z : Field n, vectorNorm (J*ᵥz) ≤ K*vectorNorm z) (h y d : Field n) :
    vectorNorm (tapField j J h (y+d)-tapField j J h y-(fieldJacobian j J y)*ᵥd)^2 ≤
      (8*(j+K)^2+128*j^2)*∑ i,d i^4 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hs : 0 ≤ ∑ i,d i^4 := Finset.sum_nonneg (fun i _ => by positivity)
  have h1 := tap_remainder_norm hn hj hK J hJ h y d
  have ha : 0 ≤ 2*(j+K)*sqrt (∑ i,d i^4) := by positivity
  have hb : 0 ≤ (8*j/sqrt (n:ℝ))*vectorNorm d^2 := by positivity
  have hsq := (sq_le_sq₀ (vectorNorm_nonneg _) (add_nonneg ha hb)).mpr h1
  have hcs : (2*(j+K)*sqrt (∑ i,d i^4)+(8*j/sqrt (n:ℝ))*vectorNorm d^2)^2 ≤
      2*(2*(j+K)*sqrt (∑ i,d i^4))^2+2*((8*j/sqrt (n:ℝ))*vectorNorm d^2)^2 := by
    nlinarith [sq_nonneg (2*(j+K)*sqrt (∑ i,d i^4)-(8*j/sqrt (n:ℝ))*vectorNorm d^2)]
  have he : 2*(2*(j+K)*sqrt (∑ i,d i^4))^2+2*((8*j/sqrt (n:ℝ))*vectorNorm d^2)^2=
      8*(j+K)^2*(∑ i,d i^4)+(128*j^2/(n:ℝ))*vectorNorm d^4 := by
    simp only [mul_pow,div_pow,Real.sq_sqrt hs,Real.sq_sqrt hn0.le]
    ring
  apply (hsq.trans hcs).trans
  rw [he]
  calc
    _ ≤ 8*(j+K)^2*(∑ i,d i^4)+(128*j^2/(n:ℝ))*((n:ℝ)*∑ i,d i^4) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (vectorNorm_fourth_le d) (by positivity))
    _ = _ := by field_simp

lemma varianceAverage_sq_difference {n : ℕ} (hn : 0 < n) (y d : Field n) :
    |varianceAverage (y+d)^2-varianceAverage y^2| ≤ 4/sqrt (n:ℝ)*vectorNorm d := by
  have hb := varianceAverage_bounds hn y
  have hb' := varianceAverage_bounds hn (y+d)
  rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg hb'.1 hb.1)]
  have hh := varianceAverage_difference hn y d
  calc
    _ ≤ 2*(2/sqrt (n:ℝ)*vectorNorm d) := mul_le_mul
      (show varianceAverage (y+d)+varianceAverage y ≤ 2 by linarith) hh
      (abs_nonneg _) (by norm_num)
    _ = _ := by ring

end SKGap
end
end

end OAI
