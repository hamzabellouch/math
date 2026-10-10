import Mathlib

namespace OAI

/-! Hermitian Pair. -/

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace MongeAmpere
variable {n : Type*} [Fintype n]

def hermPair (K : Matrix n n ℂ) (v w : n → ℂ) : ℂ := star v ⬝ᵥ (K *ᵥ w)

lemma hermPair_expand (K : Matrix n n ℂ) (v w : n → ℂ) :
    hermPair K v w = ∑ i, ∑ j, star (v i)*K i j*w j := by
  simp only [hermPair,dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc,Pi.star_apply]

lemma hermPair_add_left (K : Matrix n n ℂ) (u v w : n → ℂ) :
    hermPair K (u+v) w = hermPair K u w+hermPair K v w := by
  simp only [hermPair,star_add,add_dotProduct]

lemma hermPair_add_right (K : Matrix n n ℂ) (u v w : n → ℂ) :
    hermPair K u (v+w) = hermPair K u v+hermPair K u w := by
  simp only [hermPair,Matrix.mulVec_add,dotProduct_add]

lemma hermPair_smul_left (K : Matrix n n ℂ) (u v : n → ℂ) (c : ℂ) :
    hermPair K (c • u) v = star c*hermPair K u v := by
  simp only [hermPair,star_smul,smul_dotProduct,smul_eq_mul]

lemma hermPair_smul_right (K : Matrix n n ℂ) (u v : n → ℂ) (c : ℂ) :
    hermPair K u (c • v) = c*hermPair K u v := by
  simp only [hermPair,Matrix.mulVec_smul,dotProduct_smul,smul_eq_mul]

lemma hermPair_conj (K : Matrix n n ℂ) (hK : K.IsHermitian) (u v : n → ℂ) :
    star (hermPair K u v) = hermPair K v u := by
  simp only [hermPair]
  rw [star_dotProduct,star_star,star_mulVec,hK.eq]
  exact (dotProduct_mulVec (star v) K u).symm

lemma hermPair_mulVec_left (K C : Matrix n n ℂ) (u v : n → ℂ) :
    hermPair K (C *ᵥ u) v = hermPair (Cᴴ*K) u v := by
  simp only [hermPair,star_mulVec,← dotProduct_mulVec,Matrix.mulVec_mulVec]

lemma hermPair_mulVec_right (K C : Matrix n n ℂ) (u v : n → ℂ) :
    hermPair K u (C *ᵥ v) = hermPair (K*C) u v := by
  simp only [hermPair,Matrix.mulVec_mulVec]

lemma hermPair_nonneg {K : Matrix n n ℂ} (hK : K.PosSemidef) (u : n → ℂ) :
    0 ≤ (hermPair K u u).re := hK.re_dotProduct_nonneg u

@[instance_reducible] def hermPairCore (K : Matrix n n ℂ) (hK : K.PosSemidef) :
    PreInnerProductSpace.Core ℂ (n → ℂ) where
  inner := hermPair K
  conj_inner_symm x y := hermPair_conj K hK.isHermitian y x
  re_inner_nonneg := hermPair_nonneg hK
  add_left := hermPair_add_left K
  smul_left x y c := hermPair_smul_left K x y c

lemma hermPair_cauchySchwarz (K : Matrix n n ℂ) (hK : K.PosSemidef) (u v : n → ℂ) :
    ‖hermPair K u v‖^2 ≤ (hermPair K u u).re*(hermPair K v v).re := by
  let := hermPairCore K hK
  have h := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜:=ℂ) u v
  change ‖hermPair K u v‖*‖hermPair K v u‖ ≤ (hermPair K u u).re*(hermPair K v v).re at h
  rw [← hermPair_conj K hK.isHermitian u v,norm_star] at h
  simpa only [pow_two] using h

end MongeAmpere

end

end OAI
