import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.TensorMiddleEnd
import OAI.Combinatorics.Chromatic.Shuffle.UnitalGradeCoproductUnits

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma globalTensor_induction (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ)
    (P : UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ → Prop)
    (hz : P 0) (ha : ∀ x y,P x → P y → P (x+y))
    (ht : ∀ (k l : SlopeWeight c η hc θ) (x : unitalComponent a c η hc θ k)
      (y : unitalComponent a c η hc θ l),
      P (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x⊗ₜ[ℚ]
        DirectSum.lof ℚ _ (unitalComponent a c η hc θ) l y))
    (x : UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ) : P x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => exact ha x y hx hy
  | tmul x y =>
    induction x using DirectSum.induction_on with
    | zero => simpa only [TensorProduct.zero_tmul] using hz
    | add x x' hx hx' => rw [TensorProduct.add_tmul]; exact ha _ _ hx hx'
    | of k x =>
      induction y using DirectSum.induction_on with
      | zero => simpa only [TensorProduct.tmul_zero] using hz
      | add y y' hy hy' => rw [TensorProduct.tmul_add]; exact ha _ _ hy hy'
      | of l y => exact ht k l x y

lemma globalLof_mul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)]
    (k l : SlopeWeight c η hc θ) (x : unitalComponent a c η hc θ k)
    (y : unitalComponent a c η hc θ l) :
    DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x *
      DirectSum.lof ℚ _ (unitalComponent a c η hc θ) l y=
    DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (k+l) (GradedMonoid.GMul.mul x y) :=
  DirectSum.of_mul_of x y
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

omit [DecidableEq I] in
lemma euler_interchange_cocycle (a : I → I → ℕ) (d e f g : I → ℕ) :
    ((-1:ℚ)^eulerForm a d e) * ((-1:ℚ)^eulerForm a (d+f) g)=
      ((-1:ℚ)^eulerForm a f g) * ((-1:ℚ)^eulerForm a d (e+g)) := by
  rw [eulerForm_add_left,eulerForm_add_right,zpow_add₀ (by norm_num : (-1:ℚ)≠0),
    zpow_add₀ (by norm_num : (-1:ℚ)≠0)]
  ring

lemma globalSignedTensorMultiply_assoc_homogeneous (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)]
    (k l m n p q : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k) (y : unitalComponent a c η hc θ l)
    (z : unitalComponent a c η hc θ m) (w : unitalComponent a c η hc θ n)
    (v : unitalComponent a c η hc θ p) (u : unitalComponent a c η hc θ q) :
    globalSignedTensorMultiply a c η hc θ
      (globalSignedTensorMultiply a c η hc θ
        (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x⊗ₜ[ℚ]
          DirectSum.lof ℚ _ (unitalComponent a c η hc θ) l y)
        (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) m z⊗ₜ[ℚ]
          DirectSum.lof ℚ _ (unitalComponent a c η hc θ) n w))
      (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) p v⊗ₜ[ℚ]
        DirectSum.lof ℚ _ (unitalComponent a c η hc θ) q u)=
    globalSignedTensorMultiply a c η hc θ
      (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x⊗ₜ[ℚ]
        DirectSum.lof ℚ _ (unitalComponent a c η hc θ) l y)
      (globalSignedTensorMultiply a c η hc θ
        (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) m z⊗ₜ[ℚ]
          DirectSum.lof ℚ _ (unitalComponent a c η hc θ) n w)
        (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) p v⊗ₜ[ℚ]
          DirectSum.lof ℚ _ (unitalComponent a c η hc θ) q u)) := by
  rw [globalSignedTensorMultiply_tmul_lof,globalSignedTensorMultiply_tmul_lof]
  simp only [map_smul,LinearMap.smul_apply]
  simp only [globalLof_mul]
  rw [globalSignedTensorMultiply_tmul_lof,globalSignedTensorMultiply_tmul_lof]
  simp only [←globalLof_mul,smul_smul,mul_assoc]
  congr 1
  exact euler_interchange_cocycle a l.1.val m.1.val n.1.val p.1.val

lemma globalSignedTensorMultiply_assoc (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)]
    (x₀ y₀ z₀ : UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ) :
    globalSignedTensorMultiply a c η hc θ (globalSignedTensorMultiply a c η hc θ x₀ y₀) z₀=
      globalSignedTensorMultiply a c η hc θ x₀ (globalSignedTensorMultiply a c η hc θ y₀ z₀) := by
  induction x₀ using globalTensor_induction a c η hc θ with
  | hz => simp only [map_zero,LinearMap.zero_apply]
  | ha x x' hx hx' => simp only [map_add,LinearMap.add_apply,hx,hx']
  | ht k l x y =>
    induction y₀ using globalTensor_induction a c η hc θ with
    | hz => simp only [map_zero,LinearMap.zero_apply]
    | ha z z' hz hz' => simp only [map_add,LinearMap.add_apply,hz,hz']
    | ht m n z w =>
      induction z₀ using globalTensor_induction a c η hc θ with
      | hz => simp only [map_zero]
      | ha v v' hv hv' => simp only [map_add,hv,hv']
      | ht p q v u => exact globalSignedTensorMultiply_assoc_homogeneous a c η hc θ k l m n p q x y z w v u
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

lemma globalSignedTensorMultiply_one_left (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)]
    (x : UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ) :
    globalSignedTensorMultiply a c η hc θ
      (globalUnit a c η hc θ⊗ₜ[ℚ]globalUnit a c η hc θ) x=x := by
  induction x using globalTensor_induction a c η hc θ with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | ht k l x y =>
    rw [globalUnit,globalSignedTensorMultiply_tmul_lof]
    change ((-1:ℚ)^eulerForm a 0 k.1.val) • ((1 * _)⊗ₜ[ℚ](1 * _))=_
    simp only [eulerForm,Pi.zero_apply,Int.natCast_zero,zero_mul,mul_zero,Finset.sum_const_zero,sub_zero,zpow_zero,one_smul]
    exact congrArg₂ (fun x y : UnitalShuffle a c η hc θ=>x⊗ₜ[ℚ]y) (one_mul _) (one_mul _)

lemma globalSignedTensorMultiply_one_right (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)]
    (x : UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ) :
    globalSignedTensorMultiply a c η hc θ x
      (globalUnit a c η hc θ⊗ₜ[ℚ]globalUnit a c η hc θ)=x := by
  induction x using globalTensor_induction a c η hc θ with
  | hz => simp only [map_zero,LinearMap.zero_apply]
  | ha x y hx hy => simp only [map_add,LinearMap.add_apply,hx,hy]
  | ht k l x y =>
    rw [globalUnit,globalSignedTensorMultiply_tmul_lof]
    change ((-1:ℚ)^eulerForm a l.1.val 0) • ((_ * 1)⊗ₜ[ℚ](_ * 1))=_
    simp only [eulerForm,Pi.zero_apply,Int.natCast_zero,mul_zero,Finset.sum_const_zero,sub_zero,zpow_zero,one_smul]
    exact congrArg₂ (fun x y : UnitalShuffle a c η hc θ=>x⊗ₜ[ℚ]y) (mul_one _) (mul_one _)

def SignedGlobalTensor (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) :=
  UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ

noncomputable instance (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) : AddCommGroup (SignedGlobalTensor a c η hc θ) :=
  inferInstanceAs (AddCommGroup (UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ))
noncomputable instance (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) : Module ℚ (SignedGlobalTensor a c η hc θ) :=
  inferInstanceAs (Module ℚ (UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ))
noncomputable instance (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)] :
    Ring (SignedGlobalTensor a c η hc θ) where
  mul x y := globalSignedTensorMultiply a c η hc θ x y
  one := globalUnit a c η hc θ⊗ₜ[ℚ]globalUnit a c η hc θ
  one_mul := globalSignedTensorMultiply_one_left a c η hc θ
  mul_one := globalSignedTensorMultiply_one_right a c η hc θ
  mul_assoc := globalSignedTensorMultiply_assoc a c η hc θ
  left_distrib := fun x y z=>map_add (globalSignedTensorMultiply a c η hc θ x) y z
  right_distrib := fun x y z=>by
    exact LinearMap.congr_fun (map_add (globalSignedTensorMultiply a c η hc θ) x y) z
  zero_mul := fun x=>by
    exact LinearMap.congr_fun (map_zero (globalSignedTensorMultiply a c η hc θ)) x
  mul_zero := fun x=>map_zero (globalSignedTensorMultiply a c η hc θ x)
  natCast n := n • (globalUnit a c η hc θ⊗ₜ[ℚ]globalUnit a c η hc θ)
  natCast_zero := zero_nsmul _
  natCast_succ n := by
    change (n+1) • (globalUnit a c η hc θ⊗ₜ[ℚ]globalUnit a c η hc θ)=_
    exact succ_nsmul _ _
  intCast n := n • (globalUnit a c η hc θ⊗ₜ[ℚ]globalUnit a c η hc θ)
  intCast_ofNat n := natCast_zsmul _ _
  intCast_negSucc n := negSucc_zsmul _ _

noncomputable instance (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)] :
    Algebra ℚ (SignedGlobalTensor a c η hc θ) :=
  Algebra.ofModule
    (fun r x y=>LinearMap.congr_fun (map_smul (globalSignedTensorMultiply a c η hc θ) r x) y)
    (fun r x y=>map_smul (globalSignedTensorMultiply a c η hc θ x) r y)
end ElementaryPositivity.RawShuffle

end

end OAI
