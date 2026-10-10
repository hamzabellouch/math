import OAI.Algebra.AuslanderReiten.Ext.TTensorPolynomial
import OAI.Algebra.AuslanderReiten.Ext.TensorExtCoefficients
import OAI.Algebra.AuslanderReiten.Resolutions.BinaryKoszul

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (X U : ModuleCat.{u} A) (Y V : ModuleCat.{u} B)

private theorem diagonalFirst_injective (n : ℕ) : Function.Injective (diagonalFirst n) := by
  intro d e h
  apply Subtype.ext
  apply Prod.ext
  · have hh := congrArg (fun x : Diagonal (n+3) => x.val.1) h
    dsimp at hh
    omega
  · exact congrArg (fun x : Diagonal (n+3) => x.val.2) h

private theorem diagonalSecond_injective (n : ℕ) : Function.Injective (diagonalSecond n) := by
  intro d e h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun x : Diagonal (n+3) => x.val.1) h
  · have hh := congrArg (fun x : Diagonal (n+3) => x.val.2) h
    dsimp at hh
    omega

theorem coefficientFirst_apply (a : Ext X X 3) (n : ℕ) (d : Diagonal n)
    (z : extCoefficients k A B X U Y V n) :
    coefficientFirst k A B X U Y V a n z (diagonalFirst n d) =
      TensorProduct.map (Ext.bilinearCompOfLinear k X X U 3 d.val.1 (d.val.1+3) (by omega) a)
        LinearMap.id (z d) := by
  classical
  simp only [coefficientFirst, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Finset.sum_apply, LinearMap.single_apply]
  rw [Finset.sum_eq_single d]
  · exact Pi.single_eq_same _ _
  · intro e he hne
    apply Pi.single_eq_of_ne
    intro h
    exact hne ((diagonalFirst_injective n) h.symm)
  · simp

theorem coefficientSecond_apply (b : Ext Y Y 3) (n : ℕ) (d : Diagonal n)
    (z : extCoefficients k A B X U Y V n) :
    coefficientSecond k A B X U Y V b n z (diagonalSecond n d) =
      TensorProduct.map LinearMap.id
        (Ext.bilinearCompOfLinear k Y Y V 3 d.val.2 (d.val.2+3) (by omega) b) (z d) := by
  classical
  simp only [coefficientSecond, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Finset.sum_apply, LinearMap.single_apply]
  rw [Finset.sum_eq_single d]
  · exact Pi.single_eq_same _ _
  · intro e he hne
    apply Pi.single_eq_of_ne
    intro h
    exact hne ((diagonalSecond_injective n) h.symm)
  · simp

theorem coefficientFirst_zero (a : Ext X X 3) (n : ℕ) (d : Diagonal (n+3))
    (hd : d.val.1 < 3) (z : extCoefficients k A B X U Y V n) :
    coefficientFirst k A B X U Y V a n z d = 0 := by
  classical
  simp only [coefficientFirst, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Finset.sum_apply, LinearMap.single_apply]
  apply Finset.sum_eq_zero
  intro e he
  apply Pi.single_eq_of_ne
  intro h
  have hh := congrArg (fun x : Diagonal (n+3) => x.val.1) h
  dsimp at hh
  omega

theorem coefficientSecond_zero (b : Ext Y Y 3) (n : ℕ) (d : Diagonal (n+3))
    (hd : d.val.2 < 3) (z : extCoefficients k A B X U Y V n) :
    coefficientSecond k A B X U Y V b n z d = 0 := by
  classical
  simp only [coefficientSecond, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Finset.sum_apply, LinearMap.single_apply]
  apply Finset.sum_eq_zero
  intro e he
  apply Pi.single_eq_of_ne
  intro h
  have hh := congrArg (fun x : Diagonal (n+3) => x.val.2) h
  dsimp at hh
  omega

end ArExplicit.ExternalTensor

namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T" => ArExplicit.T k q
local notation "S" => ModuleCat.of T (Simple q)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : NoPositivePowerOne q)

def tTensorScalarEquiv (a b : ℕ) :
    TSelfExt q (3*a) ⊗[k] TSelfExt q (3*b) ≃ₗ[k] k :=
  (TensorProduct.congr (tExplicitCoefficientEquiv q hq hq1 h a).symm
    (tExplicitCoefficientEquiv q hq hq1 h b).symm).trans (TensorProduct.lid k k)

@[simp]
theorem tTensorScalarEquiv_tmul (a b : ℕ) (x : TSelfExt q (3*a)) (y : TSelfExt q (3*b)) :
    tTensorScalarEquiv q hq hq1 h a b (x ⊗ₜ[k] y) =
      (tExplicitCoefficientEquiv q hq hq1 h a).symm x *
        (tExplicitCoefficientEquiv q hq hq1 h b).symm y := rfl

theorem tExplicitCoefficientEquiv_succ (n : ℕ) (x : TSelfExt q (3*n)) :
    (tExplicitCoefficientEquiv q hq hq1 h (n+1)).symm (tPMul q (3*n) x) =
      (tExplicitCoefficientEquiv q hq hq1 h n).symm x := by
  change (tExplicitCoefficientEquiv q hq hq1 h n).symm
    ((tPMulEquiv q hq hq1 h (3*n)).symm ((tPMulEquiv q hq hq1 h (3*n)) x)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem tTensorScalarEquiv_first (a b : ℕ)
    (z : TSelfExt q (3*a) ⊗[k] TSelfExt q (3*b)) :
    tTensorScalarEquiv q hq hq1 h (a+1) b
      (TensorProduct.map (tPMul q (3*a)) LinearMap.id z) =
      tTensorScalarEquiv q hq hq1 h a b z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      rw [TensorProduct.map_tmul, tTensorScalarEquiv_tmul, tTensorScalarEquiv_tmul,
        tExplicitCoefficientEquiv_succ]
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tTensorScalarEquiv_second (a b : ℕ)
    (z : TSelfExt q (3*a) ⊗[k] TSelfExt q (3*b)) :
    tTensorScalarEquiv q hq hq1 h a (b+1)
      (TensorProduct.map LinearMap.id (tPMul q (3*b)) z) =
      tTensorScalarEquiv q hq hq1 h a b z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      rw [TensorProduct.map_tmul, tTensorScalarEquiv_tmul, tTensorScalarEquiv_tmul,
        tExplicitCoefficientEquiv_succ]
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]

def tTensorScalarAt (n : ℕ) (z : tTensorCoefficients q n) (a b : ℕ) (hab : 3*a+3*b=n) : k :=
  tTensorScalarEquiv q hq hq1 h a b (z ⟨(3*a,3*b),hab⟩)

theorem tTensorScalarAt_congr (n : ℕ) (z : tTensorCoefficients q n)
    {a b a' b' : ℕ} (ha : a=a') (hb : b=b') (hab : 3*a+3*b=n) (hab' : 3*a'+3*b'=n) :
    tTensorScalarAt q hq hq1 h n z a b hab = tTensorScalarAt q hq hq1 h n z a' b' hab' := by
  subst a'
  subst b'
  rfl

@[simp]
theorem tTensorCoefficientEquiv_apply (n : ℕ) (z : tTensorCoefficients q (3*n)) (i : Fin (n+1)) :
    tTensorCoefficientEquiv q hq hq1 h n z i =
      tTensorScalarEquiv q hq hq1 h i.val (n-i.val) (z (polynomialDiagonal n i)) := rfl

theorem polynomialDiagonal_succ (n : ℕ) (i : Fin (n+1)) :
    polynomialDiagonal (n+1) i.succ =
      ExternalTensor.diagonalFirst (3*n) (polynomialDiagonal n i) := by
  apply Subtype.ext
  apply Prod.ext <;> simp [polynomialDiagonal, Nat.mul_add]

theorem polynomialDiagonal_castSucc (n : ℕ) (i : Fin (n+1)) :
    polynomialDiagonal (n+1) i.castSucc =
      ExternalTensor.diagonalSecond (3*n) (polynomialDiagonal n i) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · have hi := i.isLt
    dsimp [polynomialDiagonal, ExternalTensor.diagonalSecond]
    omega

theorem tTensorCoefficient_first (n : ℕ) (z : tTensorCoefficients q (3*n)) :
    tTensorCoefficientEquiv q hq hq1 h (n+1)
      (ExternalTensor.coefficientFirst k T T S S S S (tExplicitP q) (3*n) z) =
      BinaryKoszul.mulX k n (tTensorCoefficientEquiv q hq hq1 h n z) := by
  funext i
  cases i using Fin.cases with
  | zero =>
      rw [BinaryKoszul.mulX_zero, tTensorCoefficientEquiv_apply]
      rw [ExternalTensor.coefficientFirst_zero k T T S S S S (tExplicitP q) (3*n)
        (polynomialDiagonal (n+1) 0) (by simp [polynomialDiagonal]) z]
      exact map_zero _
  | succ i =>
      rw [BinaryKoszul.mulX_succ, tTensorCoefficientEquiv_apply, tTensorCoefficientEquiv_apply]
      have hc := ExternalTensor.coefficientFirst_apply k T T S S S S (tExplicitP q)
        (3*n) (polynomialDiagonal n i) z
      have hd := congrArg (tTensorScalarEquiv q hq hq1 h (i.val+1) (n-i.val)) hc
      have he := hd.trans (tTensorScalarEquiv_first q hq hq1 h i.val (n-i.val) _)
      change tTensorScalarAt q hq hq1 h (3*(n+1)) _ (i.val+1)
        ((n+1)-(i.val+1)) _ = _
      exact (tTensorScalarAt_congr q hq hq1 h (3*(n+1)) _ rfl
        (show (n+1)-(i.val+1)=n-i.val by omega) _ (by have := i.isLt; omega)).trans he

theorem tTensorCoefficient_second (n : ℕ) (z : tTensorCoefficients q (3*n)) :
    tTensorCoefficientEquiv q hq hq1 h (n+1)
      (ExternalTensor.coefficientSecond k T T S S S S (tExplicitP q) (3*n) z) =
      BinaryKoszul.mulY k n (tTensorCoefficientEquiv q hq hq1 h n z) := by
  funext i
  cases i using Fin.lastCases with
  | last =>
      rw [BinaryKoszul.mulY_last, tTensorCoefficientEquiv_apply]
      rw [ExternalTensor.coefficientSecond_zero k T T S S S S (tExplicitP q) (3*n)
        (polynomialDiagonal (n+1) (Fin.last (n+1))) (by simp [polynomialDiagonal]) z]
      exact map_zero _
  | cast i =>
      rw [BinaryKoszul.mulY_castSucc, tTensorCoefficientEquiv_apply, tTensorCoefficientEquiv_apply]
      have hc := ExternalTensor.coefficientSecond_apply k T T S S S S (tExplicitP q)
        (3*n) (polynomialDiagonal n i) z
      have hd := congrArg (tTensorScalarEquiv q hq hq1 h i.val ((n-i.val)+1)) hc
      have he := hd.trans (tTensorScalarEquiv_second q hq hq1 h i.val (n-i.val) _)
      change tTensorScalarAt q hq hq1 h (3*(n+1)) _ i.val ((n+1)-i.val) _ = _
      exact (tTensorScalarAt_congr q hq hq1 h (3*(n+1)) _ rfl
        (show (n+1)-i.val=(n-i.val)+1 by have := i.isLt; omega) _
        (by have := i.isLt; omega)).trans he

end ArExplicit.Resolution

end

end OAI
