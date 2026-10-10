import OAI.Algebra.AuslanderReiten.Ext.TExplicitPolynomial
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorComplex
import OAI.Algebra.AuslanderReiten.Modules.SupportedPi
import OAI.Algebra.AuslanderReiten.Ext.TensorExtCoefficients

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : NoPositivePowerOne q)

abbrev tTensorCoefficients (n : ℕ) :=
  ExternalTensor.extCoefficients k (T k q) (T k q)
    (ModuleCat.of (T k q) (Simple q)) (ModuleCat.of (T k q) (Simple q))
    (ModuleCat.of (T k q) (Simple q)) (ModuleCat.of (T k q) (Simple q)) n

def polynomialDiagonal (n : ℕ) (i : Fin (n+1)) : ExternalTensor.Diagonal (3*n) :=
  ⟨(3*i.val,3*(n-i.val)), by have := i.isLt; dsimp; omega⟩

theorem polynomialDiagonal_injective (n : ℕ) :
    Function.Injective (polynomialDiagonal n) := by
  intro i j hij
  apply Fin.ext
  have he := congrArg (fun p : ExternalTensor.Diagonal (3*n) => p.val.1) hij
  dsimp [polynomialDiagonal] at he
  omega

theorem polynomialDiagonal_hits (n : ℕ) (p : ExternalTensor.Diagonal (3*n))
    (h₁ : 3 ∣ p.val.1) (h₂ : 3 ∣ p.val.2) :
    ∃ i, polynomialDiagonal n i = p := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  have hp := p.property
  let i : Fin (n+1) := ⟨a, by omega⟩
  refine ⟨i, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact ha.symm
  · dsimp [polynomialDiagonal, i]
    omega

omit [CharP k 2] in
private theorem tensor_zero_left {U V : Type u} [AddCommGroup U] [AddCommGroup V]
    [Module k U] [Module k V] (hu : ∀ x : U, x=0) (z : U ⊗[k] V) : z=0 := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => rw [hu x, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

omit [CharP k 2] in
private theorem tensor_zero_right {U V : Type u} [AddCommGroup U] [AddCommGroup V]
    [Module k U] [Module k V] (hv : ∀ y : V, y=0) (z : U ⊗[k] V) : z=0 := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => rw [hv y, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

include hq hq1 h

theorem tTensorCoefficient_off_diagonal (n : ℕ) (p : ExternalTensor.Diagonal (3*n))
    (hp : ¬ ∃ i, polynomialDiagonal n i = p)
    (z : TSelfExt q p.val.1 ⊗[k] TSelfExt q p.val.2) : z=0 := by
  by_cases h₁ : 3 ∣ p.val.1
  · have h₂ : ¬ 3 ∣ p.val.2 := fun h₂ => hp (polynomialDiagonal_hits n p h₁ h₂)
    exact tensor_zero_right (tSelfExt_zero_of_not_dvd q hq hq1 h p.val.2 h₂) z
  · exact tensor_zero_left (tSelfExt_zero_of_not_dvd q hq hq1 h p.val.1 h₁) z

def tTensorCoefficientEquiv (n : ℕ) : tTensorCoefficients q (3*n) ≃ₗ[k] (Fin (n+1) → k) :=
  (supportedPiEquiv (fun p : ExternalTensor.Diagonal (3*n) =>
      TSelfExt q p.val.1 ⊗[k] TSelfExt q p.val.2) (polynomialDiagonal n)
      (polynomialDiagonal_injective n) (tTensorCoefficient_off_diagonal q hq hq1 h n)).trans
    (LinearEquiv.piCongrRight fun i =>
      (TensorProduct.congr (tExplicitCoefficientEquiv q hq hq1 h i.val).symm
        (tExplicitCoefficientEquiv q hq hq1 h (n-i.val)).symm).trans (TensorProduct.lid k k))

theorem tTensorCoefficient_zero_of_not_dvd (n : ℕ) (hn : ¬ 3 ∣ n)
    (z : tTensorCoefficients q n) : z=0 := by
  funext p
  by_cases h₁ : 3 ∣ p.val.1
  · have h₂ : ¬ 3 ∣ p.val.2 := by
      intro h₂
      exact hn (p.property ▸ dvd_add h₁ h₂)
    exact tensor_zero_right (tSelfExt_zero_of_not_dvd q hq hq1 h p.val.2 h₂) (z p)
  · exact tensor_zero_left (tSelfExt_zero_of_not_dvd q hq hq1 h p.val.1 h₁) (z p)

end ArExplicit.Resolution

end

end OAI
