import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleCoefficientEquiv
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleTensorTotal
import OAI.Algebra.Finitistic.Ordinary.OrdinaryRetainedRestriction
import OAI.Algebra.Finitistic.Ordinary.OrdinaryFinitePiSupport
import OAI.Algebra.Finitistic.Ordinary.OrdinaryMiddleTensorFunctors
import OAI.Algebra.Finitistic.Ordinary.OrdinaryShiftSign

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.SingleBimoduleTensor
universe u
variable (k S A N : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable [AddCommGroup N] [Module k N] [Module S N] [Module Aᵐᵒᵖ N]
  [IsScalarTower k S N] [IsScalarTower k Aᵐᵒᵖ N] [SMulCommClass S Aᵐᵒᵖ N]

abbrev complex : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ :=
  (HomologicalComplex.single _ (.up ℤ) 0).obj (RetainedBimodule.object k S A N)

variable (Z : CochainComplex (ModuleCat.{u} A) ℤ)
open BimoduleComplexTensor

def zeroCoefficientEquiv : BimoduleCoefficients k S A ((complex k S A N).X 0) ≃ₗ[Aᵐᵒᵖ] N :=
  (BimoduleCoefficients.equiv k S A (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (RetainedBimodule.object k S A N))).trans
    (RetainedBimodule.rightEquiv k S A N)

theorem zeroCoefficientEquiv_left (s : S) (x : BimoduleCoefficients k S A ((complex k S A N).X 0)) :
    zeroCoefficientEquiv k S A N (s • x) = s • zeroCoefficientEquiv k S A N x := by
  simp only [zeroCoefficientEquiv,LinearEquiv.trans_apply,BimoduleCoefficients.equiv_left,RetainedBimodule.rightEquiv_left]

def zeroTermEquiv (n : ℤ) : term k S A (complex k S A N) Z 0 n ≃ₗ[S] (middleLeftComplex k S A N Z).X n :=
  LeftTensor.congr (zeroCoefficientEquiv k S A N) (zeroCoefficientEquiv_left k S A N)
    (LinearEquiv.refl A (ComplexTensor.leftTerm k A Z n))

theorem zeroTermEquiv_map {n m : ℤ} (g : Z.X n ⟶ Z.X m) :
    (zeroTermEquiv k S A N Z m).toLinearMap.comp (map k S A (complex k S A N) Z (𝟙 _) g) =
    ((middleLeftFunctor k S A N).map g).hom.comp (zeroTermEquiv k S A N Z n).toLinearMap := by
  let : Module k ((middleLeftComplex k S A N Z).X m) := inferInstanceAs (Module k (LeftTensor k A S N (ComplexTensor.leftTerm k A Z m)))
  let : IsScalarTower k S ((middleLeftComplex k S A N Z).X m) := inferInstanceAs (IsScalarTower k S (LeftTensor k A S N (ComplexTensor.leftTerm k A Z m)))
  apply LinearMap.restrictScalars_injective k
  apply BalancedTensor.ext
  intro x z
  rfl

variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p) (i₀ : Fin l) (h₀ : p i₀ = 0)

include hp h₀ in
theorem otherTerm_subsingleton (n : ℤ) (i : Fin l) (hi : i ≠ i₀) :
    Subsingleton (term k S A (complex k S A N) Z (p i) (n + -(p i))) := by
  have hz : p i ≠ 0 := by
    intro h
    exact hi (hp.injective (h.trans h₀.symm))
  have : Subsingleton (BimoduleCoefficients k S A ((complex k S A N).X (p i))) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (RetainedBimodule.object k S A N) (p i) hz)
  exact inferInstanceAs (Subsingleton (BalancedTensor.Tensor k A
    (BimoduleCoefficients k S A ((complex k S A N).X (p i))) (ComplexTensor.leftTerm k A Z (n + -(p i)))))

def coefficientEquivAt (q : ℤ) (hq : q = 0) :
    BimoduleCoefficients k S A ((complex k S A N).X q) ≃ₗ[Aᵐᵒᵖ] N := by
  subst q
  exact zeroCoefficientEquiv k S A N

theorem coefficientEquivAt_left (q : ℤ) (hq : q = 0) (s : S)
    (x : BimoduleCoefficients k S A ((complex k S A N).X q)) :
    coefficientEquivAt k S A N q hq (s • x) = s • coefficientEquivAt k S A N q hq x := by
  subst q
  exact zeroCoefficientEquiv_left k S A N s x

def termEquivAt (q : ℤ) (hq : q = 0) (n : ℤ) :
    term k S A (complex k S A N) Z q (n + -q) ≃ₗ[S] ((middleLeftComplex k S A N Z)⟦-q⟧).X n :=
  LeftTensor.congr (coefficientEquivAt k S A N q hq) (coefficientEquivAt_left k S A N q hq)
    (LinearEquiv.refl A (ComplexTensor.leftTerm k A Z (n + -q)))

theorem termEquivAt_map (q : ℤ) (hq : q = 0) (n m : ℤ) (g : Z.X (n + -q) ⟶ Z.X (m + -q)) :
    (termEquivAt k S A N Z q hq m).toLinearMap.comp (map k S A (complex k S A N) Z (𝟙 _) g) =
    ((middleLeftFunctor k S A N).map g).hom.comp (termEquivAt k S A N Z q hq n).toLinearMap := by
  let : Module k (((middleLeftComplex k S A N Z)⟦-q⟧).X m) :=
    inferInstanceAs (Module k (LeftTensor k A S N (ComplexTensor.leftTerm k A Z (m + -q))))
  let : IsScalarTower k S (((middleLeftComplex k S A N Z)⟦-q⟧).X m) :=
    inferInstanceAs (IsScalarTower k S (LeftTensor k A S N (ComplexTensor.leftTerm k A Z (m + -q))))
  apply LinearMap.restrictScalars_injective k
  apply BalancedTensor.ext
  intro x z
  rfl

abbrev selectedTermEquiv (n : ℤ) := termEquivAt k S A N Z (p i₀) h₀ n

def totalTermEquiv (n : ℤ) : totalTerm k S A (complex k S A N) Z p n ≃ₗ[S]
    ((middleLeftComplex k S A N Z)⟦-(p i₀)⟧).X n :=
  (FinitePiSupport.equivalence (fun i => term k S A (complex k S A N) Z (p i) (n + -(p i)))
    i₀ (otherTerm_subsingleton k S A N Z p hp i₀ h₀ n)).trans
    (selectedTermEquiv k S A N Z p i₀ h₀ n)
end LittleFinitistic.SingleBimoduleTensor

end

end OAI
