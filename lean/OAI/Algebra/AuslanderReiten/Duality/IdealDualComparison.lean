import OAI.Algebra.AuslanderReiten.Duality.IdealDualComplex

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "C" => BaseAlgebra k q
instance complex_scalarTower (n : ℕ) : IsScalarTower k C ((complex q).X n) := by
  cases n with
  | zero => exact (inferInstance : IsScalarTower k C (F q))
  | succ n => exact (inferInstance : IsScalarTower k C (E q))

private instance homETower : IsScalarTower k Cᵐᵒᵖ (E q →ₗ[C] C) where
  smul_assoc r c f := by
    apply LinearMap.ext
    intro a
    change f a * (r • c.unop) = r • (f a * c.unop)
    exact mul_smul_comm _ _ _

private instance homFTower : IsScalarTower k Cᵐᵒᵖ (F q →ₗ[C] C) where
  smul_assoc r c f := by
    apply LinearMap.ext
    intro a
    change f a * (r • c.unop) = r • (f a * c.unop)
    exact mul_smul_comm _ _ _

omit [CharP k 2] in
private theorem fromRightF_precompose (a : rightF q) :
    fromRightE q (leftU q a) = (fromRightF q a).comp (dU q) := by
  apply (homEEquiv q).injective
  change evaluateE q _ = evaluateE q _
  rw [evaluateE_fromRightE, evaluate_precompose_dU, evaluateF_fromRightF]

omit [CharP k 2] in
private theorem fromRightE_precompose (r : k) (a : rightE q) :
    fromRightE q (leftEll q r a) = (fromRightE q a).comp (dEll q r) := by
  apply (homEEquiv q).injective
  change evaluateE q _ = evaluateE q _
  rw [evaluateE_fromRightE, evaluateE_precompose, evaluateE_fromRightE]

private def rawIdealDualEquivF : RightDual k C (F q →ₗ[C] C) ≃ₗ[C] RightDual k C (rightF q) :=
  (RightDual.congr (homFRightLinearEquiv q)).symm

private def rawIdealDualEquivE : RightDual k C (E q →ₗ[C] C) ≃ₗ[C] RightDual k C (rightE q) :=
  (RightDual.congr (homERightLinearEquiv q)).symm

def idealDualEquiv : (n : ℕ) →
    (DualTensor.dualHomComplex (k := k) (complex q)).X n ≃ₗ[C] (idealDualComplex q).X n
  | 0 => rawIdealDualEquivF q
  | _ + 1 => rawIdealDualEquivE q

def idealDualComparison : DualTensor.dualHomComplex (k := k) (complex q) ≅ idealDualComplex q :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (idealDualEquiv q n).toModuleIso) (by
    intro i j hij
    obtain rfl : i = j + 1 := by simpa using hij.symm
    rw [DualTensor.dualHomComplex_d, idealDualComplex_d]
    apply ModuleCat.hom_ext
    cases j with
    | zero =>
      apply LinearMap.ext
      intro φ
      apply RightDual.ext
      apply LinearMap.ext
      intro a
      change φ.functional (fromRightE q (leftU q a)) =
        φ.functional ((fromRightF q a).comp (dU q))
      exact congrArg φ.functional (fromRightF_precompose q a)
    | succ n =>
      apply LinearMap.ext
      intro φ
      apply RightDual.ext
      apply LinearMap.ext
      intro a
      dsimp [idealDualEquiv, idealDualDifferential, DualTensor.dualHomDifferential]
      rw [show (complex q).d (n + 1 + 1) (n + 1) = differential q (n + 1) from ChainComplex.of_d _ _ _]
      change φ.functional (fromRightE q (leftEll q (q ^ n) a)) =
        φ.functional ((fromRightE q a).comp (dEll q (q ^ n)))
      exact congrArg φ.functional (fromRightE_precompose q (q ^ n) a))

instance cResolution_finite_terms (n : ℕ) : Module.Finite C ((complex q).X n) :=
  Module.Finite.of_restrictScalars_finite k C ((complex q).X n)

def tensorIdealComparison : DualTensor.tensorComplex (k := k) (complex q) ≅ idealDualComplex q :=
  DualTensor.complexIso (complex q) ≪≫ idealDualComparison q

end ArExplicit.Resolution

end

end OAI
