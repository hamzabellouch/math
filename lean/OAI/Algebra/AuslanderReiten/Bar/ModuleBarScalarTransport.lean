import OAI.Algebra.AuslanderReiten.Bar.ModuleBarCubic
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorScalar

namespace OAI

noncomputable section
namespace ArExplicit.ModuleBar
open CategoryTheory
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [AddCommGroup M] [Module R M] [μ : Module k M] [IsScalarTower k R M]

def canonicalCoefficientComplex : ChainComplex (ModuleCat.{u} R) ℕ :=
  letI : Module k M := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  letI : IsScalarTower k R M := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  complex k R M

theorem canonicalCoefficientComplex_eq : canonicalCoefficientComplex k R M = complex k R M := by
  cases ExternalTensor.canonicalScalar_eq k R M (mM := μ)
  rfl

def coefficientScalarIso : canonicalCoefficientComplex k R M ≅ complex k R M :=
  eqToIso (canonicalCoefficientComplex_eq k R M)

def canonicalCoefficientCubic (p : AbsoluteBar.Cochain3 k R) (n : ℕ) :
    (canonicalCoefficientComplex k R M).X (n+3) ⟶ (canonicalCoefficientComplex k R M).X n := by
  letI : Module k M := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  letI : IsScalarTower k R M := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  exact cubicMap k R M p n

theorem coefficientScalarIso_cubic (p : AbsoluteBar.Cochain3 k R) (n : ℕ) :
    canonicalCoefficientCubic k R M p n ≫ (coefficientScalarIso k R M).hom.f n =
      (coefficientScalarIso k R M).hom.f (n+3) ≫ cubicMap k R M p n := by
  cases ExternalTensor.canonicalScalar_eq k R M (mM := μ)
  rfl

end ArExplicit.ModuleBar

end

end OAI
