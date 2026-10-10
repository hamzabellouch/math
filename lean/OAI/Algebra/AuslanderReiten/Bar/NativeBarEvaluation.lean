import OAI.Algebra.AuslanderReiten.Bar.CanonicalBarEvaluation
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarScalarTransport
import OAI.Algebra.AuslanderReiten.Homology.ChainComparisonIso

namespace OAI

noncomputable section
namespace ArExplicit.BarBalanced
open CategoryTheory
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

def nativeComplexIso :
    ExternalBalanced.factorEvaluation k (ModuleCat.of R M) (AbsoluteBar.complex k R) ≅
      ModuleBar.complex k R M :=
  canonicalComplexIso k R (ModuleCat.of R M) ≪≫ ModuleBar.coefficientScalarIso k R M

def nativeEvaluatedCubic (p : AbsoluteBar.Cochain3 k R) (n : ℕ) :
    (ExternalBalanced.factorEvaluation k (ModuleCat.of R M) (AbsoluteBar.complex k R)).X (n+3) ⟶
      (ExternalBalanced.factorEvaluation k (ModuleCat.of R M) (AbsoluteBar.complex k R)).X n := by
  letI : Module k M := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  letI : IsScalarTower k R M := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  exact (EnvelopingBimodule.evaluationFunctor k R (ModuleCat.of R M)).map
    (ModuleCat.ofHom (X := (AbsoluteBar.complex k R).X (n+3))
      (Y := (AbsoluteBar.complex k R).X n) (AbsoluteBar.suffixComparisonMap k R p n))

omit [Module k M] [IsScalarTower k R M] in
theorem nativeEvaluatedCubic_canonical (p : AbsoluteBar.Cochain3 k R) (n : ℕ) :
    nativeEvaluatedCubic k R M p n ≫
      (canonicalComplexIso k R (ModuleCat.of R M)).hom.f n =
    (canonicalComplexIso k R (ModuleCat.of R M)).hom.f (n+3) ≫
      ModuleBar.canonicalCoefficientCubic k R M p n :=
  canonicalComplexIso_cubic k R (ModuleCat.of R M) p n

theorem nativeComplexIso_cubic (p : AbsoluteBar.Cochain3 k R) (n : ℕ) :
    nativeEvaluatedCubic k R M p n ≫
      (nativeComplexIso k R M).hom.f n =
    (nativeComplexIso k R M).hom.f (n+3) ≫ ModuleBar.cubicMap k R M p n :=
  comparisonIso_trans (canonicalComplexIso k R (ModuleCat.of R M))
    (ModuleBar.coefficientScalarIso k R M) (n+3) n
    (nativeEvaluatedCubic k R M p n) (ModuleBar.canonicalCoefficientCubic k R M p n)
    (ModuleBar.cubicMap k R M p n) (nativeEvaluatedCubic_canonical k R M p n)
    (ModuleBar.coefficientScalarIso_cubic k R M p n)

end ArExplicit.BarBalanced

end

end OAI
