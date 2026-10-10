import OAI.Algebra.AuslanderReiten.Bar.CanonicalBarSquare
import OAI.Algebra.AuslanderReiten.Ext.ExternalEvaluationTerms
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarCubic

namespace OAI

noncomputable section
namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} R)

def canonicalTermIso (n : ℕ) :
    (ExternalBalanced.factorEvaluation k X (AbsoluteBar.complex k R)).X n ≅
      (ModuleBar.complex k R X).X n :=
  (canonicalEquiv k R X (n+1)).toModuleIso

omit [CharP k 2] in
theorem canonicalDifferentialSquare (n : ℕ) :
    (EnvelopingBimodule.evaluationFunctor k R X).map
      (ModuleCat.ofHom (X := AbsoluteBar.moduleObject k R (n+1))
        (Y := AbsoluteBar.moduleObject k R n) (AbsoluteBar.differential k R n)) ≫
      (canonicalEquiv k R X n).toModuleIso.hom =
    (canonicalEquiv k R X (n+1)).toModuleIso.hom ≫
      ModuleCat.ofHom (X := ModuleBar.moduleObject k R X (n+1))
        (Y := ModuleBar.moduleObject k R X n) (ModuleBar.differential k R X n) :=
  canonical_square k R X (m := n+1) (n := n)
    (ModuleCat.ofHom (X := AbsoluteBar.moduleObject k R (n+1))
      (Y := AbsoluteBar.moduleObject k R n) (AbsoluteBar.differential k R n))
    (ModuleCat.ofHom (X := ModuleBar.moduleObject k R X (n+1))
      (Y := ModuleBar.moduleObject k R X n) (ModuleBar.differential k R X n))
    (canonicalEquiv_differential k R X n)

theorem canonicalTermIso_d (n : ℕ) :
    (canonicalTermIso k R X (n+1)).hom ≫ (ModuleBar.complex k R X).d (n+1) n =
      (ExternalBalanced.factorEvaluation k X (AbsoluteBar.complex k R)).d (n+1) n ≫
        (canonicalTermIso k R X n).hom := by
  change _ ≫ (ModuleBar.complex k R X).d (n+1) n =
    (EnvelopingBimodule.evaluationFunctor k R X).map
      ((AbsoluteBar.complex k R).d (n+1) n) ≫ _
  rw [ModuleBar.complex_d, AbsoluteBar.complex_d]
  exact (canonicalDifferentialSquare k R X (n+1)).symm

def canonicalComplexIso :
    ExternalBalanced.factorEvaluation k X (AbsoluteBar.complex k R) ≅ ModuleBar.complex k R X :=
  HomologicalComplex.Hom.isoOfComponents (canonicalTermIso k R X)
    (fun i j hij => by
      have h : j+1=i := hij
      subst i
      exact canonicalTermIso_d k R X j)

theorem canonicalComplexIso_f (n : ℕ) :
    (canonicalComplexIso k R X).hom.f n = (canonicalTermIso k R X n).hom := rfl

theorem canonicalTermIso_cubic (p : AbsoluteBar.Cochain3 k R) (n : ℕ) :
    (EnvelopingBimodule.evaluationFunctor k R X).map
      (cubicHom k R p n) ≫
      (canonicalTermIso k R X n).hom =
    (canonicalTermIso k R X (n+3)).hom ≫ ModuleBar.cubicMap k R X p n := by
  exact canonical_square k R X (m := n+4) (n := n+1)
    (cubicHom k R p n) (ModuleBar.cubicMap k R X p n)
    (canonicalEquiv_cubic k R X p n)

theorem canonicalComplexIso_cubic (p : AbsoluteBar.Cochain3 k R) (n : ℕ) :
    (EnvelopingBimodule.evaluationFunctor k R X).map
      (cubicHom k R p n) ≫
      (canonicalComplexIso k R X).hom.f n =
    (canonicalComplexIso k R X).hom.f (n+3) ≫ ModuleBar.cubicMap k R X p n := by
  rw [canonicalComplexIso_f, canonicalComplexIso_f]
  exact canonicalTermIso_cubic k R X p n

end ArExplicit.BarBalanced

end

end OAI
