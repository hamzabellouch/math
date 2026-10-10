import OAI.Algebra.AuslanderReiten.Ext.AExtZero

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] (q : k) (hq1 : 1+q ≠ 0)
include hq1

theorem aEndHom_scalar (f : ArExplicit.A.Simple q ⟶ ArExplicit.A.Simple q) :
    ∃ c : k, ∀ x : ArExplicit.A.Simple q, f.hom x = (algebraMap k (ArExplicit.A k q) c) • x := by
  refine ⟨ArExplicit.A.endScalar q f.hom, ?_⟩
  intro x
  have hf := DFunLike.congr_fun (ArExplicit.A.end_eq_scalar_id q hq1 f.hom) x
  change f.hom x = ArExplicit.A.endScalar q f.hom • x at hf
  exact hf.trans (IsScalarTower.algebraMap_smul (ArExplicit.A k q) _ _).symm

end ArExplicit.Resolution

end

end OAI
