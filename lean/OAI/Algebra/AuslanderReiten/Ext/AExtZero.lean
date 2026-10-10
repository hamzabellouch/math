import OAI.Algebra.AuslanderReiten.Ext.AExtPolynomial
import OAI.Algebra.AuslanderReiten.Stable.TensorStableEnd
import OAI.Algebra.AuslanderReiten.Ext.ExtCentralGeneration

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (hq1 : 1+q ≠ 0)
include hq1

omit [CharP k 2] in
theorem aExtZero_scalar (x : ASelfExt q 0) :
    ∃ c : k, x = c • Ext.mk₀ (𝟙 (ArExplicit.A.Simple q)) := by
  apply ResolutionProducts.extZero_scalar_of_hom (k := k) _ x
  intro f
  refine ⟨ArExplicit.A.endScalar q f.hom, ?_⟩
  apply ResolutionProducts.scalar_end_hom (k := k) (R := ArExplicit.A k q)
    (ArExplicit.A.Simple q) f
  intro x
  have hf := DFunLike.congr_fun (ArExplicit.A.end_eq_scalar_id q hq1 f.hom) x
  change f.hom x = ArExplicit.A.endScalar q f.hom • x at hf
  exact hf.trans (IsScalarTower.algebraMap_smul (ArExplicit.A k q) _ _).symm

omit [CharP k 2] in
theorem aExtZero_central (n : ℕ) (a : ASelfExt q n) (x : ASelfExt q 0) :
    a.comp x (by omega : n+0=n) = x.comp a (by omega : 0+n=n) := by
  obtain ⟨c,rfl⟩ := aExtZero_scalar q hq1 x
  rw [Ext.comp_smul, Ext.smul_comp, Ext.comp_mk₀_id, Ext.mk₀_id_comp]

end ArExplicit.Resolution

end

end OAI
