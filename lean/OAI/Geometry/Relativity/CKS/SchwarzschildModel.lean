import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.BoundaryCharts

namespace OAI

noncomputable section
open Set Manifold Bundle Filter
open scoped ContDiff Topology
namespace CKSSchwarzschild
open CKSBoundarySurface
attribute [local instance] Classical.propDecidable

@[simp] lemma join_zero (z : ℝ × E2) : join z 0 = z.1 := rfl
@[simp] lemma join_succ (z : ℝ × E2) (i : Fin 2) : join z i.succ = z.2 i := rfl
@[simp] lemma drop_join (z : ℝ × E2) : dropPlane (join z) = z.2 := by ext i; rfl
@[simp] lemma join_drop (z : E3) : join (z 0,dropPlane z) = z := by
  ext i; cases i using Fin.cases <;> rfl

@[simp] lemma halfProduct_val (z : Radial × E2) : (halfProduct z).val = join (z.1.val,z.2) := rfl
@[simp] lemma halfProduct_symm_fst (z : H3) : (halfProduct.symm z).1.val = z.val 0 := rfl
@[simp] lemma halfProduct_symm_snd (z : H3) : (halfProduct.symm z).2 = dropPlane z.val := rfl

@[simp] lemma productChart_source (s : Sphere) :
    (productChart s).source = Prod.snd ⁻¹' (chartAt E2 s).source := by
  ext p; simp [productChart]
attribute [local instance] halfSpaceDimension_neZero

@[simp] lemma productChart_target (s : Sphere) :
    (productChart s).target = (fun z : H3 => dropPlane z.val) ⁻¹' (chartAt E2 s).target := by
  ext p; simp [productChart]
@[simp] lemma productChart_apply (s : Sphere) (p : Exterior) :
    (productChart s p).val = join (p.1.val,chartAt E2 s p.2) := rfl
@[simp] lemma productChart_symm (s : Sphere) (z : H3) :
    (productChart s).symm z = (⟨z.val 0,z.property⟩,(chartAt E2 s).symm (dropPlane z.val)) := rfl

end CKSSchwarzschild

end

end OAI
