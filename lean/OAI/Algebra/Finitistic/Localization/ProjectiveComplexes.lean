import OAI.Algebra.Finitistic.Localization.BoundedHomotopy
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Finiteness.Basic

namespace OAI
noncomputable section
open CategoryTheory Limits
namespace LittleFinitistic.ProjectiveComplexes
universe u
variable (B : Type u) [Ring B]

/-- Right B-modules are left modules over the opposite ring. -/
abbrev RightModule := ModuleCat.{u} Bᵐᵒᵖ

def finiteProjective : ObjectProperty (RightModule B) :=
  fun M => Module.Finite Bᵐᵒᵖ M ∧ Module.Projective Bᵐᵒᵖ M

instance : (finiteProjective B).IsClosedUnderIsomorphisms where
  of_iso e h := by
    let := h.1
    let := h.2
    exact ⟨Module.Finite.equiv e.toLinearEquiv,
      Module.Projective.of_equiv e.toLinearEquiv⟩

instance : (finiteProjective B).ContainsZero where
  exists_zero := ⟨ModuleCat.of Bᵐᵒᵖ PUnit, ModuleCat.isZero_of_subsingleton _,
    by constructor <;> infer_instance⟩

instance : (finiteProjective B).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    let M := p.diag.obj (.mk .left)
    let N := p.diag.obj (.mk .right)
    have hM := p.prop_diag_obj (.mk .left)
    have hN := p.prop_diag_obj (.mk .right)
    let := hM.1
    let := hM.2
    let := hN.1
    let := hN.2
    have hp : finiteProjective B (ModuleCat.of Bᵐᵒᵖ (M × N)) :=
      ⟨inferInstance, inferInstance⟩
    apply (finiteProjective B).prop_of_iso _ hp
    exact IsLimit.conePointUniqueUpToIso (ModuleCat.binaryProductLimitCone M N).isLimit
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)

instance : (finiteProjective B).IsClosedUnderFiniteProducts := .mk'

/-- The additive category of finitely generated projective right B-modules. -/
abbrev Proj := (finiteProjective B).FullSubcategory

instance : HasBinaryBiproducts (Proj B) := .of_hasBinaryProducts

/-- The actual category of bounded complexes of finitely generated projectives. -/
abbrev Complex := BoundedHomotopy.Complex (Proj B)

/-- Section 3's K = Kᵇ(proj-B), with homotopy classes of chain maps. -/
abbrev K := BoundedHomotopy.K (Proj B)

example : HasBinaryBiproducts (Proj B) := inferInstance
example : IsTriangulated (K B) := inferInstance

/-- The passage from bounded projective complexes to their homotopy category. -/
abbrev quotient : Complex B ⥤ K B := BoundedHomotopy.quotient (Proj B)

end LittleFinitistic.ProjectiveComplexes

end

end OAI
