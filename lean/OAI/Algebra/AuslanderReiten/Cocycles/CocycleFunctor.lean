import OAI.Algebra.AuslanderReiten.HomComplex.FullHomFunctor
import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionProducts

namespace OAI

noncomputable section
open CategoryTheory CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
variable (F : C ⥤ D) [F.Additive]
variable {K L : CochainComplex C ℤ} {n : ℤ}

theorem cocycle_map_hom (x : Cocycle K L n) :
    Cocycle.equivHomShift.symm (fullHomCocycleMap F K L n x) =
      ShiftedHom.map (Cocycle.equivHomShift.symm x) (F.mapHomologicalComplex (.up ℤ)) := by
  ext i
  change F.map (x.val.v i (i+n) rfl) ≫ 𝟙 _ =
    F.map (x.val.v i (i+n) rfl ≫ 𝟙 _) ≫ 𝟙 _
  simp

end ArExplicit.ResolutionProducts

end

end OAI
