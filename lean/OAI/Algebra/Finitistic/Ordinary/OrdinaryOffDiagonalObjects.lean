import OAI.Algebra.Finitistic.Ordinary.OrdinaryOffDiagonalComplexMaps
import OAI.Algebra.Finitistic.Ordinary.OrdinaryRetainedRestriction

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.OffDiagonal
universe u
variable (k L R : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]
variable (O : ModuleCat.{u} (R ⊗[k] Lᵐᵒᵖ)) (T : ModuleCat.{u} (L ⊗[k] Rᵐᵒᵖ))

abbrev object : ModuleCat.{u} ((L × R) ⊗[k] (L × R)ᵐᵒᵖ) :=
  RetainedBimodule.object k (L × R) (L × R)
    (OffDiagonal (BimoduleCoefficients k R L O) (BimoduleCoefficients k L R T))

variable {O T} {O' : ModuleCat.{u} (R ⊗[k] Lᵐᵒᵖ)} {T' : ModuleCat.{u} (L ⊗[k] Rᵐᵒᵖ)}

def objectMap (f : O ⟶ O') (g : T ⟶ T') : object k L R O T ⟶ object k L R O' T' :=
  ModuleCat.ofHom (RetainedBimodule.map (k := k) (S := L × R) (A := L × R)
    (map (BimoduleCoefficients.map k R L f) (BimoduleCoefficients.map k L R g))
    (map_left (BimoduleCoefficients.map k R L f) (BimoduleCoefficients.map_left k R L f)
      (BimoduleCoefficients.map k L R g) (BimoduleCoefficients.map_left k L R g)))

def objectIso (f : O ≅ O') (g : T ≅ T') : object k L R O T ≅ object k L R O' T' where
  hom := objectMap k L R f.hom g.hom
  inv := objectMap k L R f.inv g.inv
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Prod.ext (congrArg (fun h => h.hom x.1) f.hom_inv_id)
      (congrArg (fun h => h.hom x.2) g.hom_inv_id)
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Prod.ext (congrArg (fun h => h.hom x.1) f.inv_hom_id)
      (congrArg (fun h => h.hom x.2) g.inv_hom_id)

theorem object_isZero (hO : IsZero O) (hT : IsZero T) : IsZero (object k L R O T) := by
  have := ModuleCat.isZero_iff_subsingleton.mp hO
  have := ModuleCat.isZero_iff_subsingleton.mp hT
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact inferInstanceAs (Subsingleton (O × T))
end LittleFinitistic.OrdinarySimulation.OffDiagonal

end

end OAI
