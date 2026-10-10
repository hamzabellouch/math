import OAI.NumberTheory.PiExponent.Approximation.FrameSections
import OAI.NumberTheory.PiExponent.Approximation.SectionPowerOpens
import OAI.NumberTheory.PiExponent.Approximation.TensorPure
import OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}}
def tensorFrame (L M : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) :
    (L.tensor M).sheaf.restrict U.ι ≅ O U.toScheme :=
  moduleTensorRestrict U L.sheaf M.sheaf ≪≫ moduleTensorIso e f ≪≫
    moduleTensorUnit (O U.toScheme)

end Geometry

namespace TensorPure

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}}

def tensorSection {M N : X.Modules} (s : O X ⟶ M) (t : O X ⟶ N) :
    O X ⟶ moduleTensor X M N :=
  (moduleTensorUnit (O X)).inv ≫ moduleTensorMap s t

lemma section_apply {M N : X.Modules} (s : O X ⟶ M) (t : O X ⟶ N) (U : X.Opens) :
    (tensorSection s t).app U (1 : Γ(X,U)) = pure M N U (s.app U (1 : Γ(X,U))) (t.app U (1 : Γ(X,U))) := by
  have h : (moduleTensorUnit (O X)).inv.app U (1 : Γ(X,U)) =
      pure (O X) (O X) U (1 : Γ(X,U)) (1 : Γ(X,U)) := by
    have he := unit_pure (O X) U (1 : Γ(X,U)) (1 : Γ(X,U))
    have he : (moduleTensorUnit (O X)).hom.app U (pure (O X) (O X) U (1 : Γ(X,U)) (1 : Γ(X,U))) = (1 : Γ(X,U)) := by
      simp only [O, structureSheaf] at he
      exact he.trans (by change (1 : Γ(X,U)) * 1 = 1; exact one_mul _)
    have hi := congrArg ((moduleTensorUnit (O X)).inv.app U) he
    change ((moduleTensorUnit (O X)).hom ≫ (moduleTensorUnit (O X)).inv).app U
      (pure (O X) (O X) U (1 : Γ(X,U)) (1 : Γ(X,U))) = _ at hi
    rw [Iso.hom_inv_id] at hi
    exact hi.symm
  change (moduleTensorMap s t).app U ((moduleTensorUnit (O X)).inv.app U (1 : Γ(X,U))) = _
  rw [h]
  exact map_pure s t U (1 : Γ(X,U)) (1 : Γ(X,U))

lemma framed_pure {M N : X.Modules} (e : M ≅ O X) (d : N ≅ O X) (U : X.Opens)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensorIso e d ≪≫ moduleTensorUnit (O X)).hom.app U (pure M N U m n) =
      (show Γ(X,U) from e.hom.app U m) * (show Γ(X,U) from d.hom.app U n) := by
  change (moduleTensorUnit (O X)).hom.app U ((moduleTensorMap e.hom d.hom).app U
    (pure M N U m n)) = _
  exact (congrArg ((moduleTensorUnit (O X)).hom.app U) (map_pure e.hom d.hom U m n)).trans
    (unit_pure (O X) U _ _)

lemma local_framed_pure (L M : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) (d : M.sheaf.restrict U.ι ≅ O U.toScheme)
    (V : U.toScheme.Opens) (m : L.sheaf.val.obj (op (U.ι ''ᵁ V)))
    (n : M.sheaf.val.obj (op (U.ι ''ᵁ V))) :
    (tensorFrame L M U e d).hom.app V (pure L.sheaf M.sheaf (U.ι ''ᵁ V) m n) =
      (show Γ(U.toScheme,V) from e.hom.app V m) * (show Γ(U.toScheme,V) from d.hom.app V n) := by
  change (moduleTensorIso e d ≪≫ moduleTensorUnit (O U.toScheme)).hom.app V
    ((moduleTensorRestrict U L.sheaf M.sheaf).hom.app V
      (pure L.sheaf M.sheaf (U.ι ''ᵁ V) m n)) = _
  exact (congrArg ((moduleTensorIso e d ≪≫ moduleTensorUnit (O U.toScheme)).hom.app V)
    (restrict_pure U L.sheaf M.sheaf V m n)).trans (framed_pure e d V m n)

lemma local_section_coefficient (L M : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) (d : M.sheaf.restrict U.ι ≅ O U.toScheme)
    (s : O X ⟶ L.sheaf) (t : O X ⟶ M.sheaf) :
    coefficient (tensorFrame L M U e d) (restrictSection U.ι (tensorSection s t)) =
      coefficient e (restrictSection U.ι s) * coefficient d (restrictSection U.ι t) := by
  change (tensorFrame L M U e d).hom.app ⊤
    ((tensorSection s t).app (U.ι ''ᵁ ⊤) ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme,⊤)))) =
    (show Γ(U.toScheme,⊤) from e.hom.app ⊤ (s.app (U.ι ''ᵁ ⊤)
      ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme,⊤))))) *
    (show Γ(U.toScheme,⊤) from d.hom.app ⊤ (t.app (U.ι ''ᵁ ⊤)
      ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme,⊤)))))
  rw [map_one]
  exact (congrArg ((tensorFrame L M U e d).hom.app ⊤) (section_apply s t _)).trans
    (local_framed_pure L M U e d ⊤ _ _)

lemma section_open (L M : LineBundle X) (s : O X ⟶ L.sheaf) (t : O X ⟶ M.sheaf) :
    isoOpen (tensorSection s t) = isoOpen s ⊓ isoOpen t := by
  apply SetLike.coe_injective
  ext x
  obtain ⟨U,hx,⟨e⟩,⟨d⟩⟩ := common_affine_frames L M x
  have h : U.1.ι ⁻¹ᵁ isoOpen (tensorSection s t) =
      U.1.ι ⁻¹ᵁ (isoOpen s ⊓ isoOpen t) := by
    calc
      _ = U.1.toScheme.basicOpen (coefficient (tensorFrame L M U.1 e d)
          (restrictSection U.1.ι (tensorSection s t))) :=
        preimage_isoOpen (tensorSection s t) U.1.ι (tensorFrame L M U.1 e d)
      _ = U.1.toScheme.basicOpen (coefficient e (restrictSection U.1.ι s) *
          coefficient d (restrictSection U.1.ι t)) :=
        congrArg U.1.toScheme.basicOpen (local_section_coefficient L M U.1 e d s t)
      _ = U.1.toScheme.basicOpen (coefficient e (restrictSection U.1.ι s)) ⊓
          U.1.toScheme.basicOpen (coefficient d (restrictSection U.1.ι t)) :=
        U.1.toScheme.basicOpen_mul _ _
      _ = _ := congrArg₂ (· ⊓ ·) (preimage_isoOpen s U.1.ι e).symm
        (preimage_isoOpen t U.1.ι d).symm
  exact SetLike.ext_iff.mp h ⟨x,hx⟩

end TensorPure

end PiExponentSeshadri

end

end OAI
