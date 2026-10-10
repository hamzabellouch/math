import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Blowup.LocalUniversal

namespace OAI


                                       
section

namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {X : Scheme.{0}}

lemma presented_frame_equation (I : X.IdealSheafData) (J : LineBundle X)
    (ι : J.sheaf ⟶ O X) (h : PresentsPullbackIdeal I (𝟙 X) J ι)
    (U : X.affineOpens) (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    I.ideal U = Ideal.span {U.1.topIso.hom (endValue (e.inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
        (Scheme.Modules.restrictUnitIso U.1.ι).hom))} := by
  let g : O U.1.toScheme ⟶ O U.1.toScheme :=
    e.inv ≫ restrictedInclusion J ι U.1.ι
  have H : ((I.comap (𝟙 X)).comap U.1.ι).ideal ⟨⊤,isAffineOpen_top _⟩ =
      Ideal.span {endValue g} := by
    change _ = Ideal.span {UnitEndomorphism.equation g ⊤}
    rw [← UnitEndomorphism.image_principal g ⊤,
      ← restricted_image_on_chart J ι h U.1.ι ⟨⊤,isAffineOpen_top _⟩ U
        (by simpa only [Scheme.Opens.ι_image_top,Scheme.Hom.id_preimage] using
          (le_rfl : U.1 ≤ U.1))]
    ext r
    change (∃ s, (restrictedInclusion J ι U.1.ι).val.app (op ⊤) s = r) ↔
      ∃ s, (restrictedInclusion J ι U.1.ι).val.app (op ⊤) (e.inv.val.app (op ⊤) s) = r
    constructor
    · rintro ⟨s,hs⟩
      refine ⟨e.hom.val.app (op ⊤) s,?_⟩
      have ht : e.inv.val.app (op ⊤) (e.hom.val.app (op ⊤) s) = s :=
        congrArg (fun k : J.sheaf.restrict U.1.ι ⟶ J.sheaf.restrict U.1.ι =>
          k.val.app (op ⊤) s) e.hom_inv_id
      rw [ht]; exact hs
    · rintro ⟨s,hs⟩
      exact ⟨e.inv.val.app (op ⊤) s,hs⟩
  rw [Scheme.IdealSheafData.comap_id,IdealPullback.comap_ι_top] at H
  have H' := congrArg (Ideal.map U.1.topIso.hom.hom) H
  rw [Ideal.map_map,Ideal.map_span,Set.image_singleton] at H'
  have hi : U.1.topIso.hom.hom.comp U.1.topIso.inv.hom = RingHom.id _ := by
    ext x; exact U.1.topIso.inv_hom_id_apply x
  rw [hi,Ideal.map_id] at H'
  exact H'

end
end MaximalSeshadri.InvertibleLocal

end



end OAI
