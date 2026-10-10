import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Blowup.Gluing

namespace OAI


                                      
section

namespace MaximalSeshadri
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

instance AffineBlowup.projection_proper {X : Scheme.{0}} [IsAffine X]
    [IsLocallyNoetherian X] (I : X.IdealSheafData) : IsProper (AffineBlowup.projection I) := by
  let : IsNoetherianRing Γ(X,⊤) := IsLocallyNoetherian.component_noetherian ⟨⊤,isAffineOpen_top X⟩
  unfold AffineBlowup.projection
  infer_instance

instance BlowupGluing.projection_proper {X : Scheme.{0}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) : IsProper (BlowupGluing.projection I) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsProper) (BlowupGluing.baseCover I)
  intro U
  let he := (BlowupGluing.local_pullback I U).flip.isoPullback
  have hh : he.hom ≫ pullback.snd (BlowupGluing.projection I) U.toOpens.ι =
      BlowupGluing.localProjection I U := by
    exact (BlowupGluing.local_pullback I U).flip.isoPullback_hom_snd
  have h : IsProper (BlowupGluing.localProjection I U) := by infer_instance
  rw [← hh] at h
  exact (MorphismProperty.cancel_left_of_respectsIso (@IsProper) he.hom _).mp h

end
end MaximalSeshadri

end


end OAI
