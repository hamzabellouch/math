import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.Sectors
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.OffsetFrames
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FrameCentrality

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FrameActions

variable {P H Q : Type*} [Group P] [Group H] [Group Q]

theorem CentralOn.commute_perfect [Group.IsPerfect P] (q : H →* Q) (S : Subgroup H)
    (h : CentralOn q S) (f : P →* H) (hf : f.range ≤ S) (z : H) (hz : z ∈ S)
    (hc : ∀ s, Commute (q z) (q (f s))) (s : P) : Commute z (f s) := by
  have he : (MulAut.conj z).toMonoidHom.comp f = f := by
    apply CentralOn.lift_unique q S h
    · rintro x ⟨s,rfl⟩
      exact S.mul_mem (S.mul_mem hz (hf ⟨s,rfl⟩)) (S.inv_mem hz)
    · exact hf
    · ext s : 1
      change q (z*f s*z⁻¹)=q (f s)
      rw [map_mul,map_mul,map_inv,(hc s).eq,mul_assoc,mul_inv_cancel,mul_one]
  have hh := DFunLike.congr_fun he s
  change z*f s*z⁻¹=f s at hh
  have hh' := congrArg (fun x => x*z) hh
  exact show z*f s=f s*z from by simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh'

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem frameStar_apply (I : Finset (Fin (m+1))) [Group.IsPerfect (alternatingGroup I)]
    (u : Fin (m+1) → CutRing × CutRing) (F : OffsetFrame a r m hm I u)
    (V : polygonAlgebra a) (s : UniversalExtension (alternatingGroup I))
    (i : I) (x : V.val) :
    (coverMap M (alternatingGenerator a r m hm) (B.frameStar hlarge h hr I u F V s)).val.val
      (i.val,translate a (u i.val) x.val) =
      (((universalProjection _ s).val i).val,
        translate a (u ((universalProjection _ s).val i).val) x.val) := by
  classical
  have hp := congrArg Subtype.val (B.frameStar_projection hlarge h hr I u F V s)
  change (coverMap M (alternatingGenerator a r m hm) (B.frameStar hlarge h hr I u F V s)).val =
    sourceLatticeFullMap a r m hm F.k * conditionalHom V (subtypeAlternatingHom I (universalProjection _ s)).val *
      (sourceLatticeFullMap a r m hm F.k)⁻¹ at hp
  rw [F.projection] at hp
  rw [hp]
  have hin : (trackTranslation (a := a) F.d).val (i.val,x.val) =
      (i.val,translate a (u i.val) x.val) := by
    change (i.val,translate a (F.d i.val) x.val) = _
    rw [F.prescribed i.val i.property]
  change (trackTranslation F.d).val
    (conditionalPerm V (subtypeAlternatingHom I (universalProjection _ s)).val
      ((trackTranslation F.d).val.symm (i.val,translate a (u i.val) x.val))) = _
  rw [← hin,Equiv.symm_apply_apply]
  have hcond : conditionalPerm V (subtypeAlternatingHom I (universalProjection _ s)).val
      (i.val,x.val) = (((universalProjection _ s).val i).val,x.val) := by
    change (if x.val ∈ V.val then Equiv.Perm.ofSubtype (universalProjection _ s).val i.val else i.val,x.val) = _
    rw [ite_eq_left x.property,Equiv.Perm.ofSubtype_apply_of_mem _ i.property]
  rw [hcond]
  change (_,translate a (F.d ((universalProjection _ s).val i).val) x.val)=_
  rw [F.prescribed _ ((universalProjection _ s).val i).property]

theorem frameStars_commute_perfect (I : Finset (Fin (m+1))) [Group.IsPerfect (alternatingGroup I)]
    (u : Fin (m+1) → CutRing × CutRing) (F : OffsetFrame a r m hm I u)
    (V : polygonAlgebra a) (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ ⨆ W : polygonAlgebra a, (B.frameStar hlarge h hr I u F W).range)
    (hc : ∀ s, Commute (coverMap M (alternatingGenerator a r m hm) z)
      (coverMap M (alternatingGenerator a r m hm) (B.frameStar hlarge h hr I u F V s)))
    (s : UniversalExtension (alternatingGroup I)) :
    Commute z (B.frameStar hlarge h hr I u F V s) :=
  CentralOn.commute_perfect _ _ (B.frameStars_central hlarge h hr I u F)
    (B.frameStar hlarge h hr I u F V)
    (le_iSup (fun W : polygonAlgebra a => (B.frameStar hlarge h hr I u F W).range) V) z hz hc s

end InitialCoverSystem
end FrameActions

end SimpleAmenable
end
end

end OAI
