import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ConditionalFamilyLaws
import OAI.GroupTheory.SimpleAmenable.CentralCovers.GlobalAlignedCentrality
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.OffsetFrames

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FrameCentrality

variable {H Q : Type*} [Group H] [Group Q]

theorem CentralOn.conjugate {q : H →* Q} {S : Subgroup H} (h : CentralOn q S) (z : H) :
    CentralOn q (S.map (MulAut.conj z).toMonoidHom) := by
  rw [centralOn_iff] at h ⊢
  rintro _ ⟨x,hx,rfl⟩ he _ ⟨y,hy,rfl⟩
  change q (z*x*z⁻¹) = 1 at he
  have hqx : q x = 1 := by
    have hh := congrArg (fun t => (q z)⁻¹*t*q z) he
    simpa [mul_assoc] using hh
  exact (h x hx hqx y hy).map (MulAut.conj z).toMonoidHom

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem frameStars_central (I : Finset (Fin (m+1))) [Group.IsPerfect (alternatingGroup I)]
    (u : Fin (m+1) → CutRing × CutRing) (F : OffsetFrame a r m hm I u) :
    CentralOn (coverMap M (alternatingGenerator a r m hm))
      (⨆ V : polygonAlgebra a, (B.frameStar hlarge h hr I u F V).range) := by
  apply ((B.polygonStars_central hlarge h hr).conjugate (B.t F.k)).mono
  apply iSup_le
  intro V x hx
  obtain ⟨s,rfl⟩ := hx
  exact ⟨B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) s),
    (le_iSup (fun W : polygonAlgebra a => (B.polygonStar hlarge h hr W).range) V)
      ⟨_,rfl⟩,rfl⟩

theorem frameStar_union (I : Finset (Fin (m+1))) [Group.IsPerfect (alternatingGroup I)]
    (u : Fin (m+1) → CutRing × CutRing) (F : OffsetFrame a r m hm I u)
    (V W : polygonAlgebra a) (hd : Disjoint V.val W.val)
    (s : UniversalExtension (alternatingGroup I)) :
    B.frameStar hlarge h hr I u F (V ⊔ W) s =
      B.frameStar hlarge h hr I u F V s * B.frameStar hlarge h hr I u F W s := by
  change (MulAut.conj (B.t F.k)).toMonoidHom
    (B.polygonStar hlarge h hr (V ⊔ W) (universalMap (subtypeAlternatingHom I) s)) = _
  rw [B.polygonStar_union hlarge h hr V W hd,map_mul]
  rfl

theorem frameStar_commute (I : Finset (Fin (m+1))) [Group.IsPerfect (alternatingGroup I)]
    (u : Fin (m+1) → CutRing × CutRing) (F : OffsetFrame a r m hm I u)
    (V W : polygonAlgebra a) (hd : Disjoint V.val W.val)
    (s t : UniversalExtension (alternatingGroup I)) :
    Commute (B.frameStar hlarge h hr I u F V s) (B.frameStar hlarge h hr I u F W t) :=
  (B.polygonStar_commute hlarge h hr V W hd _ _).map (MulAut.conj (B.t F.k)).toMonoidHom

theorem frameStar_empty (I : Finset (Fin (m+1))) [Group.IsPerfect (alternatingGroup I)]
    (u : Fin (m+1) → CutRing × CutRing) (F : OffsetFrame a r m hm I u) :
    B.frameStar hlarge h hr I u F ⊥ = 1 := by
  ext s : 1
  change (MulAut.conj (B.t F.k)).toMonoidHom
    (B.polygonStar hlarge h hr ⊥ (universalMap (subtypeAlternatingHom I) s)) = 1
  rw [B.polygonStar_empty hlarge h hr]
  exact map_one _

end InitialCoverSystem
end FrameCentrality

end SimpleAmenable
end
end

end OAI
