import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.SectorControl
import OAI.GroupTheory.SimpleAmenable.Homology.FinitePrimitiveResolution
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FrameActions

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section FrameDisjointness

namespace OffsetFrame
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {I J : Finset (Fin (m+1))} {u : Fin (m+1) → CutRing × CutRing}

def restrict (F : OffsetFrame a r m hm J u) (hIJ : I ⊆ J) : OffsetFrame a r m hm I u where
  k := F.k
  d := F.d
  projection := F.projection
  prescribed := fun i hi => F.prescribed i (hIJ hi)

end OffsetFrame

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem polygonStar_alphabet_aligned (I : Finset (Fin (m+1))) (hI : 5 ≤ I.card)
    [Group.IsPerfect (alternatingGroup I)] (b : Fin (m+1)) (hb : b ∉ I)
    (V : polygonAlgebra a) (s : UniversalExtension (alternatingGroup I)) :
    B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) s) ∈
      sourceAlignedGroup a r m hm M B.t I := by
  obtain ⟨S,hS⟩ := polygon_finite_primitive_resolution r hr V
  let P : S → Fin 5 × (CutRing × CutRing) := fun p => p.val
  have hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val := hS
  rw [B.polygonStar_eq hlarge h hr P V hV]
  have he := DFunLike.congr_fun (B.fullGeometricSector_inclusion hlarge P (fun J _ d hd => h S P J d hd) I hI b hb
    (h S P I b hb) V hV) s
  change B.fullGeometricSector hlarge P (fun J _ d hd => h S P J d hd) V (universalMap (subtypeAlternatingHom I) s) = _ at he
  rw [he]
  exact B.geometricSector_aligned I b hb P _ V s

theorem frameStar_subalphabet {I J : Finset (Fin (m+1))}
    [Group.IsPerfect (alternatingGroup I)] [Group.IsPerfect (alternatingGroup J)]
    (hIJ : I ⊆ J) (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm J u) (V : polygonAlgebra a) :
    (B.frameStar hlarge h hr J u F V).comp (universalMap (subalphabetHom hIJ)) =
      B.frameStar hlarge h hr I u (F.restrict hIJ) V := by
  unfold frameStar
  rw [MonoidHom.comp_assoc,MonoidHom.comp_assoc,← universalMap_comp,subtypeAlternatingHom_comp]
  rfl

theorem frameStar_disjoint_alphabets (I J : Finset (Fin (m+1)))
    (hI : 5 ≤ I.card) (hJ : 5 ≤ J.card)
    [Group.IsPerfect (alternatingGroup I)] [Group.IsPerfect (alternatingGroup J)]
    (hIJ : Disjoint I J) (b : Fin (m+1)) (hb : b ∉ I ∪ J)
    (u v : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm I u) (G : OffsetFrame a r m hm J v)
    (V W : polygonAlgebra a) (s : UniversalExtension (alternatingGroup I))
    (t : UniversalExtension (alternatingGroup J)) :
    Commute (B.frameStar hlarge h hr I u F V s) (B.frameStar hlarge h hr J v G W t) := by
  classical
  have hbI : b ∉ I := fun hi => hb (Finset.mem_union_left _ hi)
  have hbJ : b ∉ J := fun hj => hb (Finset.mem_union_right _ hj)
  let w : Fin (m+1) → CutRing × CutRing := fun i => if i ∈ I then u i else v i
  let K := balancedOffsetFrame a r m hm (I ∪ J) b hb w
  let F' : OffsetFrame a r m hm I u := {
    k := K.k
    d := K.d
    projection := K.projection
    prescribed := by
      intro i hi
      rw [K.prescribed i (Finset.mem_union_left _ hi)]
      simp only [w,hi,ite_eq_left] }
  let G' : OffsetFrame a r m hm J v := {
    k := K.k
    d := K.d
    projection := K.projection
    prescribed := by
      intro i hi
      rw [K.prescribed i (Finset.mem_union_right _ hi)]
      have hn : i ∉ I := fun hI => Finset.disjoint_left.mp hIJ hI hi
      simp only [w,hn,ite_false] }
  rw [B.frameStar_independent hlarge h hr I hI b hbI u u F F' (fun _ _ => rfl) V,
    B.frameStar_independent hlarge h hr J hJ b hbJ v v G G' (fun _ _ => rfl) W]
  exact (B.disjoint_aligned I J hIJ _
    (B.polygonStar_alphabet_aligned hlarge h hr I hI b hbI V s) _
    (B.polygonStar_alphabet_aligned hlarge h hr J hJ b hbJ W t)).map (MulAut.conj (B.t K.k)).toMonoidHom

end InitialCoverSystem
end FrameDisjointness

theorem supported_fixer_commute {α : Type*} {f g : Equiv.Perm α} {U : Set α}
    (hf : ∀ p ∈ U, f p = p) (hg : SupportedIn g U) : Commute f g := by
  apply Equiv.Perm.Disjoint.commute
  intro p
  by_cases hp : p ∈ U
  · exact Or.inl (hf p hp)
  · exact Or.inr (hg p hp)

theorem conditional_alphabet_supported {a m : ℕ} (I : Finset (Fin m))
    (V : polygonAlgebra a) (s : alternatingGroup I) :
    SupportedIn (conditionalHom V (subtypeAlternatingHom I s).val).val
      {p : TrackPoint a m | p.1 ∈ I ∧ p.2 ∈ V.val} := by
  classical
  rintro ⟨i,x⟩ hp
  change (if x∈V.val then (subtypeAlternatingHom I s).val i else i,x) = (i,x)
  by_cases hx : x ∈ V.val
  · have hi : i ∉ I := fun hi => hp ⟨hi,hx⟩
    have he : (subtypeAlternatingHom I s).val i = i := by
      change Equiv.Perm.ofSubtype s.val i = i
      exact Equiv.Perm.ofSubtype_apply_of_not_mem _ hi
    rw [ite_eq_left hx,he]
  · rw [ite_eq_right hx]

def frameDomain {a m : ℕ} (I : Finset (Fin m)) (u : Fin m → CutRing × CutRing)
    (V : polygonAlgebra a) : Set (TrackPoint a m) :=
  {p | ∃ i ∈ I, ∃ x ∈ V.val, p = (i,translate a (u i) x)}

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem frameStar_supported (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)] (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm I u) (V : polygonAlgebra a)
    (s : UniversalExtension (alternatingGroup I)) :
    SupportedIn (coverMap M (alternatingGenerator a r m hm)
      (B.frameStar hlarge h hr I u F V s)).val.val (frameDomain I u V) := by
  have hp := congrArg Subtype.val (B.frameStar_projection hlarge h hr I u F V s)
  change (coverMap M (alternatingGenerator a r m hm) (B.frameStar hlarge h hr I u F V s)).val =
    sourceLatticeFullMap a r m hm F.k * conditionalHom V (subtypeAlternatingHom I (universalProjection _ s)).val *
      (sourceLatticeFullMap a r m hm F.k)⁻¹ at hp
  rw [F.projection] at hp
  rw [hp]
  apply (supported_conjugate (trackTranslation F.d).val
    (conditional_alphabet_supported I V (universalProjection _ s))).mono
  rintro p ⟨⟨i,x⟩,⟨hi,hx⟩,rfl⟩
  refine ⟨i,hi,x,hx,?_⟩
  change (i,translate a (F.d i) x)=(i,translate a (u i) x)
  rw [F.prescribed i hi]

theorem polygonStars_pointwise_fixer (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)] (V : polygonAlgebra a)
    (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range)
    (hfix : ∀ i ∈ I, ∀ x ∈ V.val,
      (coverMap M (alternatingGenerator a r m hm) z).val.val (i,x)=(i,x))
    (s : UniversalExtension (alternatingGroup I)) :
    Commute z (B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) s)) := by
  apply CentralOn.commute_perfect (coverMap M (alternatingGenerator a r m hm)) _
    (B.polygonStars_central hlarge h hr)
    ((B.polygonStar hlarge h hr V).comp (universalMap (subtypeAlternatingHom I))) _ z hz _ s
  · rintro y ⟨t,rfl⟩
    exact (le_iSup (fun W : polygonAlgebra a => (B.polygonStar hlarge h hr W).range) V)
      ⟨universalMap (subtypeAlternatingHom I) t,rfl⟩
  · intro t
    have hp := DFunLike.congr_fun (B.polygonStar_projection hlarge h hr V)
      (universalMap (subtypeAlternatingHom I) t)
    change coverMap M (alternatingGenerator a r m hm)
      (B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) t)) =
      conditionalAlternatingHom V (universalProjection _ (universalMap (subtypeAlternatingHom I) t)) at hp
    rw [show universalProjection _ (universalMap (subtypeAlternatingHom I) t) =
      subtypeAlternatingHom I (universalProjection _ t) from
      DFunLike.congr_fun (universalMap_spec (subtypeAlternatingHom I)) t] at hp
    change Commute (coverMap M (alternatingGenerator a r m hm) z)
      (coverMap M (alternatingGenerator a r m hm)
        (B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) t)))
    rw [hp]
    have hc := supported_fixer_commute (fun (p : TrackPoint a (m+1)) (hp : p.1 ∈ I ∧ p.2 ∈ V.val) => hfix _ hp.1 _ hp.2)
      (conditional_alphabet_supported I V (universalProjection _ t))
    exact show _*_ = _*_ from Subtype.ext (Subtype.ext hc.eq)

end InitialCoverSystem

end SimpleAmenable

end OAI
