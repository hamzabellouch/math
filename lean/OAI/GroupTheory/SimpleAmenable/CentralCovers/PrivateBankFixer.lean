import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PrivateBankWord

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
namespace InitialCoverSystem

section
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem private_bank_fixer (e : (Fin 5 × Fin 5) ↪ Fin (m+1))
    (b : Fin (m+1)) (hb : b ∉ bankAlphabet e)
    (u : Fin (m+1) → CutRing × CutRing) (v : Fin 5 → CutRing × CutRing)
    (hu : ∀ i j, u (e (i,j))=v i) (F : OffsetFrame a r m hm (bankAlphabet e) u)
    (V : polygonAlgebra a) (J : Finset (Fin (m+1)))
    (hJ : Disjoint J (orderedTrackAlphabet (bankColumn e 1)))
    (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range)
    (hzJ : z ∈ sourceAlignedGroup a r m hm M B.t J)
    (hfix : ∀ (i j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (e (i,j),translate a (u (e (i,j))) x.val) =
        (e (i,j),translate a (u (e (i,j))) x.val))
    (s : UniversalExtension (alternatingGroup (Fin 5))) :
    Commute z (B.distinctSlotStar hlarge h hr (bankColumn e 0) u
      (F.restrict (bankColumn_subset e 0)) V s) := by
  obtain ⟨w,hw,hzw,ht⟩ := B.private_bank_evacuation hlarge h hr e b hb u v hu F V z hz hfix
  have he := DFunLike.congr_fun (B.distinctSlotStar_common_frame_transport hlarge h hr
    (bankColumn e 0) (bankColumn e 1) u u
    (F.restrict (bankColumn_subset e 0)) (F.restrict (bankColumn_subset e 1)) rfl V w hw ht) s
  change w*B.distinctSlotStar hlarge h hr (bankColumn e 0) u
      (F.restrict (bankColumn_subset e 0)) V s*w⁻¹ =
    B.distinctSlotStar hlarge h hr (bankColumn e 1) u
      (F.restrict (bankColumn_subset e 1)) V s at he
  have hc : Commute z (B.distinctSlotStar hlarge h hr (bankColumn e 1) u
      (F.restrict (bankColumn_subset e 1)) V s) := by
    apply B.disjoint_aligned J (orderedTrackAlphabet (bankColumn e 1)) hJ z hzJ
    exact B.frameStar_alphabet_mem hlarge h hr _
      (by rw [orderedTrackAlphabet,Finset.card_map,Finset.card_univ,Fintype.card_fin])
      b (fun hi => hb (bankColumn_subset e 1 hi)) u
      (F.restrict (bankColumn_subset e 1)) V (universalMap (orderedTrackHom (bankColumn e 1)) s)
  have hh := (hzw.inv_right.mul_right hc).mul_right hzw
  rw [← he] at hh
  have he' : w⁻¹*(w*B.distinctSlotStar hlarge h hr (bankColumn e 0) u
      (F.restrict (bankColumn_subset e 0)) V s*w⁻¹)*w =
    B.distinctSlotStar hlarge h hr (bankColumn e 0) u (F.restrict (bankColumn_subset e 0)) V s := by group
  rwa [he'] at hh

end

section
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem sourceAlignedGroup_supported (J : Finset (Fin (m+1)))
    (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ sourceAlignedGroup a r m hm M B.t J) :
    SupportedIn (coverMap M (alternatingGenerator a r m hm) z).val.val
      {p : TrackPoint a (m+1) | p.1 ∈ J} := by
  classical
  let q : BoundedRelationCover M (alternatingGenerator a r m hm) →* Equiv.Perm (TrackPoint a (m+1)) :=
    (polygonFullGroup a (m+1)).subtype.comp
      ((polygonAlternatingGroup a (m+1)).subtype.comp (coverMap M (alternatingGenerator a r m hm)))
  let K : Subgroup (BoundedRelationCover M (alternatingGenerator a r m hm)) := {
    carrier := {z | SupportedIn (q z) {p : TrackPoint a (m+1) | p.1 ∈ J}}
    one_mem' := by intro p hp; simp
    mul_mem' := by
      intro x y hx hy p hp
      rw [map_mul,Equiv.Perm.mul_apply,hy p hp,hx p hp]
    inv_mem' := by
      intro x hx
      change SupportedIn (q x⁻¹) _
      rw [map_inv]
      exact supported_inv hx }
  have hK : sourceAlignedGroup a r m hm M B.t J ≤ K := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨c,hc,k,rfl⟩
    change SupportedIn (q (B.t k * PresentedGroup.of (sourceConditionalLabel m c) * (B.t k)⁻¹)) _
    rw [map_mul,map_mul,map_inv]
    obtain ⟨d,hd⟩ := sourceLatticeFullMap_translation a r m hm k
    have ht : q (B.t k) = (trackTranslation (a:=a) d).val := by
      have ht := congrArg Subtype.val (DFunLike.congr_fun B.t_projection k)
      change (coverMap M (alternatingGenerator a r m hm) (B.t k)).val =
        sourceLatticeFullMap a r m hm k at ht
      exact congrArg Subtype.val (ht.trans hd)
    rw [ht]
    have hs : SupportedIn (q (PresentedGroup.of (sourceConditionalLabel m c)))
        {p : TrackPoint a (m+1) | p.1 ∈ J} := by
      intro p hp
      have hf : c.2.val p.1=p.1 := Equiv.Perm.notMem_support.mp (fun hi => hp (hc hi))
      change (conditionalPerm (initialTest a r c.1) c.2.val) p=p
      simp [conditionalPerm,hf]
    apply (supported_conjugate (trackTranslation (a:=a) d).val hs).mono
    rintro p ⟨⟨i,x⟩,hi,rfl⟩
    exact hi
  exact hK hz

end

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem private_bank_source_fixer (e : (Fin 5 × Fin 5) ↪ Fin (m+1))
    (b : Fin (m+1)) (hb : b ∉ bankAlphabet e)
    (u : Fin (m+1) → CutRing × CutRing) (v : Fin 5 → CutRing × CutRing)
    (hu : ∀ i j, u (e (i,j))=v i) (F : OffsetFrame a r m hm (bankAlphabet e) u)
    (V : polygonAlgebra a) (J : Finset (Fin (m+1)))
    (hprivate : ∀ i j : Fin 5, j≠0 → e (i,j) ∉ J)
    (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range)
    (hzJ : z ∈ sourceAlignedGroup a r m hm M B.t J)
    (hfix : ∀ (i : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (e (i,0),translate a (u (e (i,0))) x.val) =
        (e (i,0),translate a (u (e (i,0))) x.val))
    (s : UniversalExtension (alternatingGroup (Fin 5))) :
    Commute z (B.distinctSlotStar hlarge h hr (bankColumn e 0) u
      (F.restrict (bankColumn_subset e 0)) V s) := by
  apply B.private_bank_fixer hlarge h hr e b hb u v hu F V J _ z hz hzJ _ s
  · apply Finset.disjoint_left.mpr
    intro k hk hk'
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hk'
    exact hprivate j 1 (by decide) hk
  · intro i j x
    by_cases hj : j=0
    · subst j; exact hfix i x
    · exact B.sourceAlignedGroup_supported J z hzJ _ (hprivate i j hj)

end InitialCoverSystem

end SimpleAmenable

end OAI
