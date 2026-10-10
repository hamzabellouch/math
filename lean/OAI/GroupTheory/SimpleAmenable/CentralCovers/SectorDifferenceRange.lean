import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.AxisAnchorFamily
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ClippedIntervals

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SectorDifferenceRange
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_sdiff_range (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V W : polygonAlgebra a) (hWV : W ≤ V)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) W.val)
    (K : Subgroup (BoundedRelationCover M (alternatingGenerator a r m hm)))
    (hV : (B.fullGeometricSector hlarge P h V).range ≤ K)
    (hW' : (B.fullGeometricSector hlarge P h W).range ≤ K) :
    (B.fullGeometricSector hlarge P h (V \ W)).range ≤ K := by
  have he : W ⊔ (V \ W) = V := by
    apply Subtype.ext
    ext x
    change (x ∈ W.val ∨ x ∈ V.val ∧ x ∉ W.val) ↔ x ∈ V.val
    constructor
    · rintro (hx|hx); exact hWV hx; exact hx.1
    · intro hx; by_cases hh : x ∈ W.val; exact Or.inl hh; exact Or.inr ⟨hx,hh⟩
  have hd : Disjoint W.val (V \ W).val := Set.disjoint_left.mpr (by rintro x hx ⟨_,h⟩; exact h hx)
  rintro x ⟨s,rfl⟩
  have hh := B.fullGeometricSector_union hlarge P h W (V \ W) hW hd s
  rw [he] at hh
  have hm := K.mul_mem (K.inv_mem (hW' ⟨s,rfl⟩)) (hV ⟨s,rfl⟩)
  rw [hh,inv_mul_cancel_left] at hm
  exact hm

end InitialCoverSystem
end SectorDifferenceRange

section AnchorIntersectionRange
attribute [local instance] cutOrdinaryOrder
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem axisSector_anchor_intersection_range (hlarge : 15 < m+1) (n : ℕ) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (k : ℕ) (hk : k ≤ n) (p : ℤ) (u v s t : CutRing)
    (huv : ordinary u ≤ ordinary v) (hlen : ordinary v-ordinary u < 1)
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k)
    (hs : p ≤ endpointLabel s ∧ endpointLabel s < p+k)
    (ht : p ≤ endpointLabel t ∧ endpointLabel t < p+k)
    (K : Subgroup (BoundedRelationCover M (alternatingGenerator a r m hm)))
    (hU : (B.axisSector hlarge n g d k hk p (coordinateInterval a d u v)).range ≤ K)
    (hS : (B.axisSector hlarge n g d k hk p
      (coordinateInterval a d u (clippedLabel u v (endpointLabel s)))).range ≤ K)
    (hT : (B.axisSector hlarge n g d k hk p
      (coordinateInterval a d u (clippedLabel u v (endpointLabel t)))).range ≤ K) :
    (B.axisSector hlarge n g d k hk p
      (coordinateInterval a d u v ⊓ coordinateInterval a d s t)).range ≤ K := by
  let S := coordinateInterval a d u (clippedLabel u v (endpointLabel s))
  let T := coordinateInterval a d u (clippedLabel u v (endpointLabel t))
  have hsl : p ≤ endpointLabel (clippedLabel u v (endpointLabel s)) ∧
      endpointLabel (clippedLabel u v (endpointLabel s)) < p+k := by
    rcases clippedLabel_label u v (endpointLabel s) with h|h <;> rw [h] <;> assumption
  have htl : p ≤ endpointLabel (clippedLabel u v (endpointLabel t)) ∧
      endpointLabel (clippedLabel u v (endpointLabel t)) < p+k := by
    rcases clippedLabel_label u v (endpointLabel t) with h|h <;> rw [h] <;> assumption
  have hSr := axisInterval_resolved (a := a) (r := r) d k p u _ hu hsl
  have hTr := axisInterval_resolved (a := a) (r := r) d k p u _ hu htl
  have hSb := clippedLabel_bounds u v (endpointLabel s) huv
  have hTb := clippedLabel_bounds u v (endpointLabel t) huv
  rw [coordinateInterval_anchor_formula d u v s t huv hlen]
  split_ifs with h
  · apply B.fullGeometricSector_sdiff_range hlarge _ _ T S ?_ hSr K hT hS
    apply coordinateInterval_mono d _ _ _ _ le_rfl hSb.1 ?_ (by linarith)
    exact min_le_min_left v h
  · have hST : T ≤ S := by
      apply coordinateInterval_mono d _ _ _ _ le_rfl hTb.1 ?_ (by linarith)
      exact min_le_min_left v (le_of_not_ge h)
    have hdiff : (B.axisSector hlarge n g d k hk p (S \ T)).range ≤ K :=
      B.fullGeometricSector_sdiff_range hlarge _ _ S T hST hTr K hS hT
    apply B.fullGeometricSector_sdiff_range hlarge _ _ _ (S \ T) ?_ ?_ K hU hdiff
    · exact (sdiff_le : S \ T ≤ S).trans (coordinateInterval_mono d _ _ _ _ le_rfl hSb.1 hSb.2 hlen)
    · exact BooleanSubalgebra.sdiff_mem (L := resolvedAlgebra _) hSr hTr

end InitialCoverSystem
end AnchorIntersectionRange

section AnchorGeneration
namespace AxisAnchorFamily
variable {n l : ℕ} {q : ℤ} (A : AxisAnchorFamily n l q)
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (g : B.CoordinateWindowLaw n) (d : Fin 2)

noncomputable def prefixGroup : Subgroup (BoundedRelationCover M (alternatingGenerator a r m hm)) :=
  ⨆ i : Fin l, ⨆ j : Fin (A.count i+1), ((A.cuts i).prefixCopy B hlarge g d j.val).range

theorem anchor_range_prefixGroup (i : Fin l) :
    ((A.cuts i).anchorCopy B hlarge g d).range ≤ A.prefixGroup B hlarge g d := by
  unfold prefixGroup
  rw [← (A.cuts i).prefix_last B hlarge g d]
  exact (le_iSup (fun j : Fin (A.count i+1) => ((A.cuts i).prefixCopy B hlarge g d j.val).range)
    (Fin.last (A.count i))).trans (le_iSup (fun i : Fin l => ⨆ j : Fin (A.count i+1),
      ((A.cuts i).prefixCopy B hlarge g d j.val).range) i)

theorem interval_prefix_range (i : Fin l) (k : ℕ) (hk : k ≤ n) (p : ℤ) (v : CutRing)
    (hu : p ≤ endpointLabel ((A.cuts i).cut 0) ∧ endpointLabel ((A.cuts i).cut 0) < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k)
    (hcut : v ∈ Set.range (A.cuts i).cut) :
    (B.axisSector hlarge n g d k hk p (coordinateInterval a d ((A.cuts i).cut 0) v)).range ≤
      A.prefixGroup B hlarge g d := by
  unfold prefixGroup
  obtain ⟨j,rfl⟩ := hcut
  have he : B.axisSector hlarge n g d k hk p (coordinateInterval a d ((A.cuts i).cut 0) ((A.cuts i).cut j)) =
      (A.cuts i).prefixCopy B hlarge g d j.val := by
    simp only [AxisCutSequence.prefixCopy,AxisCutSequence.index_fin]
    exact B.axisInterval_copy_eq hlarge n g d _ _ _ _ _ _ _ _ hu hv
      ((A.cuts i).lower_label j) ((A.cuts i).cut_label j)
  rw [he]
  exact (le_iSup (fun j : Fin (A.count i+1) => ((A.cuts i).prefixCopy B hlarge g d j.val).range) j).trans
    (le_iSup (fun i : Fin l => ⨆ j : Fin (A.count i+1),
      ((A.cuts i).prefixCopy B hlarge g d j.val).range) i)

theorem old_interval_range (hl : 201 ≤ l) (k : ℕ) (hk : k ≤ n) (p : ℤ) (s t : CutRing)
    (hs : p ≤ endpointLabel s ∧ endpointLabel s < p+k)
    (ht : p ≤ endpointLabel t ∧ endpointLabel t < p+k)
    (hanchor : ∀ j : Fin (l+1), p ≤ endpointLabel (windowCut l q j) ∧ endpointLabel (windowCut l q j) < p+k)
    (hcuts : ∀ i : Fin l, ∀ z ∈ ({s,t} : Finset CutRing),
      clippedLabel ((A.cuts i).cut 0) ((A.cuts i).cut (Fin.last (A.count i))) (endpointLabel z) ∈
        Set.range (A.cuts i).cut) :
    (B.axisSector hlarge n g d k hk p (coordinateInterval a d s t)).range ≤ A.prefixGroup B hlarge g d := by
  classical
  let f : Fin l → polygonAlgebra a := fun i => windowCell a d l q i ⊓ coordinateInterval a d s t
  have hV := axisInterval_resolved (a := a) (r := r) d k p s t hs ht
  have hW (i : Fin l) : ResolvedBy (fun j => (InitialCoverSystem.primitiveTests (a := a) (r := r)
      (axisWindowPrimitives d k p) j).val) (f i).val := by
    exact BooleanSubalgebra.inf_mem (L := resolvedAlgebra _)
      (axisInterval_resolved d k p _ _ (hanchor i.castSucc) (hanchor i.succ)) hV
  apply (B.fullGeometricSector_partition_range hlarge (axisWindowPrimitives d k p)
    (fun I _ b hb => B.axisFamilyLaw n g d k hk p I b hb) _ f hW ?_ ?_).trans
  · apply iSup_le
    intro i
    change (B.axisSector hlarge n g d k hk p (windowCell a d l q i ⊓ coordinateInterval a d s t)).range ≤ _
    have hlu := hanchor i.castSucc
    have hlv := hanchor i.succ
    rw [← A.lower i] at hlu
    rw [← A.upper i] at hlv
    change (B.axisSector hlarge n g d k hk p (coordinateInterval a d _ _ ⊓ _)).range ≤ _
    rw [← A.lower i,← A.upper i]
    apply B.axisSector_anchor_intersection_range hlarge n g d k hk p _ _ s t
      ((A.cuts i).ordered (Fin.last (A.count i))).1 (A.intervalLength hl i) hlu hlv hs ht
    · have he : B.axisSector hlarge n g d k hk p
          (coordinateInterval a d ((A.cuts i).cut 0) ((A.cuts i).cut (Fin.last (A.count i)))) =
          (A.cuts i).anchorCopy B hlarge g d := by
        exact B.axisInterval_copy_eq hlarge n g d _ _ _ _ _ _ _ _ hlu hlv
          ((A.cuts i).lower_label 0) ((A.cuts i).upper_label 0)
      rw [he]
      exact A.anchor_range_prefixGroup B hlarge g d i
    · apply A.interval_prefix_range B hlarge g d i k hk p _ hlu ?_ (hcuts i s (by simp))
      rcases clippedLabel_label ((A.cuts i).cut 0) ((A.cuts i).cut (Fin.last (A.count i))) (endpointLabel s) with h|h
      · rw [h]; exact hlv
      · rw [h]; exact hs
    · apply A.interval_prefix_range B hlarge g d i k hk p _ hlu ?_ (hcuts i t (by simp))
      rcases clippedLabel_label ((A.cuts i).cut 0) ((A.cuts i).cut (Fin.last (A.count i))) (endpointLabel t) with h|h
      · rw [h]; exact hlv
      · rw [h]; exact ht
  · intro i j hij
    exact (windowCell_pairwise_disjoint d l hl q hij).mono Set.inter_subset_left Set.inter_subset_left
  · intro x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := windowCell_cover d l hl q x
      exact ⟨i,hi,hx⟩
    · rintro ⟨i,hi⟩; exact hi.2

end AxisAnchorFamily
end AnchorGeneration

end SimpleAmenable
end
end

end OAI
