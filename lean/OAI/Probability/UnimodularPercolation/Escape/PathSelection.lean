import Mathlib
import OAI.Probability.UnimodularPercolation.Escape.SelectionBounds

namespace OAI

/-! Selection of geometrically separated paths from labelled escape events. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section EscapeGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

namespace HoldingWalk
variable {H : SimpleGraph V}

theorem mem_vertices_append {k l : ℕ} {x y z b : V}
    (w : HoldingWalk H k x y) (v : HoldingWalk H l y z) :
    b ∈ (w.append v).vertices ↔ b ∈ w.vertices ∨ b ∈ v.vertices := by
  induction w with
  | nil x =>
    have hx : x ∈ v.vertices := by simpa using v.position_mem_vertices 0
    simp only [append, vertices, List.mem_singleton]
    exact ⟨fun h => Or.inr h, fun h => h.elim (fun he => he ▸ hx) id⟩
  | hold w ih => simp only [append, vertices, List.mem_cons, ih, or_assoc]
  | step h w ih => simp only [append, vertices, List.mem_cons, ih, or_assoc]

theorem mem_vertices_fromPositions (k : ℕ) (f : Fin (k+1) → V)
    (h : ∀ i : Fin k, H.Adj (f i.castSucc) (f i.succ)) (b : V) :
    b ∈ (fromPositions k f h).vertices ↔ ∃ i, f i = b := by
  rw [mem_vertices_iff_position]
  constructor
  · rintro ⟨i, hi, he⟩
    exact ⟨⟨i,by omega⟩, (position_fromPositions k f h i hi).symm.trans he⟩
  · rintro ⟨i,hi⟩
    exact ⟨i.val,by omega,(position_fromPositions k f h i.val (by omega)).trans hi⟩

end HoldingWalk

 
def negativeStem (H : SimpleGraph V) (J : ℕ) (s : Fin (J+J+1) → V)
    (hs : ∀ i : Fin (J+J), H.Adj (s i.castSucc) (s i.succ)) :
    HoldingWalk H J (s (segmentCenter J)) (s 0) :=
  (HoldingWalk.fromPositions J (fun i => s ⟨i.val,by omega⟩)
    (fun i => hs ⟨i.val,by omega⟩)).reverse

theorem positiveStem_vertices (H : SimpleGraph V) (J : ℕ) (s : Fin (J+J+1) → V)
    (hs : ∀ i : Fin (J+J), H.Adj (s i.castSucc) (s i.succ)) (z : V) :
    z ∈ (positiveStem H J s hs).vertices ↔ ∃ i : Fin (J+1), s ⟨J+i.val,by omega⟩ = z := by
  exact HoldingWalk.mem_vertices_fromPositions J _ _ z

theorem negativeStem_vertices (H : SimpleGraph V) (J : ℕ) (s : Fin (J+J+1) → V)
    (hs : ∀ i : Fin (J+J), H.Adj (s i.castSucc) (s i.succ)) (z : V) :
    z ∈ (negativeStem H J s hs).vertices ↔ ∃ i : Fin (J+1), s ⟨i.val,by omega⟩ = z := by
  let w := HoldingWalk.fromPositions J (fun i : Fin (J+1) => s ⟨i.val,by omega⟩)
    (fun i : Fin J => hs ⟨i.val,by omega⟩)
  have he : z ∈ w.reverse.vertices ↔ z ∈ w.vertices := by
    rw [HoldingWalk.vertices_reverse, List.mem_reverse]
  exact he.trans (HoldingWalk.mem_vertices_fromPositions J _ _ z)

 
def labelLeftEscape (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) :
    HoldingWalk (openSimpleGraph G Set.univ) (m+J)
      (ξ.first (segmentCenter J)) ξ.leftTail.1 :=
  (negativeStem _ J ξ.first (orbitSegment_consecutive G J γ ξ.first hγ ξ.first_mem)).append ξ.leftTail.2

 
def labelCorridor (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) : RawCorridor G ((J+L)+J) :=
  ⟨ξ.first (segmentCenter J), ξ.last (segmentCenter J), escapeLabelRaw G J L m γ hγ ξ⟩

def segmentPositiveIndex (J : ℕ) : Fin (J+1) → Fin (J+J+1) :=
  fun i => ⟨J+i.val,by omega⟩
def segmentNegativeIndex (J : ℕ) : Fin (J+1) → Fin (J+J+1) :=
  fun i => ⟨i.val,by omega⟩

theorem segmentOrbit_injective {I : Type*} (G : BondGraph V E) (γ s : I → V)
    (hγ : Function.Injective γ) (hs : s ∈ segmentOrbit G γ) : Function.Injective s := by
  obtain ⟨a,b,hab,rfl⟩ := hs
  exact a.injective.comp hγ

 

theorem labelLeftEscape_raw_intersection (G : BondGraph V E) (J L m : ℕ)
    (γ : Fin (J+J+1) → V) (hinj : Function.Injective γ)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m)
    (hgood : ¬labelFirstEscapeCollision G γ (Fin.last (J+J)) 0 J L m
      (segmentPositiveIndex J) (segmentNegativeIndex J) (segmentPositiveIndex J) ξ)
    (z : V) (hz : z ∈ (labelLeftEscape G J L m γ hγ ξ).vertices)
    (hr : z ∈ (escapeLabelRaw G J L m γ hγ ξ).vertices) :
    z = ξ.first (segmentCenter J) := by
  have hfirst := segmentOrbit_injective G γ ξ.first hinj ξ.first_mem
  have hfail := hgood
  unfold labelFirstEscapeCollision firstEscapeCollision at hfail
  have hraw : (∃ i : Fin (J+1), ξ.first (segmentPositiveIndex J i) = z) ∨
      z ∈ ξ.middle.vertices ∨ (∃ i : Fin (J+1), ξ.last (segmentPositiveIndex J i) = z) := by
    simpa only [escapeLabelRaw, HoldingWalk.mem_vertices_append,
      HoldingWalk.vertices_reverse, List.mem_reverse, positiveStem_vertices,
      segmentPositiveIndex] using hr
  have hleft : (∃ i : Fin (J+1), ξ.first (segmentNegativeIndex J i) = z) ∨
      z ∈ ξ.leftTail.2.vertices := by
    simpa only [labelLeftEscape, HoldingWalk.mem_vertices_append,
      negativeStem_vertices, segmentNegativeIndex] using hz
  rcases hleft with ⟨i,hi⟩ | ht
  · rcases hraw with ⟨j,hj⟩ | hm | ⟨j,hj⟩
    · have he := congrArg Fin.val (hfirst (hi.trans hj.symm))
      change i.val = J+j.val at he
      have hiJ : i.val = J := by omega
      rw [←hi]
      congr 1
      apply Fin.ext
      exact hiJ
    · exact False.elim (hfail (Or.inl (Or.inl (Or.inr ⟨i,by simpa only [hi] using hm⟩))))
    · exact False.elim (hfail (Or.inr (Or.inl ⟨(j,i),hj.trans hi.symm⟩)))
  · rcases hraw with ⟨i,hi⟩ | hm | ⟨i,hi⟩
    · exact False.elim (hfail (Or.inl (Or.inl (Or.inl ⟨i,by simpa only [hi] using ht⟩))))
    · exact False.elim (hfail (Or.inl (Or.inr ⟨z,ht,hm⟩)))
    · obtain ⟨l,hl,he⟩ := ξ.leftTail.2.mem_vertices_iff_position.mp ht
      exact False.elim (hfail (Or.inr (Or.inr ⟨(⟨l,by omega⟩,i),he.trans hi.symm⟩)))

 
theorem labelRaw_reverse_vertices (G : BondGraph V E) (J L m : ℕ)
    (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) (z : V) :
    z ∈ (escapeLabelRaw G J L m γ hγ ξ.reverse).vertices ↔
      z ∈ (escapeLabelRaw G J L m γ hγ ξ).vertices := by
  simp only [escapeLabelRaw, HoldingWalk.mem_vertices_append,
    HoldingWalk.vertices_reverse, List.mem_reverse, EscapeLabel.reverse]
  tauto

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem interior_mem_raw (w : RawCorridor G k) {z : V} (hz : z ∈ w.interior) :
    z ∈ w.2.2.vertices := by
  have hp : z ∈ w.path.support := List.mem_toFinset.mp (Finset.mem_sdiff.mp hz).1
  exact w.2.2.erase_support.subset hp

 
noncomputable def neighborhood (hloc : LocallyFinite G) (w : RawCorridor G k) : Finset V :=
  w.interior ∪ w.interior.biUnion (neighbors G hloc)

theorem coe_neighborhood (hloc : LocallyFinite G) (w : RawCorridor G k) :
    (w.neighborhood hloc : Set V) = closedBondNeighborhood G (w.interior : Set V) :=
  (closedBondNeighborhood_finset G hloc w.interior).symm

 
def HasEscape (hloc : LocallyFinite G) (p : unitInterval) (j : ℕ) (t : ℝ)
    (w : RawCorridor G k) (x : V) : Prop :=
  ∃ z, ∃ q : (openSimpleGraph G Set.univ).Walk x z,
    q.IsPath ∧ q.length ≤ j ∧ (∀ v ∈ q.support, v ∉ w.interior) ∧
      (∑ b ∈ w.neighborhood hloc, twoPoint G p z b) ≤ t

 
def Selected (hloc : LocallyFinite G) (p : unitInterval) (j : ℕ) (t : ℝ)
    (w : RawCorridor G k) : Prop :=
  3 ≤ w.path.length ∧ w.HasEscape hloc p j t w.base ∧ w.HasEscape hloc p j t w.endpoint

end RawCorridor

 

noncomputable def spineVertices (G : BondGraph V E) (J L : ℕ)
    (s : Fin (J+J+1) → V)
    (mid : RawFrom (openSimpleGraph G Set.univ) L (s (Fin.last (J+J))))
    (h : Fin (J+J+1) → V) : Finset V :=
  Finset.univ.image (s ∘ segmentPositiveIndex J) ∪ mid.2.vertices.toFinset ∪
    Finset.univ.image (h ∘ segmentPositiveIndex J)

noncomputable def spineNeighborhood (G : BondGraph V E) (hloc : LocallyFinite G) (J L : ℕ)
    (s : Fin (J+J+1) → V)
    (mid : RawFrom (openSimpleGraph G Set.univ) L (s (Fin.last (J+J))))
    (h : Fin (J+J+1) → V) : Finset V :=
  let W := spineVertices G J L s mid h
  W ∪ W.biUnion (neighbors G hloc)

theorem mem_spineVertices (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) (z : V) :
    z ∈ spineVertices G J L ξ.first ⟨ξ.last (Fin.last (J+J)),ξ.middle⟩ ξ.last ↔
      z ∈ (escapeLabelRaw G J L m γ hγ ξ).vertices := by
  simp only [spineVertices, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and, Function.comp_apply, List.mem_toFinset, escapeLabelRaw,
    HoldingWalk.mem_vertices_append, HoldingWalk.vertices_reverse, List.mem_reverse,
    positiveStem_vertices, segmentPositiveIndex]
  tauto

theorem labelCorridor_neighborhood_subset (G : BondGraph V E) (hloc : LocallyFinite G)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) :
    (labelCorridor G J L m γ hγ ξ).neighborhood hloc ⊆
      spineNeighborhood G hloc J L ξ.first ⟨ξ.last (Fin.last (J+J)),ξ.middle⟩ ξ.last := by
  have hi : (labelCorridor G J L m γ hγ ξ).interior ⊆
      spineVertices G J L ξ.first ⟨ξ.last (Fin.last (J+J)),ξ.middle⟩ ξ.last := by
    intro z hz
    exact (mem_spineVertices G J L m γ hγ ξ z).mpr
      ((labelCorridor G J L m γ hγ ξ).interior_mem_raw hz)
  exact Finset.union_subset_union hi (Finset.biUnion_subset_biUnion_of_subset_left _ hi)

theorem neighborhood_card_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (W : Finset V) :
    (W ∪ W.biUnion (neighbors G hloc)).card ≤ (d+1)*W.card := by
  have hb : (W.biUnion (neighbors G hloc)).card ≤ W.card*d :=
    Finset.card_biUnion_le_card_mul _ _ _
      (fun x _ => (neighbors_card_le_degree G hloc x).trans (hd x))
  calc
    _ ≤ W.card + (W.biUnion (neighbors G hloc)).card := Finset.card_union_le _ _
    _ ≤ W.card + W.card*d := Nat.add_le_add_left hb _
    _ = _ := by ring

theorem spineVertices_card_le (G : BondGraph V E) (J L : ℕ)
    (s : Fin (J+J+1) → V)
    (mid : RawFrom (openSimpleGraph G Set.univ) L (s (Fin.last (J+J))))
    (h : Fin (J+J+1) → V) :
    (spineVertices G J L s mid h).card ≤ ((J+L)+J)+3 := by
  have h₁ : (Finset.univ.image (s ∘ segmentPositiveIndex J)).card ≤ J+1 :=
    (Finset.card_image_le).trans (by simp)
  have h₂ : mid.2.vertices.toFinset.card ≤ L+1 :=
    (List.toFinset_card_le _).trans (le_of_eq mid.2.length_vertices)
  have h₃ : (Finset.univ.image (h ∘ segmentPositiveIndex J)).card ≤ J+1 :=
    (Finset.card_image_le).trans (by simp)
  have hauto := (Finset.card_union_le
    (Finset.univ.image (s ∘ segmentPositiveIndex J)) mid.2.vertices.toFinset)
  have hauto' := (Finset.card_union_le
    (Finset.univ.image (s ∘ segmentPositiveIndex J) ∪ mid.2.vertices.toFinset)
    (Finset.univ.image (h ∘ segmentPositiveIndex J)))
  unfold spineVertices
  omega

theorem spineNeighborhood_card_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (J L : ℕ)
    (s : Fin (J+J+1) → V)
    (mid : RawFrom (openSimpleGraph G Set.univ) L (s (Fin.last (J+J))))
    (h : Fin (J+J+1) → V) :
    ((spineNeighborhood G hloc J L s mid h).card : ℝ) ≤
      (3*(d:ℝ)+3)*((((J+L)+J):ℕ)+1) := by
  have hn := neighborhood_card_le G hloc d hd (spineVertices G J L s mid h)
  have hs := spineVertices_card_le G J L s mid h
  have hb : (spineNeighborhood G hloc J L s mid h).card ≤ (d+1)*(((J+L)+J)+3) :=
    hn.trans (Nat.mul_le_mul_left _ hs)
  have hb' : ((spineNeighborhood G hloc J L s mid h).card : ℝ) ≤
      ((d:ℝ)+1)*((((J+L)+J):ℕ)+3) := by exact_mod_cast hb
  have hk : (0:ℝ) ≤ (((J+L)+J):ℕ) := Nat.cast_nonneg _
  nlinarith [show (0:ℝ) ≤ (d:ℝ) from Nat.cast_nonneg d]

 

theorem selected_of_good_label (G : BondGraph V E) (hloc : LocallyFinite G)
    (J L m : ℕ) (γ : Fin (J+J+1) → V) (hinj : Function.Injective γ)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) (p : unitInterval) (t : ℝ)
    (hleft : ¬labelFirstEscapeCollision G γ (Fin.last (J+J)) 0 J L m
      (segmentPositiveIndex J) (segmentNegativeIndex J) (segmentPositiveIndex J) ξ)
    (hright : ¬labelFirstEscapeCollision G γ (Fin.last (J+J)) 0 J L m
      (segmentPositiveIndex J) (segmentNegativeIndex J) (segmentPositiveIndex J) ξ.reverse)
    (hdist : ξ.last (segmentCenter J) ∉ reachBall G (ξ.first (segmentCenter J)) 2)
    (hpot : ¬labelPotentialFailure G p γ (Fin.last (J+J)) 0 L m
      (spineNeighborhood G hloc J L) t ξ) :
    (labelCorridor G J L m γ hγ ξ).Selected hloc p (J+m) t := by
  let w := labelCorridor G J L m γ hγ ξ
  have hlength : 3 ≤ w.path.length := by
    by_contra h
    have hx : w.endpoint ∈ reachBall G w.base w.path.length := by
      simpa only [Nat.zero_add] using walk_mem_reachBall G Set.univ w.path 0 rfl
    exact hdist (reachBall_mono_local G w.base (by omega : w.path.length ≤ 2) hx)
  have hn := labelCorridor_neighborhood_subset G hloc J L m γ hγ ξ
  have hp := not_or.mp hpot
  have hp₁ : (∑ b ∈ w.neighborhood hloc, twoPoint G p ξ.leftTail.1 b) ≤ t := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hn (fun b _ _ => twoPoint_nonneg G p _ b))
    exact le_of_not_gt hp.1
  have hp₂ : (∑ b ∈ w.neighborhood hloc, twoPoint G p ξ.rightTail.1 b) ≤ t := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hn (fun b _ _ => twoPoint_nonneg G p _ b))
    exact le_of_not_gt hp.2
  refine ⟨hlength, ?_, ?_⟩
  · let e := labelLeftEscape G J L m γ hγ ξ
    refine ⟨ξ.leftTail.1, e.erase, e.erase_isPath, ?_, ?_, hp₁⟩
    · exact e.erase_length.trans (by omega)
    · intro z hz hzI
      have hr := w.interior_mem_raw hzI
      have he := labelLeftEscape_raw_intersection G J L m γ hinj hγ ξ hleft z
        (e.erase_support.subset hz) hr
      change z = w.base at he
      apply w.base_not_interior
      simpa only [he] using hzI
  · let e := labelLeftEscape G J L m γ hγ ξ.reverse
    refine ⟨ξ.rightTail.1, e.erase, e.erase_isPath, ?_, ?_, hp₂⟩
    · exact e.erase_length.trans (by omega)
    · intro z hz hzI
      have hr := w.interior_mem_raw hzI
      have he := labelLeftEscape_raw_intersection G J L m γ hinj hγ ξ.reverse hright z
        (e.erase_support.subset hz) ((labelRaw_reverse_vertices G J L m γ hγ ξ z).mpr hr)
      change z = w.endpoint at he
      apply w.endpoint_not_interior
      simpa only [he] using hzI

end EscapeGeometry
end Percolation

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SelectedLabelMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

 

theorem rooted_selected_label_mass_lower [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (p : unitInterval) (hA : HasKernel G p A)
    (J L m : ℕ) (γ : Fin (J+J+1) → V) (hinj : Function.Injective γ)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) (J+J))
    (x : V) (hx : x ∈ vertexOrbit G (γ (segmentCenter J))) (hρ : ‖P‖ < 1)
    (hsep : ∀ s ∈ segmentOrbit G γ,
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s 0) (s (segmentPositiveIndex J i))) ∧
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s (Fin.last (J+J))) (s (segmentNegativeIndex J i))) ∧
      2*J ≤ (openSimpleGraph G Set.univ).dist (s 0) (s (Fin.last (J+J))))
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (t : ℝ) (ht : 0 < t) :
    1 - (4*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) +
      2*((3*(d:ℝ)+3)*((((J+L)+J):ℕ)+1)*Real.sqrt c*‖P‖^m)/t +
      2*c*(((d+1)^2:ℕ):ℝ)*Real.sqrt c*‖P‖^L) ≤
    ∑' ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x},
      if (labelCorridor G J L m γ hγ ξ.1).Selected hloc p (J+m) t then
        escapeLabelProbability G hloc a γ (J+J) hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m ξ.1 else 0 := by
  let F := spineNeighborhood G hloc J L
  let μ := fun ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x} =>
    escapeLabelProbability G hloc a γ (J+J) hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m ξ.1
  let B₁ := fun ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x} =>
    (labelFirstEscapeCollision G γ (Fin.last (J+J)) 0 J L m
        (segmentPositiveIndex J) (segmentNegativeIndex J) (segmentPositiveIndex J) ξ.1 ∨
      labelFirstEscapeCollision G γ (Fin.last (J+J)) 0 J L m
        (segmentPositiveIndex J) (segmentNegativeIndex J) (segmentPositiveIndex J) ξ.1.reverse) ∨
      labelPotentialFailure G p γ (Fin.last (J+J)) 0 L m F t ξ.1
  let B₂ := fun ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x} =>
    ξ.1.last (segmentCenter J) ∈ reachBall G x 2
  have hb := rooted_label_collision_potential_failure_bound G hloc a root weight htr hcov hw hw1 c hc hmin
    P A hpos hsym hP hdiag p hA γ (J+J) hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x hx hρ
    J (segmentPositiveIndex J) (segmentNegativeIndex J) (segmentPositiveIndex J) hsep F
    ((3*(d:ℝ)+3)*((((J+L)+J):ℕ)+1)) (spineNeighborhood_card_le G hloc d hd J L) t ht
  have he := rooted_label_endpoint_ball_bound G hloc a root weight (vertexAut G) (Set.Subset.refl _)
    htr hw hw1 hcov c hc hmin γ (J+J) hdiam (segmentCenter J) (Fin.last (J+J)) 0
    P hpos hsym hP hdiag m L x hx d hd 2
  have hs := (rooted_label_probability_hasSum G hloc a root weight (vertexAut G) (Set.Subset.refl _)
    htr hcov hw hw1 c hc hmin P hpos hsym hP hdiag γ (J+J) hdiam
    (segmentCenter J) (Fin.last (J+J)) 0 L m x hx).tsum_eq
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  let := finite_rootedEscapeLabels G hloc γ (J+J) hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x
  let := Fintype.ofFinite {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x}
  have hμ (ξ) : 0 ≤ μ ξ := escapeLabelProbability_nonneg G hloc a hK γ (J+J) hdiam
    (segmentCenter J) (Fin.last (J+J)) 0 L m ξ.1
  simp only [tsum_fintype] at hs hb he ⊢
  have hu := (finite_weighted_event_or μ hμ B₁ B₂).trans (add_le_add hb he)
  have hl := finite_weighted_success_lower μ hs (fun ξ => B₁ ξ ∨ B₂ ξ) _ hu
  apply hl.trans
  apply Finset.sum_le_sum
  intro ξ _
  by_cases h : B₁ ξ ∨ B₂ ξ
  · simp only [h,not_true_eq_false,ite_false]
    split_ifs <;> first | exact hμ ξ | rfl
  · have h₁ := not_or.mp (not_or.mp h).1
    have h₂ := not_or.mp h₁.1
    have hdist : ξ.1.last (segmentCenter J) ∉ reachBall G (ξ.1.first (segmentCenter J)) 2 := by
      simpa only [ξ.2] using (not_or.mp h).2
    have hsel := selected_of_good_label G hloc J L m γ hinj hγ ξ.1 p t h₂.1 h₂.2 hdist h₁.2
    simp only [h,not_false_eq_true,hsel,ite_true]
    exact le_rfl

end SelectedLabelMass
end Percolation

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SelectedRawMass
attribute [local instance] Classical.propDecidable Classical.decEq

theorem rootedEscapeLabelRaw_corridor (G : BondGraph V E) (J L m : ℕ)
    (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (x : V) (ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x}) :
    (⟨x,rootedEscapeLabelRaw G J L m γ hγ x ξ⟩ : RawCorridor G ((J+L)+J)) =
      labelCorridor G J L m γ hγ ξ.1 := by
  rcases ξ with ⟨ξ,hξ⟩
  subst x
  rfl

 

theorem selected_raw_mass_of_label_mass (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (ha : 0 < a) (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) (J+J)) (x : V)
    (hx : x ∈ vertexOrbit G (γ (segmentCenter J)))
    (q : ℝ) (hq : 0 < q) (hqle : q ≤ segmentReturnMass G hloc a γ (Fin.last (J+J)) L (γ (Fin.last (J+J))))
    (p : unitInterval) (t b : ℝ)
    (hb : b ≤ ∑' ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x},
      if (labelCorridor G J L m γ hγ ξ.1).Selected hloc p (J+m) t then
        escapeLabelProbability G hloc a γ (J+J) hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m ξ.1 else 0) :
    b*(a^(J+J)*q) ≤ ∑' w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x,
      if RawCorridor.Selected hloc p (J+m) t (⟨x,w⟩ : RawCorridor G ((J+L)+J)) then
        w.2.mass (walkKernel G hloc a) else 0 := by
  have hh := rooted_label_raw_event_bound G hloc a ha hK J L m γ hγ (J+J) hdiam x hx
    q hq hqle (fun w => RawCorridor.Selected hloc p (J+m) t (⟨x,w⟩ : RawCorridor G ((J+L)+J)))
  simp only [rootedEscapeLabelRaw_corridor] at hh
  exact (le_div_iff₀ (mul_pos (pow_pos ha _) hq)).mp (hb.trans hh)

end SelectedRawMass

section FullSelectionCutoffs
 

theorem exists_full_selection_cutoffs (ρ c d τ : ℝ)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) (hd : 0 ≤ d) (hτ : 0 < τ) :
    ∃ J : ℕ, 0 < J ∧ ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ k₀ : ℕ, J+J ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k → ∀ R : ℝ, 1 ≤ R →
        4*c*(earlyCollisionCost ρ J + suffixCollisionCost ρ c J*ρ^(k-(J+J))) +
          2*((3*d+3)*((k:ℝ)+1)*Real.sqrt c*ρ^⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊)/(τ/R) +
          2*c*(d+1)^2*Real.sqrt c*ρ^(k-(J+J)) ≤ 1/2 := by
  obtain ⟨J,hJ,L₀,C₁,hC₁,_,k₀,hk₀,hk⟩ :=
    exists_joint_collision_potential_cutoffs ρ c (3*d+2) τ hρ hρ1 hc (by linarith) hτ
  have ht : Filter.Tendsto (fun L : ℕ => 2*c*(d+1)^2*Real.sqrt c*ρ^L) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1).const_mul
      (2*c*(d+1)^2*Real.sqrt c)
  obtain ⟨L₁,hL₁⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds (show (0:ℝ) < 1/8 by norm_num)))
  refine ⟨J,hJ,C₁,hC₁,max k₀ (J+J+L₁),by omega,fun k hk' R hR => ?_⟩
  have h₁ := hk k (le_trans (le_max_left _ _) hk') R hR
  have h₂ := hL₁ (k-(J+J)) (by omega)
  have he : 3*d+2+1 = 3*d+3 := by ring
  rw [he] at h₁
  linarith
end FullSelectionCutoffs
end Percolation

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FullPathSelection
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

 

theorem exists_selected_path_mass [Countable V] [Countable E] [Infinite V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (a : ℝ) (ha : 0 < a) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (τ : ℝ) (hτ : 0 < τ) :
    ∃ J : ℕ, ∃ C₁ : ℝ, ∃ k₀ : ℕ, ∃ b : ℝ,
      0 < J ∧ 0 < C₁ ∧ 3 ≤ k₀ ∧ 0 < b ∧
      ∀ p : unitInterval, (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ k : ℕ, k₀ ≤ k → ∀ R : ℝ, 1 ≤ R →
        b ≤ rawPathAverage G (walkKernel G hloc a) k root weight
          (fun w => if w.Selected hloc p (J+⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊) (τ/R) then 1 else 0) := by
  let x₀ : V := Classical.arbitrary V
  have hρpos : 0 < ‖P‖ := by
    have hh := (hdiag x₀).trans ((Complex.re_le_norm _).trans (matrixCoeff_norm_le P x₀ x₀))
    linarith
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  obtain ⟨J,hJ,C₁,hC₁,k₀,hJk,hcut⟩ := exists_full_selection_cutoffs ‖P‖ c d τ hρpos hρ hc (Nat.cast_nonneg d) hτ
  obtain ⟨y,q,hqN,hq⟩ := exists_geodesic_length G hloc hconn x₀ (J+J)
  let γ := geodesicSegment G q (J+J)
  have hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ) :=
    fun i => geodesicSegment_adj G q (J+J) hqN i.val i.isLt
  have hinj : Function.Injective γ := geodesicSegment_injective G q (J+J) hqN hq
  have hdiam := geodesicSegment_diameter G q (J+J) hqN
  have hsep : ∀ s ∈ segmentOrbit G γ,
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s 0) (s (segmentPositiveIndex J i))) ∧
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s (Fin.last (J+J))) (s (segmentNegativeIndex J i))) ∧
      2*J ≤ (openSimpleGraph G Set.univ).dist (s 0) (s (Fin.last (J+J))) := by
    rintro s ⟨g,e,hge,rfl⟩
    constructor
    · intro i
      change J ≤ (openSimpleGraph G Set.univ).dist (g (q.getVert 0)) (g (q.getVert (J+i.val)))
      rw [graph_dist_aut G hconn hge,geodesic_getVert_dist _ q hq 0 (J+i.val) (by omega) (by omega)]
      omega
    constructor
    · intro i
      change J ≤ (openSimpleGraph G Set.univ).dist (g (q.getVert (J+J))) (g (q.getVert i.val))
      rw [graph_dist_aut G hconn hge,SimpleGraph.dist_comm,
        geodesic_getVert_dist _ q hq i.val (J+J) (by omega) (by omega)]
      omega
    · change 2*J ≤ (openSimpleGraph G Set.univ).dist (g (q.getVert 0)) (g (q.getVert (J+J)))
      rw [graph_dist_aut G hconn hge,geodesic_getVert_dist _ q hq 0 (J+J) (by omega) (by omega)]
      omega
  obtain ⟨i,g,hg,hgx⟩ := hcov (γ (segmentCenter J))
  obtain ⟨e,he⟩ := hg
  have hx : root i ∈ vertexOrbit G (γ (segmentCenter J)) :=
    ⟨g.symm,e.symm,isAut_symm G he,by rw [←hgx,g.symm_apply_apply]⟩
  let b : ℝ := weight i * ((1/2)*(a^(J+J)*(1/(2*c))))
  have hb : 0 < b := mul_pos (hw i) (mul_pos (by norm_num)
    (mul_pos (pow_pos ha _) (by positivity)))
  refine ⟨J,C₁,max k₀ 3,b,hJ,hC₁,le_max_right _ _,hb,?_⟩
  intro p _hpnear hp k hk R hR
  have hk₀ : k₀ ≤ k := (le_max_left _ _).trans hk
  have hJk' : J+J ≤ k := hJk.trans hk₀
  obtain ⟨L,rfl⟩ : ∃ L : ℕ, (J+L)+J = k := ⟨k-(J+J),by omega⟩
  let m' := ⌈C₁*Real.log ((((((J+L)+J):ℕ):ℝ)+1)*R)⌉₊
  obtain ⟨A,hA⟩ := operatorBounded_of_lt_pc G hloc hqt p hp
  have hcost := hcut ((J+L)+J) hk₀ R hR
  have hL : (J+L)+J-(J+J) = L := by omega
  rw [hL] at hcost
  have hcost' :
      4*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) +
      2*((3*(d:ℝ)+3)*((((J+L)+J):ℕ)+1)*Real.sqrt c*‖P‖^m')/(τ/R) +
      2*c*(((d+1)^2:ℕ):ℝ)*Real.sqrt c*‖P‖^L ≤ 1/2 := by
    simpa only [m',Nat.cast_pow,Nat.cast_add,Nat.cast_one] using hcost
  have hl := rooted_selected_label_mass_lower G hloc a root weight htr hcov hw hw1 c hc hmin
    P A hpos hsym hP hdiag p hA J L m' γ hinj hγ hdiam (root i) hx hρ hsep d hd (τ/R)
    (div_pos hτ (lt_of_lt_of_le zero_lt_one hR))
  have hhalf : (1/2:ℝ) ≤ ∑' ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m' // ξ.first (segmentCenter J) = root i},
      if (labelCorridor G J L m' γ hγ ξ.1).Selected hloc p (J+m') (τ/R) then
        escapeLabelProbability G hloc a γ (J+J) hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m' ξ.1 else 0 := by
    linarith
  have hqreturn := segmentReturnMass_uniform_lower G hloc a root weight (vertexAut G) (Set.Subset.refl _)
    htr hcov hw hw1 c hc hmin P hpos hsym hP hdiag γ (Fin.last (J+J)) L
  have hmraw := selected_raw_mass_of_label_mass G hloc a ha hK J L m' γ hγ hdiam (root i) hx
    (1/(2*c)) (by positivity) hqreturn p (τ/R) (1/2) hhalf
  have hroot := mul_le_mul_of_nonneg_left hmraw (hw i).le
  apply hroot.trans
  unfold rawPathAverage
  have hall (r : ι) : 0 ≤ weight r * ∑' w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) (root r),
      w.2.mass (walkKernel G hloc a) *
        (if RawCorridor.Selected hloc p (J+m') (τ/R) ⟨root r,w⟩ then 1 else 0) := by
    apply mul_nonneg (hw r).le
    apply tsum_nonneg
    intro w
    apply mul_nonneg (w.2.mass_nonneg _ hK)
    split_ifs <;> norm_num
  have hi := Finset.single_le_sum (s := Finset.univ) (fun r _ => hall r) (Finset.mem_univ i)
  simpa only [mul_ite,mul_one,mul_zero] using hi

end FullPathSelection
end Percolation

end OAI
