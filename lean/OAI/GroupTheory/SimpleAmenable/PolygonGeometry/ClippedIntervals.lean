import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.SortedAxisCuts

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ClippedIntervals
attribute [local instance] cutOrdinaryOrder

theorem coordinateInterval_mem_lifted {a : ℕ} (d : Fin 2) (b u v : CutRing)
    (hbu : ordinary b ≤ ordinary u) (huv : ordinary u ≤ ordinary v)
    (hvb : ordinary v < ordinary b+1) (x : GenericSquare a) :
    x ∈ (coordinateInterval a d u v).val ↔
      ordinary u ≤ liftedCoordinate d b x ∧ liftedCoordinate d b x < ordinary v := by
  change x ∈ coordinateBetween a d u v ↔ _
  rw [mem_coordinateBetween_iff d u v huv (by linarith) x]
  constructor
  · rintro ⟨k,hk,hk'⟩
    have hf : (⌊coordinate d x-ordinary b⌋:ℤ) = -k := by
      apply Int.floor_eq_iff.mpr
      simp only [Int.cast_neg]
      constructor <;> linarith
    simp only [liftedCoordinate,hf,Int.cast_neg,sub_neg_eq_add]
    exact ⟨hk,hk'⟩
  · rintro ⟨hk,hk'⟩
    refine ⟨-⌊coordinate d x-ordinary b⌋,?_,?_⟩
    · simpa only [liftedCoordinate,Int.cast_neg,sub_eq_add_neg] using hk
    · simpa only [liftedCoordinate,Int.cast_neg,sub_eq_add_neg] using hk'

theorem coordinateInterval_prefix_difference {a : ℕ} (d : Fin 2) (b u v : CutRing)
    (hbu : ordinary b ≤ ordinary u) (huv : ordinary u ≤ ordinary v)
    (hvb : ordinary v < ordinary b+1) :
    coordinateInterval a d u v = coordinateInterval a d b v \ coordinateInterval a d b u := by
  apply Subtype.ext
  ext x
  change x ∈ (coordinateInterval a d u v).val ↔
    x ∈ (coordinateInterval a d b v).val ∧ x ∉ (coordinateInterval a d b u).val
  rw [coordinateInterval_mem_lifted d b u v hbu huv hvb,
    coordinateInterval_mem_lifted d b b v le_rfl (hbu.trans huv) hvb,
    coordinateInterval_mem_lifted d b b u le_rfl hbu (by linarith)]
  have hb := (liftedCoordinate_bounds d b x).1
  constructor
  · rintro ⟨h,h'⟩; exact ⟨⟨hb,h'⟩,by rintro ⟨_,h''⟩; linarith⟩
  · rintro ⟨⟨_,h'⟩,h⟩; exact ⟨by by_contra hh; exact h ⟨hb,lt_of_not_ge hh⟩,h'⟩

theorem coordinateInterval_prefix_clip {a : ℕ} (d : Fin 2) (u v z : CutRing)
    (huv : ordinary u ≤ ordinary v) (hv : ordinary v < ordinary u+1)
    (huz : ordinary u ≤ ordinary z) (hz : ordinary z < ordinary u+1) :
    coordinateInterval a d u v ⊓ coordinateInterval a d u z = coordinateInterval a d u (min v z) := by
  by_cases h : ordinary v ≤ ordinary z
  · have hh : v ≤ z := h
    rw [min_eq_left hh]
    exact inf_eq_left.mpr (coordinateInterval_mono d u v u z le_rfl huv h (by linarith))
  · have hh : z ≤ v := le_of_not_ge h
    rw [min_eq_right hh]
    exact inf_eq_right.mpr (coordinateInterval_mono d u z u v le_rfl huz hh (by linarith))

theorem coordinateInterval_label_eq {a : ℕ} (d : Fin 2) (u v u' v' : CutRing)
    (hu : endpointLabel u=endpointLabel u') (hv : endpointLabel v=endpointLabel v') :
    coordinateInterval a d u v = coordinateInterval a d u' v' := by
  have hu' : u = u'+((u.re-u'.re:ℤ):CutRing) := by
    apply QuadraticAlgebra.ext <;> simp [show u.im = u'.im from hu]
  have hv' : v = v'+((v.re-v'.re:ℤ):CutRing) := by
    apply QuadraticAlgebra.ext <;> simp [show v.im = v'.im from hv]
  apply Subtype.ext
  change coordinateBetween a d u v = coordinateBetween a d u' v'
  rw [hu',hv',coordinateBetween_period]

noncomputable def clippedLabel (u v : CutRing) (q : ℤ) : CutRing := min v (labelLift u q)

theorem clippedLabel_bounds (u v : CutRing) (q : ℤ) (huv : ordinary u ≤ ordinary v) :
    ordinary u ≤ ordinary (clippedLabel u v q) ∧ ordinary (clippedLabel u v q) ≤ ordinary v := by
  change u ≤ min v (labelLift u q) ∧ min v (labelLift u q) ≤ v
  exact ⟨le_min huv (labelLift_bounds u q).1,min_le_left _ _⟩

theorem clippedLabel_label (u v : CutRing) (q : ℤ) :
    endpointLabel (clippedLabel u v q)=endpointLabel v ∨ endpointLabel (clippedLabel u v q)=q := by
  unfold clippedLabel
  rcases le_total v (labelLift u q) with h|h
  · rw [min_eq_left h]; exact Or.inl rfl
  · rw [min_eq_right h]; exact Or.inr (endpointLabel_labelLift u q)

theorem clippedLabel_mem (N : ℕ) (p : ℤ) (u v : CutRing) (q : ℤ)
    (huv : ordinary u ≤ ordinary v) (hlen : ordinary v-ordinary u < 1)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+N)
    (hq : p ≤ q ∧ q < p+N) : clippedLabel u v q ∈ anchorCutSet N p u v := by
  apply mem_anchorCutSet N p u v _ ?_ (clippedLabel_bounds u v q huv) hlen
  rcases clippedLabel_label u v q with h|h <;> rw [h] <;> assumption

theorem coordinateInterval_anchor_formula {a : ℕ} (d : Fin 2) (u v s t : CutRing)
    (huv : ordinary u ≤ ordinary v) (hlen : ordinary v-ordinary u < 1) :
    coordinateInterval a d u v ⊓ coordinateInterval a d s t =
      if ordinary (labelLift u (endpointLabel s)) ≤ ordinary (labelLift u (endpointLabel t)) then
        coordinateInterval a d u (clippedLabel u v (endpointLabel t)) \
          coordinateInterval a d u (clippedLabel u v (endpointLabel s))
      else coordinateInterval a d u v \ (coordinateInterval a d u (clippedLabel u v (endpointLabel s)) \
          coordinateInterval a d u (clippedLabel u v (endpointLabel t))) := by
  let s' := labelLift u (endpointLabel s)
  let t' := labelLift u (endpointLabel t)
  have hs := labelLift_bounds u (endpointLabel s)
  have ht := labelLift_bounds u (endpointLabel t)
  rw [coordinateInterval_label_eq d s t s' t' (by simp [s']) (by simp [t'])]
  split_ifs with h
  · rw [coordinateInterval_prefix_difference d u s' t' hs.1 h ht.2]
    have hset : ∀ (A B C : polygonAlgebra a), A ⊓ (B \ C) = (A ⊓ B) \ (A ⊓ C) := by
      intro A B C; apply Subtype.ext; ext x; change _ ∧ (_ ∧ ¬_) ↔ (_ ∧ _) ∧ ¬(_ ∧ _); tauto
    rw [hset,coordinateInterval_prefix_clip d u v t' huv (by linarith) ht.1 ht.2,
      coordinateInterval_prefix_clip d u v s' huv (by linarith) hs.1 hs.2]
    rfl
  · have hts : ordinary t' < ordinary s' := lt_of_not_ge h
    have he : coordinateInterval a d s' t' = (coordinateInterval a d t' s')ᶜ := by
      apply Subtype.ext
      exact coordinateBetween_reverse d t' s' (by
        rw [map_sub,Int.fract_eq_self.mpr ⟨by linarith,by linarith⟩]; linarith)
    rw [he,coordinateInterval_prefix_difference d u t' s' ht.1 hts.le hs.2]
    have hset : ∀ (A B C : polygonAlgebra a), A ⊓ (B \ C)ᶜ = A \ ((A ⊓ B) \ (A ⊓ C)) := by
      intro A B C; apply Subtype.ext; ext x; change _ ∧ ¬(_ ∧ ¬_) ↔ _ ∧ ¬((_ ∧ _) ∧ ¬(_ ∧ _)); tauto
    rw [hset,coordinateInterval_prefix_clip d u v s' huv (by linarith) hs.1 hs.2,
      coordinateInterval_prefix_clip d u v t' huv (by linarith) ht.1 ht.2]
    rfl

end ClippedIntervals

end SimpleAmenable
end
end

end OAI
