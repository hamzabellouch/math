import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.SeparatedSupportNets

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set TopologicalSpace

structure SeparatedCover {X : Type*} [MetricSpace X] (E : Set X) (r : ℝ) where
  points : Set X
  subset : points ⊆ E
  separated : points.Pairwise (fun x y => r ≤ dist x y)
  covers : ∀ x ∈ E, ∃ z ∈ points, dist x z < r

def extendSeparatedCover {X : Type*} [MetricSpace X]
    (E A : Set X) (r : ℝ) (hr : 0 < r) (hAE : A ⊆ E)
    (hA : A.Pairwise fun x y => r ≤ dist x y) : SeparatedCover E r :=
  let h := exists_separated_cover_extension E A r hr hAE hA
  { points := h.choose
    subset := h.choose_spec.2.1
    separated := h.choose_spec.2.2.1
    covers := h.choose_spec.2.2.2 }

theorem subset_extendSeparatedCover {X : Type*} [MetricSpace X]
    (E A : Set X) (r : ℝ) (hr : 0 < r) (hAE : A ⊆ E)
    (hA : A.Pairwise fun x y => r ≤ dist x y) :
    A ⊆ (extendSeparatedCover E A r hr hAE hA).points :=
  (exists_separated_cover_extension E A r hr hAE hA).choose_spec.1

def nestedSeparatedCovers {X : Type*} [MetricSpace X]
    (E : Set X) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (hstep : ∀ k, r (k + 1) ≤ r k) :
    (k : ℕ) → SeparatedCover E (r k)
  | 0 => extendSeparatedCover E ∅ (r 0) (hr 0) (empty_subset _) (pairwise_empty _)
  | k + 1 =>
    let N := nestedSeparatedCovers E r hr hstep k
    extendSeparatedCover E N.points (r (k + 1)) (hr (k + 1)) N.subset
      (N.separated.mono' (fun _ _ h => (hstep k).trans h))

theorem nestedSeparatedCovers_step_subset {X : Type*} [MetricSpace X]
    (E : Set X) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (hstep : ∀ k, r (k + 1) ≤ r k)
    (k : ℕ) :
    (nestedSeparatedCovers E r hr hstep k).points ⊆
      (nestedSeparatedCovers E r hr hstep (k + 1)).points := by
  exact subset_extendSeparatedCover E _ (r (k + 1)) (hr (k + 1))
    (nestedSeparatedCovers E r hr hstep k).subset
    ((nestedSeparatedCovers E r hr hstep k).separated.mono' (fun _ _ h => (hstep k).trans h))

theorem nestedSeparatedCovers_monotone {X : Type*} [MetricSpace X]
    (E : Set X) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (hstep : ∀ k, r (k + 1) ≤ r k) :
    Monotone (fun k => (nestedSeparatedCovers E r hr hstep k).points) :=
  monotone_nat_of_le_succ (nestedSeparatedCovers_step_subset E r hr hstep)

theorem nestedSeparatedCovers_countable {X : Type*} [MetricSpace X] [SeparableSpace X]
    (E : Set X) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (hstep : ∀ k, r (k + 1) ≤ r k)
    (k : ℕ) : (nestedSeparatedCovers E r hr hstep k).points.Countable :=
  separated_set_countable _ (r k) (hr k) (nestedSeparatedCovers E r hr hstep k).separated

theorem nestedSeparatedCovers_locally_finite {X : Type*} [MetricSpace X]
    (E : Set X) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (hstep : ∀ k, r (k + 1) ≤ r k)
    (k : ℕ) (K : Set X) (hK : IsCompact K) :
    ((nestedSeparatedCovers E r hr hstep k).points ∩ K).Finite :=
  separated_set_finite_inter_compact _ K (r k) (hr k)
    (nestedSeparatedCovers E r hr hstep k).separated hK

end

end RieszRectifiability

end OAI
