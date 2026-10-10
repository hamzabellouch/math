import OAI.Geometry.EinsteinFour.ClassificationScaling
import OAI.Geometry.EinsteinFour.OrientationQuotient
import OAI.Geometry.EinsteinFour.TopologicalNumbers
import Mathlib.Topology.Covering.Basic

namespace OAI

/-! The metric and Euler reductions for an actual two-sheeted cover.
The raw metric facts are the pullback/local-isometry and geodesic-lifting
consequences of Petersen, §1.3.3 and Proposition 5.6.3. The minimum-distance
formula, two-point fiber count, antipodal quotient and parity obstruction
are derived here. -/

namespace PositiveEinsteinFour

open EinsteinFour
open scoped Manifold ContDiff ENNReal

noncomputable section

universe u v

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace FourSpace M] [ChartedSpace FourSpace N]
  [IsManifold I4 ∞ M] [IsManifold I4 ∞ N]

/-- Raw data of a Riemannian two-sheeted cover. `distance_lift` is the
endpoint of a lift of a minimizing base geodesic from the specified point;
the other distance inequality is length preservation under projection. -/
structure MetricDoubleCover (g : SmoothMetric M) (h : SmoothMetric N) where
  projection : N → M
  covering : IsCoveringMap projection
  surjective : Function.Surjective projection
  deck : N → N
  involutive : Function.Involutive deck
  free : ∀ x, deck x ≠ x
  fibers : ∀ x y, projection x = projection y ↔ x = y ∨ x = deck y
  deck_distance : ∀ x y, scaledEDistance h 1 (deck x) (deck y) = scaledEDistance h 1 x y
  distance_down : ∀ x y, scaledEDistance g 1 (projection x) (projection y) ≤
    scaledEDistance h 1 x y
  distance_lift : ∀ x y, ∃ z, projection z = projection y ∧
    scaledEDistance h 1 x z ≤ scaledEDistance g 1 (projection x) (projection y)

namespace MetricDoubleCover

variable {g : SmoothMetric M} {h : SmoothMetric N} (C : MetricDoubleCover g h)

theorem projection_deck (x : N) : C.projection (C.deck x) = C.projection x :=
  (C.fibers _ _).mpr (Or.inr rfl)

/-- Freeness and the explicit deck fibers give the actual sheet number. -/
theorem fiber_card (y : M) : Nat.card {x : N // C.projection x = y} = 2 := by
  classical
  obtain ⟨x, hx⟩ := C.surjective y
  let f : Bool → {z : N // C.projection z = y} := fun b =>
    if b then ⟨C.deck x, (C.projection_deck x).trans hx⟩ else ⟨x, hx⟩
  have hinj : Function.Injective f := by
    intro b c hbc
    cases b <;> cases c
    · rfl
    · have he := congrArg Subtype.val hbc
      exact False.elim (C.free x (by simpa only [f, Bool.false_eq_true, ite_false, ite_true] using he.symm))
    · have he := congrArg Subtype.val hbc
      exact False.elim (C.free x (by simpa only [f, Bool.false_eq_true, ite_false, ite_true] using he))
    · rfl
  have hsurj : Function.Surjective f := by
    intro z
    have hz : C.projection z.val = C.projection x := z.property.trans hx.symm
    rcases (C.fibers z.val x).mp hz with hz | hz
    · refine ⟨false, ?_⟩
      apply Subtype.ext
      simpa only [f, Bool.false_eq_true, ite_false] using hz.symm
    · refine ⟨true, ?_⟩
      apply Subtype.ext
      simpa only [f, ite_true] using hz.symm
  have hc := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩).symm
  simpa only [Nat.card_eq_fintype_card, Fintype.card_bool] using hc

theorem quotient_distance_one (x y : N) :
    scaledEDistance g 1 (C.projection x) (C.projection y) =
      min (scaledEDistance h 1 x y) (scaledEDistance h 1 x (C.deck y)) := by
  apply le_antisymm
  · apply le_min (C.distance_down x y)
    simpa only [C.projection_deck] using C.distance_down x (C.deck y)
  · obtain ⟨z, hz, hd⟩ := C.distance_lift x y
    rcases (C.fibers z y).mp hz with hzy | hzy
    · subst z
      exact (min_le_left _ _).trans hd
    · subst z
      exact (min_le_right _ _).trans hd

theorem scaled_distance (k : SmoothMetric M) (a : ℝ) (ha : 0 ≤ a) (x y : M) :
    scaledEDistance k a x y = ENNReal.ofReal (Real.sqrt a) * scaledEDistance k 1 x y := by
  simpa only [mul_one] using scaledEDistance_mul k a 1 ha x y

theorem deck_distance_scaled (a : ℝ) (ha : 0 ≤ a) (x y : N) :
    scaledEDistance h a (C.deck x) (C.deck y) = scaledEDistance h a x y := by
  rw [scaled_distance h a ha, scaled_distance h a ha, C.deck_distance]

theorem quotient_distance (a : ℝ) (ha : 0 ≤ a) (x y : N) :
    scaledEDistance g a (C.projection x) (C.projection y) =
      min (scaledEDistance h a x y) (scaledEDistance h a x (C.deck y)) := by
  rw [scaled_distance g a ha, C.quotient_distance_one, mul_min,
    ← scaled_distance h a ha, ← scaled_distance h a ha]

include C

/-- The round branch is the existing concrete projective quotient theorem,
after transporting the deck action through the given sphere identification. -/
theorem classified_of_round (a : ℝ) (ha : 0 < a)
    (hround : ScaledIsometricTo h a roundDistance) : Classified g := by
  obtain ⟨e, he⟩ := hround
  have hdeck (x y : N) : roundDistance (e (C.deck x)) (e (C.deck y)) =
      roundDistance (e x) (e y) := by
    apply (ENNReal.ofReal_eq_ofReal_iff
      (Real.arccos_nonneg _) (Real.arccos_nonneg _)).mp
    exact (he (C.deck x) (C.deck y)).trans
      ((C.deck_distance_scaled a ha.le x y).trans (he x y).symm)
  have hdist (x y : N) : scaledEDistance g a (C.projection x) (C.projection y) =
      ENNReal.ofReal (min (roundDistance (e x) (e y))
        (roundDistance (e x) (e (C.deck y)))) := by
    rw [C.quotient_distance a ha.le, ENNReal.ofReal_min, he, he]
  exact classified_of_round_double_cover g a ha e C.deck C.involutive C.free hdeck
    C.projection C.surjective C.fibers hdist

end MetricDoubleCover

/-- Hatcher, Chapter 2, Exercise 22, specialized to the actual two-sheeted
cover of closed smooth four-manifolds. The finite-CW comparison and Hatcher
3.26(c) identify the Euler characteristic with `Topology.eulerFour`. -/
def HatcherDoubleEulerInput : Prop :=
  CompactSpace M → CompactSpace N →
  ∀ p : N → M, IsCoveringMap p → Function.Surjective p →
    (∀ y, Nat.card {x : N // p x = y} = 2) →
      Topology.eulerFour N = 2 * Topology.eulerFour M

/-- The degree-zero through degree-four consequence of Hatcher 3.19 for a
manifold identified with CP², using the ordinary isometry/homeomorphism
and singular-homology invariance. No curvature classification is assumed. -/
def HatcherProjectiveBettiInput (h : SmoothMetric N) : Prop :=
  ∀ a : ℝ, 0 < a → ScaledIsometricTo h a fubiniStudyDistance →
    ∀ i : Fin 5, Topology.rationalBetti N i.val = if i.val % 2 = 0 then 1 else 0

theorem eulerThree_of_projective_betti {h : SmoothMetric N}
    (hp : HatcherProjectiveBettiInput h) (a : ℝ) (ha : 0 < a)
    (he : ScaledIsometricTo h a fubiniStudyDistance) : Topology.eulerFour N = 3 := by
  unfold Topology.eulerFour
  simp only [hp a ha he]
  norm_num [Fin.sum_univ_succ]

theorem MetricDoubleCover.classified_of_two_models {g : SmoothMetric M} {h : SmoothMetric N}
    [CompactSpace M] [CompactSpace N]
    (C : MetricDoubleCover g h) (hEuler : HatcherDoubleEulerInput (M := M) (N := N))
    (hBetti : HatcherProjectiveBettiInput h)
    (hmodels : ∃ a : ℝ, 0 < a ∧
      (ScaledIsometricTo h a roundDistance ∨ ScaledIsometricTo h a fubiniStudyDistance)) :
    Classified g := by
  obtain ⟨a, ha, hs | hp⟩ := hmodels
  · exact C.classified_of_round a ha hs
  · have hthree : Topology.eulerFour N = 3 := eulerThree_of_projective_betti hBetti a ha hp
    have hcover : Topology.eulerFour N = 2 * Topology.eulerFour M :=
      hEuler inferInstance inferInstance C.projection C.covering C.surjective C.fiber_card
    omega

end
end PositiveEinsteinFour

end OAI
