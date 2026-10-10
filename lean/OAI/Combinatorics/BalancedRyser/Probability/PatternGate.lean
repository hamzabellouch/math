import OAI.Combinatorics.BalancedRyser.Probability.FiniteCenteredPatternLemmas

namespace OAI

namespace Balanced.PatternModel

noncomputable section
open scoped Classical BigOperators
open MeasureTheory

abbrev gated (P : PatternModel) (A : Finset P.Color) (E : Set P.Sample)
    (hE : MeasurableSet E)
    (hdep : ∀ x y, (∀ c ∈ A, x c = y c) → (x ∈ E ↔ y ∈ E)) : PatternModel where
  Color := P.Color
  Value := P.Value
  law := P.law
  Label := P.Label
  support a := P.support a ∪ A
  event a := E ∩ P.event a
  eventMeasurable a := hE.inter (P.eventMeasurable a)
  dependsOn a x y h := by
    have h₁ := hdep x y (fun c hc => h c (Finset.mem_union_right _ hc))
    have h₂ := P.dependsOn a x y (fun c hc => h c (Finset.mem_union_left _ hc))
    exact and_congr h₁ h₂

variable (P : PatternModel) (A : Finset P.Color) (E : Set P.Sample)
    (hE : MeasurableSet E)
    (hdep : ∀ x y, (∀ c ∈ A, x c = y c) → (x ∈ E ↔ y ∈ E))

@[simp] theorem gated_measure : (P.gated A E hE hdep).measure = P.measure := rfl

@[simp] theorem gated_fixCoordinates (D : Finset P.Color) (x ω : P.Sample) :
    (P.gated A E hE hdep).fixCoordinates D x ω = P.fixCoordinates D x ω := rfl

@[simp] theorem gated_fixedExpectation (D : Finset P.Color) (x : P.Sample)
    (f : P.Sample → ℝ) :
    (P.gated A E hE hdep).fixedExpectation D x f = P.fixedExpectation D x f := rfl

theorem gated_support_card_le (r : ℕ) (hr : ∀ a, (P.support a).card ≤ r)
    (a : P.Label) : ((P.gated A E hE hdep).support a).card ≤ r + A.card := by
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right (hr a) _)

theorem gated_indicator (a : P.Label) (ω : P.Sample) :
    (P.gated A E hE hdep).indicator a ω = if ω ∈ E then P.indicator a ω else 0 := by
  by_cases h : ω ∈ E <;> simp [indicator, gated, Set.indicator_apply, h]

theorem gated_count (ω : P.Sample) :
    (P.gated A E hE hdep).count ω = if ω ∈ E then P.count ω else 0 := by
  unfold count
  simp_rw [gated_indicator]
  by_cases h : ω ∈ E <;> simp [h]

theorem gated_overlapCount (K₀ K : Finset P.Color) (hA : A ⊆ K₀) (ω : P.Sample) :
    (P.gated A E hE hdep).overlapCount K₀ K ω =
      if ω ∈ E then P.overlapCount K₀ K ω else 0 := by
  have hsupport (a : P.Label) :
      (P.support a ∪ A) \ K₀ = P.support a \ K₀ := by
    rw [Finset.union_sdiff_distrib, Finset.sdiff_eq_empty_iff_subset.mpr hA,
      Finset.union_empty]
  unfold overlapCount
  change (∑ a, if Disjoint ((P.support a ∪ A) \ K₀) K then 0 else
      (P.gated A E hE hdep).indicator a ω) = _
  simp_rw [hsupport, gated_indicator]
  by_cases h : ω ∈ E <;> simp [h]

include hdep

theorem gate_fixed_iff (D : Finset P.Color) (hAD : A ⊆ D) (x ω : P.Sample) :
    P.fixCoordinates D x ω ∈ E ↔ x ∈ E := by
  apply hdep
  intro c hc
  simp [fixCoordinates, hAD hc]

theorem fixedExpectation_gated_function (D : Finset P.Color) (hAD : A ⊆ D)
    (x : P.Sample) (f : P.Sample → ℝ) :
    P.fixedExpectation D x (fun ω => if ω ∈ E then f ω else 0) =
      if x ∈ E then P.fixedExpectation D x f else 0 := by
  unfold fixedExpectation
  by_cases hx : x ∈ E
  · simp only [ite_eq_left hx]
    apply integral_congr_ae
    filter_upwards [] with ω
    simp only [ite_eq_left ((gate_fixed_iff P A E hdep D hAD x ω).mpr hx)]
  · simp only [ite_eq_right hx]
    have hz : (fun ω => if P.fixCoordinates D x ω ∈ E then
        f (P.fixCoordinates D x ω) else (0 : ℝ)) = fun _ => 0 := by
      funext ω
      exact ite_eq_right (fun h => hx ((gate_fixed_iff P A E hdep D hAD x ω).mp h))
    rw [hz, integral_zero]

theorem gated_fixed_count (D : Finset P.Color) (hAD : A ⊆ D) (x : P.Sample) :
    (P.gated A E hE hdep).fixedExpectation D x (P.gated A E hE hdep).count =
      if x ∈ E then P.fixedExpectation D x P.count else 0 := by
  rw [gated_fixedExpectation]
  have hc : (P.gated A E hE hdep).count =
      fun ω => if ω ∈ E then P.count ω else 0 :=
    funext (gated_count P A E hE hdep)
  rw [hc]
  exact fixedExpectation_gated_function P A E hdep D hAD x P.count

theorem gated_fixed_overlapCount (K₀ K D : Finset P.Color)
    (hA₀ : A ⊆ K₀) (hAD : A ⊆ D) (x : P.Sample) :
    (P.gated A E hE hdep).fixedExpectation D x
      ((P.gated A E hE hdep).overlapCount K₀ K) =
      if x ∈ E then P.fixedExpectation D x (P.overlapCount K₀ K) else 0 := by
  rw [gated_fixedExpectation]
  have hc : (P.gated A E hE hdep).overlapCount K₀ K =
      fun ω => if ω ∈ E then P.overlapCount K₀ K ω else 0 :=
    funext (gated_overlapCount P A E hE hdep K₀ K hA₀)
  rw [hc]
  exact fixedExpectation_gated_function P A E hdep D hAD x (P.overlapCount K₀ K)

theorem gated_centered_moment_le (K₀ : Finset P.Color) (hA₀ : A ⊆ K₀)
    (x : P.Sample) (s r : ℕ) (q C : ℝ) (hq : 1 ≤ q) (hC : 0 ≤ C)
    (hsupport : ∀ a, (P.support a).card ≤ r)
    (htotal : ∀ K : Finset P.Color, K.card ≤ (2 * s) * (r + A.card) →
      ∀ y, y ∈ E → P.fixedExpectation (K₀ ∪ K) y P.count ≤ C * q)
    (hoverlap : ∀ K : Finset P.Color, K.card ≤ (2 * s) * (r + A.card) →
      ∀ y, y ∈ E → P.fixedExpectation (K₀ ∪ K) y (P.overlapCount K₀ K) ≤ C) :
    (P.gated A E hE hdep).fixedExpectation K₀ x
      (fun ω => |(P.gated A E hE hdep).count ω -
        (P.gated A E hE hdep).fixedExpectation K₀ x
          (P.gated A E hE hdep).count| ^ (2 * s)) ≤
      ((2 * s).factorial : ℝ) * 2 ^ (2 * s) * (2 * C) ^ (2 * s) * q ^ s := by
  apply (P.gated A E hE hdep).centered_moment_le_of_exposureBounds
    K₀ x s (r + A.card) q C hq hC
    (fun a => gated_support_card_le P A E hE hdep r hsupport a)
  · intro K hK y
    rw [gated_fixed_count P A E hE hdep (K₀ ∪ K)
      (hA₀.trans Finset.subset_union_left) y]
    split_ifs with hy
    · exact htotal K hK y hy
    · exact mul_nonneg hC (by linarith)
  · intro K hK y
    rw [gated_fixed_overlapCount P A E hE hdep K₀ K (K₀ ∪ K) hA₀
      (hA₀.trans Finset.subset_union_left) y]
    split_ifs with hy
    · exact hoverlap K hK y hy
    · exact hC

end
end Balanced.PatternModel

end OAI
