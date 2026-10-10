import OAI.Combinatorics.BalancedRyser.Probability.PatternCenteredAssembly
import OAI.Combinatorics.BalancedRyser.Probability.PatternSupportCompatibility
import OAI.Combinatorics.BalancedRyser.Probability.PatternWeightExtensions

namespace OAI

section

namespace Balanced.PatternModel
open scoped _root_.Balanced

noncomputable section
open scoped Classical BigOperators
open MeasureTheory

theorem centered_moment_le_of_exposureBounds (P : PatternModel)
    (K₀ : Finset P.Color) (x : P.Sample) (s r : ℕ) (q C : ℝ)
    (hq : 1 ≤ q) (hC : 0 ≤ C)
    (hsupport : ∀ a, (P.support a).card ≤ r)
    (htotal : ∀ K : Finset P.Color, K.card ≤ (2 * s) * r → ∀ y,
      P.fixedExpectation (K₀ ∪ K) y P.count ≤ C * q)
    (hoverlap : ∀ K : Finset P.Color, K.card ≤ (2 * s) * r → ∀ y,
      P.fixedExpectation (K₀ ∪ K) y (P.overlapCount K₀ K) ≤ C) :
    P.fixedExpectation K₀ x
      (fun ω => |P.count ω - P.fixedExpectation K₀ x P.count| ^ (2 * s)) ≤
        ((2 * s).factorial : ℝ) * 2 ^ (2 * s) * (2 * C) ^ (2 * s) * q ^ s := by
  apply PatternModelMoments.centered_moment_bound_of_productWeight_costs
    P K₀ x s q (2 * C) hq (by positivity)
  · intro pre hpre
    have hK : (P.additionalSupport K₀ pre).card ≤ (2 * s) * r :=
      (P.additionalSupport_card_le K₀ pre r hsupport).trans
        (Nat.mul_le_mul_right r (by omega))
    have h := P.productWeight_free_extension_le K₀ x pre (C * q)
      (mul_nonneg hC (by linarith))
      (fun y => htotal (P.additionalSupport K₀ pre) hK y)
    convert h using 1; ring
  · intro pre hpre
    have hK : (P.additionalSupport K₀ pre).card ≤ (2 * s) * r :=
      (P.additionalSupport_card_le K₀ pre r hsupport).trans
        (Nat.mul_le_mul_right r (by omega))
    have h := P.productWeight_overlap_extension_le K₀ x pre C hC
      (fun y => hoverlap (P.additionalSupport K₀ pre) hK y)
    have heq :
        (∑ a, if PatternMoments.supportOverlap P.support K₀ pre a then
          P.productWeight K₀ x (a :: pre) else 0) =
        (∑ a, if Disjoint (P.support a \ K₀) (P.additionalSupport K₀ pre)
          then 0 else P.productWeight K₀ x (a :: pre)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [P.additionalSupport_eq_freshPrefixSupport]
      unfold PatternMoments.supportOverlap PatternModel.freshPrefixSupport
      split_ifs <;> simp_all
    rw [heq]
    exact h

theorem overlapCount_le_allExposed (P : PatternModel)
    (K₀ K : Finset P.Color) (ω : P.Sample) :
    P.overlapCount K₀ K ω ≤ P.overlapCount ∅ (K₀ ∪ K) ω := by
  unfold overlapCount
  apply Finset.sum_le_sum
  intro a _
  by_cases h : Disjoint (P.support a \ K₀) K
  · rw [ite_eq_left h]
    split_ifs
    · exact le_rfl
    · exact P.indicator_nonneg a ω
  · have hn : ¬ Disjoint (P.support a \ ∅) (K₀ ∪ K) := by
      obtain ⟨c, hc, hcK⟩ := Finset.not_disjoint_iff.mp h
      exact Finset.not_disjoint_iff.mpr ⟨c,
        by simpa using (Finset.mem_sdiff.mp hc).1,
        Finset.mem_union_right _ hcK⟩
    rw [ite_eq_right h, ite_eq_right hn]

theorem integrable_fixed_overlapCount (P : PatternModel)
    (D : Finset P.Color) (x : P.Sample) (K₀ K : Finset P.Color) :
    Integrable (fun ω => P.overlapCount K₀ K (P.fixCoordinates D x ω)) P.measure := by
  unfold overlapCount
  apply integrable_finsetSum
  intro a _
  by_cases h : Disjoint (P.support a \ K₀) K
  · simp only [ite_eq_left h]
    exact integrable_const 0
  · simp only [ite_eq_right h]
    exact P.integrable_fixed_indicator D x a

theorem centered_moment_le_of_allExposedBounds (P : PatternModel)
    (K₀ : Finset P.Color) (x : P.Sample) (s r : ℕ) (q C : ℝ)
    (hq : 1 ≤ q) (hC : 0 ≤ C)
    (hsupport : ∀ a, (P.support a).card ≤ r)
    (htotal : ∀ D : Finset P.Color, D.card ≤ K₀.card + (2 * s) * r → ∀ y,
      P.fixedExpectation D y P.count ≤ C * q)
    (hoverlap : ∀ D : Finset P.Color, D.card ≤ K₀.card + (2 * s) * r → ∀ y,
      P.fixedExpectation D y (P.overlapCount ∅ D) ≤ C) :
    P.fixedExpectation K₀ x
      (fun ω => |P.count ω - P.fixedExpectation K₀ x P.count| ^ (2 * s)) ≤
        ((2 * s).factorial : ℝ) * 2 ^ (2 * s) * (2 * C) ^ (2 * s) * q ^ s := by
  apply P.centered_moment_le_of_exposureBounds K₀ x s r q C hq hC hsupport
  · intro K hK y
    exact htotal (K₀ ∪ K) ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hK _)) y
  · intro K hK y
    apply le_trans ?_ (hoverlap (K₀ ∪ K)
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hK _)) y)
    apply integral_mono (P.integrable_fixed_overlapCount (K₀ ∪ K) y K₀ K)
      (P.integrable_fixed_overlapCount (K₀ ∪ K) y ∅ (K₀ ∪ K))
    intro ω
    exact P.overlapCount_le_allExposed K₀ K _

end
end Balanced.PatternModel

end

section

open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced

universe u

theorem uniformCenteredPatternMoments_of_exposureBounds
    (P : ℕ → PatternModel.{u}) (K₀ : ∀ q, Finset (P q).Color)
    (hsupport : UniformPatternSupports P)
    (htotal : UniformPatternTotalBound P K₀ (fun q => (q : ℝ)))
    (hoverlap : UniformPatternOverlapBound P K₀) :
    UniformCenteredPatternMoments P K₀ := by
  classical
  intro s _hs
  obtain ⟨C, hC, q₀, hcost⟩ :=
    uniform_productWeight_extensions P K₀ hsupport htotal hoverlap (2 * s)
  refine ⟨((2 * s).factorial : ℝ) * 2 ^ (2 * s) * C ^ (2 * s),
    by positivity, max q₀ 1, ?_⟩
  intro q hq x
  have hq₀ : q₀ ≤ q := (le_max_left q₀ 1).trans hq
  have hq₁ : (1 : ℝ) ≤ q := by
    exact_mod_cast (le_max_right q₀ 1).trans hq
  apply PatternModelMoments.centered_moment_bound_of_productWeight_costs
    (P q) (K₀ q) x s q C hq₁ hC.le
  · intro pre hpre
    exact (hcost q hq₀ x pre hpre).1
  · intro pre hpre
    have heq :
        (∑ a, if PatternMoments.supportOverlap (P q).support (K₀ q) pre a then
          (P q).productWeight (K₀ q) x (a :: pre) else 0) =
        (∑ a, if Disjoint ((P q).support a \ K₀ q)
          ((P q).additionalSupport (K₀ q) pre) then 0 else
          (P q).productWeight (K₀ q) x (a :: pre)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [(P q).additionalSupport_eq_freshPrefixSupport]
      unfold PatternMoments.supportOverlap PatternModel.freshPrefixSupport
      split_ifs <;> simp_all
    rw [heq]
    exact (hcost q hq₀ x pre hpre).2

theorem patternMoments_proof : PatternMomentsResult.{u} := by
  intro P K₀ hsupport _hinitial
  constructor
  · exact uniformPatternMoments_of_totalBound P K₀ hsupport
  · intro htotal hoverlap
    exact uniformCenteredPatternMoments_of_exposureBounds P K₀ hsupport htotal hoverlap

end Balanced

end

end OAI
