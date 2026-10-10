import OAI.Combinatorics.BalancedRyser.Probability.PatternIntegrability
import OAI.Combinatorics.BalancedRyser.Probability.PatternMomentModel

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced.PatternModel
open scoped _root_.Balanced

theorem sum_productWeight_cons_eq (P : PatternModel)
    (K₀ : Finset P.Color) (x : P.Sample) (as : List P.Label) (S : Finset P.Label) :
    (∑ a ∈ S, P.productWeight K₀ x (a :: as)) =
      P.fixedExpectation K₀ x (fun ω => P.positiveProduct K₀ x as ω *
        ((∑ a ∈ S, P.indicator a ω) +
          P.fixedExpectation K₀ x (fun η => ∑ a ∈ S, P.indicator a η))) := by
  classical
  have hES : P.fixedExpectation K₀ x (fun η => ∑ a ∈ S, P.indicator a η) =
      ∑ a ∈ S, P.fixedExpectation K₀ x (P.indicator a) := by
    unfold fixedExpectation
    exact integral_finsetSum S (fun a _ => P.integrable_fixed_indicator K₀ x a)
  rw [hES]
  simp only [productWeight, fixedExpectation]
  rw [← integral_finsetSum S (fun a _ =>
    P.integrable_fixed_positiveProduct K₀ K₀ x x (a :: as))]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [positiveProduct, List.map_cons, List.prod_cons, fixedExpectation]
  rw [← Finset.sum_mul, Finset.sum_add_distrib]
  ring

theorem productWeight_subset_extension_le (P : PatternModel)
    (K₀ : Finset P.Color) (x : P.Sample) (as : List P.Label)
    (S : Finset P.Label) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ y, P.fixedExpectation (K₀ ∪ P.additionalSupport K₀ as) y
      (fun ω => ∑ a ∈ S, P.indicator a ω) ≤ C) :
    (∑ a ∈ S, P.productWeight K₀ x (a :: as)) ≤
      (2 * C) * P.productWeight K₀ x as := by
  classical
  rw [P.sum_productWeight_cons_eq K₀ x as S]
  apply P.fixedExpectation_positive_extension_le K₀ (P.additionalSupport K₀ as) x
    (P.positiveProduct K₀ x as) (fun ω => ∑ a ∈ S, P.indicator a ω)
    C (2 ^ as.length) (S.card : ℝ) hC
    (P.measurable_positiveProduct K₀ x as)
    (Finset.measurable_sum S (fun a _ => P.measurable_indicator a))
    (P.positiveProduct_nonneg K₀ x as)
    (fun ω => Finset.sum_nonneg (fun a _ => P.indicator_nonneg a ω))
    (P.positiveProduct_le K₀ x as)
  · intro ω
    calc
      (∑ a ∈ S, P.indicator a ω) ≤ ∑ _a ∈ S, (1 : ℝ) :=
        Finset.sum_le_sum (fun a _ => P.indicator_le_one a ω)
      _ = (S.card : ℝ) := by simp
  · exact P.positiveProduct_dependsOn K₀ x as
  · exact hbound

theorem productWeight_free_extension_le (P : PatternModel)
    (K₀ : Finset P.Color) (x : P.Sample) (as : List P.Label)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ y, P.fixedExpectation (K₀ ∪ P.additionalSupport K₀ as) y P.count ≤ C) :
    (∑ a, P.productWeight K₀ x (a :: as)) ≤ (2 * C) * P.productWeight K₀ x as := by
  exact P.productWeight_subset_extension_le K₀ x as Finset.univ C hC hbound

theorem productWeight_overlap_extension_le (P : PatternModel)
    (K₀ : Finset P.Color) (x : P.Sample) (as : List P.Label)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ y, P.fixedExpectation (K₀ ∪ P.additionalSupport K₀ as) y
      (P.overlapCount K₀ (P.additionalSupport K₀ as)) ≤ C) :
    (∑ a, if Disjoint (P.support a \ K₀) (P.additionalSupport K₀ as)
      then 0 else P.productWeight K₀ x (a :: as)) ≤
        (2 * C) * P.productWeight K₀ x as := by
  classical
  have h := P.productWeight_subset_extension_le K₀ x as
    (Finset.univ.filter (fun a => ¬Disjoint (P.support a \ K₀) (P.additionalSupport K₀ as)))
    C hC (by
      intro y
      simp only [Finset.sum_filter, ite_not]
      exact hbound y)
  simpa only [Finset.sum_filter, ite_not] using h

theorem additionalSupport_card_le (P : PatternModel)
    (K₀ : Finset P.Color) (as : List P.Label) (r : ℕ)
    (h : ∀ a, (P.support a).card ≤ r) :
    (P.additionalSupport K₀ as).card ≤ as.length * r := by
  classical
  calc
    (P.additionalSupport K₀ as).card ≤
        ∑ a ∈ as.toFinset, (P.support a \ K₀).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ as.toFinset, r := Finset.sum_le_sum
      (fun a _ => (Finset.card_le_card Finset.sdiff_subset).trans (h a))
    _ = as.toFinset.card * r := by simp
    _ ≤ as.length * r := Nat.mul_le_mul_right r (List.toFinset_card_le as)

end Balanced.PatternModel

namespace Balanced
open scoped _root_.Balanced

theorem uniform_productWeight_extensions
    (P : ℕ → PatternModel) (K₀ : ∀ q, Finset (P q).Color)
    (hsupport : UniformPatternSupports P)
    (htotal : UniformPatternTotalBound P K₀ (fun q => (q : ℝ)))
    (hoverlap : UniformPatternOverlapBound P K₀) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ x : (P q).Sample,
      ∀ as : List (P q).Label, as.length < N →
        ((∑ a, (P q).productWeight (K₀ q) x (a :: as)) ≤
          (C * q) * (P q).productWeight (K₀ q) x as) ∧
        ((∑ a, if Disjoint ((P q).support a \ K₀ q) ((P q).additionalSupport (K₀ q) as)
          then 0 else (P q).productWeight (K₀ q) x (a :: as)) ≤
            C * (P q).productWeight (K₀ q) x as) := by
  classical
  obtain ⟨r, hr⟩ := hsupport
  obtain ⟨Cf, hCf, qf, hqf⟩ := htotal (N * r)
  obtain ⟨Ct, hCt, qt, hqt⟩ := hoverlap (N * r)
  refine ⟨2 * max Cf Ct, mul_pos (by norm_num) (hCf.trans_le (le_max_left _ _)),
    max qf qt, ?_⟩
  intro q hq x as has
  have hK : ((P q).additionalSupport (K₀ q) as).card ≤ N * r :=
    ((P q).additionalSupport_card_le (K₀ q) as r (hr q)).trans
      (Nat.mul_le_mul_right r (by omega))
  have hfree := (P q).productWeight_free_extension_le (K₀ q) x as (Cf * q)
    (mul_nonneg hCf.le (Nat.cast_nonneg q))
    (fun y => hqf q ((le_max_left qf qt).trans hq) _ hK y)
  have htouch := (P q).productWeight_overlap_extension_le (K₀ q) x as Ct hCt.le
    (fun y => hqt q ((le_max_right qf qt).trans hq) _ hK y)
  have hW := (P q).productWeight_nonneg (K₀ q) x as
  constructor
  · apply hfree.trans
    apply mul_le_mul_of_nonneg_right _ hW
    calc
      2 * (Cf * (q : ℝ)) = (2 * Cf) * q := by ring
      _ ≤ (2 * max Cf Ct) * q := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_max_left Cf Ct) (by norm_num)) (Nat.cast_nonneg q)
  · exact htouch.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_max_right Cf Ct) (by norm_num)) hW)

end Balanced

end OAI
