import OAI.Combinatorics.BalancedRyser.Probability.PatternAllowedGate
import OAI.Combinatorics.BalancedRyser.Probability.PatternSourceTails

namespace OAI

open MeasureTheory

namespace Balanced
open scoped _root_.Balanced

universe u

def UniformAllowedPatternTotalBound (P : ℕ → PatternModel.{u})
    (K₀ : ∀ q, Finset (P q).Color) (S : ∀ q, Set (P q).Sample)
    (scale : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ q, N ≤ q →
    ∀ K : Finset (P q).Color, K.card ≤ m → ∀ x ∈ S q,
      (P q).fixedExpectation (K₀ q ∪ K) x (P q).count ≤ C * scale q

def UniformAllowedPatternOverlapBound (P : ℕ → PatternModel.{u})
    (K₀ : ∀ q, Finset (P q).Color) (S : ∀ q, Set (P q).Sample) : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ q, N ≤ q →
    ∀ K : Finset (P q).Color, K.card ≤ m → ∀ x ∈ S q,
      (P q).fixedExpectation (K₀ q ∪ K) x ((P q).overlapCount (K₀ q) K) ≤ C

namespace PatternModel

variable (P : ℕ → PatternModel.{u}) (K₀ : ∀ q, Finset (P q).Color)
    (S : ∀ q, Set (P q).Sample) (hS : ∀ q, MeasurableSet (S q))
    (hdepends : ∀ q x y, (∀ c ∈ K₀ q, x c = y c) → (x ∈ S q ↔ y ∈ S q))

theorem uniform_gateInitialEvent_supports
    (hsupport : UniformPatternSupports P) (hinitial : BoundedInitialColors P K₀) :
    UniformPatternSupports (fun q => (P q).gateInitialEvent (K₀ q) (S q) (hS q) (hdepends q)) := by
  obtain ⟨r, hr⟩ := hsupport
  obtain ⟨r₀, hr₀⟩ := hinitial
  refine ⟨r₀ + r, ?_⟩
  intro q a
  exact ((P q).gateInitialEvent_support_card_le (K₀ q) (S q) (hS q) (hdepends q)
    r (hr q) a).trans (Nat.add_le_add_right (hr₀ q) r)

theorem uniform_gateInitialEvent_totalBound (scale : ℕ → ℝ)
    (hscale : ∀ q, 0 ≤ scale q) (htotal : UniformAllowedPatternTotalBound P K₀ S scale) :
    UniformPatternTotalBound
      (fun q => (P q).gateInitialEvent (K₀ q) (S q) (hS q) (hdepends q)) K₀ scale := by
  intro m
  obtain ⟨C, hC, N, hN⟩ := htotal m
  refine ⟨C, hC, N, ?_⟩
  intro q hq K hK x
  exact (P q).gateInitialEvent_total_bound (K₀ q) (S q) (hS q) (hdepends q) K
    (C * scale q) (mul_nonneg hC.le (hscale q)) (hN q hq K hK) x

theorem uniform_gateInitialEvent_overlapBound
    (hoverlap : UniformAllowedPatternOverlapBound P K₀ S) :
    UniformPatternOverlapBound
      (fun q => (P q).gateInitialEvent (K₀ q) (S q) (hS q) (hdepends q)) K₀ := by
  intro m
  obtain ⟨C, hC, N, hN⟩ := hoverlap m
  refine ⟨C, hC, N, ?_⟩
  intro q hq K hK x
  exact (P q).gateInitialEvent_overlap_bound (K₀ q) (S q) (hS q) (hdepends q)
    K C hC.le (hN q hq K hK) x

end PatternModel

namespace PatternAllowedSourceTails

theorem gate_count_fix_of_mem (P : PatternModel.{u}) (K₀ : Finset P.Color)
    (S : Set P.Sample) (hS : MeasurableSet S)
    (hdepends : ∀ x y, (∀ c ∈ K₀, x c = y c) → (x ∈ S ↔ y ∈ S))
    (x : P.Sample) (hx : x ∈ S) (ω : P.Sample) :
    (P.gateInitialEvent K₀ S hS hdepends).count (P.fixCoordinates K₀ x ω) =
      P.count (P.fixCoordinates K₀ x ω) := by
  rw [P.gateInitialEvent_count, ite_eq_left]
  exact (P.mem_fixed_event_iff K₀ S hdepends x ω).mpr hx

theorem gate_mean_of_mem (P : PatternModel.{u}) (K₀ : Finset P.Color)
    (S : Set P.Sample) (hS : MeasurableSet S)
    (hdepends : ∀ x y, (∀ c ∈ K₀, x c = y c) → (x ∈ S ↔ y ∈ S))
    (x : P.Sample) (hx : x ∈ S) :
    (P.gateInitialEvent K₀ S hS hdepends).fixedExpectation K₀ x
      (P.gateInitialEvent K₀ S hS hdepends).count = P.fixedExpectation K₀ x P.count := by
  change (∫ ω, (P.gateInitialEvent K₀ S hS hdepends).count
    (P.fixCoordinates K₀ x ω) ∂P.measure) = _
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (gate_count_fix_of_mem P K₀ S hS hdepends x hx)

variable (P : ℕ → PatternModel.{u}) (K₀ : ∀ q, Finset (P q).Color)
    (S : ∀ q, Set (P q).Sample) (hS : ∀ q, MeasurableSet (S q))
    (hdepends : ∀ q x y, (∀ c ∈ K₀ q, x c = y c) → (x ∈ S q ↔ y ∈ S q))
    (hsupport : UniformPatternSupports P) (hinitial : BoundedInitialColors P K₀)

include hS hdepends hsupport hinitial

theorem raw_moments_of_allowed_exposureBounds
    (htotal : UniformAllowedPatternTotalBound P K₀ S (fun _ => 1))
    (s : ℕ) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ q, N ≤ q → ∀ x ∈ S q,
      (P q).fixedExpectation (K₀ q) x (fun ω => (P q).count ω ^ s) ≤ C := by
  let Q := fun q => (P q).gateInitialEvent (K₀ q) (S q) (hS q) (hdepends q)
  have hsup := PatternModel.uniform_gateInitialEvent_supports
    P K₀ S hS hdepends hsupport hinitial
  have htot := PatternModel.uniform_gateInitialEvent_totalBound
    P K₀ S hS hdepends (fun _ => 1) (fun _ => zero_le_one) htotal
  obtain ⟨C, hC, N, hN⟩ := uniformPatternMoments_of_totalBound Q K₀ hsup htot s hs
  refine ⟨C, hC, N, ?_⟩
  intro q hq x hx
  have heq : (Q q).fixedExpectation (K₀ q) x (fun ω => (Q q).count ω ^ s) =
      (P q).fixedExpectation (K₀ q) x (fun ω => (P q).count ω ^ s) := by
    apply integral_congr_ae
    filter_upwards [] with ω
    exact congrArg (fun z : ℝ => z ^ s)
      (gate_count_fix_of_mem (P q) (K₀ q) (S q) (hS q) (hdepends q) x hx ω)
  rw [← heq]
  exact hN q hq x

theorem centered_moments_of_allowed_exposureBounds
    (htotal : UniformAllowedPatternTotalBound P K₀ S (fun q => (q : ℝ)))
    (hoverlap : UniformAllowedPatternOverlapBound P K₀ S)
    (s : ℕ) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ q, N ≤ q → ∀ x ∈ S q,
      (P q).fixedExpectation (K₀ q) x
        (fun ω => |(P q).count ω - (P q).fixedExpectation (K₀ q) x (P q).count| ^
          (2 * s)) ≤ C * (q : ℝ) ^ s := by
  let Q := fun q => (P q).gateInitialEvent (K₀ q) (S q) (hS q) (hdepends q)
  have hsup := PatternModel.uniform_gateInitialEvent_supports
    P K₀ S hS hdepends hsupport hinitial
  have htot := PatternModel.uniform_gateInitialEvent_totalBound
    P K₀ S hS hdepends (fun q => (q : ℝ)) Nat.cast_nonneg htotal
  have hov := PatternModel.uniform_gateInitialEvent_overlapBound P K₀ S hS hdepends hoverlap
  obtain ⟨C, hC, N, hN⟩ :=
    uniformCenteredPatternMoments_of_exposureBounds Q K₀ hsup htot hov s hs
  refine ⟨C, hC, N, ?_⟩
  intro q hq x hx
  have heq : (Q q).fixedExpectation (K₀ q) x
      (fun ω => |(Q q).count ω - (Q q).fixedExpectation (K₀ q) x (Q q).count| ^ (2 * s)) =
      (P q).fixedExpectation (K₀ q) x
        (fun ω => |(P q).count ω - (P q).fixedExpectation (K₀ q) x (P q).count| ^ (2 * s)) := by
    apply integral_congr_ae
    filter_upwards [] with ω
    exact congrArg₂ (fun count mean : ℝ => |count - mean| ^ (2 * s))
      (gate_count_fix_of_mem (P q) (K₀ q) (S q) (hS q) (hdepends q) x hx ω)
      (gate_mean_of_mem (P q) (K₀ q) (S q) (hS q) (hdepends q) x hx)
  rw [← heq]
  exact hN q hq x

theorem raw_tail_of_allowed_exposureBounds
    (htotal : UniformAllowedPatternTotalBound P K₀ S (fun _ => 1)) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ q, N ≤ q → ∀ x ∈ S q,
      (P q).measure.real {ω | (q : ℝ) ^ (1 / 100 : ℝ) ≤
        (P q).count ((P q).fixCoordinates (K₀ q) x ω)} ≤ C / (q : ℝ) ^ (r + 1) := by
  let Q := fun q => (P q).gateInitialEvent (K₀ q) (S q) (hS q) (hdepends q)
  have hsup := PatternModel.uniform_gateInitialEvent_supports
    P K₀ S hS hdepends hsupport hinitial
  have htot := PatternModel.uniform_gateInitialEvent_totalBound
    P K₀ S hS hdepends (fun _ => 1) (fun _ => zero_le_one) htotal
  obtain ⟨C, hC, N, hN⟩ :=
    PatternSourceTails.uniform_raw_pattern_tail_of_totalBound Q K₀ hsup htot r
  refine ⟨C, hC, N, ?_⟩
  intro q hq x hx
  have h := hN q hq x
  change (P q).measure.real {ω | (q : ℝ) ^ (1 / 100 : ℝ) ≤
    (Q q).count ((P q).fixCoordinates (K₀ q) x ω)} ≤ _ at h
  dsimp only [Q] at h
  simpa only [gate_count_fix_of_mem (P q) (K₀ q) (S q) (hS q) (hdepends q) x hx] using h

theorem centered_tail_of_allowed_exposureBounds
    (htotal : UniformAllowedPatternTotalBound P K₀ S (fun q => (q : ℝ)))
    (hoverlap : UniformAllowedPatternOverlapBound P K₀ S)
    (s : ℕ) (hs : 0 < s) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ q, N ≤ q → ∀ x ∈ S q,
      (P q).measure.real {ω | η * (q : ℝ) ≤
        |(P q).count ((P q).fixCoordinates (K₀ q) x ω) -
          (P q).fixedExpectation (K₀ q) x (P q).count|} ≤ C / (q : ℝ) ^ s := by
  let Q := fun q => (P q).gateInitialEvent (K₀ q) (S q) (hS q) (hdepends q)
  have hsup := PatternModel.uniform_gateInitialEvent_supports
    P K₀ S hS hdepends hsupport hinitial
  have htot := PatternModel.uniform_gateInitialEvent_totalBound
    P K₀ S hS hdepends (fun q => (q : ℝ)) Nat.cast_nonneg htotal
  have hov := PatternModel.uniform_gateInitialEvent_overlapBound P K₀ S hS hdepends hoverlap
  obtain ⟨C, hC, N, hN⟩ := PatternSourceTails.uniform_centered_pattern_tail_of_exposureBounds
    Q K₀ hsup htot hov s hs η hη
  refine ⟨C, hC, N, ?_⟩
  intro q hq x hx
  have h := hN q hq x
  change (P q).measure.real {ω | η * (q : ℝ) ≤
    |(Q q).count ((P q).fixCoordinates (K₀ q) x ω) -
      (Q q).fixedExpectation (K₀ q) x (Q q).count|} ≤ _ at h
  dsimp only [Q] at h
  simpa only [gate_count_fix_of_mem (P q) (K₀ q) (S q) (hS q) (hdepends q) x hx,
    gate_mean_of_mem (P q) (K₀ q) (S q) (hS q) (hdepends q) x hx] using h

theorem joint_raw_tail_of_allowed_exposureBounds
    (htotal : UniformAllowedPatternTotalBound P K₀ S (fun _ => 1)) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ q, N ≤ q →
      (P q).measure.real (S q ∩ {ω | (q : ℝ) ^ (1 / 100 : ℝ) ≤ (P q).count ω}) ≤
        (C / (q : ℝ) ^ (r + 1)) * (P q).measure.real (S q) := by
  obtain ⟨C, hC, N, hN⟩ := raw_tail_of_allowed_exposureBounds
    P K₀ S hS hdepends hsupport hinitial htotal r
  refine ⟨C, hC, N, ?_⟩
  intro q hq
  apply (P q).measureReal_inter_le_of_fixed_measureReal_le (K₀ q) (S q) _
    (hS q) (measurableSet_le measurable_const (P q).measurable_count) (hdepends q)
    (C / (q : ℝ) ^ (r + 1)) (by positivity)
  intro x hx
  exact hN q hq x hx

theorem joint_centered_tail_of_allowed_exposureBounds
    (htotal : UniformAllowedPatternTotalBound P K₀ S (fun q => (q : ℝ)))
    (hoverlap : UniformAllowedPatternOverlapBound P K₀ S)
    (s : ℕ) (hs : 0 < s) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ q, N ≤ q →
      (P q).measure.real (S q ∩ {ω | η * (q : ℝ) ≤
        |(P q).count ω - (P q).fixedExpectation (K₀ q) ω (P q).count|}) ≤
          (C / (q : ℝ) ^ s) * (P q).measure.real (S q) := by
  obtain ⟨C, hC, N, hN⟩ := centered_tail_of_allowed_exposureBounds
    P K₀ S hS hdepends hsupport hinitial htotal hoverlap s hs η hη
  refine ⟨C, hC, N, ?_⟩
  intro q hq
  have hm := (P q).measurable_fixedExpectation (K₀ q) (P q).measurable_count
  apply (P q).measureReal_inter_le_of_fixed_measureReal_le (K₀ q) (S q) _
    (hS q) (measurableSet_le measurable_const (((P q).measurable_count.sub hm).abs))
    (hdepends q) (C / (q : ℝ) ^ s) (by positivity)
  intro x hx
  simpa only [Set.preimage_ofPred_eq, Pi.sub_apply, (P q).fixedExpectation_fixCoordinates] using hN q hq x hx

end PatternAllowedSourceTails
end Balanced

end OAI
