import OAI.Combinatorics.BalancedRyser.Candidates.CandidateGeneratorPairModel
import OAI.Combinatorics.BalancedRyser.Incidence.CandidateIncidenceMean
import OAI.Combinatorics.BalancedRyser.Probability.PatternIntegrability

namespace OAI

namespace Balanced.CandidateGeneratorPair

noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateExposure

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance : MeasurableSpace F := ⊤

theorem probabilitySum_le (e D : Finset (Direction F)) (a : MergedPairs F)
    (he : e.card = 2) (heD : e ⊆ D) (m : ℕ) (hD : D.card ≤ m) :
    probabilitySum e D a ≤ (32768 * (m + 1)^4 : ℝ) := by
  have h := probabilitySum_le_exposure_strata e D a he heD
  have h2 := sum_targets_success_two_three_le D a m 2 hD (Or.inl rfl)
  have h3 := sum_targets_success_two_three_le D a m 3 hD (Or.inr rfl)
  have h4 := sum_targets_success_four_le D a
  have hcard : (D.card : ℝ) ≤ (m : ℝ) + 1 := by
    exact_mod_cast (show D.card ≤ m + 1 by omega)
  have hpow : (D.card : ℝ)^4 ≤ ((m : ℝ) + 1)^4 :=
    pow_le_pow_left₀ (by positivity) hcard _
  rw [show Finset.Icc 2 4 = {2, 3, 4} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at h
  have hn : 0 ≤ ((m : ℝ) + 1)^4 := by positivity
  linarith

theorem fixed_count_le_of_subset (e D : Finset (Direction F)) (a : MergedPairs F)
    (he : e.card = 2) (heD : e ⊆ D) (m : ℕ) (hD : D.card ≤ m) :
    (patternModel e).fixedExpectation D a (patternModel e).count ≤
      (32768 * (m + 1)^4 : ℝ) := by
  rw [fixedExpectation_exposed]
  simp_rw [patternModel_count]
  rw [integral_count]
  exact probabilitySum_le e D a he heD m hD

theorem model_count_nonneg (e : Finset (Direction F)) (M : MergedPairs F) :
    0 ≤ (patternModel e).count M := by rw [patternModel_count]; positivity

theorem model_count_le_card (e : Finset (Direction F)) (M : MergedPairs F) :
    (patternModel e).count M ≤ Fintype.card (patternModel e).Label := by
  calc
    _ ≤ ∑ _a : (patternModel e).Label, (1 : ℝ) :=
      Finset.sum_le_sum (fun a _ => (patternModel e).indicator_le_one a M)
    _ = _ := by simp

theorem fixed_count_le (e D : Finset (Direction F)) (a : MergedPairs F)
    (he : e.card = 2) (m : ℕ) (hD : D.card ≤ m) :
    (patternModel e).fixedExpectation D a (patternModel e).count ≤
      (32768 * (m + 3)^4 : ℝ) := by
  let P := patternModel e
  have hbound (y : P.Sample) : P.fixedExpectation (D ∪ e) y P.count ≤
      (32768 * (m + 3)^4 : ℝ) := by
    have hc : (D ∪ e).card ≤ m + 2 := by
      have h := Finset.card_union_le D e
      omega
    have h := fixed_count_le_of_subset e (D ∪ e) y he (Finset.subset_union_right)
      (m + 2) hc
    convert h using 1
    push_cast
    ring
  have h := P.fixedExpectation_mul_le_of_fixedBounds D e a
    (fun _ => 1) P.count (32768 * (m + 3)^4) 1
    (Fintype.card P.Label) (by positivity) measurable_const P.measurable_count
    (fun _ => zero_le_one) (model_count_nonneg e) (fun _ => le_rfl)
    (model_count_le_card e) (by intros; rfl) hbound
  simpa [PatternModel.fixedExpectation, PatternModel.measure] using h

theorem fixed_moment_le (e D : Finset (Direction F)) (a : MergedPairs F)
    (he : e.card = 2) (m s : ℕ) (hD : D.card ≤ m) :
    (patternModel e).fixedExpectation D a
      (fun M => (patternModel e).count M ^ s) ≤
      (32768 * ((m + (s - 1)*4 : ℕ) + 3)^4 : ℝ)^s := by
  apply (patternModel e).fixed_moment_le_pow D a 4 s _ (by positivity)
    (fun b => (support_card e b).le)
  intro K hK y
  exact fixed_count_le e (D ∪ K) y he (m + (s - 1)*4)
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hD hK))

theorem conditional_count_moment_le (e D : Finset (Direction F)) (a : MergedPairs F)
    (he : e.card = 2) (m s : ℕ) (hD : D.card ≤ m) :
    (∫ M, (count e M : ℝ)^s ∂(exposedLaw D a).toMeasure) ≤
      (32768 * ((m + (s - 1)*4 : ℕ) + 3)^4 : ℝ)^s := by
  have h := fixed_moment_le e D a he m s hD
  rw [fixedExpectation_exposed] at h
  simpa only [patternModel_count] using h

theorem count_moment_le (e : Finset (Direction F)) (he : e.card = 2) (s : ℕ) :
    (∫ M, (count e M : ℝ)^s ∂(offsetLaw F).toMeasure) ≤
      (32768 * (((s - 1)*4 : ℕ) + 3)^4 : ℝ)^s := by
  have h := fixed_moment_le e ∅ (fun _ _ => 0) he 0 s (by simp)
  have hfix (M : MergedPairs F) :
      (patternModel e).fixCoordinates ∅ (fun _ _ => 0) M = M := by
    funext d
    simp [PatternModel.fixCoordinates]
  simp only [PatternModel.fixedExpectation] at h
  simp_rw [hfix, patternModel_count] at h
  rw [patternModel_measure] at h
  simpa only [zero_add] using h

end
end Balanced.CandidateGeneratorPair

end OAI
