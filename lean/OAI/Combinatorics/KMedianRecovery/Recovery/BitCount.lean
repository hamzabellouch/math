import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.IndexedFiniteExperiment
import OAI.Combinatorics.KMedianRecovery.Geometry.Metric
import OAI.Combinatorics.KMedianRecovery.Recovery.Failure
import OAI.Combinatorics.KMedianRecovery.Encoding.RecoveryIndex

namespace OAI

namespace MetricKMedianRecovery.GlobalAssembly
open LocalSearch Sampling FiniteSampling IntegralAssembly IndexedCopies RoundedAssembly

noncomputable def bitCount (v : ℚ) (Nstar : ℕ) (c a : ℝ) (I : RationalMetricInput) : ℕ :=
  let C := Rounding.cap I.clients.card (gamma/16)
  let L0 := countBound (commonL v Nstar I.clients.card C)
  let ζ := FailureBudget.failure gamma ⌈a⌉₊ I.size
  let n := repetitions c L0 ζ
  recoveryBitCount (marked false I.clients) (marked true I.facilities) C L0 (I.clients.card*C) n

lemma absolute_gap_pos : 0 < gamma/4 := div_pos gamma_pos (by norm_num)

theorem global_semantic_fair_experiment : ∃ v : ℚ, 0 < v ∧ ∃ Nstar : ℕ, 1 ≤ Nstar ∧
    ∃ c : ℝ, 0 < c ∧ ∀ (a : ℝ), 0 < a → ∀ I : RationalMetricInput,
    ∃ out : (Fin (bitCount v Nstar c a I) → Bool) → Finset (Fin I.pointCount),
      (∀ bits, I.Feasible (out bits) ∧ (I.cost (out bits):ℝ) ≤ 6*(I.optimum:ℝ)) ∧
      1-Real.rpow ((I.size:ℝ)+2) (-a) ≤
        probability (fun bits => (I.cost (out bits):ℝ) ≤ (2-gamma/4)*(I.optimum:ℝ)) ∧
      average (fun bits => (I.cost (out bits):ℝ)) ≤ (2-gamma/4)*(I.optimum:ℝ) := by
  classical
  obtain ⟨v,hv,Nstar,hNstar,c,hc,H⟩ := indexed_finite_experiment
  refine ⟨v,hv,Nstar,hNstar,c,hc,?_⟩
  intro a _ha I
  let ζ := FailureBudget.failure gamma ⌈a⌉₊ I.size
  have hζ : 0 < ζ := FailureBudget.failure_pos gamma_pos _ _
  have hζmargin : ζ ≤ gamma/24 := FailureBudget.failure_le_margin gamma_pos.le _ _
  have hζtail : ζ ≤ Real.rpow ((I.size:ℝ)+2) (-a) :=
    FailureBudget.failure_le_power gamma_lt_one.le _
  obtain ⟨run,hfeas,hprob,hexp⟩ := @H (Fin I.pointCount) I.metric inferInstance inferInstance
    I.facilities I.clients I.budget ζ I.facilities_nonempty I.budget_pos hζ
  simp only [RationalMetricInput.metric_cost,RationalMetricInput.metric_optimum] at hfeas hprob hexp
  let C := Rounding.cap I.clients.card (gamma/16)
  let L0 := countBound (commonL v Nstar I.clients.card C)
  let n := repetitions c L0 ζ
  let E := recoveryTapeEquiv (marked false I.clients) (marked true I.facilities) C L0 (I.clients.card*C) n
  let out (bits : Fin (bitCount v Nstar c a I) → Bool) := run (E bits)
  have hop : (0:ℝ) ≤ (I.optimum:ℝ) := by exact_mod_cast I.optimum_nonneg
  refine ⟨out,?_,?_,?_⟩
  · intro bits
    exact ⟨⟨(hfeas (E bits)).1,(hfeas (E bits)).2.2.1,fun _ => (hfeas (E bits)).2.1⟩,
      (hfeas (E bits)).2.2.2⟩
  · have heq : probability (fun bits => (I.cost (out bits):ℝ) ≤ (2-gamma/4)*(I.optimum:ℝ)) =
        probability (fun seed => (I.cost (run seed):ℝ) ≤ (2-gamma/4)*(I.optimum:ℝ)) :=
      average_equiv E _ _ (fun _ => rfl)
    rw [heq]
    apply (sub_le_sub_left hζtail 1).trans
    refine hprob.trans (probability_mono (fun seed hs => hs.trans ?_))
    apply mul_le_mul_of_nonneg_right _ hop
    linarith [gamma_pos]
  · have heq : average (fun bits => (I.cost (out bits):ℝ)) = average (fun seed => (I.cost (run seed):ℝ)) :=
      average_equiv E _ _ (fun _ => rfl)
    rw [heq]
    exact hexp.trans (FailureBudget.expectation_margin hop hζmargin)

end MetricKMedianRecovery.GlobalAssembly
namespace MetricKMedianRecovery.Categorical

noncomputable def stepCoefficient (epsilon : ℝ) : ℕ := Nat.ceil (2 / tolerance epsilon)
noncomputable def sampleCoefficient (epsilon : ℝ) : ℕ :=
  Nat.ceil (1 / (2 * tolerance epsilon ^ 4)) + 1

lemma step_polynomial_bound (a : ℕ) {epsilon : ℝ} (he : 0 < epsilon) :
    2 ^ stepExponent a epsilon ≤ stepCoefficient epsilon * (a+1)^2 := by
  have hm := stepExponent_mono (Nat.le_succ a) epsilon
  have hp : 2 ^ stepExponent a epsilon ≤ (2:ℕ) ^ stepExponent (a+1) epsilon := by
    gcongr
  have hs := (stepExponent_spec (Nat.succ_pos a) he).2
  have hC : 2 / tolerance epsilon ≤ (stepCoefficient epsilon : ℝ) := Nat.le_ceil _
  have hh : ((2 ^ stepExponent a epsilon : ℕ) : ℝ) ≤
      (stepCoefficient epsilon : ℝ) * ((a+1:ℕ):ℝ)^2 := by
    calc
      _ ≤ ((2 ^ stepExponent (a+1) epsilon : ℕ) : ℝ) := Nat.cast_le.mpr hp
      _ ≤ 2 * ((a+1:ℕ):ℝ)^2 / tolerance epsilon := hs.le
      _ = (2 / tolerance epsilon) * ((a+1:ℕ):ℝ)^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC (sq_nonneg _)
  exact_mod_cast hh

lemma exponent_polynomial_bound (a : ℕ) {epsilon : ℝ} (he : 0 < epsilon) :
    stepExponent a epsilon ≤ stepCoefficient epsilon * (a+1)^2 :=
  (Nat.lt_two_pow_self.le).trans (step_polynomial_bound a he)

lemma sample_polynomial_bound (q a : ℕ) {epsilon : ℝ} (he : 0 < epsilon) :
    sampleCount q a epsilon ≤ sampleCoefficient epsilon * (q+1) * (a+1)^4 := by
  have hm := sampleCount_mono (Nat.le_succ q) (Nat.le_succ a) epsilon
  have hs := (sampleCount_spec (Nat.succ_pos q) (Nat.succ_pos a) he).2.2
  have hC : 1 / (2 * tolerance epsilon ^ 4) ≤
      ((sampleCoefficient epsilon - 1 : ℕ) : ℝ) := by
    simpa only [sampleCoefficient, Nat.add_sub_cancel] using Nat.le_ceil (1 / (2 * tolerance epsilon ^ 4))
  have hA : (1:ℝ) ≤ ((q+1:ℕ):ℝ) * ((a+1:ℕ):ℝ)^4 := by
    have hq : (1:ℝ) ≤ ((q+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos q
    have ha : (1:ℝ) ≤ ((a+1:ℕ):ℝ)^4 := one_le_pow₀ (by exact_mod_cast Nat.succ_pos a)
    nlinarith
  have hCeq : ((sampleCoefficient epsilon : ℕ) : ℝ) =
      ((sampleCoefficient epsilon - 1 : ℕ) : ℝ) + 1 := by simp [sampleCoefficient]
  have hh : (sampleCount q a epsilon : ℝ) ≤
      (sampleCoefficient epsilon : ℝ) * ((q+1:ℕ):ℝ) * ((a+1:ℕ):ℝ)^4 := by
    calc
      _ ≤ (sampleCount (q+1) (a+1) epsilon : ℝ) := Nat.cast_le.mpr hm
      _ ≤ ((q+1:ℕ):ℝ)*((a+1:ℕ):ℝ)^4 / (2*tolerance epsilon^4) + 1 := hs.le
      _ = (1 / (2*tolerance epsilon^4)) *
          (((q+1:ℕ):ℝ)*((a+1:ℕ):ℝ)^4) + 1 := by ring
      _ ≤ ((sampleCoefficient epsilon - 1 : ℕ):ℝ) *
          (((q+1:ℕ):ℝ)*((a+1:ℕ):ℝ)^4) + 1 := by gcongr
      _ ≤ (sampleCoefficient epsilon : ℝ) * ((q+1:ℕ):ℝ) * ((a+1:ℕ):ℝ)^4 := by
        rw [hCeq]; nlinarith only [hA]
  exact_mod_cast hh

noncomputable def completionOracleBits (f m : ℕ) (epsilon : ℝ) : ℕ :=
  let e := stepExponent m epsilon
  ((2^e*(m*f)*sampleCount (m*f) m epsilon*m)+m)*e

lemma completionOracleBits_polynomial (f m : ℕ) {epsilon : ℝ} (he : 0 < epsilon) :
    completionOracleBits f m epsilon ≤
      (stepCoefficient epsilon ^ 2 * sampleCoefficient epsilon + stepCoefficient epsilon) *
        (m+f+1)^13 := by
  let T := m+f+1
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hm : m ≤ T := by dsimp [T]; omega
  have hm1 : m+1 ≤ T := by dsimp [T]; omega
  have hq : m*f ≤ T^2 := by dsimp [T]; nlinarith
  have hq1 : m*f+1 ≤ T^2 := by dsimp [T]; nlinarith
  have hp := (step_polynomial_bound m he).trans
    (Nat.mul_le_mul_left (stepCoefficient epsilon) (Nat.pow_le_pow_left hm1 2))
  have hexp := (exponent_polynomial_bound m he).trans
    (Nat.mul_le_mul_left (stepCoefficient epsilon) (Nat.pow_le_pow_left hm1 2))
  have hL : sampleCount (m*f) m epsilon ≤ sampleCoefficient epsilon * T^6 := by
    calc
      _ ≤ sampleCoefficient epsilon * (m*f+1) * (m+1)^4 := sample_polynomial_bound _ _ he
      _ ≤ sampleCoefficient epsilon * T^2 * T^4 := by gcongr
      _ = _ := by ring
  have hpow : T^3 ≤ T^13 := Nat.pow_le_pow_right hT (by decide)
  change ((2 ^ stepExponent m epsilon * (m*f) * sampleCount (m*f) m epsilon * m)+m) *
      stepExponent m epsilon ≤ _
  calc
    _ ≤ ((stepCoefficient epsilon*T^2 * T^2 * (sampleCoefficient epsilon*T^6) * T)+T) *
        (stepCoefficient epsilon*T^2) := by gcongr
    _ = stepCoefficient epsilon ^ 2 * sampleCoefficient epsilon * T^13 +
        stepCoefficient epsilon * T^3 := by ring
    _ ≤ (stepCoefficient epsilon ^ 2 * sampleCoefficient epsilon + stepCoefficient epsilon) *
        T^13 := by nlinarith [Nat.mul_le_mul_left (stepCoefficient epsilon) hpow]

end MetricKMedianRecovery.Categorical

end OAI
