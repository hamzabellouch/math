import Mathlib
import OAI.Probability.SKGap.Localization.PoissonWeight
import OAI.Probability.SKGap.Terminal.PairingPairingAddError

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SKGapCutoff.Clock

theorem poisson_to_binomial_in_probability {q B : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hB : 0 < B) {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) (good : (n : ℕ) → Ω n → Prop)
    (hgood : Tendsto (fun n => μ n {ω | ¬good n ω}) atTop (𝓝 0))
    {ι : ℕ → Type*} (M : (n : ℕ) → Ω n → ℕ)
    (hM : ∀ K : ℕ, ∀ᶠ n in atTop, ∀ ω, good n ω → K ≤ M n ω)
    (a : (n : ℕ) → Ω n → ι n → ℕ → ℝ)
    (hab : ∀ n ω, good n ω → ∀ i j, |a n ω i j| ≤ B)
    (hp : ∀ y ε : ℝ, 0 < ε → Tendsto (fun n => μ n
      {ω | good n ω ∧ ∃ i, ε < |∑' j,
        poissonMass (q*M n ω+y*Real.sqrt (M n ω)) j*a n ω i j|}) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ n
      {ω | ∃ i, ε < |∑' j, binomialMass q (M n ω) j*a n ω i j|}) atTop (𝓝 0) := by
  classical
  intro ε hε
  obtain ⟨s,δ,hδ,N,hN⟩ := finite_clock_certificate hq hq1 hB hε
  let E : (n : ℕ) → ℝ → Set (Ω n) := fun n y =>
    {ω | good n ω ∧ ∃ i, δ/2 < |∑' j,
      poissonMass (q*M n ω+(-y)*Real.sqrt (M n ω)) j*a n ω i j|}
  have hsum : Tendsto (fun n => ∑ y ∈ s, μ n (E n y)) atTop (𝓝 0) := by
    simpa only [E, Finset.sum_const_zero] using tendsto_finsetSum s (fun y _ => hp (-y) (δ/2) (by positivity))
  have hlimit := hgood.add hsum
  simp only [add_zero] at hlimit
  apply tendsto_const_nhds.squeeze' hlimit (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [hM N] with n hn
  calc
    _ ≤ μ n ({ω | ¬good n ω} ∪ ⋃ y ∈ s, E n y) := by
      apply measure_mono
      intro ω hω
      by_cases hg : good n ω
      · apply Or.inr
        by_contra hnone
        have hsmall : ∀ i y, y ∈ s → |∑' j,
            poissonMass (q*M n ω+(-y)*Real.sqrt (M n ω)) j*a n ω i j| < δ := by
          intro i y hy
          have hnE : ω ∉ E n y := by
            intro hh
            exact hnone (Set.mem_iUnion.mpr ⟨y,Set.mem_iUnion.mpr ⟨hy,hh⟩⟩)
          have hle : |∑' j, poissonMass (q*M n ω+(-y)*Real.sqrt (M n ω)) j*
              a n ω i j| ≤ δ/2 := by
            by_contra h
            exact hnE ⟨hg,i,lt_of_not_ge h⟩
          linarith
        obtain ⟨i,hi⟩ := hω
        exact (not_lt_of_ge (hN (M n ω) (hn ω hg) (a n ω i) (hab n ω hg i)
          (hsmall i)).le) hi
      · exact Or.inl hg
    _ ≤ μ n {ω | ¬good n ω}+μ n (⋃ y ∈ s, E n y) := measure_union_le _ _
    _ ≤ μ n {ω | ¬good n ω}+∑ y ∈ s, μ n (E n y) :=
      add_le_add le_rfl (measure_biUnion_finset_le s (E n))

end SKGapCutoff.Clock

open MeasureTheory Filter ProbabilityTheory ContinuousLinearMap
open scoped Topology NNReal ENNReal

namespace SKGapCutoff

noncomputable def residualAttempt {n : ℕ} (J : Interaction n) (q : ℝ) :
    Observables n →L[ℝ] Observables n :=
  q⁻¹ • (attemptLM J-(1-q) • 1)

lemma residualAttempt_apply {n : ℕ} (J : Interaction n) (q : ℝ)
    (f : Observables n) (x : Spin n) :
    residualAttempt J q f x = (attemptLM J f x-(1-q)*f x)/q := by
  simp [residualAttempt,div_eq_mul_inv,mul_comm]

lemma attempt_eq_lazy_residual {n : ℕ} (J : Interaction n) {q : ℝ} (hq : q ≠ 0) :
    attemptLM J = q • residualAttempt J q+(1-q) • 1 := by
  simp only [residualAttempt,smul_smul,mul_inv_cancel₀ hq,one_smul,sub_add_cancel]

lemma residualAttempt_const {n : ℕ} (J : Interaction n) {q : ℝ} (hq : q ≠ 0)
    (c : ℝ) : residualAttempt J q (fun _ => c) = fun _ => c := by
  ext x
  rw [residualAttempt_apply,attempt_const]
  field_simp
  ring

lemma residualAttempt_pow_const {n : ℕ} (J : Interaction n) {q : ℝ} (hq : q ≠ 0)
    (k : ℕ) (c : ℝ) : (residualAttempt J q ^ k) (fun _ => c) = fun _ => c := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ',mul_apply_eq_comp,ih,residualAttempt_const J hq]

lemma residualAttempt_nonneg {n : ℕ} (J : Interaction n) {q : ℝ} (hq : 0 < q)
    (hhold : ∀ x, 1-q ≤ discreteKernel J 1 x x)
    (f : Observables n) (hf : ∀ x, 0 ≤ f x) (x : Spin n) :
    0 ≤ residualAttempt J q f x := by
  rw [← kernel_apply (residualAttempt J q) f x]
  apply Finset.sum_nonneg
  intro y _
  apply mul_nonneg _ (hf y)
  rw [residualAttempt_apply]
  apply div_nonneg _ hq.le
  by_cases hxy : x=y
  · subst y
    simpa [discreteKernel,pow_one] using sub_nonneg.mpr (hhold x)
  · simpa only [hxy,↓reduceIte,mul_zero,sub_zero,discreteKernel,pow_one] using
      discreteKernel_nonneg J 1 x y

lemma residualAttempt_pow_nonneg {n : ℕ} (J : Interaction n) {q : ℝ} (hq : 0 < q)
    (hhold : ∀ x, 1-q ≤ discreteKernel J 1 x x)
    (k : ℕ) (f : Observables n) (hf : ∀ x, 0 ≤ f x) (x : Spin n) :
    0 ≤ (residualAttempt J q ^ k) f x := by
  induction k generalizing x with
  | zero => exact hf x
  | succ k ih =>
    rw [pow_succ',mul_apply_eq_comp]
    exact residualAttempt_nonneg J hq hhold _ (fun x => ih x) x

lemma residualAttempt_pow_abs_le {n : ℕ} (J : Interaction n) {q : ℝ} (hq : 0 < q)
    (hhold : ∀ x, 1-q ≤ discreteKernel J 1 x x)
    (k : ℕ) (f : Observables n) (hf : ∀ x, |f x| ≤ 1) (x : Spin n) :
    |(residualAttempt J q ^ k) f x| ≤ 1 := by
  have hup := residualAttempt_pow_nonneg J hq hhold k (fun y => 1-f y)
    (fun y => by have := (abs_le.mp (hf y)).2; linarith) x
  have hlo := residualAttempt_pow_nonneg J hq hhold k (fun y => f y+1)
    (fun y => by have := (abs_le.mp (hf y)).1; linarith) x
  change 0 ≤ (residualAttempt J q ^ k) ((fun _ => 1)-f) x at hup
  change 0 ≤ (residualAttempt J q ^ k) (f+(fun _ => 1)) x at hlo
  rw [map_sub,residualAttempt_pow_const J hq.ne'] at hup
  rw [map_add,residualAttempt_pow_const J hq.ne'] at hlo
  simp only [Pi.add_apply,Pi.sub_apply] at hlo hup
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma residual_semigroup_uniformization {n : ℕ} (hn : 0 < n)
    (J : Interaction n) {q : ℝ} (hq : q ≠ 0) (t : ℝ) :
    semigroup J t = Real.exp (-(q*n*t)) •
      NormedSpace.exp ((q*n*t) • residualAttempt J q) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have heq : t • generatorCLM J =
      (-(q*n*t)) • (1 : Observables n →L[ℝ] Observables n) +
        (q*n*t) • residualAttempt J q := by
    unfold residualAttempt attemptLM
    simp only [smul_smul,smul_sub,smul_add]
    have hc : q*n*t*q⁻¹ = (n:ℝ)*t := by field_simp
    have hc' : q*n*t*(q⁻¹*(n:ℝ)⁻¹) = t := by field_simp
    have hc'' : q*n*t*(q⁻¹*(1-q)) = (n:ℝ)*t*(1-q) := by field_simp
    rw [hc,hc',hc'']
    module
  let : NormedAlgebra ℚ (Observables n →L[ℝ] Observables n) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  unfold semigroup
  rw [heq,NormedSpace.exp_add_of_commute
    (((Commute.one_left (residualAttempt J q)).smul_left _).smul_right _),
    exp_smul_identity,smul_mul_assoc,one_mul]

lemma residual_poisson_hasSum {n : ℕ} (hn : 0 < n)
    (J : Interaction n) {q : ℝ} (hq : q ≠ 0) (t : ℝ)
    (f : Observables n) (x : Spin n) :
    HasSum (fun j => Clock.poissonMass (q*n*t) j*(residualAttempt J q ^ j) f x)
      (semigroup J t f x) := by
  have hs := (Pi.hasSum.mp (exp_apply_hasSum ((q*n*t) • residualAttempt J q) f) x).mul_left
    (Real.exp (-(q*n*t)))
  convert! hs using 1
  · funext j
    simp only [smul_pow,_root_.smul_apply,Pi.smul_apply,smul_eq_mul,Clock.poissonMass]
    ring
  · rw [residual_semigroup_uniformization hn J hq]
    rfl

lemma natCastCLM_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (f : E) : (k : E →L[ℝ] E) f = (k:ℝ) • f := by
  induction k with
  | zero => simp
  | succ k ih => simp [Nat.cast_succ,ih,add_smul]

lemma residual_binomial_sum {n : ℕ} (J : Interaction n) {q : ℝ} (hq : q ≠ 0)
    (M : ℕ) (f : Observables n) (x : Spin n) :
    (∑ j ∈ Finset.range (M+1), Clock.binomialMass q M j*
      (residualAttempt J q ^ j) f x) = (attemptLM J ^ M) f x := by
  rw [attempt_eq_lazy_residual J hq]
  rw [(((Commute.one_right (residualAttempt J q)).smul_left q).smul_right (1-q)).add_pow]
  simp only [_root_.sum_apply,smul_pow,one_pow,smul_mul_assoc,mul_smul_comm,mul_one,
    Clock.binomialMass,mul_apply_eq_comp,_root_.smul_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [natCastCLM_apply,map_smul,Pi.smul_apply,smul_eq_mul]
  ring

lemma residual_binomial_hasSum {n : ℕ} (J : Interaction n) {q : ℝ} (hq : q ≠ 0)
    (M : ℕ) (f : Observables n) (x : Spin n) :
    HasSum (fun j => Clock.binomialMass q M j*(residualAttempt J q ^ j) f x)
      ((attemptLM J ^ M) f x) := by
  rw [← residual_binomial_sum J hq M f x]
  apply hasSum_sum_of_ne_finset_zero
  intro j hj
  have hj' : M < j := by simp only [Finset.mem_range,not_lt] at hj; omega
  simp [Clock.binomialMass,Nat.choose_eq_zero_of_lt hj']

lemma gibbsExpectation_abs_le_one {n : ℕ} (J : Interaction n) (f : Observables n)
    (hf : ∀ x, |f x| ≤ 1) : |gibbsExpectation J f| ≤ 1 := by
  unfold gibbsExpectation
  calc
    _ ≤ ∑ x, |gibbs J x*f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, gibbs J x := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul,abs_of_nonneg (gibbs_pos J x).le]
      exact mul_le_of_le_one_right (gibbs_pos J x).le (hf x)
    _ = _ := gibbs_sum J

lemma residual_test_bound {n : ℕ} (J : Interaction n) {q : ℝ} (hq : 0 < q)
    (hhold : ∀ x, 1-q ≤ discreteKernel J 1 x x)
    (f : Observables n) (hf : ∀ x, |f x| ≤ 1) (x : Spin n) (j : ℕ) :
    |(residualAttempt J q ^ j) f x-gibbsExpectation J f| ≤ 2 := by
  have h := abs_sub ((residualAttempt J q ^ j) f x) (gibbsExpectation J f)
  linarith [residualAttempt_pow_abs_le J hq hhold j f hf x,
    gibbsExpectation_abs_le_one J f hf]

lemma residual_poisson_test {n : ℕ} (hn : 0 < n)
    (J : Interaction n) {q : ℝ} (hq : q ≠ 0) (m : ℝ)
    (f : Observables n) (x : Spin n) :
    (∑' j, Clock.poissonMass m j*((residualAttempt J q ^ j) f x-gibbsExpectation J f)) =
      semigroup J (m/(q*n)) f x-gibbsExpectation J f := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : q*n*(m/(q*n)) = m := by field_simp
  have hs := residual_poisson_hasSum hn J hq (m/(q*n)) f x
  rw [he] at hs
  have hh := hs.sub ((Clock.hasSum_poissonMass m).mul_right (gibbsExpectation J f))
  simpa only [one_mul,← mul_sub] using hh.tsum_eq

lemma residual_binomial_test {n : ℕ} (J : Interaction n) {q : ℝ} (hq : q ≠ 0)
    (M : ℕ) (f : Observables n) (x : Spin n) :
    (∑' j, Clock.binomialMass q M j*((residualAttempt J q ^ j) f x-gibbsExpectation J f)) =
      (attemptLM J ^ M) f x-gibbsExpectation J f := by
  have hs := residual_binomial_hasSum J hq M f x
  have hh := hs.sub ((Clock.hasSum_binomialMass q M).mul_right (gibbsExpectation J f))
  simpa only [one_mul,← mul_sub] using hh.tsum_eq

lemma totalVariation_test_bound {n : ℕ} (p r f : Spin n → ℝ)
    (hf : ∀ y, |f y| ≤ 1) :
    |(∑ y, p y*f y)-(∑ y, r y*f y)| ≤ 2*totalVariation p r := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  calc
    _ ≤ ∑ y, |(p y-r y)*f y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y, |p y-r y| := by
      apply Finset.sum_le_sum
      intro y _
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hf y)
    _ = _ := by dsimp [totalVariation]; ring

lemma continuous_test_bound {n : ℕ} (J : Interaction n) (t : ℝ)
    (f : Observables n) (hf : ∀ y, |f y| ≤ 1) (x : Spin n) :
    |semigroup J t f x-gibbsExpectation J f| ≤ 2*worstContinuous J t := by
  rw [← kernel_apply (semigroup J t) f x]
  apply (totalVariation_test_bound (continuousKernel J t x) (gibbs J) f hf).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.le_sup' (fun x => totalVariation (continuousKernel J t x) (gibbs J))
    (Finset.mem_univ x)

lemma totalVariation_has_test {n : ℕ} (p r : Spin n → ℝ) :
    ∃ f : Observables n, (∀ y, |f y| ≤ 1) ∧
      (∑ y, p y*f y)-(∑ y, r y*f y) = 2*totalVariation p r := by
  let f : Observables n := fun y => if 0 ≤ p y-r y then 1 else -1
  refine ⟨f,fun y => ?_,?_⟩
  · dsimp [f]; split_ifs <;> norm_num
  · rw [← Finset.sum_sub_distrib]
    have hf (y : Spin n) : p y*f y-r y*f y = |p y-r y| := by
      dsimp [f]
      split_ifs with h
      · rw [abs_of_nonneg h]; ring
      · rw [abs_of_neg (lt_of_not_ge h)]; ring
    simp_rw [hf]
    dsimp [totalVariation]
    ring

lemma worstDiscrete_has_test {n : ℕ} (J : Interaction n) (M : ℕ) :
    ∃ (x : Spin n) (f : Observables n), (∀ y, |f y| ≤ 1) ∧
      (attemptLM J ^ M) f x-gibbsExpectation J f = 2*worstDiscrete J M := by
  obtain ⟨x,_,hx⟩ := Finset.exists_max_image (Finset.univ : Finset (Spin n))
    (fun x => totalVariation (discreteKernel J M x) (gibbs J)) Finset.univ_nonempty
  obtain ⟨f,hf,hfe⟩ := totalVariation_has_test (discreteKernel J M x) (gibbs J)
  refine ⟨x,f,hf,?_⟩
  have hm : worstDiscrete J M = totalVariation (discreteKernel J M x) (gibbs J) := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun y hy => hx y hy)
    · exact Finset.le_sup' (fun z => totalVariation (discreteKernel J M z) (gibbs J))
        (Finset.mem_univ x)
  rw [hm,← kernel_apply (attemptLM J ^ M) f x]
  exact hfe

lemma semigroup_add_eq_comp {n : ℕ} (J : Interaction n) (s t : ℝ) :
    semigroup J (s+t) = semigroup J s*semigroup J t := by
  let : NormedAlgebra ℚ (Observables n →L[ℝ] Observables n) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  unfold semigroup
  rw [add_smul,NormedSpace.exp_add_of_commute
    (((Commute.refl (generatorCLM J)).smul_left s).smul_right t)]

lemma continuousKernel_add {n : ℕ} (J : Interaction n) (s t : ℝ) (x y : Spin n) :
    continuousKernel J (s+t) x y = ∑ z, continuousKernel J s x z*continuousKernel J t z y := by
  unfold continuousKernel
  rw [semigroup_add_eq_comp,mul_apply_eq_comp]
  exact (kernel_apply (semigroup J s) _ x).symm

lemma worstContinuous_add_le {n : ℕ} (J : Interaction n) (s t : ℝ) (hs : 0 ≤ s) :
    worstContinuous J (s+t) ≤ worstContinuous J t := by
  apply Finset.sup'_le
  intro x _
  change totalVariation (fun y => continuousKernel J (s+t) x y) (gibbs J) ≤ _
  simp_rw [continuousKernel_add]
  apply (totalVariation_mixture_le _ (continuousKernel_nonneg J s hs x)
    (continuousKernel_sum J s x) _ _).trans
  calc
    _ ≤ ∑ z, continuousKernel J s x z*worstContinuous J t := by
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ (continuousKernel_nonneg J s hs x z)
      exact Finset.le_sup' (fun z => totalVariation (continuousKernel J t z) (gibbs J))
        (Finset.mem_univ z)
    _ = _ := by rw [← Finset.sum_mul,continuousKernel_sum,one_mul]

lemma worstContinuous_mono_time {n : ℕ} (J : Interaction n) {s t : ℝ} (h : s ≤ t) :
    worstContinuous J t ≤ worstContinuous J s := by
  simpa only [sub_add_cancel] using worstContinuous_add_le J (t-s) s (sub_nonneg.mpr h)

end SKGapCutoff

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

end

end OAI
