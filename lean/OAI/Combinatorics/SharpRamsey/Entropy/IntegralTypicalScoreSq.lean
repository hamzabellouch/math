import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.HighMoments

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*}
lemma integral_typicalScore_sq_le (rate : ι → ℝ≥0) {R : ℕ} (H : Finset κ)
    (directions : κ → Finset ι) (b : ℝ) (own : κ → Fin R → Bool) :
    (∫ ω, (typicalScore H directions b own ω)^2 ∂scheduleMeasure rate R) ≤
      ∑ h ∈ H, ∑ k ∈ H, |pairMean rate (directions h) (directions k) b|^R := by
  rw [integral_typicalScore_sq]
  apply Finset.sum_le_sum
  intro h _
  apply Finset.sum_le_sum
  intro k _
  rw [← integral_scoreTerm_mul]
  exact (le_abs_self _).trans
    (abs_integral_scoreTerm_mul_le rate (directions h) (directions k) b (own h) (own k))

section TupleCalculation

variable {ν : Type*} [DecidableEq ν]
omit [Fintype ι] in

lemma prod_emptyIndicator (I : Finset ν) (directions : ν → Finset ι) (ω : ι → ℕ) :
    (∏ h ∈ I, emptyIndicator (directions h) ω) =
      emptyIndicator (I.biUnion directions) ω := by
  induction I using Finset.induction_on with
  | empty => simp [emptyIndicator, emptyEvent]
  | @insert h I hh ih =>
    rw [Finset.prod_insert hh, Finset.biUnion_insert, ih, emptyIndicator_mul]
omit [Fintype ι] in

lemma prod_centeredFactor (I : Finset ν) (directions : ν → Finset ι) (b : ℝ)
    (ω : ι → ℕ) :
    (∏ h ∈ I, centeredFactor (directions h) b ω) =
      ∑ J ∈ I.powerset, (-b) ^ (I \ J).card * emptyIndicator (J.biUnion directions) ω := by
  simp only [centeredFactor, sub_eq_add_neg]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro J _
  rw [prod_emptyIndicator, Finset.prod_const]
  ring

lemma integrable_prod_centeredFactor (rate : ι → ℝ≥0) (I : Finset ν)
    (directions : ν → Finset ι) (b : ℝ) :
    Integrable (fun ω => ∏ h ∈ I, centeredFactor (directions h) b ω) (batchMeasure rate) := by
  simp_rw [prod_centeredFactor]
  exact integrable_finsetSum _ (fun J _ =>
    (integrable_emptyIndicator rate _).const_mul _)

noncomputable def tupleMean (rate : ι → ℝ≥0) (I : Finset ν)
    (directions : ν → Finset ι) (b : ℝ) : ℝ :=
  ∑ J ∈ I.powerset, (-b) ^ (I \ J).card * Real.exp (-mass rate (J.biUnion directions))

lemma integral_prod_centeredFactor (rate : ι → ℝ≥0) (I : Finset ν)
    (directions : ν → Finset ι) (b : ℝ) :
    (∫ ω, ∏ h ∈ I, centeredFactor (directions h) b ω ∂batchMeasure rate) =
      tupleMean rate I directions b := by
  simp_rw [prod_centeredFactor]
  rw [integral_finsetSum _ (fun J _ =>
    (integrable_emptyIndicator rate _).const_mul _)]
  simp only [integral_const_mul, integral_emptyIndicator, tupleMean]

omit [Fintype ι] [DecidableEq ι] [DecidableEq ν] in
lemma prod_scoreTerm (I : Finset ν) (directions : ν → Finset ι) (b : ℝ)
    {R : ℕ} (own : ν → Fin R → Bool) (ω : Fin R → ι → ℕ) :
    (∏ h ∈ I, scoreTerm (directions h) b (own h) ω) =
      ∏ r, if ∀ h ∈ I, own h r then ∏ h ∈ I, centeredFactor (directions h) b (ω r) else 0 := by
  simp only [scoreTerm]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro r _
  exact Finset.prod_ite_zero

lemma integrable_prod_scoreTerm (rate : ι → ℝ≥0) (I : Finset ν)
    (directions : ν → Finset ι) (b : ℝ) {R : ℕ} (own : ν → Fin R → Bool) :
    Integrable (fun ω => ∏ h ∈ I, scoreTerm (directions h) b (own h) ω)
      (scheduleMeasure rate R) := by
  simp_rw [prod_scoreTerm]
  apply Integrable.fintype_prod (f := fun r ω => if ∀ h ∈ I, own h r then
    ∏ h ∈ I, centeredFactor (directions h) b ω else 0)
  intro r
  split_ifs
  · exact integrable_prod_centeredFactor rate I directions b
  · exact integrable_const 0

lemma integral_prod_scoreTerm (rate : ι → ℝ≥0) (I : Finset ν)
    (directions : ν → Finset ι) (b : ℝ) {R : ℕ} (own : ν → Fin R → Bool) :
    (∫ ω, ∏ h ∈ I, scoreTerm (directions h) b (own h) ω ∂scheduleMeasure rate R) =
      ∏ r, if ∀ h ∈ I, own h r then tupleMean rate I directions b else 0 := by
  simp_rw [prod_scoreTerm]
  unfold scheduleMeasure
  rw [integral_fintype_prod_eq_prod (f := fun r ω => if ∀ h ∈ I, own h r then
    ∏ h ∈ I, centeredFactor (directions h) b ω else 0)]
  apply Finset.prod_congr rfl
  intro r _
  split_ifs <;> simp [integral_prod_centeredFactor]

lemma abs_integral_prod_scoreTerm_le (rate : ι → ℝ≥0) (I : Finset ν)
    (directions : ν → Finset ι) (b : ℝ) {R : ℕ} (own : ν → Fin R → Bool) :
    |∫ ω, ∏ h ∈ I, scoreTerm (directions h) b (own h) ω ∂scheduleMeasure rate R| ≤
      |tupleMean rate I directions b| ^ R := by
  rw [integral_prod_scoreTerm, Finset.abs_prod]
  calc
    _ ≤ ∏ _ : Fin R, |tupleMean rate I directions b| := by
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro r _
      split_ifs <;> simp
    _ = _ := by simp

end TupleCalculation

lemma integral_typicalScore_pow (rate : ι → ℝ≥0) {R : ℕ} (H : Finset κ)
    (directions : κ → Finset ι) (b : ℝ) (own : κ → Fin R → Bool) (p : ℕ) :
    (∫ ω, (typicalScore H directions b own ω)^p ∂scheduleMeasure rate R) =
      ∑ hs ∈ Fintype.piFinset (fun _ : Fin p => H),
        ∏ r, if ∀ i : Fin p, own (hs i) r then
          tupleMean rate Finset.univ (fun i => directions (hs i)) b else 0 := by
  classical
  simp only [typicalScore]
  simp_rw [Finset.sum_pow']
  rw [integral_finsetSum _ (fun hs _ =>
    integrable_prod_scoreTerm rate Finset.univ (fun i => directions (hs i)) b (fun i => own (hs i)))]
  apply Finset.sum_congr rfl
  intro hs _
  simpa using integral_prod_scoreTerm rate Finset.univ (fun i => directions (hs i)) b (fun i => own (hs i))

noncomputable def maskedFactor (s : Finset ι) (b : ℝ) (own touched : Bool)
    (ω : ι → ℕ) : ℝ :=
  if own then (if touched then -b else centeredFactor s b ω) else 0

noncomputable def maskedTerm {R : ℕ} (s : Finset ι) (b : ℝ)
    (own touched : Fin R → Bool) (ω : Fin R → ι → ℕ) : ℝ :=
  ∏ r, maskedFactor s b (own r) (touched r) (ω r)
omit [Fintype ι] [DecidableEq ι] in

lemma abs_maskedFactor_le_one (s : Finset ι) {b : ℝ} (hb : b ∈ Set.Icc 0 1)
    (own touched : Bool) (ω : ι → ℕ) : |maskedFactor s b own touched ω| ≤ 1 := by
  cases own <;> cases touched <;> simp [maskedFactor, abs_centeredFactor_le_one s b hb ω,
    abs_of_nonneg hb.1, hb.2]
omit [Fintype ι] [DecidableEq ι] in

lemma abs_maskedTerm_le_one {R : ℕ} (s : Finset ι) {b : ℝ} (hb : b ∈ Set.Icc 0 1)
    (own touched : Fin R → Bool) (ω : Fin R → ι → ℕ) :
    |maskedTerm s b own touched ω| ≤ 1 := by
  rw [maskedTerm, Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => abs_maskedFactor_le_one s hb _ _ _)

omit [DecidableEq ι] in
lemma integrable_schedule_of_abs_le (rate : ι → ℝ≥0) {R : ℕ}
    (f : (Fin R → ι → ℕ) → ℝ) (C : ℝ) (h : ∀ ω, |f ω| ≤ C) :
    Integrable f (scheduleMeasure rate R) := by
  apply Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable C
  exact Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using h ω)
omit [DecidableEq ι] in

lemma integrable_maskedFactor (rate : ι → ℝ≥0) (s : Finset ι) (b : ℝ)
    (own touched : Bool) : Integrable (maskedFactor s b own touched) (batchMeasure rate) := by
  cases own <;> cases touched
  · exact integrable_const 0
  · exact integrable_const 0
  · exact integrable_centeredFactor rate s b
  · exact integrable_const (-b)
omit [DecidableEq ι] in

lemma integral_maskedFactor (rate : ι → ℝ≥0) (s : Finset ι) (b : ℝ)
    (own touched : Bool) :
    (∫ ω, maskedFactor s b own touched ω ∂batchMeasure rate) =
      if own then (if touched then -b else Real.exp (-mass rate s) - b) else 0 := by
  cases own <;> cases touched <;> simp [maskedFactor, integral_centeredFactor]
omit [DecidableEq ι] in

lemma integral_maskedTerm (rate : ι → ℝ≥0) {R : ℕ} (s : Finset ι) (b : ℝ)
    (own touched : Fin R → Bool) :
    (∫ ω, maskedTerm s b own touched ω ∂scheduleMeasure rate R) =
      ∏ r, if own r then (if touched r then -b else Real.exp (-mass rate s) - b) else 0 := by
  unfold maskedTerm scheduleMeasure
  rw [integral_fintype_prod_eq_prod]
  simp only [integral_maskedFactor]
omit [DecidableEq ι] in

lemma integral_abs_maskedFactor_exp_le (rate : ι → ℝ≥0) (s : Finset ι)
    (own touched : Bool) {L lam base c : ℝ} (hL : 0 ≤ L)
    (hmass : mass rate s = L * lam) (hlam : c ≤ lam) (hbase : c ≤ base) :
    (∫ ω, |maskedFactor s (Real.exp (-L * base)) own touched ω| ∂batchMeasure rate) ≤
      2 * Real.exp (-L * c) := by
  have he := Real.exp_pos (-L * c)
  have hb : Real.exp (-L * base) ≤ Real.exp (-L * c) :=
    Real.exp_le_exp.mpr (by nlinarith)
  cases own <;> cases touched <;> simp only [maskedFactor, Bool.false_eq_true, ↓reduceIte]
  · simp only [abs_zero, integral_zero]; positivity
  · simp only [abs_zero, integral_zero]; positivity
  · exact integral_abs_centeredFactor_exp_le rate s hL hmass hlam hbase
  · simp only [abs_neg, abs_of_pos (Real.exp_pos _), integral_const, probReal_univ,
      smul_eq_mul, one_mul]
    linarith
omit [DecidableEq ι] in

lemma integral_abs_maskedTerm_exp_le (rate : ι → ℝ≥0) {R : ℕ} (s : Finset ι)
    (own touched : Fin R → Bool) {L lam base c : ℝ} (hL : 0 ≤ L)
    (hmass : mass rate s = L * lam) (hlam : c ≤ lam) (hbase : c ≤ base) :
    (∫ ω, |maskedTerm s (Real.exp (-L * base)) own touched ω| ∂scheduleMeasure rate R) ≤
      (2 * Real.exp (-L * c)) ^ R := by
  simp only [maskedTerm, Finset.abs_prod, scheduleMeasure]
  rw [integral_fintype_prod_eq_prod (f := fun r ω =>
    |maskedFactor s (Real.exp (-L * base)) (own r) (touched r) ω|)]
  calc
    _ ≤ ∏ _ : Fin R, 2 * Real.exp (-L * c) := by
      apply Finset.prod_le_prod₀ (fun _ _ => integral_nonneg (fun _ => abs_nonneg _))
      intro r _
      exact integral_abs_maskedFactor_exp_le rate s (own r) (touched r) hL hmass hlam hbase
    _ = _ := by simp
omit [Fintype ι] [DecidableEq ι] in

lemma abs_prod_maskedTerm_le {ν : Type*} [DecidableEq ν] {R : ℕ}
    (I : Finset ν) (directions : ν → Finset ι) {b : ℝ} (hb : b ∈ Set.Icc 0 1)
    (own touched : ν → Fin R → Bool) {h : ν} (hh : h ∈ I) (ω : Fin R → ι → ℕ) :
    |∏ i ∈ I, maskedTerm (directions i) b (own i) (touched i) ω| ≤
      |maskedTerm (directions h) b (own h) (touched h) ω| := by
  rw [Finset.abs_prod, ← Finset.prod_erase_mul _ _ hh]
  have hp : (∏ i ∈ I.erase h, |maskedTerm (directions i) b (own i) (touched i) ω|) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => abs_maskedTerm_le_one _ hb _ _ _)
  simpa using mul_le_mul_of_nonneg_right hp
    (abs_nonneg (maskedTerm (directions h) b (own h) (touched h) ω))

omit [DecidableEq ι] in

lemma integral_abs_component_indicator_le (rate : ι → ℝ≥0)
    {ν : Type*} [DecidableEq ν] {R : ℕ} (I : Finset ν) (directions : ν → Finset ι)
    (own touched : ν → Fin R → Bool) (E : Set (Fin R → ι → ℕ))
    {h : ν} (hh : h ∈ I) {L lam base c : ℝ} (hL : 0 ≤ L) (hc : 0 ≤ c)
    (hmass : mass rate (directions h) = L * lam) (hlam : c ≤ lam) (hbase : c ≤ base) :
    (∫ ω, |E.indicator (fun ω => ∏ i ∈ I,
      maskedTerm (directions i) (Real.exp (-L * base)) (own i) (touched i) ω) ω|
        ∂scheduleMeasure rate R) ≤ (2 * Real.exp (-L * c)) ^ R := by
  have hb : Real.exp (-L * base) ∈ Set.Icc 0 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by nlinarith)⟩
  have hpoint : ∀ ω, |E.indicator (fun ω => ∏ i ∈ I,
      maskedTerm (directions i) (Real.exp (-L * base)) (own i) (touched i) ω) ω| ≤
      |maskedTerm (directions h) (Real.exp (-L * base)) (own h) (touched h) ω| := by
    intro ω
    by_cases he : ω ∈ E
    · simpa only [Set.indicator_of_mem he] using abs_prod_maskedTerm_le I directions hb own touched hh ω
    · simp only [Set.indicator_of_notMem he, abs_zero]; exact abs_nonneg _
  calc
    _ ≤ ∫ ω, |maskedTerm (directions h) (Real.exp (-L * base)) (own h) (touched h) ω|
        ∂scheduleMeasure rate R := by
      apply integral_mono
      · apply integrable_schedule_of_abs_le rate _ 1
        intro ω
        rw [abs_abs]
        exact (hpoint ω).trans (abs_maskedTerm_le_one _ hb _ _ _)
      · exact (integrable_schedule_of_abs_le rate _ 1 (abs_maskedTerm_le_one _ hb _ _)).abs
      · exact hpoint
    _ ≤ _ := integral_abs_maskedTerm_exp_le rate _ _ _ hL hmass hlam hbase

def untouchedBatches {R : ℕ} (touched : Fin R → Bool) : Finset (Fin R) :=
  Finset.univ.filter (fun r => touched r = false)

omit [DecidableEq ι] in

lemma abs_integral_maskedTerm_le_untouched (rate : ι → ℝ≥0) {R : ℕ}
    (s : Finset ι) (own touched : Fin R → Bool) {L base c delta alpha : ℝ}
    (hL : 1 ≤ L) (hmass : mass rate s = L * (base + delta - alpha))
    (hinternal : c ≤ base + delta - alpha) (hbase : c ≤ base) (ha : 0 ≤ alpha) :
    |∫ ω, maskedTerm s (Real.exp (-L * base)) own touched ω ∂scheduleMeasure rate R| ≤
      (L * Real.exp (-L * c)) ^ R * (|delta| + alpha) ^ (untouchedBatches touched).card := by
  have hL0 : 0 ≤ L := by linarith
  have he := (Real.exp_pos (-L * c)).le
  have hd : 0 ≤ |delta| + alpha := add_nonneg (abs_nonneg _) ha
  have hu := abs_integral_centeredFactor_le rate s hL0 hmass hinternal hbase
  rw [integral_centeredFactor] at hu
  have hdif : |base + delta - alpha - base| ≤ |delta| + alpha := by
    calc
      |base + delta - alpha - base| = |delta - alpha| := by congr 1; ring
      _ ≤ |delta| + |alpha| := abs_sub _ _
      _ = _ := by rw [abs_of_nonneg ha]
  have hu' := hu.trans (mul_le_mul_of_nonneg_left hdif (mul_nonneg hL0 he))
  have hb : Real.exp (-L * base) ≤ L * Real.exp (-L * c) := by
    have h₁ : Real.exp (-L * base) ≤ Real.exp (-L * c) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h₂ := mul_le_mul_of_nonneg_right hL he
    nlinarith
  rw [integral_maskedTerm, Finset.abs_prod]
  calc
    _ ≤ ∏ r, (L * Real.exp (-L * c)) * (if touched r then 1 else |delta| + alpha) := by
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro r _
      cases ho : own r <;> cases ht : touched r <;>
        simp only [Bool.false_eq_true, ↓reduceIte, abs_neg, abs_zero, mul_one]
      · exact mul_nonneg (mul_nonneg hL0 he) hd
      · exact mul_nonneg hL0 he
      · exact hu'
      · simpa only [abs_of_pos (Real.exp_pos _)] using hb
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp [Finset.prod_ite, untouchedBatches]
omit [DecidableEq ι] in

lemma abs_integral_maskedTerm_le_designations (rate : ι → ℝ≥0) {R : ℕ}
    (s : Finset ι) (own touched : Fin R → Bool) {L base c delta alpha : ℝ}
    (hL : 1 ≤ L) (hmass : mass rate s = L * (base + delta - alpha))
    (hinternal : c ≤ base + delta - alpha) (hbase : c ≤ base)
    (ha : 0 ≤ alpha) (hd : |delta| + alpha ≤ 1) {N K : ℕ}
    (hN : N ≤ (untouchedBatches touched).card) (hK : K ≤ N) :
    |∫ ω, maskedTerm s (Real.exp (-L * base)) own touched ω ∂scheduleMeasure rate R| ≤
      (2 * L * Real.exp (-L * c)) ^ R * (|delta| ^ N + alpha ^ K) := by
  have hNR : N ≤ R := hN.trans (by simpa using Finset.card_le_univ (untouchedBatches touched))
  have hKpow : alpha ^ N ≤ alpha ^ K :=
    pow_le_pow_of_le_one ha (by linarith [abs_nonneg delta]) hK
  have h2pow : (2 : ℝ) ^ (N - 1) ≤ 2 ^ R :=
    pow_le_pow_right₀ (by norm_num) ((Nat.sub_le N 1).trans hNR)
  have hsplit : (|delta| + alpha) ^ (untouchedBatches touched).card ≤
      2 ^ R * (|delta| ^ N + alpha ^ K) := calc
    _ ≤ (|delta| + alpha) ^ N := pow_le_pow_of_le_one (by positivity) hd hN
    _ ≤ 2 ^ (N - 1) * (|delta| ^ N + alpha ^ N) := add_pow_le (abs_nonneg _) ha N
    _ ≤ _ := mul_le_mul h2pow (add_le_add le_rfl hKpow) (by positivity) (by positivity)
  calc
    _ ≤ (L * Real.exp (-L * c)) ^ R * (|delta| + alpha) ^ (untouchedBatches touched).card :=
      abs_integral_maskedTerm_le_untouched rate s own touched hL hmass hinternal hbase ha
    _ ≤ (L * Real.exp (-L * c)) ^ R * (2 ^ R * (|delta| ^ N + alpha ^ K)) :=
      mul_le_mul_of_nonneg_left hsplit (by positivity)
    _ = _ := by rw [← mul_assoc, ← mul_pow]; congr 2; ring

lemma two_mul_le_exp_small {L : ℝ} (hL : 10000 ≤ L) :
    2 * L ≤ Real.exp ((3 / 50 : ℝ) * L) := by
  have hL0 : 0 ≤ L := by linarith
  have he := Real.quadratic_le_exp_of_nonneg (show 0 ≤ (3 / 50 : ℝ) * L by positivity)
  have hs : 10000 * L ≤ L ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hL) hL0]
  nlinarith

lemma two_mul_score_attenuation {L : ℝ} (hL : 10000 ≤ L) (R : ℕ) :
    (2 * L * Real.exp (-(37 / 50 : ℝ) * L)) ^ R ≤
      Real.exp (-(17 / 25 : ℝ) * (L * R)) := by
  have h := mul_le_mul_of_nonneg_right (two_mul_le_exp_small hL)
    (Real.exp_pos (-(37 / 50 : ℝ) * L)).le
  rw [← Real.exp_add] at h
  have heq : (3 / 50 : ℝ) * L + -(37 / 50 : ℝ) * L = -(17 / 25 : ℝ) * L := by ring
  rw [heq] at h
  have hp := pow_le_pow_left₀ (show 0 ≤ 2 * L * Real.exp (-(37 / 50 : ℝ) * L) by
    have : 0 ≤ L := by linarith
    positivity) h R
  rw [← Real.exp_nat_mul] at hp
  convert hp using 1
  congr 1
  ring

omit [DecidableEq ι] in

lemma simple_singleton_attenuation (rate : ι → ℝ≥0) {R : ℕ}
    (s : Finset ι) (own touched : Fin R → Bool) {L base delta alpha : ℝ}
    (hL : 10000 ≤ L) (hmass : mass rate s = L * (base + delta - alpha))
    (hinternal : (37 / 50 : ℝ) ≤ base + delta - alpha) (hbase : (37 / 50 : ℝ) ≤ base)
    (ha : 0 ≤ alpha) (hd : |delta| + alpha ≤ 1) {N K : ℕ}
    (hN : N ≤ (untouchedBatches touched).card) (hK : K ≤ N) :
    |∫ ω, maskedTerm s (Real.exp (-L * base)) own touched ω ∂scheduleMeasure rate R| ≤
      Real.exp (-(17 / 25 : ℝ) * (L * R)) * (|delta| ^ N + alpha ^ K) := by
  have h := abs_integral_maskedTerm_le_designations rate s own touched
    (show 1 ≤ L by linarith) hmass hinternal hbase ha hd hN hK
  apply h.trans
  simpa only [neg_mul, mul_comm L (37 / 50 : ℝ)] using
    mul_le_mul_of_nonneg_right (two_mul_score_attenuation hL R)
    (show 0 ≤ |delta| ^ N + alpha ^ K by positivity)

noncomputable def hitIndicator (i : ι) (ω : ι → ℕ) : ℝ :=
  1 - emptyIndicator {i} ω

omit [Fintype ι] [DecidableEq ι] in
lemma hitIndicator_eq (i : ι) (ω : ι → ℕ) :
    hitIndicator i ω = if ω i = 0 then 0 else 1 := by
  simp only [hitIndicator, emptyIndicator, emptyEvent
    ]
  by_cases h : ω i = 0 <;> simp [h]
omit [Fintype ι] [DecidableEq ι] in

lemma hitIndicator_nonneg (i : ι) (ω : ι → ℕ) : 0 ≤ hitIndicator i ω := by
  rw [hitIndicator_eq]; split <;> norm_num
omit [Fintype ι] [DecidableEq ι] in

lemma hitIndicator_le_one (i : ι) (ω : ι → ℕ) : hitIndicator i ω ≤ 1 := by
  rw [hitIndicator_eq]; split <;> norm_num
omit [DecidableEq ι] in

lemma integrable_hitIndicator (rate : ι → ℝ≥0) (i : ι) :
    Integrable (hitIndicator i) (batchMeasure rate) :=
  (integrable_const 1).sub (integrable_emptyIndicator rate {i})
omit [DecidableEq ι] in

lemma integral_hitIndicator (rate : ι → ℝ≥0) (i : ι) :
    (∫ ω, hitIndicator i ω ∂batchMeasure rate) = 1 - Real.exp (-(rate i : ℝ)) := by
  unfold hitIndicator
  rw [integral_sub (integrable_const 1) (integrable_emptyIndicator rate {i}),
    integral_emptyIndicator]
  simp [mass]
omit [Fintype ι] [DecidableEq ι] in

lemma maskedFactor_mul_hit (s : Finset ι) (i : ι) (hi : i ∈ s) (b : ℝ)
    (own touched : Bool) (ω : ι → ℕ) :
    maskedFactor s b own touched ω * hitIndicator i ω =
      (if own then -b else 0) * hitIndicator i ω := by
  rw [hitIndicator_eq]
  by_cases hz : ω i = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte, mul_one]
    have hh : ω ∉ emptyEvent s := by
      intro h
      exact hz (h i hi)
    cases own <;> cases touched <;> simp [maskedFactor, centeredFactor_of_hit s b ω hi hz]
omit [DecidableEq ι] in

lemma integral_abs_maskedFactor_hit_le (rate : ι → ℝ≥0)
    (s : Finset ι) (i : ι) (hi : i ∈ s) (own touched : Bool)
    {L base c : ℝ} (hL : 0 ≤ L) (hbase : c ≤ base) :
    (∫ ω, |maskedFactor s (Real.exp (-L * base)) own touched ω| * hitIndicator i ω
      ∂batchMeasure rate) ≤ Real.exp (-L * c) * (rate i : ℝ) := by
  have heq : (fun ω => |maskedFactor s (Real.exp (-L * base)) own touched ω| * hitIndicator i ω) =
      fun ω => (if own then Real.exp (-L * base) else 0) * hitIndicator i ω := by
    funext ω
    rw [← abs_of_nonneg (hitIndicator_nonneg i ω), ← abs_mul, maskedFactor_mul_hit s i hi]
    cases own <;>
      simp [abs_mul, abs_of_nonneg (hitIndicator_nonneg i ω), abs_of_pos (Real.exp_pos _)]
  rw [heq, integral_const_mul, integral_hitIndicator]
  have hnonneg : 0 ≤ 1 - Real.exp (-(rate i : ℝ)) := by
    have : Real.exp (-(rate i : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (rate i).coe_nonneg)
    linarith
  have hb : Real.exp (-L * base) ≤ Real.exp (-L * c) := Real.exp_le_exp.mpr (by nlinarith)
  cases own
  · simp only [Bool.false_eq_true, ↓reduceIte, zero_mul]; positivity
  · simp only [↓reduceIte]
    exact mul_le_mul hb (one_sub_exp_neg_le (rate i : ℝ)) hnonneg (Real.exp_pos _).le

noncomputable def forcedHits {R : ℕ} (i : ι) (T : Finset (Fin R))
    (ω : Fin R → ι → ℕ) : ℝ := ∏ r ∈ T, hitIndicator i (ω r)
omit [Fintype ι] [DecidableEq ι] in

lemma forcedHits_nonneg {R : ℕ} (i : ι) (T : Finset (Fin R)) (ω : Fin R → ι → ℕ) :
    0 ≤ forcedHits i T ω := Finset.prod_nonneg (fun _ _ => hitIndicator_nonneg _ _)

end SharpRamseyFive.PoissonScore
end

end OAI
