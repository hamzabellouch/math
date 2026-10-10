import Mathlib

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.PoissonScore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def batchMeasure (rate : ι → ℝ≥0) : Measure (ι → ℕ) :=
  Measure.pi (fun i => poissonMeasure (rate i))

instance flat_HighMomentRecovered_1 (rate : ι → ℝ≥0) : IsProbabilityMeasure (batchMeasure rate) := by
  unfold batchMeasure
  infer_instance

def emptyEvent (s : Finset ι) : Set (ι → ℕ) :=
  (s : Set ι).pi (fun _ => {0})

noncomputable def emptyIndicator (s : Finset ι) (ω : ι → ℕ) : ℝ :=
  (emptyEvent s).indicator (fun _ => 1) ω

noncomputable def mass (rate : ι → ℝ≥0) (s : Finset ι) : ℝ :=
  ∑ i ∈ s, (rate i : ℝ)

omit [Fintype ι] [DecidableEq ι] in
lemma measurableSet_emptyEvent (s : Finset ι) : MeasurableSet (emptyEvent s) := by
  exact MeasurableSet.pi (s.finite_toSet.countable) (fun _ _ => measurableSet_singleton 0)

omit [DecidableEq ι] in
lemma measure_emptyEvent (rate : ι → ℝ≥0) (s : Finset ι) :
    batchMeasure rate (emptyEvent s) = ENNReal.ofReal (Real.exp (-mass rate s)) := by
  rw [batchMeasure, emptyEvent, Measure.pi_pi_finset]
  simp_rw [poissonMeasure_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    mul_one, div_one]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),
    ← Real.exp_sum, Finset.sum_neg_distrib]
  rfl
omit [DecidableEq ι] in

lemma integral_emptyIndicator (rate : ι → ℝ≥0) (s : Finset ι) :
    ∫ ω, emptyIndicator s ω ∂batchMeasure rate = Real.exp (-mass rate s) := by
  simp only [emptyIndicator]
  rw [integral_indicator_const _ (measurableSet_emptyEvent s),
    Measure.real, measure_emptyEvent, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  simp
omit [DecidableEq ι] in

lemma integrable_emptyIndicator (rate : ι → ℝ≥0) (s : Finset ι) :
    Integrable (emptyIndicator s) (batchMeasure rate) :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_emptyEvent s)

omit [Fintype ι] in
lemma emptyIndicator_mul (s t : Finset ι) (ω : ι → ℕ) :
    emptyIndicator s ω * emptyIndicator t ω = emptyIndicator (s ∪ t) ω := by
  have hu : emptyEvent (s ∪ t) = emptyEvent s ∩ emptyEvent t := by
    ext x
    simp [emptyEvent, Set.mem_pi, or_imp, forall_and]
  rw [emptyIndicator, emptyIndicator, emptyIndicator, hu]
  by_cases hs : ω ∈ emptyEvent s <;> by_cases ht : ω ∈ emptyEvent t <;>
    simp [hs, ht]

omit [Fintype ι] in
lemma mass_union_inter (rate : ι → ℝ≥0) (s t : Finset ι) :
    mass rate (s ∪ t) + mass rate (s ∩ t) = mass rate s + mass rate t := by
  exact Finset.sum_union_inter

noncomputable def centeredFactor (s : Finset ι) (b : ℝ) (ω : ι → ℕ) : ℝ :=
  emptyIndicator s ω - b
omit [DecidableEq ι] in

lemma integrable_centeredFactor (rate : ι → ℝ≥0) (s : Finset ι) (b : ℝ) :
    Integrable (centeredFactor s b) (batchMeasure rate) :=
  (integrable_emptyIndicator rate s).sub (integrable_const b)
omit [DecidableEq ι] in

lemma integral_centeredFactor (rate : ι → ℝ≥0) (s : Finset ι) (b : ℝ) :
    ∫ ω, centeredFactor s b ω ∂batchMeasure rate = Real.exp (-mass rate s) - b := by
  simp only [centeredFactor]
  rw [integral_sub (integrable_emptyIndicator rate s)
    (integrable_const b), integral_emptyIndicator]
  simp

lemma integral_centeredFactor_mul (rate : ι → ℝ≥0) (s t : Finset ι) (b : ℝ) :
    (∫ ω, centeredFactor s b ω * centeredFactor t b ω ∂batchMeasure rate) =
      (Real.exp (-mass rate s) - b) * (Real.exp (-mass rate t) - b) +
      Real.exp (-(mass rate s + mass rate t)) *
        (Real.exp (mass rate (s ∩ t)) - 1) := by
  have he : (fun ω => centeredFactor s b ω * centeredFactor t b ω) =
      fun ω => emptyIndicator (s ∪ t) ω - b * emptyIndicator s ω -
        b * emptyIndicator t ω + b ^ 2 := by
    funext ω
    rw [centeredFactor, centeredFactor]
    have := emptyIndicator_mul s t ω
    nlinarith [this]
  rw [he]
  have hs := integrable_emptyIndicator rate s
  have ht := integrable_emptyIndicator rate t
  have hu := integrable_emptyIndicator rate (s ∪ t)
  have h1 := integral_sub hu (hs.const_mul b)
  have h2 := integral_sub (hu.sub (hs.const_mul b)) (ht.const_mul b)
  have h3 := integral_add ((hu.sub (hs.const_mul b)).sub (ht.const_mul b))
    (integrable_const (b ^ 2))
  simp only [Pi.sub_apply] at h1 h2 h3
  rw [h3, h2, h1]
  simp only [integral_const_mul, integral_emptyIndicator, integral_const,
    probReal_univ, one_smul]
  have hmass := mass_union_inter rate s t
  have hu : Real.exp (-mass rate (s ∪ t)) =
      Real.exp (-(mass rate s + mass rate t)) * Real.exp (mass rate (s ∩ t)) := by
    rw [← Real.exp_add]
    congr 1
    linarith
  have hp : Real.exp (-mass rate s) * Real.exp (-mass rate t) =
      Real.exp (-(mass rate s + mass rate t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hu]
  nlinarith [hp]

omit [Fintype ι] [DecidableEq ι] in
lemma emptyIndicator_nonneg (s : Finset ι) (ω : ι → ℕ) : 0 ≤ emptyIndicator s ω := by
  unfold emptyIndicator
  apply Set.indicator_nonneg
  intro _ _
  norm_num

omit [Fintype ι] [DecidableEq ι] in
lemma abs_centeredFactor_le_one (s : Finset ι) (b : ℝ) (hb : b ∈ Set.Icc 0 1)
    (ω : ι → ℕ) : |centeredFactor s b ω| ≤ 1 := by
  unfold centeredFactor emptyIndicator
  by_cases h : ω ∈ emptyEvent s <;> simp [h, abs_le] <;> constructor <;> linarith [hb.1, hb.2]

omit [Fintype ι] [DecidableEq ι] in
lemma centeredFactor_of_hit (s : Finset ι) (b : ℝ) (ω : ι → ℕ)
    {i : ι} (hi : i ∈ s) (hhit : ω i ≠ 0) : centeredFactor s b ω = -b := by
  have h : ω ∉ emptyEvent s := by
    intro he
    exact hhit (he i hi)
  simp [centeredFactor, emptyIndicator, h]
omit [DecidableEq ι] in

lemma integral_abs_centeredFactor_le (rate : ι → ℝ≥0) (s : Finset ι) (b : ℝ) :
    (∫ ω, |centeredFactor s b ω| ∂batchMeasure rate) ≤ Real.exp (-mass rate s) + |b| := by
  calc
    _ ≤ ∫ ω, emptyIndicator s ω + |b| ∂batchMeasure rate := by
      apply integral_mono (integrable_centeredFactor rate s b).abs
        ((integrable_emptyIndicator rate s).add (integrable_const |b|))
      intro ω
      dsimp [centeredFactor]
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg (emptyIndicator_nonneg s ω)])
    _ = _ := by
      rw [integral_add (integrable_emptyIndicator rate s) (integrable_const |b|),
        integral_emptyIndicator]
      simp

lemma abs_exp_neg_sub_exp_neg_le {a b c : ℝ} (ha : c ≤ a) (hb : c ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ Real.exp (-c) * |a - b| := by
  have ordered : ∀ {a b : ℝ}, c ≤ a → a ≤ b →
      Real.exp (-a) - Real.exp (-b) ≤ Real.exp (-c) * (b - a) := by
    intro a b hca hab
    have he := Real.add_one_le_exp (a - b)
    have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (-a)).le
    have hprod : Real.exp (-a) * Real.exp (a - b) = Real.exp (-b) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hprod] at hm
    have hec : Real.exp (-a) ≤ Real.exp (-c) := Real.exp_le_exp.mpr (neg_le_neg hca)
    have hd := mul_le_mul_of_nonneg_right hec (sub_nonneg.mpr hab)
    nlinarith
  rcases le_total a b with hab | hba
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (neg_le_neg hab))),
      abs_of_nonpos (sub_nonpos.mpr hab)]
    simpa only [neg_sub] using ordered ha hab
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr (neg_le_neg hba))),
      abs_of_nonneg (sub_nonneg.mpr hba)]
    simpa only [neg_sub] using ordered hb hba

omit [DecidableEq ι] in

lemma abs_integral_centeredFactor_le (rate : ι → ℝ≥0) (s : Finset ι)
    {L lam base c : ℝ} (hL : 0 ≤ L) (hmass : mass rate s = L * lam)
    (hlam : c ≤ lam) (hbase : c ≤ base) :
    |∫ ω, centeredFactor s (Real.exp (-L * base)) ω ∂batchMeasure rate| ≤
      L * Real.exp (-L * c) * |lam - base| := by
  rw [integral_centeredFactor, hmass]
  have he := abs_exp_neg_sub_exp_neg_le
    (mul_le_mul_of_nonneg_left hlam hL) (mul_le_mul_of_nonneg_left hbase hL)
  simpa only [neg_mul, mul_neg, ← mul_sub, abs_mul, abs_of_nonneg hL, mul_comm,
    mul_left_comm, mul_assoc] using he

omit [DecidableEq ι] in

lemma integral_abs_centeredFactor_exp_le (rate : ι → ℝ≥0) (s : Finset ι)
    {L lam base c : ℝ} (hL : 0 ≤ L) (hmass : mass rate s = L * lam)
    (hlam : c ≤ lam) (hbase : c ≤ base) :
    (∫ ω, |centeredFactor s (Real.exp (-L * base)) ω| ∂batchMeasure rate) ≤
      2 * Real.exp (-L * c) := by
  have h1 := integral_abs_centeredFactor_le rate s (Real.exp (-L * base))
  rw [hmass, abs_of_pos (Real.exp_pos _)] at h1
  have h2 : Real.exp (-(L * lam)) ≤ Real.exp (-L * c) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h3 : Real.exp (-L * base) ≤ Real.exp (-L * c) :=
    Real.exp_le_exp.mpr (by nlinarith)
  linarith

lemma integrable_centeredFactor_mul (rate : ι → ℝ≥0) (s t : Finset ι) (b : ℝ) :
    Integrable (fun ω => centeredFactor s b ω * centeredFactor t b ω) (batchMeasure rate) := by
  have he : (fun ω => centeredFactor s b ω * centeredFactor t b ω) =
      fun ω => emptyIndicator (s ∪ t) ω - b * emptyIndicator s ω -
        b * emptyIndicator t ω + b ^ 2 := by
    funext ω
    rw [centeredFactor, centeredFactor]
    nlinarith [emptyIndicator_mul s t ω]
  rw [he]
  exact (((integrable_emptyIndicator rate (s ∪ t)).sub
    ((integrable_emptyIndicator rate s).const_mul b)).sub
    ((integrable_emptyIndicator rate t).const_mul b)).add (integrable_const (b^2))

omit [Fintype ι] [DecidableEq ι] in
lemma mass_nonneg (rate : ι → ℝ≥0) (s : Finset ι) : 0 ≤ mass rate s := by
  exact Finset.sum_nonneg (fun i _ => (rate i).coe_nonneg)

omit [Fintype ι] [DecidableEq ι] in
lemma mass_mono (rate : ι → ℝ≥0) {s t : Finset ι} (hst : s ⊆ t) :
    mass rate s ≤ mass rate t := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun i _ _ => (rate i).coe_nonneg)

lemma one_sub_exp_neg_le (a : ℝ) : 1 - Real.exp (-a) ≤ a := by
  have := Real.add_one_le_exp (-a)
  linarith

omit [Fintype ι] in

lemma covariance_le (rate : ι → ℝ≥0) (s t : Finset ι) :
    Real.exp (-(mass rate s + mass rate t)) *
      (Real.exp (mass rate (s ∩ t)) - 1) ≤
    mass rate (s ∩ t) * Real.exp (-mass rate (s ∪ t)) := by
  have hu := mass_union_inter rate s t
  have he : Real.exp (-(mass rate s + mass rate t)) =
      Real.exp (-mass rate (s ∪ t)) * Real.exp (-mass rate (s ∩ t)) := by
    rw [← Real.exp_add]
    congr 1
    linarith
  rw [he]
  have hh : Real.exp (-mass rate (s ∩ t)) * Real.exp (mass rate (s ∩ t)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hb := mul_le_mul_of_nonneg_left (one_sub_exp_neg_le (mass rate (s ∩ t)))
    (Real.exp_pos (-mass rate (s ∪ t))).le
  calc
    _ = Real.exp (-mass rate (s ∪ t)) * (1 - Real.exp (-mass rate (s ∩ t))) := by
      rw [mul_assoc, mul_sub, hh, mul_one]
    _ ≤ _ := by simpa only [mul_comm] using hb
omit [Fintype ι] in

lemma covariance_nonneg (rate : ι → ℝ≥0) (s t : Finset ι) :
    0 ≤ Real.exp (-(mass rate s + mass rate t)) *
      (Real.exp (mass rate (s ∩ t)) - 1) := by
  apply mul_nonneg (Real.exp_pos _).le
  exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mass_nonneg rate _))

lemma abs_integral_centeredFactor_mul_le_mass (rate : ι → ℝ≥0)
    (s t : Finset ι) (b : ℝ) :
    |∫ ω, centeredFactor s b ω * centeredFactor t b ω ∂batchMeasure rate| ≤
      |Real.exp (-mass rate s) - b| * |Real.exp (-mass rate t) - b| +
      mass rate (s ∩ t) * Real.exp (-mass rate (s ∪ t)) := by
  rw [integral_centeredFactor_mul]
  calc
    _ ≤ |(Real.exp (-mass rate s) - b) * (Real.exp (-mass rate t) - b)| +
        |Real.exp (-(mass rate s + mass rate t)) *
          (Real.exp (mass rate (s ∩ t)) - 1)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg (covariance_nonneg rate s t)]
      exact add_le_add le_rfl (covariance_le rate s t)

lemma abs_integral_centeredFactor_mul_exp_le (rate : ι → ℝ≥0)
    (s t : Finset ι) {L lam₁ lam₂ base c θ : ℝ}
    (hL : 1 ≤ L) (hc : 0 ≤ c)
    (hs : mass rate s = L * lam₁) (ht : mass rate t = L * lam₂)
    (hi : mass rate (s ∩ t) = L * θ)
    (h₁ : c ≤ lam₁) (h₂ : c ≤ lam₂) (hbase : c ≤ base) :
    |∫ ω, centeredFactor s (Real.exp (-L * base)) ω *
      centeredFactor t (Real.exp (-L * base)) ω ∂batchMeasure rate| ≤
        L ^ 2 * Real.exp (-L * c) * (|lam₁ - base| * |lam₂ - base| + θ) := by
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have hi0 := mass_nonneg rate (s ∩ t)
  have hθ : 0 ≤ θ := by rw [hi] at hi0; nlinarith
  have hu : L * c ≤ mass rate (s ∪ t) := by
    calc
      _ ≤ L * lam₁ := mul_le_mul_of_nonneg_left h₁ hL0
      _ = mass rate s := hs.symm
      _ ≤ mass rate (s ∪ t) := mass_mono rate Finset.subset_union_left
  have huse : Real.exp (-mass rate (s ∪ t)) ≤ Real.exp (-L * c) :=
    Real.exp_le_exp.mpr (by linarith)
  have hepos := Real.exp_pos (-L * c)
  have hele : Real.exp (-L * c) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have e₁ := abs_integral_centeredFactor_le rate s hL0 hs h₁ hbase
  have e₂ := abs_integral_centeredFactor_le rate t hL0 ht h₂ hbase
  rw [integral_centeredFactor] at e₁ e₂
  have hmul := mul_le_mul e₁ e₂ (abs_nonneg _)
    (mul_nonneg (mul_nonneg hL0 hepos.le) (abs_nonneg _))
  have hab := mul_nonneg (abs_nonneg (lam₁ - base)) (abs_nonneg (lam₂ - base))
  have hpow : Real.exp (-L * c) ^ 2 ≤ Real.exp (-L * c) := by nlinarith
  have hbound := mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (sq_nonneg L) hab)
  have hcov := mul_le_mul_of_nonneg_left huse hi0
  rw [hi] at hcov
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have hcov' := mul_le_mul_of_nonneg_right hLsq (mul_nonneg hθ hepos.le)
  have hfinal := abs_integral_centeredFactor_mul_le_mass rate s t (Real.exp (-L * base))
  nlinarith

noncomputable def scheduleMeasure (rate : ι → ℝ≥0) (R : ℕ) :
    Measure (Fin R → ι → ℕ) :=
  Measure.pi (fun _ : Fin R => batchMeasure rate)

instance flat_HighMomentRecovered_2 (rate : ι → ℝ≥0) (R : ℕ) : IsProbabilityMeasure (scheduleMeasure rate R) := by
  unfold scheduleMeasure
  infer_instance

noncomputable def scoreTerm {R : ℕ} (s : Finset ι) (b : ℝ) (own : Fin R → Bool)
    (ω : Fin R → ι → ℕ) : ℝ :=
  ∏ r, if own r then centeredFactor s b (ω r) else 0
omit [DecidableEq ι] in

lemma integrable_scoreTerm (rate : ι → ℝ≥0) {R : ℕ} (s : Finset ι) (b : ℝ)
    (own : Fin R → Bool) : Integrable (scoreTerm s b own) (scheduleMeasure rate R) := by
  apply Integrable.fintype_prod (f := fun r ω => if own r then centeredFactor s b ω else 0)
  intro r
  cases h : own r <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact integrable_const 0
  · exact integrable_centeredFactor rate s b
omit [DecidableEq ι] in

lemma integral_scoreTerm (rate : ι → ℝ≥0) {R : ℕ} (s : Finset ι) (b : ℝ)
    (own : Fin R → Bool) :
    (∫ ω, scoreTerm s b own ω ∂scheduleMeasure rate R) =
      ∏ r, if own r then Real.exp (-mass rate s) - b else 0 := by
  unfold scoreTerm scheduleMeasure
  rw [integral_fintype_prod_eq_prod (f := fun r ω => if own r then centeredFactor s b ω else 0)]
  congr 1
  funext r
  cases h : own r <;> simp [integral_centeredFactor]

noncomputable def pairMean (rate : ι → ℝ≥0) (s t : Finset ι) (b : ℝ) : ℝ :=
  (Real.exp (-mass rate s) - b) * (Real.exp (-mass rate t) - b) +
    Real.exp (-(mass rate s + mass rate t)) *
      (Real.exp (mass rate (s ∩ t)) - 1)

lemma integrable_scoreTerm_mul (rate : ι → ℝ≥0) {R : ℕ} (s t : Finset ι) (b : ℝ)
    (ownS ownT : Fin R → Bool) :
    Integrable (fun ω => scoreTerm s b ownS ω * scoreTerm t b ownT ω)
      (scheduleMeasure rate R) := by
  simp only [scoreTerm, ← Finset.prod_mul_distrib]
  apply Integrable.fintype_prod (f := fun r ω => (if ownS r then centeredFactor s b ω else 0) * (if ownT r then centeredFactor t b ω else 0))
  intro r
  cases hs : ownS r <;> cases ht : ownT r <;>
    simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, mul_zero]
  · exact integrable_const 0
  · exact integrable_const 0
  · exact integrable_const 0
  · exact integrable_centeredFactor_mul rate s t b

lemma integral_scoreTerm_mul (rate : ι → ℝ≥0) {R : ℕ} (s t : Finset ι) (b : ℝ)
    (ownS ownT : Fin R → Bool) :
    (∫ ω, scoreTerm s b ownS ω * scoreTerm t b ownT ω ∂scheduleMeasure rate R) =
      ∏ r, if ownS r && ownT r then pairMean rate s t b else 0 := by
  simp only [scoreTerm, ← Finset.prod_mul_distrib, scheduleMeasure]
  rw [integral_fintype_prod_eq_prod (f := fun r ω => (if ownS r then centeredFactor s b ω else 0) * (if ownT r then centeredFactor t b ω else 0))]
  congr 1
  funext r
  cases hs : ownS r <;> cases ht : ownT r <;>
    simp [integral_centeredFactor_mul, pairMean]

lemma abs_integral_scoreTerm_mul_le (rate : ι → ℝ≥0) {R : ℕ} (s t : Finset ι) (b : ℝ)
    (ownS ownT : Fin R → Bool) :
    |∫ ω, scoreTerm s b ownS ω * scoreTerm t b ownT ω ∂scheduleMeasure rate R| ≤
      |pairMean rate s t b| ^ R := by
  rw [integral_scoreTerm_mul, Finset.abs_prod]
  calc
    _ ≤ ∏ _ : Fin R, |pairMean rate s t b| := by
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro r _
      split_ifs <;> simp
    _ = _ := by simp

variable {κ : Type*}

noncomputable def typicalScore {R : ℕ} (H : Finset κ) (directions : κ → Finset ι)
    (b : ℝ) (own : κ → Fin R → Bool) (ω : Fin R → ι → ℕ) : ℝ :=
  ∑ h ∈ H, scoreTerm (directions h) b (own h) ω

lemma integral_typicalScore_sq (rate : ι → ℝ≥0) {R : ℕ} (H : Finset κ)
    (directions : κ → Finset ι) (b : ℝ) (own : κ → Fin R → Bool) :
    (∫ ω, (typicalScore H directions b own ω)^2 ∂scheduleMeasure rate R) =
      ∑ h ∈ H, ∑ k ∈ H,
        ∏ r, if own h r && own k r then pairMean rate (directions h) (directions k) b else 0 := by
  simp only [typicalScore, pow_two]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum H (fun h _ =>
    integrable_finsetSum H (fun k _ =>
      integrable_scoreTerm_mul rate (directions h) (directions k) b (own h) (own k)))]
  apply Finset.sum_congr rfl
  intro h _
  rw [integral_finsetSum H (fun k _ =>
      integrable_scoreTerm_mul rate (directions h) (directions k) b (own h) (own k))]
  apply Finset.sum_congr rfl
  intro k _
  exact integral_scoreTerm_mul rate (directions h) (directions k) b (own h) (own k)

end SharpRamseyFive.PoissonScore
end

end OAI
