import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.IntegralTypicalScoreSq

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*}
omit [Fintype ι] [DecidableEq ι] in
lemma forcedHits_le_one {R : ℕ} (i : ι) (T : Finset (Fin R)) (ω : Fin R → ι → ℕ) :
    forcedHits i T ω ≤ 1 := Finset.prod_le_one₀ (fun _ _ => hitIndicator_nonneg _ _)
      (fun _ _ => hitIndicator_le_one _ _)

omit [Fintype ι] [DecidableEq ι] in
lemma abs_maskedTerm_mul_forcedHits {R : ℕ} (s : Finset ι) (i : ι)
    (T : Finset (Fin R)) (b : ℝ) (own touched : Fin R → Bool) (ω : Fin R → ι → ℕ) :
    |maskedTerm s b own touched ω| * forcedHits i T ω =
      ∏ r, (|maskedFactor s b (own r) (touched r) (ω r)| *
        if r ∈ T then hitIndicator i (ω r) else 1) := by
  simp only [maskedTerm, Finset.abs_prod, Finset.prod_mul_distrib,
    Finset.prod_ite_mem, Finset.univ_inter, forcedHits]
omit [DecidableEq ι] in

lemma integral_abs_maskedTerm_forcedHits_le (rate : ι → ℝ≥0) {R : ℕ}
    (s : Finset ι) (i : ι) (hi : i ∈ s) (T : Finset (Fin R))
    (own touched : Fin R → Bool) {L lam base c : ℝ} (hL : 0 ≤ L)
    (hmass : mass rate s = L * lam) (hlam : c ≤ lam) (hbase : c ≤ base) :
    (∫ ω, |maskedTerm s (Real.exp (-L * base)) own touched ω| * forcedHits i T ω
      ∂scheduleMeasure rate R) ≤
      (2 * Real.exp (-L * c)) ^ R * (rate i : ℝ) ^ T.card := by
  simp_rw [abs_maskedTerm_mul_forcedHits]
  unfold scheduleMeasure
  rw [integral_fintype_prod_eq_prod (f := fun r ω =>
    |maskedFactor s (Real.exp (-L * base)) (own r) (touched r) ω| *
        if r ∈ T then hitIndicator i ω else 1)]
  calc
    _ ≤ ∏ r, (2 * Real.exp (-L * c)) * (if r ∈ T then (rate i : ℝ) else 1) := by
      apply Finset.prod_le_prod₀
      · intro r _
        apply integral_nonneg
        intro ω
        apply mul_nonneg (abs_nonneg _)
        split
        · exact hitIndicator_nonneg _ _
        · norm_num
      · intro r _
        by_cases hr : r ∈ T
        · simp only [hr, ↓reduceIte]
          have h := integral_abs_maskedFactor_hit_le rate s i hi (own r) (touched r) hL hbase
          have he := Real.exp_pos (-L * c)
          have hi0 : 0 ≤ (rate i : ℝ) := (rate i).coe_nonneg
          nlinarith
        · simp only [hr, ↓reduceIte, mul_one]
          exact integral_abs_maskedFactor_exp_le rate s _ _ hL hmass hlam hbase
    _ = _ := by rw [Finset.prod_mul_distrib]; simp [Finset.prod_ite_mem]

def hitBatches {R : ℕ} (i : ι) (ω : Fin R → ι → ℕ) : Finset (Fin R) :=
  Finset.univ.filter (fun r => ω r i ≠ 0)

def overloaded {R : ℕ} (s : Finset ι) (J : ℕ) : Set (Fin R → ι → ℕ) :=
  {ω | ∃ i ∈ s, J ≤ (hitBatches i ω).card}

omit [Fintype ι] [DecidableEq ι] in

lemma overloaded_eq_empty {R J : ℕ} (s : Finset ι) (h : R < J) :
    (overloaded s J : Set (Fin R → ι → ℕ)) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro ω he
  obtain ⟨i, hi, hJ⟩ := he
  have hc : (hitBatches i ω).card ≤ R := by
    simpa only [hitBatches, Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.filter_subset (fun r : Fin R => ω r i ≠ 0) Finset.univ)
  omega
omit [Fintype ι] [DecidableEq ι] in

lemma forcedHits_eq_one_of_subset {R : ℕ} (i : ι) (T : Finset (Fin R))
    (ω : Fin R → ι → ℕ) (h : T ⊆ hitBatches i ω) : forcedHits i T ω = 1 := by
  apply Finset.prod_eq_one
  intro r hr
  rw [hitIndicator_eq]
  have hz : ω r i ≠ 0 := (Finset.mem_filter.mp (h hr)).2
  simp [hz]
omit [Fintype ι] [DecidableEq ι] in

lemma overload_indicator_le_certificates {R : ℕ} (s : Finset ι) (J : ℕ)
    (ω : Fin R → ι → ℕ) :
    (overloaded s J).indicator (fun _ => (1 : ℝ)) ω ≤
      ∑ i ∈ s, ∑ T ∈ (Finset.univ : Finset (Fin R)).powersetCard J, forcedHits i T ω := by
  have hnonneg : ∀ i, 0 ≤ ∑ T ∈ (Finset.univ : Finset (Fin R)).powersetCard J, forcedHits i T ω := by
    intro i
    exact Finset.sum_nonneg (fun T _ => forcedHits_nonneg i T ω)
  by_cases h : ω ∈ overloaded s J
  · rw [Set.indicator_of_mem h]
    obtain ⟨i, hi, hcard⟩ := h
    obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hcard
    have hTm : T ∈ (Finset.univ : Finset (Fin R)).powersetCard J := by
      simp only [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hTc⟩
    calc
      1 = forcedHits i T ω := (forcedHits_eq_one_of_subset i T ω hT).symm
      _ ≤ ∑ U ∈ (Finset.univ : Finset (Fin R)).powersetCard J, forcedHits i U ω :=
        Finset.single_le_sum (fun U _ => forcedHits_nonneg i U ω) hTm
      _ ≤ _ := Finset.single_le_sum (fun i _ => hnonneg i) hi
  · rw [Set.indicator_of_notMem h]
    exact Finset.sum_nonneg (fun i _ => hnonneg i)
omit [DecidableEq ι] in

lemma integrable_abs_maskedTerm_forcedHits (rate : ι → ℝ≥0) {R : ℕ}
    (s : Finset ι) {b : ℝ} (hb : b ∈ Set.Icc 0 1) (own touched : Fin R → Bool)
    (i : ι) (T : Finset (Fin R)) :
    Integrable (fun ω => |maskedTerm s b own touched ω| * forcedHits i T ω)
      (scheduleMeasure rate R) := by
  apply integrable_schedule_of_abs_le rate _ 1
  intro ω
  rw [abs_mul, abs_abs, abs_of_nonneg (forcedHits_nonneg i T ω)]
  exact (mul_le_of_le_one_left (forcedHits_nonneg i T ω)
    (abs_maskedTerm_le_one s hb own touched ω)).trans (forcedHits_le_one i T ω)

omit [DecidableEq ι] in

lemma truncation_error_raw (rate : ι → ℝ≥0) {R : ℕ} (s : Finset ι) (J : ℕ)
    (own touched : Fin R → Bool) {L lam base c : ℝ} (hL : 0 ≤ L) (hc : 0 ≤ c)
    (hmass : mass rate s = L * lam) (hlam : c ≤ lam) (hbase : c ≤ base) :
    (∫ ω, (overloaded s J).indicator (fun ω =>
        |maskedTerm s (Real.exp (-L * base)) own touched ω|) ω ∂scheduleMeasure rate R) ≤
      (2 * Real.exp (-L * c)) ^ R * ∑ i ∈ s, ((R : ℝ) * (rate i : ℝ)) ^ J := by
  have hb : Real.exp (-L * base) ∈ Set.Icc 0 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by nlinarith)⟩
  let f := fun ω => |maskedTerm s (Real.exp (-L * base)) own touched ω|
  have hf (i : ι) (T : Finset (Fin R)) := integrable_abs_maskedTerm_forcedHits rate s hb own touched i T
  have hpoint (ω) : (overloaded s J).indicator f ω ≤
      ∑ i ∈ s, ∑ T ∈ (Finset.univ : Finset (Fin R)).powersetCard J, f ω * forcedHits i T ω := by
    have hh := mul_le_mul_of_nonneg_left (overload_indicator_le_certificates s J ω) (abs_nonneg
      (maskedTerm s (Real.exp (-L * base)) own touched ω))
    by_cases he : ω ∈ overloaded s J
    · simpa [he, f, Finset.mul_sum] using hh
    · simpa [he, f, Finset.mul_sum] using hh
  calc
    _ ≤ ∫ ω, ∑ i ∈ s, ∑ T ∈ (Finset.univ : Finset (Fin R)).powersetCard J,
        f ω * forcedHits i T ω ∂scheduleMeasure rate R := by
      apply integral_mono
      · apply integrable_schedule_of_abs_le rate _ 1
        intro ω
        by_cases h : ω ∈ overloaded s J
        · simpa [h] using abs_maskedTerm_le_one s hb own touched ω
        · simp [h]
      · exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun T _ => hf i T))
      · exact hpoint
    _ = ∑ i ∈ s, ∑ T ∈ (Finset.univ : Finset (Fin R)).powersetCard J,
        ∫ ω, f ω * forcedHits i T ω ∂scheduleMeasure rate R := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun T _ => hf i T))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum _ (fun T _ => hf i T)]
    _ ≤ ∑ i ∈ s, (2 * Real.exp (-L * c)) ^ R * ((R : ℝ) * (rate i : ℝ)) ^ J := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ ∑ T ∈ (Finset.univ : Finset (Fin R)).powersetCard J,
            (2 * Real.exp (-L * c)) ^ R * (rate i : ℝ) ^ J := by
          apply Finset.sum_le_sum
          intro T hT
          have hTJ := (Finset.mem_powersetCard.mp hT).2
          simpa only [hTJ] using integral_abs_maskedTerm_forcedHits_le rate s i hi T
            own touched hL hmass hlam hbase
        _ = (R.choose J : ℝ) * ((2 * Real.exp (-L * c)) ^ R * (rate i : ℝ) ^ J) := by simp
        _ ≤ _ := by
          have hchoose : (R.choose J : ℝ) ≤ (R : ℝ) ^ J := by exact_mod_cast Nat.choose_le_pow R J
          calc
            _ ≤ (R : ℝ) ^ J * ((2 * Real.exp (-L * c)) ^ R * (rate i : ℝ) ^ J) :=
              mul_le_mul_of_nonneg_right hchoose (by positivity)
            _ = _ := by rw [mul_pow]; ring
    _ = _ := (Finset.mul_sum _ _ _).symm
omit [DecidableEq ι] in

lemma truncation_error (rate : ι → ℝ≥0) {R : ℕ} (s : Finset ι) (J : ℕ)
    (own touched : Fin R → Bool) {L lam base : ℝ} (hL : 10000 ≤ L)
    (hmass : mass rate s = L * lam) (hlam : (37 / 50 : ℝ) ≤ lam)
    (hbase : (37 / 50 : ℝ) ≤ base) :
    (∫ ω, (overloaded s J).indicator (fun ω =>
        |maskedTerm s (Real.exp (-L * base)) own touched ω|) ω ∂scheduleMeasure rate R) ≤
      Real.exp (-(17 / 25 : ℝ) * (L * R)) *
        ∑ i ∈ s, ((R : ℝ) * (rate i : ℝ)) ^ J := by
  have hraw := truncation_error_raw rate s J own touched (show 0 ≤ L by linarith)
    (show (0 : ℝ) ≤ 37 / 50 by norm_num) hmass hlam hbase
  apply hraw.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => by positivity))
  calc
    (2 * Real.exp (-L * (37 / 50 : ℝ))) ^ R ≤
        (2 * L * Real.exp (-L * (37 / 50 : ℝ))) ^ R := by
      apply pow_le_pow_left₀ (by positivity)
      have := Real.exp_pos (-L * (37 / 50 : ℝ))
      nlinarith
    _ ≤ _ := by simpa only [neg_mul, mul_comm L (37 / 50 : ℝ)] using two_mul_score_attenuation hL R
omit [DecidableEq ι] in

lemma abs_integral_compl_indicator_le (rate : ι → ℝ≥0) {R : ℕ}
    (s : Finset ι) {b : ℝ} (hb : b ∈ Set.Icc 0 1) (own touched : Fin R → Bool)
    (E : Set (Fin R → ι → ℕ)) :
    |∫ ω, Eᶜ.indicator (maskedTerm s b own touched) ω ∂scheduleMeasure rate R| ≤
      |∫ ω, maskedTerm s b own touched ω ∂scheduleMeasure rate R| +
        ∫ ω, E.indicator (fun ω => |maskedTerm s b own touched ω|) ω ∂scheduleMeasure rate R := by
  have hf := integrable_schedule_of_abs_le rate _ 1 (abs_maskedTerm_le_one s hb own touched)
  have hEf : Integrable (E.indicator (maskedTerm s b own touched)) (scheduleMeasure rate R) := by
    apply integrable_schedule_of_abs_le rate _ 1
    intro ω
    by_cases h : ω ∈ E
    · simpa [h] using abs_maskedTerm_le_one s hb own touched ω
    · simp [h]
  have heq : Eᶜ.indicator (maskedTerm s b own touched) =
      fun ω => maskedTerm s b own touched ω - E.indicator (maskedTerm s b own touched) ω := by
    funext ω
    by_cases h : ω ∈ E <;> simp [h]
  rw [heq, integral_sub hf hEf]
  apply (abs_sub _ _).trans
  apply add_le_add le_rfl
  have habs : (fun ω => |E.indicator (maskedTerm s b own touched) ω|) =
      (E.indicator (fun ω => |maskedTerm s b own touched ω|)) := by
    funext ω
    by_cases h : ω ∈ E <;> simp [h]
  rw [← habs]
  exact abs_integral_le_integral_abs

omit [DecidableEq ι] in

lemma simple_singleton_truncated (rate : ι → ℝ≥0) {R : ℕ}
    (s : Finset ι) (J : ℕ) (own touched : Fin R → Bool) {L base delta alpha : ℝ}
    (hL : 10000 ≤ L) (hmass : mass rate s = L * (base + delta - alpha))
    (hinternal : (37 / 50 : ℝ) ≤ base + delta - alpha) (hbase : (37 / 50 : ℝ) ≤ base)
    (ha : 0 ≤ alpha) (hd : |delta| + alpha ≤ 1) {N K : ℕ}
    (hN : N ≤ (untouchedBatches touched).card) (hK : K ≤ N) :
    |∫ ω, (overloaded s J)ᶜ.indicator
        (maskedTerm s (Real.exp (-L * base)) own touched) ω ∂scheduleMeasure rate R| ≤
      Real.exp (-(17 / 25 : ℝ) * (L * R)) *
        (|delta| ^ N + alpha ^ K + ∑ i ∈ s, ((R : ℝ) * (rate i : ℝ)) ^ J) := by
  have hb : Real.exp (-L * base) ∈ Set.Icc 0 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by nlinarith)⟩
  calc
    _ ≤ _ := abs_integral_compl_indicator_le rate s hb own touched (overloaded s J)
    _ ≤ Real.exp (-(17 / 25 : ℝ) * (L * R)) * (|delta| ^ N + alpha ^ K) +
        Real.exp (-(17 / 25 : ℝ) * (L * R)) * ∑ i ∈ s, ((R : ℝ) * (rate i : ℝ)) ^ J :=
      add_le_add (simple_singleton_attenuation rate s own touched hL hmass hinternal hbase ha hd hN hK)
        (truncation_error rate s J own touched hL hmass hinternal hbase)
    _ = _ := by ring

omit [DecidableEq ι] in
lemma measurePreserving_uncurry_schedule (rate : ι → ℝ≥0) (R : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin R) ι ℕ).symm
      (scheduleMeasure rate R) (batchMeasure (fun p : Fin R × ι => rate p.2)) := by
  refine ⟨(MeasurableEquiv.curry (Fin R) ι ℕ).symm.measurable, ?_⟩
  simpa only [Measure.infinitePi_eq_pi, scheduleMeasure, batchMeasure] using
    Measure.infinitePi_map_curry_symm (fun (_ : Fin R) i => poissonMeasure (rate i))

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

noncomputable def partitionEquiv (label : ι → κ) :
    (ι → ℕ) ≃ᵐ (∀ c : κ, {i : ι // label i = c} → ℕ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : ι => ℕ) (Equiv.sigmaFiberEquiv label)).symm.trans
    (MeasurableEquiv.piCurry (fun (c : κ) (_ : {i : ι // label i = c}) => ℕ))

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
@[simp] lemma partitionEquiv_apply (label : ι → κ) (ω : ι → ℕ) (c : κ)
    (i : {i : ι // label i = c}) : partitionEquiv label ω c i = ω i := rfl

omit [DecidableEq ι] in
lemma measurePreserving_partition (rate : ι → ℝ≥0) (label : ι → κ) :
    MeasurePreserving (partitionEquiv label) (batchMeasure rate)
      (Measure.pi (fun c : κ => batchMeasure (fun i : {i : ι // label i = c} => rate i))) := by
  have hc : MeasurePreserving
      (MeasurableEquiv.piCurry (fun (c : κ) (_ : {i : ι // label i = c}) => ℕ))
      (Measure.pi (fun p : (c : κ) × {i : ι // label i = c} => poissonMeasure (rate p.2)))
      (Measure.pi (fun c : κ => batchMeasure (fun i : {i : ι // label i = c} => rate i))) := by
    refine ⟨(MeasurableEquiv.piCurry _).measurable, ?_⟩
    simpa only [Measure.infinitePi_eq_pi, batchMeasure] using
      Measure.infinitePi_map_piCurry (fun (c : κ) (i : {i : ι // label i = c}) =>
        poissonMeasure (rate i))
  exact hc.comp ((measurePreserving_piCongrLeft (fun i => poissonMeasure (rate i))
    (Equiv.sigmaFiberEquiv label)).symm)

omit [DecidableEq ι] in

lemma integral_partition_prod (rate : ι → ℝ≥0) (label : ι → κ)
    (f : ∀ c : κ, ({i : ι // label i = c} → ℕ) → ℝ) :
    (∫ ω, ∏ c, f c (fun i => ω i) ∂batchMeasure rate) =
      ∏ c, ∫ ω, f c ω ∂batchMeasure (fun i : {i : ι // label i = c} => rate i) := by
  calc
    _ = ∫ ω, ∏ c, f c (ω c) ∂Measure.pi
        (fun c : κ => batchMeasure (fun i : {i : ι // label i = c} => rate i)) :=
      (measurePreserving_partition rate label).integral_comp
        (partitionEquiv label).measurableEmbedding _
    _ = _ := integral_fintype_prod_eq_prod _

noncomputable def externalEquiv (label : ι → Option κ) :
    (ι → ℕ) ≃ᵐ ((∀ c : κ, {i : ι // label i = some c} → ℕ) ×
      ({i : ι // label i = none} → ℕ)) :=
  (partitionEquiv label).trans (MeasurableEquiv.piOptionEquivProd
    (fun c : Option κ => {i : ι // label i = c} → ℕ))
omit [DecidableEq ι] in

lemma measurePreserving_external (rate : ι → ℝ≥0) (label : ι → Option κ) :
    MeasurePreserving (externalEquiv label) (batchMeasure rate)
      ((Measure.pi (fun c : κ => batchMeasure
          (fun i : {i : ι // label i = some c} => rate i))).prod
        (batchMeasure (fun i : {i : ι // label i = none} => rate i))) := by
  have h : MeasurePreserving
      (MeasurableEquiv.piOptionEquivProd
        (fun c : Option κ => {i : ι // label i = c} → ℕ)).symm
      ((Measure.pi (fun c : κ => batchMeasure
          (fun i : {i : ι // label i = some c} => rate i))).prod
        (batchMeasure (fun i : {i : ι // label i = none} => rate i)))
      (Measure.pi (fun c : Option κ => batchMeasure
          (fun i : {i : ι // label i = c} => rate i))) :=
    ⟨(MeasurableEquiv.piOptionEquivProd _).symm.measurable,
      Measure.pi_map_piOptionEquivProd (fun c : Option κ =>
        batchMeasure (fun i : {i : ι // label i = c} => rate i))⟩
  exact h.symm.comp (measurePreserving_partition rate label)

omit [DecidableEq ι] in

lemma integral_external_components (rate : ι → ℝ≥0) (label : ι → Option κ)
    (weight : ({i : ι // label i = none} → ℕ) → ℝ)
    (f : ∀ c : κ, ({i : ι // label i = none} → ℕ) →
      ({i : ι // label i = some c} → ℕ) → ℝ)
    (hw : ∀ z, |weight z| ≤ 1) (hf : ∀ c z x, |f c z x| ≤ 1) :
    (∫ ω, weight (fun i => ω i) * ∏ c, f c (fun i => ω i) (fun i => ω i)
      ∂batchMeasure rate) =
      ∫ z, weight z * ∏ c, ∫ x, f c z x
        ∂batchMeasure (fun i : {i : ι // label i = some c} => rate i)
      ∂batchMeasure (fun i : {i : ι // label i = none} => rate i) := by
  let μ := Measure.pi (fun c : κ => batchMeasure
    (fun i : {i : ι // label i = some c} => rate i))
  let ν := batchMeasure (fun i : {i : ι // label i = none} => rate i)
  let F : (∀ c : κ, {i : ι // label i = some c} → ℕ) ×
      ({i : ι // label i = none} → ℕ) → ℝ :=
    fun p => weight p.2 * ∏ c, f c p.2 (p.1 c)
  have hF : Integrable F (μ.prod ν) := by
    apply Integrable.of_bound (measurable_of_countable F).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro p
    simp only [F, Real.norm_eq_abs, abs_mul, Finset.abs_prod]
    exact (mul_le_of_le_one_left (by positivity) (hw _)).trans
      (Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => hf _ _ _))
  calc
    _ = ∫ p, F p ∂μ.prod ν := (measurePreserving_external rate label).integral_comp
      (externalEquiv label).measurableEmbedding F
    _ = ∫ z, ∫ x, weight z * ∏ c, f c z (x c) ∂μ ∂ν :=
      integral_prod_symm F hF
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      dsimp only
      rw [integral_const_mul]
      congr 1
      exact integral_fintype_prod_eq_prod _

section ComponentGeometry

variable {H : Type*} [Fintype H] [DecidableEq H]

noncomputable def strongGraph (rate : ι → ℝ≥0) (s : H → Finset ι) (t : ℝ) :
    SimpleGraph H where
  Adj h k := h ≠ k ∧ t < mass rate (s h ∩ s k)
  symm := ⟨by
    intro h k hk
    exact ⟨hk.1.symm, by simpa only [Finset.inter_comm] using hk.2⟩⟩
  loopless := ⟨by intro h hh; exact hh.1 rfl⟩

omit [Fintype ι] [Fintype H] [DecidableEq H] in
lemma cross_component_overlap (rate : ι → ℝ≥0) (s : H → Finset ι) (t : ℝ)
    {h k : H} (hd : (strongGraph rate s t).connectedComponentMk h ≠
      (strongGraph rate s t).connectedComponentMk k) :
    mass rate (s h ∩ s k) ≤ t := by
  by_contra hn
  have hk : h ≠ k := by intro e; exact hd (congrArg _ e)
  exact hd (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    (G := strongGraph rate s t) ⟨hk, lt_of_not_ge hn⟩)

def External (rate : ι → ℝ≥0) (s : H → Finset ι) (t : ℝ) (i : ι) : Prop :=
  ∃ h k : H, i ∈ s h ∧ i ∈ s k ∧
    (strongGraph rate s t).connectedComponentMk h ≠
      (strongGraph rate s t).connectedComponentMk k

omit [Fintype ι] [Fintype H] [DecidableEq H] in
lemma external_iff_other (rate : ι → ℝ≥0) (s : H → Finset ι) (t : ℝ)
    {h : H} {i : ι} (hi : i ∈ s h) :
    External rate s t i ↔ ∃ k : H, i ∈ s k ∧
      (strongGraph rate s t).connectedComponentMk h ≠
        (strongGraph rate s t).connectedComponentMk k := by
  classical
  constructor
  · rintro ⟨u, v, hu, hv, huv⟩
    by_cases e : (strongGraph rate s t).connectedComponentMk h =
        (strongGraph rate s t).connectedComponentMk u
    · exact ⟨v, hv, by simpa only [e] using huv⟩
    · exact ⟨u, hu, e⟩
  · rintro ⟨k, hk, hd⟩
    exact ⟨h, k, hi, hk, hd⟩

noncomputable def externalPart (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) (h : H) : Finset ι := by
  classical
  exact (s h).filter (External rate s t)

noncomputable def internalPart (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) (h : H) : Finset ι := by
  classical
  exact (s h).filter (fun i => ¬ External rate s t i)

omit [Fintype ι] [Fintype H] [DecidableEq H] in
lemma internal_external_mass (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) (h : H) :
    mass rate (externalPart rate s t h) + mass rate (internalPart rate s t h) =
      mass rate (s h) := by
  classical
  exact Finset.sum_filter_add_sum_filter_not _ _ _

noncomputable def otherComponents (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) (h : H) : Finset H := by
  classical
  exact Finset.univ.filter (fun k =>
    (strongGraph rate s t).connectedComponentMk h ≠
      (strongGraph rate s t).connectedComponentMk k)

omit [Fintype ι] [DecidableEq H] in

lemma external_mass_le_sum (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) (h : H) :
    mass rate (externalPart rate s t h) ≤
      ∑ k ∈ otherComponents rate s t h, mass rate (s h ∩ s k) := by
  classical
  let K := otherComponents rate s t h
  have hp (i : ι) (hi : i ∈ s h) :
      (if External rate s t i then (rate i : ℝ) else 0) ≤
        ∑ k ∈ K, if i ∈ s k then (rate i : ℝ) else 0 := by
    split_ifs with he
    · obtain ⟨k, hk, hd⟩ := (external_iff_other rate s t hi).mp he
      have hkK : k ∈ K := by
        simpa only [K, otherComponents, Finset.mem_filter, Finset.mem_univ, true_and] using hd
      simpa only [ite_eq_left hk] using
        (Finset.single_le_sum (f := fun j : H => if i ∈ s j then (rate i : ℝ) else 0)
          (fun j (_ : j ∈ K) => by split_ifs <;> positivity) hkK :
          (if i ∈ s k then (rate i : ℝ) else 0) ≤
            ∑ j ∈ K, if i ∈ s j then (rate i : ℝ) else 0)
    · exact Finset.sum_nonneg (by intro k hk; split_ifs <;> positivity)
  calc
    _ = ∑ i ∈ s h, if External rate s t i then (rate i : ℝ) else 0 := by
      simp only [externalPart, mass, Finset.sum_filter]
    _ ≤ ∑ i ∈ s h, ∑ k ∈ K, if i ∈ s k then (rate i : ℝ) else 0 :=
      Finset.sum_le_sum hp
    _ = ∑ k ∈ K, mass rate (s h ∩ s k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [mass, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
    _ = _ := rfl

end ComponentGeometry
end SharpRamseyFive.PoissonScore
end

end OAI
