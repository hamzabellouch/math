import Mathlib
import OAI.Probability.Ballisticity.Renewal.RegenerationWords

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma renewal_occupation_lower {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (T : ℕ → α → ℕ) (hT : ∀ i, Measurable (T i))
    (hbig : ∀ᵐ x ∂μ, ∀ i, i ≤ T i x) {p : ℝ}
    (hlow : ∀ r, 0 < r → p ≤ μ.real {x | ∃ i, T i x = r}) (H : ℕ) :
    (H : ℝ) * p ≤ ∑ i ∈ Finset.range (H+1), μ.real {x | T i x ≤ H} := by
  classical
  have hlow' (r : ℕ) (hr : r ∈ Finset.Icc 1 H) :
      p ≤ ∑ i ∈ Finset.range (H+1), μ.real {x | T i x = r} := by
    have hsub : {x | ∃ i, T i x = r} ≤ᵐ[μ]
        ⋃ i ∈ Finset.range (H+1), {x | T i x = r} := by
      filter_upwards [hbig] with x hx hi
      obtain ⟨i, hi⟩ := hi
      refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr ?_, hi⟩⟩
      have hh := hx i
      have hrH := (Finset.mem_Icc.mp hr).2
      omega
    exact (hlow r (by have := (Finset.mem_Icc.mp hr).1; omega)).trans
      ((ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)).trans
        (measureReal_biUnion_finset_le _ _))
  calc
    (H : ℝ) * p = ∑ r ∈ Finset.Icc 1 H, p := by simp
    _ ≤ ∑ r ∈ Finset.Icc 1 H, ∑ i ∈ Finset.range (H+1), μ.real {x | T i x = r} :=
      Finset.sum_le_sum hlow'
    _ = ∑ i ∈ Finset.range (H+1), ∑ r ∈ Finset.Icc 1 H, μ.real {x | T i x = r} :=
      Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      have he := sum_measureReal_preimage_singleton (μ := μ) (Finset.Icc 1 H)
        (fun r _ => (hT i) (measurableSet_singleton r))
      change (∑ r ∈ Finset.Icc 1 H, μ.real (T i ⁻¹' {r})) ≤ _
      rw [he]
      exact measureReal_mono (fun x hx => show T i x ≤ H from (Finset.mem_Icc.mp hx).2)

lemma nat_integrable_of_truncated_mean_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (S : α → ℕ) (hS : Measurable S) {B : ℝ}
    (hB : ∀ K : ℕ, (∫ x, ((min (S x) K : ℕ) : ℝ) ∂μ) ≤ B) :
    Integrable (fun x => (S x : ℝ)) μ ∧ (∫ x, (S x : ℝ) ∂μ) ≤ B := by
  have hKint (K : ℕ) : Integrable (fun x => ((min (S x) K : ℕ) : ℝ)) μ :=
    integrable_of_nonneg_bound μ ((measurable_of_countable (f := fun n : ℕ => (n : ℝ))).comp (hS.min measurable_const)) (B := K)
      fun x => ⟨Nat.cast_nonneg _, by exact_mod_cast min_le_right (S x) K⟩
  have hB0 : 0 ≤ B := by simpa only [Nat.min_zero, Nat.cast_zero, integral_zero] using hB 0
  have hbound : (∫⁻ x, (S x : ℝ≥0∞) ∂μ) ≤ ENNReal.ofReal B := by
    have he (x : α) : (S x : ℝ≥0∞) = ⨆ K : ℕ, ((min (S x) K : ℕ) : ℝ≥0∞) := by
      apply le_antisymm
      · exact le_iSup_of_le (S x) (by simp)
      · exact iSup_le fun K => by exact_mod_cast min_le_left (S x) K
    simp_rw [he]
    rw [lintegral_iSup (f := fun K x => ((min (S x) K : ℕ) : ℝ≥0∞)) (fun K => (measurable_of_countable (f := fun n : ℕ =>
      ((min n K : ℕ) : ℝ≥0∞))).comp hS) (fun i j hij x => by
        dsimp only
        exact_mod_cast min_le_min_left (S x) hij)]
    apply iSup_le
    intro K
    have hh := ofReal_integral_eq_lintegral_ofReal (hKint K)
      (Filter.Eventually.of_forall fun x => Nat.cast_nonneg (min (S x) K))
    simp only [ENNReal.ofReal_natCast] at hh
    rw [← hh]
    exact ENNReal.ofReal_le_ofReal (hB K)
  have hint : Integrable (fun x => (S x : ℝ)) μ := by
    refine ⟨((measurable_of_countable (f := fun n : ℕ => (n : ℝ))).comp hS).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => Nat.cast_nonneg (S x))]
    simp only [ENNReal.ofReal_natCast]
    exact hbound.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  have he := ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => Nat.cast_nonneg (S x))
  simp only [ENNReal.ofReal_natCast] at he
  rw [← he] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff hB0).mp hbound

lemma renewal_mean_bound {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (S : ℕ → α → ℕ) (hS : ∀ i, Measurable (S i)) (hind : iIndepFun S μ)
    (hident : ∀ i, IdentDistrib (S i) (S 0) μ μ)
    (hpos : ∀ᵐ x ∂μ, ∀ i, 0 < S i x) {p : ℝ} (hp : 0 < p)
    (hlow : ∀ r, 0 < r → p ≤ μ.real {x | ∃ i, (∑ j ∈ Finset.range i, S j x) = r}) :
    Integrable (fun x => (S 0 x : ℝ)) μ ∧ (∫ x, (S 0 x : ℝ) ∂μ) ≤ 1 / p := by
  apply nat_integrable_of_truncated_mean_bound μ (S 0) (hS 0)
  intro K
  let E := ∫ x, ((min (S 0 x) K : ℕ) : ℝ) ∂μ
  have hE : 0 ≤ E := integral_nonneg fun x => Nat.cast_nonneg _
  have hbig : ∀ᵐ x ∂μ, ∀ i, i ≤ ∑ j ∈ Finset.range i, S j x := by
    filter_upwards [hpos] with x hx i
    calc
      i = ∑ _j ∈ Finset.range i, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => hx j
  have hbound (H : ℕ) : (H : ℝ) * p * E ≤ (H : ℝ) + K :=
    (mul_le_mul_of_nonneg_right (renewal_occupation_lower μ _
      (fun i => Finset.measurable_fun_sum _ (fun j _ => hS j)) hbig hlow H) hE).trans
      (renewal_wald_bound μ S hS hind hident H K)
  have hpE : p * E ≤ 1 := by
    by_contra h
    have hpos' : 0 < p * E - 1 := by linarith
    obtain ⟨H, hH⟩ := exists_nat_gt ((K : ℝ) / (p * E - 1))
    have hH' := (div_lt_iff₀ hpos').mp hH
    have hh := hbound H
    nlinarith
  exact (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hpE)

lemma trueRecord_eq_regenerationTime {d : ℕ} (ℓ : Vector d) (X : Path d) (h0 : X 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n))
    {j : ℕ} (hj : TrueRecord ℓ X j) : ∃ n, regenerationTimes ℓ X n = j := by
  have hmono := regenerationTimes_strictMono ℓ X hX
  have hbig (n : ℕ) : n ≤ regenerationTimes ℓ X n := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact Nat.succ_le_of_lt (ih.trans_lt (hmono (Nat.lt_succ_self n)))
  have hex : ∃ n, j < regenerationTimes ℓ X n := ⟨j+1, (Nat.lt_succ_self j).trans_le (hbig _)⟩
  let n := Nat.find hex
  have hn : j < regenerationTimes ℓ X n := Nat.find_spec hex
  have hn0 : 0 < n := by
    by_contra h
    have he : n = 0 := by omega
    simp only [he, regenerationTimes_zero, not_lt_zero] at hn
  have hn' : n - 1 + 1 = n := by omega
  have hbefore : regenerationTimes ℓ X (n-1) ≤ j :=
    le_of_not_gt (Nat.find_min hex (show n-1 < Nat.find hex by change n-1 < n; omega))
  by_cases he : regenerationTimes ℓ X (n-1) = j
  · exact ⟨n-1, he⟩
  · exact False.elim (regenerationTimes_no_true_between ℓ X h0 hX (n-1) j
      (lt_of_le_of_ne hbefore he) (by simpa only [hn'] using hn) hj)

lemma conditioned_wordRecordCount_integrable {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    Integrable (fun X => (wordRecordCount ℓ (firstWord ℓ X) : ℝ)) (conditionedLaw ν ℓ) ∧
      (∫ X, (wordRecordCount ℓ (firstWord ℓ X) : ℝ) ∂conditionedLaw ν ℓ) ≤
        1 / (annealedLaw ν).real (NoDrop ℓ 0) := by
  have hp := noDrop_positive_of_directionallyTransient ν ℓ htrans
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ (ne_of_gt hp)
  let S : ℕ → Path d → ℕ := fun n X => wordRecordCount ℓ (regenerationWords ℓ X n)
  have hS (n : ℕ) : Measurable (S n) :=
    (measurable_of_countable (wordRecordCount ℓ)).comp (measurable_regenerationWord ℓ n)
  have hind : iIndepFun S (conditionedLaw ν ℓ) :=
    (regenerationWords_independent ν ℓ htrans).comp (fun _ => wordRecordCount ℓ)
      (fun _ => measurable_of_countable _)
  have hident (n : ℕ) : IdentDistrib (S n) (S 0) (conditionedLaw ν ℓ) (conditionedLaw ν ℓ) :=
    (regenerationWords_identDistrib ν ℓ htrans n).comp (measurable_of_countable (wordRecordCount ℓ))
  have hall := conditioned_all_firstWords ν ℓ htrans
  have hpos : ∀ᵐ X ∂conditionedLaw ν ℓ, ∀ n, 0 < S n X := by
    filter_upwards [hall] with X hX n
    exact wordRecordCount_positive ℓ _
      (((firstTrueWord_characterization ℓ _ _ (hX n).2.1).mp ⟨(hX n).1, (hX n).2.2⟩).1)
  have hp' : 0 < (annealedLaw ν).real (NoDrop ℓ 0) :=
    ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top _ _)
  have hlow (r : ℕ) (hr : 0 < r) : (annealedLaw ν).real (NoDrop ℓ 0) ≤
      (conditionedLaw ν ℓ).real {X | ∃ n, (∑ j ∈ Finset.range n, S j X) = r} := by
    apply (ENNReal.toReal_mono (measure_ne_top _ _) (conditioned_true_at_index_lower ν ℓ htrans hr)).trans
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [hall, (conditionedLaw_absolutelyContinuous ν ℓ).ae_le (annealed_initial ν)]
      with X hX h0 hR
    obtain ⟨j, _, hj, hcount⟩ := hR
    obtain ⟨n, hn⟩ := trueRecord_eq_regenerationTime ℓ X h0 hX hj
    exact ⟨n, (recordCount_regenerationTimes ℓ X h0 hX n).symm.trans (hn ▸ hcount)⟩
  exact renewal_mean_bound (conditionedLaw ν ℓ) S hS hind hident hpos hp' hlow

lemma height_le_recordCount {d : ℕ} (ℓ : Vector d) (X : Path d)
    (hstep : ∀ n, dot (realPosition (X (n+1))) ℓ ≤ dot (realPosition (X n)) ℓ + 1)
    (n : ℕ) : dot (realPosition (X n)) ℓ - dot (realPosition (X 0)) ℓ ≤
      (recordCount ℓ X n : ℝ) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      by_cases hr : StrictRecord ℓ X (n+1)
      · rw [recordCount_succ, ite_eq_left hr, Nat.cast_add, Nat.cast_one]
        have := ih n (by omega)
        linarith [hstep n]
      · obtain ⟨j, hj, hjh⟩ : ∃ j < n+1,
            dot (realPosition (X (n+1))) ℓ ≤ dot (realPosition (X j)) ℓ := by
          simpa only [StrictRecord, not_forall, exists_prop, not_lt] using hr
        have hle : (recordCount ℓ X j : ℝ) ≤ (recordCount ℓ X (n+1) : ℝ) :=
          Nat.cast_le.mpr (recordCount_mono ℓ X hj.le)
        linarith [ih j hj]

lemma wordPath_step_or_stay {d : ℕ} (x : Lattice d) (w : List (Direction d)) (n : ℕ) :
    wordPath x w (n+1) = wordPath x w n ∨
      ∃ e : Direction d, wordPath x w (n+1) = wordPath x w n + step e := by
  induction w generalizing x n with
  | nil => exact Or.inl rfl
  | cons e w ih =>
    cases n with
    | zero => exact Or.inr ⟨e, by simp only [wordPath, wordPath_zero]⟩
    | succ n => exact ih (x + step e) n

lemma dot_step {d : ℕ} (ℓ : Vector d) (e : Direction d) :
    dot (realPosition (step e)) ℓ = if e.2 then ℓ e.1 else -ℓ e.1 := by
  classical
  simp only [dot, realPosition, step, Int.cast_ite, Int.cast_one, Int.cast_neg,
    Int.cast_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  split <;> simp_all

noncomputable def wordHeightGain {d : ℕ} (ℓ : Vector d) (w : List (Direction d)) : ℝ :=
  dot (realPosition (wordPath 0 w w.length)) ℓ

lemma wordHeightGain_le_recordCount {d : ℕ} (ℓ : Vector d)
    (hℓ : ∀ i, |ℓ i| ≤ 1) (w : List (Direction d)) :
    wordHeightGain ℓ w ≤ (wordRecordCount ℓ w : ℝ) := by
  have hs (n : ℕ) : dot (realPosition (wordPath 0 w (n+1))) ℓ ≤
      dot (realPosition (wordPath 0 w n)) ℓ + 1 := by
    rcases wordPath_step_or_stay 0 w n with he | ⟨e, he⟩
    · rw [he]; linarith
    · rw [he, dot_realPosition_add, dot_step]
      have hl := (abs_le.mp (hℓ e.1))
      split <;> linarith
  simpa only [wordHeightGain, wordRecordCount, wordPath_zero, dot, realPosition,
    Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero, sub_zero] using
    height_le_recordCount ℓ (wordPath 0 w) hs w.length

lemma wordHeightGain_positive {d : ℕ} (ℓ : Vector d) (w : List (Direction d))
    (hw : AdmissibleTrueWord ℓ w) : 0 < wordHeightGain ℓ w := by
  simpa only [wordPath_zero, dot, realPosition, Pi.zero_apply, Int.cast_zero,
    zero_mul, Finset.sum_const_zero, wordHeightGain] using (hw.2.1 0 hw.1).2

lemma conditioned_wordHeightGain_moments {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hℓ : ∀ i, |ℓ i| ≤ 1) (htrans : DirectionallyTransient ν ℓ) :
    Integrable (fun X => wordHeightGain ℓ (firstWord ℓ X)) (conditionedLaw ν ℓ) ∧
      0 < (∫ X, wordHeightGain ℓ (firstWord ℓ X) ∂conditionedLaw ν ℓ) ∧
      (∫ X, wordHeightGain ℓ (firstWord ℓ X) ∂conditionedLaw ν ℓ) ≤
        1 / (annealedLaw ν).real (NoDrop ℓ 0) := by
  have hp := noDrop_positive_of_directionallyTransient ν ℓ htrans
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ (ne_of_gt hp)
  have hm : Measurable (fun X => wordHeightGain ℓ (firstWord ℓ X)) :=
    (measurable_of_countable (wordHeightGain ℓ)).comp (measurable_firstWord ℓ)
  have hpos : ∀ᵐ X ∂conditionedLaw ν ℓ, 0 < wordHeightGain ℓ (firstWord ℓ X) := by
    filter_upwards [conditioned_all_firstWords ν ℓ htrans] with X hX
    have he := hX 0
    simp only [Function.iterate_zero, id_eq, regenerationWords] at he
    exact wordHeightGain_positive ℓ _
      ((firstTrueWord_characterization ℓ _ X he.2.1).mp ⟨he.1, he.2.2⟩).1
  obtain ⟨hcount, hbound⟩ := conditioned_wordRecordCount_integrable ν ℓ htrans
  have hint : Integrable (fun X => wordHeightGain ℓ (firstWord ℓ X)) (conditionedLaw ν ℓ) := by
    apply hcount.mono' hm.aestronglyMeasurable
    filter_upwards [hpos] with X hX
    rw [Real.norm_eq_abs, abs_of_pos hX]
    exact wordHeightGain_le_recordCount ℓ hℓ _
  refine ⟨hint, ?_, (integral_mono_ae hint hcount
    (Filter.Eventually.of_forall fun X => wordHeightGain_le_recordCount ℓ hℓ _)).trans hbound⟩
  rw [integral_pos_iff_support_of_nonneg_ae (hpos.mono fun _ h => h.le) hint]
  have he : Function.support (fun X => wordHeightGain ℓ (firstWord ℓ X)) =ᵐ[conditionedLaw ν ℓ]
      Set.univ := by
    filter_upwards [hpos] with X hX
    apply propext
    change (wordHeightGain ℓ (firstWord ℓ X) ≠ 0) ↔ True
    exact iff_true_intro (ne_of_gt hX)
  rw [measure_congr he, measure_univ]
  exact zero_lt_one

lemma nonnegative_interval_count (a : ℝ) (ha : 0 ≤ a) (K : ℕ)
    (u b : ℕ → ℝ) (hu : ∀ i, 0 ≤ u i) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1)
    (hw : ∀ i, b i ≠ 0 → ∃ k, 0 < k ∧ k ≤ K ∧
      a * (k : ℝ) ≤ ∑ j ∈ Finset.range k, u (i+j))
    (M : ℕ) : a * (∑ i ∈ Finset.range M, b i) ≤
      ∑ i ∈ Finset.range (M+K), u i := by
  induction M using Nat.strong_induction_on generalizing u b with
  | h M ih =>
    by_cases hM : M = 0
    · subst M
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero, Nat.zero_add]
      exact Finset.sum_nonneg fun i _ => hu i
    by_cases hb0 : b 0 = 0
    · have hrec := ih (M-1) (by omega) (fun i => u (1+i)) (fun i => b (1+i))
        (fun i => hu _) (fun i => hb _) (by
          intro i hi
          obtain ⟨k,hk,hkK,hku⟩ := hw (1+i) hi
          exact ⟨k,hk,hkK,by simpa only [Nat.add_assoc] using hku⟩)
      have hfirst : (∑ i ∈ Finset.range M, b i) = ∑ i ∈ Finset.range (M-1), b (1+i) := by
        conv_lhs => rw [show M = 1+(M-1) by omega, Finset.sum_range_add, Finset.sum_range_one,
          hb0, zero_add]
      rw [hfirst]
      calc
        _ ≤ ∑ i ∈ Finset.range (M-1+K), u (1+i) := hrec
        _ ≤ u 0 + ∑ i ∈ Finset.range (M-1+K), u (1+i) := le_add_of_nonneg_left (hu 0)
        _ = _ := by
          conv_rhs => rw [show M+K = 1+(M-1+K) by omega, Finset.sum_range_add,
            Finset.sum_range_one]
    · obtain ⟨k,hk,hkK,hkw⟩ := hw 0 hb0
      simp only [Nat.zero_add] at hkw
      by_cases hkM : k ≤ M
      · have hrec := ih (M-k) (by omega) (fun i => u (k+i)) (fun i => b (k+i))
          (fun i => hu _) (fun i => hb _) (by
            intro i hi
            obtain ⟨l,hl,hlK,hlu⟩ := hw (k+i) hi
            exact ⟨l,hl,hlK,by simpa only [Nat.add_assoc] using hlu⟩)
        have hbfirst : (∑ i ∈ Finset.range k, b i) ≤ (k : ℝ) := by
          calc
            _ ≤ ∑ i ∈ Finset.range k, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hb i).2
            _ = _ := by simp
        calc
          _ = a * (∑ i ∈ Finset.range k, b i) +
              a * (∑ i ∈ Finset.range (M-k), b (k+i)) := by
            conv_lhs => arg 2; rw [show M = k+(M-k) by omega, Finset.sum_range_add]
            rw [mul_add]
          _ ≤ (∑ i ∈ Finset.range k, u i) +
              (∑ i ∈ Finset.range (M-k+K), u (k+i)) :=
            add_le_add ((mul_le_mul_of_nonneg_left hbfirst ha).trans hkw) hrec
          _ = _ := by
            conv_rhs => rw [show M+K = k+(M-k+K) by omega, Finset.sum_range_add]
      · have hbfirst : (∑ i ∈ Finset.range M, b i) ≤ (k : ℝ) := by
          calc
            _ ≤ ∑ i ∈ Finset.range M, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hb i).2
            _ = (M : ℝ) := by simp
            _ ≤ k := Nat.cast_le.mpr (by omega)
        exact ((mul_le_mul_of_nonneg_left hbfirst ha).trans hkw).trans
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
            (fun i _ _ => hu i))

lemma stationary_initial_average_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (f : Ω → ℝ) (hf : Measurable f) (hfi : Integrable f μ) (hfn : ∀ x, 0 ≤ f x)
    (K : ℕ) (a : ℝ) (ha : 0 < a) :
    a * μ.real {x | ∃ k, 0 < k ∧ k ≤ K ∧
      a * (k : ℝ) < ∑ j ∈ Finset.range k, f (T^[j] x)} ≤ ∫ x, f x ∂μ := by
  classical
  let B : Set Ω := {x | ∃ k, 0 < k ∧ k ≤ K ∧
    a * (k : ℝ) < ∑ j ∈ Finset.range k, f (T^[j] x)}
  have hB : MeasurableSet B := by
    simp only [B, Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro k
    have hs : Measurable (fun x => ∑ j ∈ Finset.range k, f (T^[j] x)) :=
      Finset.measurable_fun_sum _ (fun j _ => hf.comp (hT.iterate j).measurable)
    by_cases h0 : 0 < k
    · by_cases hk : k ≤ K
      · simpa only [h0, hk, true_and] using measurableSet_lt measurable_const hs
      · simp only [hk, false_and, and_false, Set.ofPred_false]; exact MeasurableSet.empty
    · simp only [h0, false_and, Set.ofPred_false]; exact MeasurableSet.empty
  let b : Ω → ℝ := B.indicator (fun _ => (1 : ℝ))
  have hbi : Integrable b μ := integrable_const _ |>.indicator hB
  have hb (x : Ω) : 0 ≤ b x ∧ b x ≤ 1 := by
    simp only [b, Set.indicator]; split <;> norm_num
  have hcomp (g : Ω → ℝ) (hg : Integrable g μ) (n : ℕ) :
      Integrable (fun x => g (T^[n] x)) μ ∧ (∫ x, g (T^[n] x) ∂μ) = ∫ x, g x ∂μ := by
    refine ⟨(hT.iterate n).integrable_comp_of_integrable hg, ?_⟩
    have hgm : AEStronglyMeasurable g (μ.map (T^[n])) := by
      rw [(hT.iterate n).map_eq]
      exact hg.aestronglyMeasurable
    rw [← integral_map (hT.iterate n).measurable.aemeasurable hgm, (hT.iterate n).map_eq]
  have hbi' : (∫ x, b x ∂μ) = μ.real B := by
    exact integral_indicator_one hB
  have hbme (M : ℕ) : (∫ x, ∑ i ∈ Finset.range M, b (T^[i] x) ∂μ) = M * μ.real B := by
    rw [integral_finsetSum _ (fun i _ => (hcomp b hbi i).1)]
    simp_rw [(hcomp b hbi _).2, hbi']
    simp
  have hfme (M : ℕ) : (∫ x, ∑ i ∈ Finset.range M, f (T^[i] x) ∂μ) = M * ∫ x, f x ∂μ := by
    rw [integral_finsetSum _ (fun i _ => (hcomp f hfi i).1)]
    simp_rw [(hcomp f hfi _).2]
    simp
  have hbound (M : ℕ) : a * ((M : ℝ) * μ.real B) ≤ ((M+K : ℕ) : ℝ) * ∫ x, f x ∂μ := by
    have hpt (x : Ω) : a * (∑ i ∈ Finset.range M, b (T^[i] x)) ≤
        ∑ i ∈ Finset.range (M+K), f (T^[i] x) := by
      apply nonnegative_interval_count a ha.le K _ _ (fun i => hfn _) (fun i => hb _)
      intro i hi
      have hmem : T^[i] x ∈ B := by
        by_contra h
        exact hi (Set.indicator_of_notMem h _)
      obtain ⟨k, hk, hkK, hkg⟩ := hmem
      refine ⟨k, hk, hkK, ?_⟩
      simpa only [← Function.iterate_add_apply, Nat.add_comm] using hkg.le
    have hintb : Integrable (fun x => a * ∑ i ∈ Finset.range M, b (T^[i] x)) μ :=
      (integrable_finsetSum _ (fun i _ => (hcomp b hbi i).1)).const_mul a
    have hintf : Integrable (fun x => ∑ i ∈ Finset.range (M+K), f (T^[i] x)) μ :=
      integrable_finsetSum _ (fun i _ => (hcomp f hfi i).1)
    have h := integral_mono hintb hintf hpt
    simpa only [integral_const_mul, hbme, hfme] using h
  change a * μ.real B ≤ ∫ x, f x ∂μ
  by_contra h
  have hδ : 0 < a * μ.real B - ∫ x, f x ∂μ := sub_pos.mpr (lt_of_not_ge h)
  obtain ⟨M, hM⟩ := exists_nat_gt ((K : ℝ) * (∫ x, f x ∂μ) /
    (a * μ.real B - ∫ x, f x ∂μ))
  have hgt := (div_lt_iff₀ hδ).mp hM
  have hle := hbound M
  push_cast at hle
  nlinarith

lemma integrable_min_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun x => min (f x) s) μ := by
  apply (integrable_const s).mono' (hf.min measurable_const).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hfn x) hs)]
    exact min_le_right _ _

noncomputable def truncatedMean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (s : ℝ) : ℝ := ∫ x, min (f x) s ∂μ

lemma truncatedMean_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hfn : ∀ x, 0 ≤ f x)
    {s : ℝ} (hs : 0 ≤ s) : 0 ≤ truncatedMean μ f s :=
  integral_nonneg fun x => le_min (hfn x) hs

lemma truncatedMean_mono {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    truncatedMean μ f s ≤ truncatedMean μ f t :=
  integral_mono (integrable_min_nonneg μ f hf hfn s hs)
    (integrable_min_nonneg μ f hf hfn t (hs.trans hst))
    (fun _ => min_le_min le_rfl hst)

lemma truncatedMean_mul_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) {s c : ℝ} (hs : 0 ≤ s) (hc : 1 ≤ c) :
    truncatedMean μ f (c*s) ≤ c * truncatedMean μ f s := by
  rw [truncatedMean, truncatedMean, ← integral_const_mul]
  apply integral_mono (integrable_min_nonneg μ f hf hfn _ (mul_nonneg (by linarith) hs))
    ((integrable_min_nonneg μ f hf hfn s hs).const_mul c)
  intro x
  dsimp only
  by_cases h : f x ≤ s
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (le_mul_of_one_le_left (hfn x) hc)
  · rw [min_eq_right (le_of_not_ge h)]
    exact min_le_right _ _

end DirectionalTransience
end
end

end OAI
