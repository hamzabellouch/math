import OAI.Dynamics.StandardMap.EntropyEndpoint

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace BoundedSubadditive

variable {X : Type*}

noncomputable def excess (T : X → X) (h : X → ℝ) (δ : ℝ) : ℕ → X → ℝ
  | 0, _ => 0
  | n + 1, x => max 0 (h x - δ + excess T h δ n (T x))

lemma excess_nonneg (T : X → X) (h : X → ℝ) (δ : ℝ) (n : ℕ) (x : X) :
    0 ≤ excess T h δ n x := by
  cases n with
  | zero => rfl
  | succ n => exact le_max_left _ _

lemma excess_succ_mono (T : X → X) (h : X → ℝ) (δ : ℝ) (n : ℕ) (x : X) :
    excess T h δ n x ≤ excess T h δ (n + 1) x := by
  induction n generalizing x with
  | zero => exact excess_nonneg T h δ 1 x
  | succ n ih =>
    exact max_le_max le_rfl (add_le_add le_rfl (ih (T x)))

lemma excess_mono (T : X → X) (h : X → ℝ) (δ : ℝ) (x : X) :
    Monotone (fun n => excess T h δ n x) :=
  monotone_nat_of_le_succ (fun n => excess_succ_mono T h δ n x)

lemma sum_sub_le_excess (T : X → X) (h : X → ℝ) (δ : ℝ) (n : ℕ) (x : X) :
    birkhoffSum T h n x - (n : ℝ) * δ ≤ excess T h δ n x := by
  induction n generalizing x with
  | zero => simp [birkhoffSum, excess]
  | succ n ih =>
    rw [birkhoffSum_succ_apply']
    have hm : h x - δ + excess T h δ n (T x) ≤ excess T h δ (n + 1) x :=
      le_max_right _ _
    have hi := ih (T x)
    push_cast
    linarith

lemma excess_account (T : X → X) (h : X → ℝ) (δ : ℝ)
    (hh : ∀ x, 0 ≤ h x) (n : ℕ) (x : X) :
    (if 0 < excess T h δ (n + 1) x then δ else 0) ≤
      h x + excess T h δ (n + 1) (T x) - excess T h δ (n + 1) x := by
  split_ifs with hp
  · have he : excess T h δ (n + 1) x = h x - δ + excess T h δ n (T x) := by
      apply max_eq_right
      change 0 < max 0 (h x - δ + excess T h δ n (T x)) at hp
      exact (lt_max_iff.mp hp).resolve_left (lt_irrefl 0) |>.le
    rw [he]
    linarith [excess_succ_mono T h δ n (T x)]
  · have he : excess T h δ (n + 1) x = 0 :=
      le_antisymm (not_lt.mp hp) (excess_nonneg T h δ _ x)
    rw [he]
    linarith [hh x, excess_nonneg T h δ (n + 1) (T x)]

section Measure
variable [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable {T : X → X} {h : X → ℝ} {δ : ℝ}

lemma measurable_excess (hT : Measurable T) (hh : Measurable h) (n : ℕ) :
    Measurable (excess T h δ n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_const.max ((hh.sub measurable_const).add (ih.comp hT))

lemma integrable_excess (hT : MeasurePreserving T μ μ) (hh : Integrable h μ) (n : ℕ) :
    Integrable (excess T h δ n) μ := by
  induction n with
  | zero => exact integrable_const 0
  | succ n ih =>
    exact (integrable_const (0 : ℝ)).sup
      ((hh.sub (integrable_const δ)).add (hT.integrable_comp_of_integrable ih))

omit [IsFiniteMeasure μ] in
lemma integral_comp (hT : MeasurePreserving T μ μ) {g : X → ℝ}
    (hg : AEStronglyMeasurable g μ) : (∫ x, g (T x) ∂μ) = ∫ x, g x ∂μ := by
  have hg' : AEStronglyMeasurable g (Measure.map T μ) := by rwa [hT.map_eq]
  simpa only [hT.map_eq] using (integral_map hT.measurable.aemeasurable hg').symm

lemma excess_measure_bound (hT : MeasurePreserving T μ μ) (hm : Measurable h)
    (hi : Integrable h μ) (h0 : ∀ x, 0 ≤ h x) (hδ : 0 < δ) (n : ℕ) :
    μ {x | 0 < excess T h δ n x} ≤ ENNReal.ofReal ((∫ x, h x ∂μ) / δ) := by
  cases n with
  | zero => simp [excess]
  | succ n =>
    let s : Set X := {x | 0 < excess T h δ (n + 1) x}
    have hs : MeasurableSet s := measurableSet_lt measurable_const
      (measurable_excess hT.measurable hm _)
    have he := integrable_excess (δ := δ) hT hi (n + 1)
    have heT : Integrable (fun x => excess T h δ (n + 1) (T x)) μ :=
      hT.integrable_comp_of_integrable he
    have hb : (∫ x, s.indicator (fun _ => δ) x ∂μ) ≤
        ∫ x, h x + excess T h δ (n + 1) (T x) - excess T h δ (n + 1) x ∂μ := by
      apply integral_mono ((integrable_const δ).indicator hs)
        ((hi.add heT).sub he)
      intro x
      simpa only [Set.indicator, s, Set.mem_ofPred_eq, Pi.sub_apply, Pi.add_apply, Function.comp_apply] using excess_account T h δ h0 n x
    have hsub := integral_sub (hi.add heT) he
    have hadd := integral_add hi heT
    simp only [Pi.add_apply] at hsub hadd
    rw [integral_indicator_const δ hs, hsub, hadd,
      integral_comp hT he.aestronglyMeasurable] at hb
    have hb' : μ.real s ≤ (∫ x, h x ∂μ) / δ := by
      apply (le_div_iff₀ hδ).mpr
      simpa only [smul_eq_mul, add_sub_cancel_right] using hb
    calc
      μ s = ENNReal.ofReal (μ.real s) := (ENNReal.ofReal_toReal (measure_ne_top μ s)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hb'

lemma maximal_measure_bound (hT : MeasurePreserving T μ μ) (hm : Measurable h)
    (hi : Integrable h μ) (h0 : ∀ x, 0 ≤ h x) (hδ : 0 < δ) :
    μ {x | ∃ n : ℕ, (n : ℝ) * δ < birkhoffSum T h n x} ≤
      ENNReal.ofReal ((∫ x, h x ∂μ) / δ) := by
  have hsub : {x | ∃ n : ℕ, (n : ℝ) * δ < birkhoffSum T h n x} ⊆
      ⋃ n : ℕ, {x | 0 < excess T h δ n x} := by
    rintro x ⟨n, hn⟩
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    exact lt_of_lt_of_le (sub_pos.mpr hn) (sum_sub_le_excess T h δ n x)
  refine (measure_mono hsub).trans ?_
  have hm' : Monotone (fun n : ℕ => {x | 0 < excess T h δ n x}) := by
    intro m n hmn x hx
    exact lt_of_lt_of_le hx (excess_mono T h δ x hmn)
  rw [hm'.measure_iUnion]
  exact iSup_le (fun n => excess_measure_bound hT hm hi h0 hδ n)

end Measure

structure Cocycle (X : Type*) [MeasurableSpace X] (T : X → X) where
  value : ℕ → X → ℝ
  measurable : ∀ n, Measurable (value n)
  nonneg : ∀ n x, 0 ≤ value n x
  le_time : ∀ n x, value n x ≤ n
  subadd : ∀ m n x, value (m + n) x ≤ value m x + value n (T^[m] x)
  shift_bound : ∀ n x, |value n (T x) - value n x| ≤ 2

namespace Cocycle
variable [MeasurableSpace X] {T : X → X} (f : Cocycle X T)

noncomputable def average (n : ℕ) (x : X) : ℝ := f.value n x / (n : ℝ)
noncomputable def lowerRate (x : X) : ℝ := liminf (fun n => f.average n x) atTop
noncomputable def upperRate (x : X) : ℝ := limsup (fun n => f.average n x) atTop

lemma average_bounds (n : ℕ) (x : X) : 0 ≤ f.average n x ∧ f.average n x ≤ 1 := by
  refine ⟨div_nonneg (f.nonneg n x) (Nat.cast_nonneg n), ?_⟩
  by_cases hn : n = 0
  · simp [average, hn]
  · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr (f.le_time n x)

lemma average_bdd_above (x : X) : IsBoundedUnder (· ≤ ·) atTop (fun n => f.average n x) :=
  isBoundedUnder_of ⟨1, fun n => (f.average_bounds n x).2⟩

lemma average_bdd_below (x : X) : IsBoundedUnder (· ≥ ·) atTop (fun n => f.average n x) :=
  isBoundedUnder_of ⟨0, fun n => (f.average_bounds n x).1⟩

lemma lowerRate_bounds (x : X) : 0 ≤ f.lowerRate x ∧ f.lowerRate x ≤ 1 := by
  constructor
  · exact le_liminf_of_le (f.average_bdd_above x).isCoboundedUnder_ge
      (Eventually.of_forall fun n => (f.average_bounds n x).1)
  · have hh := liminf_le_liminf (Eventually.of_forall fun n => (f.average_bounds n x).2)
      (f.average_bdd_below x) (isBoundedUnder_const.isCoboundedUnder_ge)
    simpa only [liminf_const, lowerRate] using hh

lemma lowerRate_le_upperRate (x : X) : f.lowerRate x ≤ f.upperRate x :=
  liminf_le_limsup (f.average_bdd_above x) (f.average_bdd_below x)

lemma measurable_average (n : ℕ) : Measurable (f.average n) :=
  (f.measurable n).div_const _

lemma measurable_lowerRate : Measurable f.lowerRate :=
  Measurable.liminf (fun n => f.measurable_average n)

lemma measurable_upperRate : Measurable f.upperRate :=
  Measurable.limsup (fun n => f.measurable_average n)

lemma average_shift_bound (n : ℕ) (x : X) :
    |f.average n (T x) - f.average n x| ≤ 2 / (n : ℝ) := by
  rw [average, average, ← sub_div, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]
  exact div_le_div_of_nonneg_right (f.shift_bound n x) (Nat.cast_nonneg n)

lemma lowerRate_shift (x : X) : f.lowerRate (T x) = f.lowerRate x := by
  have hc : Tendsto (fun n : ℕ => (2 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have haux (a b : X) (hab : ∀ n, f.average n a - f.average n b ≤ 2 / (n : ℝ)) :
      f.lowerRate a ≤ f.lowerRate b := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have he : ∀ᶠ n : ℕ in atTop, f.average n a ≤ f.average n b + ε := by
      filter_upwards [hc.eventually (gt_mem_nhds hε)] with n hn
      linarith [hab n]
    have hb : IsBoundedUnder (· ≤ ·) atTop (fun n => f.average n b + ε) :=
      isBoundedUnder_of ⟨1 + ε, fun n => add_le_add (f.average_bounds n b).2 le_rfl⟩
    have hh := liminf_le_liminf he (f.average_bdd_below a) hb.isCoboundedUnder_ge
    rw [liminf_add_const atTop (fun n => f.average n b) ε
      (f.average_bdd_above b).isCoboundedUnder_ge (f.average_bdd_below b)] at hh
    exact hh
  apply le_antisymm
  · exact haux (T x) x (fun n => (abs_le.mp (f.average_shift_bound n x)).2)
  · apply haux x (T x)
    intro n
    have hh := (abs_le.mp (f.average_shift_bound n x)).1
    linarith

lemma lowerRate_iterate (n : ℕ) (x : X) : f.lowerRate (T^[n] x) = f.lowerRate x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', f.lowerRate_shift, ih]

noncomputable def badSet (ε : ℝ) (N : ℕ) : Set X :=
  (⋃ n ∈ Set.Ioc 0 N, {x | f.value n x ≤ (n : ℝ) * (f.lowerRate x + ε)})ᶜ

noncomputable def badObservation (ε : ℝ) (N : ℕ) : X → ℝ :=
  (f.badSet ε N).indicator (fun _ => 1)

lemma measurableSet_badSet (ε : ℝ) (N : ℕ) : MeasurableSet (f.badSet ε N) := by
  apply MeasurableSet.compl
  apply MeasurableSet.biUnion (Set.to_countable _)
  intro n hn
  exact measurableSet_le (f.measurable n)
    (measurable_const.mul (f.measurable_lowerRate.add_const ε))

lemma measurable_badObservation (ε : ℝ) (N : ℕ) : Measurable (f.badObservation ε N) :=
  measurable_const.indicator (f.measurableSet_badSet ε N)

lemma badObservation_bounds (ε : ℝ) (N : ℕ) (x : X) :
    0 ≤ f.badObservation ε N x ∧ f.badObservation ε N x ≤ 1 := by
  classical
  by_cases hx : x ∈ f.badSet ε N <;> simp [badObservation, hx]

lemma exists_good_block (x : X) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ f.value n x ≤ (n : ℝ) * (f.lowerRate x + ε) := by
  have hh : ∃ᶠ n : ℕ in atTop, f.average n x < f.lowerRate x + ε :=
    frequently_lt_of_liminf_lt (f.average_bdd_above x).isCoboundedUnder_ge (lt_add_of_pos_right _ hε)
  obtain ⟨n, hn, he⟩ := frequently_atTop.mp hh 1
  have hn' : 0 < n := by omega
  refine ⟨n, hn', ?_⟩
  have hi := (div_lt_iff₀ (Nat.cast_pos.mpr hn')).mp he
  nlinarith

lemma badObservation_tendsto_zero (x : X) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => f.badObservation ε N x) atTop (𝓝 0) := by
  obtain ⟨n, hn, hg⟩ := f.exists_good_block x ε hε
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with N hN
  symm
  apply Set.indicator_of_notMem
  simp only [badSet, mem_compl_iff, mem_iUnion, mem_ofPred_eq, not_not]
  exact ⟨n, ⟨hn, hN⟩, hg⟩

lemma birkhoff_bad_nonneg (ε : ℝ) (N n : ℕ) (x : X) :
    0 ≤ birkhoffSum T (f.badObservation ε N) n x := by
  exact Finset.sum_nonneg fun i hi => (f.badObservation_bounds ε N (T^[i] x)).1

lemma block_bound (ε : ℝ) (hε : 0 ≤ ε) (N n : ℕ) (x : X) :
    f.value n x ≤ (n : ℝ) * (f.lowerRate x + ε) +
      birkhoffSum T (f.badObservation ε N) n x + (N : ℝ) := by
  classical
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    have ha : 0 ≤ f.lowerRate x + ε := add_nonneg (f.lowerRate_bounds x).1 hε
    by_cases hn : n ≤ N
    · have hcast : (n : ℝ) ≤ N := by exact_mod_cast hn
      have hp := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) ha
      linarith [f.le_time n x, f.birkhoff_bad_nonneg ε N n x]
    · by_cases hx : x ∈ f.badSet ε N
      · have hn0 : 1 ≤ n := by omega
        have he : 1 + (n - 1) = n := by omega
        have hs := f.subadd 1 (n - 1) x
        simp only [he, Function.iterate_one] at hs
        have hi := ih (n - 1) (by omega) (T x)
        rw [f.lowerRate_shift] at hi
        rw [Nat.cast_sub hn0, Nat.cast_one, sub_mul, one_mul] at hi
        have hb : f.badObservation ε N x = 1 := by simp [badObservation, hx]
        have hsum : birkhoffSum T (f.badObservation ε N) n x =
            1 + birkhoffSum T (f.badObservation ε N) (n - 1) (T x) := by
          conv_lhs => rw [show n = (n - 1) + 1 by omega]
          rw [birkhoffSum_succ_apply', hb]
        rw [hsum]
        have h1 := f.le_time 1 x
        norm_num only [Nat.cast_one] at h1
        linarith
      · have hg : x ∈ ⋃ m ∈ Set.Ioc 0 N,
            {y | f.value m y ≤ (m : ℝ) * (f.lowerRate y + ε)} := not_not.mp hx
        obtain ⟨m, hgm⟩ := mem_iUnion.mp hg
        obtain ⟨hm, hfm⟩ := mem_iUnion.mp hgm
        have hmn : m ≤ n := by have := hm.2; omega
        have he : m + (n - m) = n := Nat.add_sub_of_le hmn
        have hs := f.subadd m (n - m) x
        rw [he] at hs
        have hi := ih (n - m) (by have := hm.1; omega) (T^[m] x)
        rw [f.lowerRate_iterate, Nat.cast_sub hmn, sub_mul] at hi
        have hsum : birkhoffSum T (f.badObservation ε N) n x =
            birkhoffSum T (f.badObservation ε N) m x +
              birkhoffSum T (f.badObservation ε N) (n - m) (T^[m] x) := by
          simpa only [he] using birkhoffSum_add_right_apply T (f.badObservation ε N) m (n - m) x
        rw [hsum]
        have hp := f.birkhoff_bad_nonneg ε N m x
        change f.value m x ≤ (m : ℝ) * (f.lowerRate x + ε) at hfm
        linarith

lemma upperRate_le_of_bad_averages (ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) (δ : ℝ) (x : X)
    (hb : ∀ n, birkhoffSum T (f.badObservation ε N) n x ≤ (n : ℝ) * δ) :
    f.upperRate x ≤ f.lowerRate x + ε + δ := by
  apply le_of_forall_pos_le_add
  intro γ hγ
  have hc : Tendsto (fun n : ℕ => (N : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply limsup_le_of_le (f.average_bdd_below x).isCoboundedUnder_le
  filter_upwards [hc.eventually (gt_mem_nhds hγ), eventually_gt_atTop 0] with n hsmall hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hN := (div_lt_iff₀ hn').mp hsmall
  apply (div_le_iff₀ hn').mpr
  have hB := f.block_bound ε hε N n x
  have hbad := hb n
  nlinarith

section Measure
variable {μ : Measure X} [IsFiniteMeasure μ]

lemma integrable_badObservation (ε : ℝ) (N : ℕ) :
    Integrable (f.badObservation ε N) μ :=
  (integrable_const (1 : ℝ)).indicator (f.measurableSet_badSet ε N)

lemma integral_badObservation_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => ∫ x, f.badObservation ε N x ∂μ) atTop (𝓝 0) := by
  have hh := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ : X => (1 : ℝ))
    (fun N => (f.measurable_badObservation ε N).aestronglyMeasurable)
    (integrable_const 1)
    (fun N => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (f.badObservation_bounds ε N x).1]
      exact (f.badObservation_bounds ε N x).2)
    (Eventually.of_forall fun x => f.badObservation_tendsto_zero x ε hε)
  simpa only [integral_zero] using hh

lemma ae_upperRate_le_add (hT : MeasurePreserving T μ μ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ x ∂μ, f.upperRate x ≤ f.lowerRate x + 2 * ε := by
  let E : Set X := {x | f.lowerRate x + 2 * ε < f.upperRate x}
  have hbound (N : ℕ) : μ E ≤
      ENNReal.ofReal ((∫ x, f.badObservation ε N x ∂μ) / ε) := by
    have hsub : E ⊆ {x | ∃ n : ℕ, (n : ℝ) * ε < birkhoffSum T (f.badObservation ε N) n x} := by
      intro x hx
      by_contra hn
      change ¬ ∃ n : ℕ, (n : ℝ) * ε < birkhoffSum T (f.badObservation ε N) n x at hn
      push Not at hn
      have hh := f.upperRate_le_of_bad_averages ε hε.le N ε x hn
      change f.lowerRate x + 2 * ε < f.upperRate x at hx
      linarith
    exact (measure_mono hsub).trans
      (maximal_measure_bound hT (f.measurable_badObservation ε N)
        (f.integrable_badObservation ε N) (fun x => (f.badObservation_bounds ε N x).1) hε)
  have hc : Tendsto (fun N => ENNReal.ofReal ((∫ x, f.badObservation ε N x ∂μ) / ε))
      atTop (𝓝 0) := by
    have hh := (f.integral_badObservation_tendsto_zero (μ := μ) ε hε).div_const ε
    simpa only [Function.comp_def, zero_div, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hh
  have hzero : μ E = 0 := le_antisymm (ge_of_tendsto' hc hbound) zero_le
  simpa only [ae_iff, not_le] using hzero

theorem ae_tendsto_average (hT : MeasurePreserving T μ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => f.average n x) atTop (𝓝 (f.lowerRate x)) := by
  have ha : ∀ᵐ x ∂μ, ∀ j : ℕ, f.upperRate x ≤ f.lowerRate x + 2 * (1 / ((j : ℝ) + 1)) := by
    apply ae_all_iff.mpr
    intro j
    exact f.ae_upperRate_le_add hT _ (by positivity)
  filter_upwards [ha] with x hx
  have hc : Tendsto (fun j : ℕ => f.lowerRate x + 2 * (1 / ((j : ℝ) + 1)))
      atTop (𝓝 (f.lowerRate x)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hu : f.upperRate x ≤ f.lowerRate x := ge_of_tendsto' hc hx
  exact tendsto_of_le_liminf_of_limsup_le le_rfl hu
    (f.average_bdd_above x) (f.average_bdd_below x)

lemma integrable_lowerRate : Integrable f.lowerRate μ :=
  (integrable_const (1 : ℝ)).mono' f.measurable_lowerRate.aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (f.lowerRate_bounds x).1]
      exact (f.lowerRate_bounds x).2)

lemma integrable_average (n : ℕ) : Integrable (f.average n) μ :=
  (integrable_const (1 : ℝ)).mono' (f.measurable_average n).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (f.average_bounds n x).1]
      exact (f.average_bounds n x).2)

theorem tendsto_integral_average (hT : MeasurePreserving T μ μ) :
    Tendsto (fun n => ∫ x, f.average n x ∂μ) atTop (𝓝 (∫ x, f.lowerRate x ∂μ)) := by
  exact tendsto_integral_of_dominated_convergence (fun _ : X => (1 : ℝ))
    (fun n => (f.measurable_average n).aestronglyMeasurable) (integrable_const 1)
    (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (f.average_bounds n x).1]
      exact (f.average_bounds n x).2)
    (f.ae_tendsto_average hT)

end Measure
end Cocycle
end BoundedSubadditive

namespace StandardMapEntropy
open BoundedSubadditive

lemma torusIter_nat_apply (k : ℝ) (n : ℕ) (z : Torus) :
    torusIter k (n : ℤ) z = (torusStep k)^[n] z := by
  simp only [torusIter, zpow_natCast, Equiv.Perm.coe_pow]

lemma productDistance_one_shift_bound (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (z : Torus) :
    |productDistance k (torusStep k z) 0 (n : ℤ) - productDistance k z 0 (n : ℤ)| ≤ 2 := by
  have ht : torusStep k z = torusIter k 1 z := by
    simp only [torusIter, zpow_one]
  rw [ht, productDistance_shift]
  simp only [zero_add]
  have h10 := productDistance_le k hk z 1 0
  have h01 := productDistance_le k hk z 0 1
  have hnn := productDistance_le k hk z (n : ℤ) ((n : ℤ) + 1)
  have hnn' := productDistance_le k hk z ((n : ℤ) + 1) (n : ℤ)
  norm_num only [Int.cast_one, Int.cast_zero, zero_sub, sub_zero, abs_neg, abs_one] at h10 h01
  have hncast : (((n : ℤ) + 1 : ℤ) : ℝ) = (n : ℝ) + 1 := by push_cast; rfl
  rw [hncast, Int.cast_natCast, add_sub_cancel_left, abs_one] at hnn
  rw [hncast, Int.cast_natCast, sub_add_cancel_left, abs_neg, abs_one] at hnn'
  apply abs_le.mpr
  constructor
  · have h1 := productDistance_triangle k hk z 0 1 (n : ℤ)
    have h2 := productDistance_triangle k hk z 1 ((n : ℤ) + 1) (n : ℤ)
    linarith
  · have h1 := productDistance_triangle k hk z 1 0 ((n : ℤ) + 1)
    have h2 := productDistance_triangle k hk z 0 (n : ℤ) ((n : ℤ) + 1)
    linarith

noncomputable def transferCocycle (k : ℝ) (hk : 0 ≤ k) : Cocycle Torus (torusStep k) where
  value n z := productDistance k z 0 (n : ℤ)
  measurable n := (continuous_productDistance k hk 0 (n : ℤ)).measurable
  nonneg n z := productDistance_nonneg k hk z 0 (n : ℤ)
  le_time n z := by simpa using productDistance_le k hk z 0 (n : ℤ)
  subadd m n z := by
    have hh := productDistance_triangle k hk z 0 (m : ℤ) ((m : ℤ) + (n : ℤ))
    rw [← torusIter_nat_apply, productDistance_shift]
    simpa only [Nat.cast_add, zero_add, add_zero, add_comm] using hh
  shift_bound n z := productDistance_one_shift_bound k hk n z

noncomputable def transferLyapunov (k : ℝ) (hk : 0 ≤ k) (z : Torus) : ℝ :=
  Real.log (growthBase k) * (transferCocycle k hk).lowerRate z

def TransferLimit (k : ℝ) (L : Torus → ℝ) : Prop :=
  Measurable L ∧ Integrable L area ∧ (∀ z, 0 ≤ L z) ∧
  (∀ z, L (torusStep k z) = L z) ∧
  ∀ᵐ z ∂area, Tendsto
    (fun n : ℕ => Real.log ‖torusSegmentTransfer k z 0 n‖ / (n : ℝ))
    atTop (𝓝 (L z))

lemma lognorm_average_eq (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (z : Torus) :
    Real.log ‖torusSegmentTransfer k z 0 n‖ / (n : ℝ) =
      Real.log (growthBase k) * (transferCocycle k hk).average n z := by
  change _ = Real.log (growthBase k) * (productDistance k z 0 (n : ℤ) / (n : ℝ))
  have hf : productDistance k z 0 (n : ℤ) =
      Real.log ‖torusSegmentTransfer k z 0 n‖ / Real.log (growthBase k) := by
    simpa only [zero_add] using productDistance_forward k z 0 n
  rw [hf]
  have hlog := (log_growthBase_pos k hk).ne'
  calc
    _ = (Real.log (growthBase k) * (Real.log ‖torusSegmentTransfer k z 0 n‖ /
        Real.log (growthBase k))) / (n : ℝ) := by rw [mul_div_cancel₀ _ hlog]
    _ = _ := by ring

lemma transferLyapunov_limit (k : ℝ) (hk : 0 ≤ k) :
    TransferLimit k (transferLyapunov k hk) := by
  let f := transferCocycle k hk
  refine ⟨measurable_const.mul f.measurable_lowerRate,
    f.integrable_lowerRate.const_mul _, ?_, ?_, ?_⟩
  · intro z
    exact mul_nonneg (log_growthBase_pos k hk).le (f.lowerRate_bounds z).1
  · intro z
    exact congrArg (fun a => Real.log (growthBase k) * a) (f.lowerRate_shift z)
  · filter_upwards [f.ae_tendsto_average (measurePreserving_torusStep k)] with z hz
    have hh : Tendsto (fun n => Real.log (growthBase k) * f.average n z) atTop
        (𝓝 (Real.log (growthBase k) * f.lowerRate z)) := tendsto_const_nhds.mul hz
    simpa only [transferLyapunov, f, ← lognorm_average_eq] using hh

theorem ae_transfer_limit (k : ℝ) (hk : 0 ≤ k) :
    ∃ L : Torus → ℝ, TransferLimit k L :=
  ⟨transferLyapunov k hk, transferLyapunov_limit k hk⟩

lemma integral_lowerRate_of_deficit (k : ℝ) (hk : 0 ≤ k) (η : ℝ)
    (hdef : ∀ n : ℕ, 0 < n → meanDeficit k n < η) :
    1 - η ≤ ∫ z, (transferCocycle k hk).lowerRate z ∂area := by
  have hc := (transferCocycle k hk).tendsto_integral_average (measurePreserving_torusStep k)
  apply ge_of_tendsto hc
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hh := hdef n hn
  have he : (∫ z, (transferCocycle k hk).average n z ∂area) =
      (∫ z, productDistance k z 0 (n : ℤ) ∂area) / (n : ℝ) := by
    change (∫ z, productDistance k z 0 (n : ℤ) / (n : ℝ) ∂area) = _
    exact integral_div (n : ℝ) _
  rw [he]
  unfold meanDeficit at hh
  linarith

lemma positive_transferLyapunov_of_deficit (k : ℝ) (hk : 0 ≤ k)
    (hdef : ∀ n : ℕ, 0 < n → meanDeficit k n < (1 / 8 : ℝ)) :
    0 < area {z | 0 < transferLyapunov k hk z} := by
  have hl := integral_lowerRate_of_deficit k hk (1 / 8) hdef
  have hI : 0 < ∫ z, transferLyapunov k hk z ∂area := by
    unfold transferLyapunov
    rw [integral_const_mul]
    exact mul_pos (log_growthBase_pos k hk) (by linarith)
  by_contra hh
  have hz : area {z | 0 < transferLyapunov k hk z} = 0 :=
    le_antisymm (not_lt.mp hh) zero_le
  have hae : ∀ᵐ z ∂area, transferLyapunov k hk z = 0 := by
    have hnone : ∀ᵐ z ∂area, ¬ 0 < transferLyapunov k hk z := by
      simpa only [ae_iff, not_not] using hz
    filter_upwards [hnone] with z hnot
    exact le_antisymm (not_lt.mp hnot) ((transferLyapunov_limit k hk).2.2.1 z)
  have hi : (∫ z, transferLyapunov k hk z ∂area) = 0 := by
    rw [integral_congr_ae hae, integral_zero]
  linarith

theorem positive_transfer_limit :
    ∃ k₀ : ℝ, 0 < k₀ ∧ ∀ k : ℝ, k₀ ≤ k →
      ∃ L : Torus → ℝ, TransferLimit k L ∧ 0 < area {z | 0 < L z} := by
  obtain ⟨K, hK, hdef⟩ := eventually_meanDeficit_small (1 / 8 : ℝ) (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro k hk
  have hk0 : 0 ≤ k := (hK.trans_le hk).le
  exact ⟨transferLyapunov k hk0, transferLyapunov_limit k hk0,
    positive_transferLyapunov_of_deficit k hk0 (hdef k hk)⟩

end StandardMapEntropy

end
end

end OAI
