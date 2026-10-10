import Mathlib
import OAI.Probability.Ballisticity.Estimates.FirstBelow

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma inverse_moment_of_geometric_tail {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ≥0∞) (hf : Measurable f)
    (hp : ∀ᵐ x ∂μ, 0 < f x ∧ f x ≠ ∞)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ < 1) {ρ : ℝ≥0∞} (hρ : ρ < 1)
    (htail : ∀ j : ℕ, μ {x | f x < ((δ ^ (j + 1) : ℝ≥0) : ℝ≥0∞)} ≤ ρ ^ j) :
    ∃ lam : ℝ, 0 < lam ∧ (∫⁻ x, f x ^ (-lam) ∂μ) < ∞ := by
  obtain ⟨lam, hlam, hr⟩ := exists_inverse_geometric_ratio hδ hρ
  let c : ℝ≥0∞ := ((δ ^ (-lam) : ℝ≥0) : ℝ≥0∞)
  let E := fun j : ℕ => {x | f x < ((δ ^ (j + 1) : ℝ≥0) : ℝ≥0∞)}
  have hE (j : ℕ) : MeasurableSet (E j) := measurableSet_lt hf measurable_const
  have hbound : ∀ᵐ x ∂μ, f x ^ (-lam) ≤ c + ∑' j : ℕ, (E j).indicator (fun _ => c ^ (j + 2)) x := by
    filter_upwards [hp] with x hx
    have hh := inverse_power_le_series hδ hδ1 hlam (ENNReal.toNNReal_pos hx.1.ne' hx.2)
    rw [ENNReal.coe_rpow_of_ne_zero (ENNReal.toNNReal_pos hx.1.ne' hx.2).ne', ENNReal.coe_toNNReal hx.2] at hh
    convert hh using 1
    congr 1
    apply tsum_congr
    intro j
    simp only [Set.indicator, E, Set.mem_ofPred_eq, Set.mem_Iio]
    have heq : (f x).toNNReal < δ ^ (j + 1) ↔ f x < ((δ ^ (j + 1) : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hx.2]
    simp only [heq, c]
  have hi : (∫⁻ x, f x ^ (-lam) ∂μ) ≤ c + ∑' j : ℕ, c ^ (j + 2) * ρ ^ j := by
    apply (lintegral_mono_ae hbound).trans
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_tsum (fun j => (measurable_const.indicator (hE j)).aemeasurable)]
    refine add_le_add le_rfl ?_
    apply ENNReal.tsum_le_tsum
    intro j
    rw [lintegral_indicator (hE j), lintegral_const, Measure.restrict_apply_univ]
    exact mul_le_mul' le_rfl (htail j)
  have heq : (∑' j : ℕ, c ^ (j + 2) * ρ ^ j) = c ^ 2 * (1 - c * ρ)⁻¹ := by
    simp_rw [pow_add, mul_right_comm (c ^ _) (c ^ 2), ← mul_pow]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, mul_comm]
  refine ⟨lam, hlam, lt_of_le_of_lt hi ?_⟩
  rw [heq]
  apply ENNReal.add_lt_top.mpr
  constructor
  · exact ENNReal.coe_lt_top
  · apply ENNReal.mul_lt_top (by simp [c])
    exact ENNReal.inv_lt_top.mpr (tsub_pos_iff_lt.mpr (by simpa [mul_comm] using hr))

lemma exists_positive_step {d : ℕ} (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1) :
    ∃ e : Direction d, 0 < dot (realPosition (step e)) ℓ := by
  have hn : ∃ i, ℓ i ≠ 0 := by
    by_contra h
    push Not at h
    have hz : dot ℓ ℓ = 0 := by simp [dot, h]
    linarith
  obtain ⟨i, hi⟩ := hn
  rcases lt_or_gt_of_ne hi with hi | hi
  · refine ⟨(i, false), ?_⟩
    simpa [dot, realPosition, step] using neg_pos.mpr hi
  · refine ⟨(i, true), ?_⟩
    simpa [dot, realPosition, step] using hi

lemma quenched_noDrop_positive_of_directionallyTransient {d : ℕ}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ x, 0 < noDropQuenched ℓ x ω := by
  obtain ⟨e, he⟩ := exists_positive_step ℓ hℓ
  exact noDropQuenched_positive_ae ν hue ℓ e he
    (noDrop_positive_of_directionallyTransient ν ℓ htrans)

lemma noDrop_inverse_moment {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) :
    ∃ lam : ℝ, 0 < lam ∧
      (∫⁻ ω, noDropQuenched ℓ 0 ω ^ (-lam) ∂environmentLaw ν) < ∞ := by
  obtain ⟨e, he⟩ := exists_positive_step ℓ hℓ
  obtain ⟨δ, ρ, hδ, hδ1, hρ, htail⟩ := noDrop_geometric_tail ν hue ℓ e he htrans
  apply inverse_moment_of_geometric_tail (environmentLaw ν) (noDropQuenched ℓ 0)
    (measurable_noDropQuenched ℓ 0) _ hδ hδ1 hρ htail
  filter_upwards [quenched_noDrop_positive_of_directionallyTransient ν hue ℓ hℓ htrans] with ω hω
  exact ⟨hω 0, measure_ne_top _ _⟩

lemma integer_quantile (μ : Measure ℤ) [IsFiniteMeasure μ]
    {t : ℝ≥0∞} (ht : 0 < t) (htμ : t < μ Set.univ) :
    ∃ j : ℤ, t ≤ μ (Set.Iic j) ∧ μ (Set.Iio j) < t := by
  have hbot : Tendsto (fun j : ℤ => μ (Set.Iic j)) atBot (𝓝 0) := by
    have hi : (⋂ j : ℤ, Set.Iic j) = ∅ := by
      ext z
      simp only [Set.mem_iInter, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
      push Not
      exact ⟨z - 1, by omega⟩
    have h := tendsto_measure_iInter_atBot
      (μ := μ) (s := fun j : ℤ => Set.Iic j)
      (fun _ => (measurableSet_Iic).nullMeasurableSet)
      (fun _ _ hab => Set.Iic_subset_Iic.mpr hab)
      ⟨0, measure_ne_top μ _⟩
    simpa only [hi, measure_empty, Function.comp_def] using h
  obtain ⟨b, hb⟩ := (hbot.eventually_lt_const ht).exists
  obtain ⟨k, hk⟩ := ((tendsto_measure_Iic_atTop μ).eventually_const_lt htμ).exists
  obtain ⟨j, hj, hleast⟩ := Int.exists_least_of_bdd
    (P := fun j => t ≤ μ (Set.Iic j))
    ⟨b, fun z hz => by
      by_contra hzb
      have hzμ : μ (Set.Iic z) ≤ μ (Set.Iic b) :=
        measure_mono (Set.Iic_subset_Iic.mpr (by omega))
      exact (not_lt_of_ge (hz.trans hzμ)) hb⟩
    ⟨k, hk.le⟩
  refine ⟨j, hj, ?_⟩
  have hi : Set.Iio j = Set.Iic (j - 1) := by
    ext z
    simp only [Set.mem_Iio, Set.mem_Iic]
    omega
  rw [hi]
  apply lt_of_not_ge
  intro h
  have := hleast (j - 1) h
  omega

lemma order_mass_cut (μ ν : Measure ℤ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ Set.univ ≤ 1) (hν : ν Set.univ ≤ 1) (R : ℤ) :
    let Q := (μ.prod ν) {p : ℤ × ℤ | p.1 + R ≤ p.2}
    ∃ j : ℤ, Q / 2 ≤ μ (Set.Iic j) ∧ Q / 2 ≤ ν (Set.Ici (j + R)) := by
  dsimp only
  let Q := (μ.prod ν) {p : ℤ × ℤ | p.1 + R ≤ p.2}
  change ∃ j : ℤ, Q / 2 ≤ μ (Set.Iic j) ∧ Q / 2 ≤ ν (Set.Ici (j + R))
  by_cases hQ : Q = 0
  · exact ⟨0, by simp [hQ], by simp [hQ]⟩
  have hQμ : Q ≤ μ Set.univ := by
    calc
      Q ≤ (μ.prod ν) (Set.univ ×ˢ Set.univ) := measure_mono (by simp)
      _ = μ Set.univ * ν Set.univ := Measure.prod_prod _ _
      _ ≤ μ Set.univ := mul_le_of_le_one_right zero_le hν
  have hQt : Q ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top μ _) hQμ
  obtain ⟨j, hj, hjprev⟩ := integer_quantile μ (ENNReal.half_pos hQ)
    ((ENNReal.half_lt_self hQ hQt).trans_le hQμ)
  refine ⟨j, hj, ?_⟩
  by_contra hnot
  have hjright : ν (Set.Ici (j + R)) < Q / 2 := lt_of_not_ge hnot
  have hsub : {p : ℤ × ℤ | p.1 + R ≤ p.2} ⊆
      (Set.Iio j ×ˢ Set.univ) ∪ (Set.univ ×ˢ Set.Ici (j + R)) := by
    intro p hp
    by_cases h : p.1 < j
    · exact Or.inl ⟨h, Set.mem_univ _⟩
    · refine Or.inr ⟨Set.mem_univ _, ?_⟩
      change p.1 + R ≤ p.2 at hp
      change j + R ≤ p.2
      omega
  have bound : Q < Q := calc
    Q ≤ (μ.prod ν) ((Set.Iio j ×ˢ Set.univ) ∪
        (Set.univ ×ˢ Set.Ici (j + R))) := measure_mono hsub
    _ ≤ (μ.prod ν) (Set.Iio j ×ˢ Set.univ) +
        (μ.prod ν) (Set.univ ×ˢ Set.Ici (j + R)) := measure_union_le _ _
    _ = μ (Set.Iio j) * ν Set.univ + μ Set.univ * ν (Set.Ici (j + R)) := by
      rw [Measure.prod_prod, Measure.prod_prod]
    _ ≤ μ (Set.Iio j) + ν (Set.Ici (j + R)) :=
      add_le_add (mul_le_of_le_one_right zero_le hν)
        (mul_le_of_le_one_left zero_le hμ)
    _ < Q / 2 + Q / 2 := ENNReal.add_lt_add hjprev hjright
    _ = Q := ENNReal.add_halves Q
  exact (lt_irrefl Q) bound

def lowerClip (n : ℕ) (x : ℝ) : ℝ := max x (-(n : ℝ))

lemma lowerClip_tendsto (x : ℝ) :
    Tendsto (fun n => lowerClip n x) atTop (𝓝 x) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (-x)
  have heq : (fun n => lowerClip n x) =ᶠ[atTop] (fun _ => x) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
    exact max_eq_left (by linarith)
  exact (tendsto_congr' heq).mpr tendsto_const_nhds

lemma lowerClip_sub_bound (n : ℕ) (x y g : ℝ) (hg : g ≤ y - x) :
    |min g (lowerClip n y - lowerClip n x)| ≤ |g| := by
  have hd : min g 0 ≤ lowerClip n y - lowerClip n x := by
    rcases le_total x (-(n : ℝ)) with hx | hx
    · rw [lowerClip, lowerClip, max_eq_right hx]
      have := le_max_right y (-(n : ℝ))
      have := min_le_right g 0
      linarith
    · rw [lowerClip, lowerClip, max_eq_left hx]
      have := le_max_left y (-(n : ℝ))
      have := min_le_left g 0
      linarith
  apply abs_le.mpr
  constructor
  · apply le_min
    · exact neg_abs_le g
    · exact (le_min (neg_abs_le g) (by simp)).trans hd
  · exact (min_le_left _ _).trans (le_abs_self g)

lemma integral_le_zero_of_identDistrib_lower_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {X Y G : α → ℝ} (hXY : IdentDistrib X Y μ μ)
    (hX : ∀ᵐ a ∂μ, X a ≤ 0) (hY : ∀ᵐ a ∂μ, Y a ≤ 0)
    (hG : Integrable G μ) (hlower : ∀ᵐ a ∂μ, G a ≤ Y a - X a) :
    ∫ a, G a ∂μ ≤ 0 := by
  let D : ℕ → α → ℝ := fun n a => lowerClip n (Y a) - lowerClip n (X a)
  let F : ℕ → α → ℝ := fun n a => min (G a) (D n a)
  have hclipmeas (n : ℕ) : Measurable (lowerClip n) :=
    measurable_id.max measurable_const
  have hclipint (Z : α → ℝ) (hZm : AEMeasurable Z μ)
      (hZ : ∀ᵐ a ∂μ, Z a ≤ 0) (n : ℕ) :
      Integrable (fun a => lowerClip n (Z a)) μ := by
    apply Integrable.of_bound ((hclipmeas n).comp_aemeasurable hZm).aestronglyMeasurable n
    filter_upwards [hZ] with a ha
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · exact le_max_right _ _
    · show max (Z a) (-(n : ℝ)) ≤ (n : ℝ)
      exact max_le (ha.trans (Nat.cast_nonneg n)) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hDX (n : ℕ) := hclipint X hXY.aemeasurable_fst hX n
  have hDY (n : ℕ) := hclipint Y hXY.aemeasurable_snd hY n
  have hDint (n : ℕ) : Integrable (D n) μ := (hDY n).sub (hDX n)
  have hFm (n : ℕ) : AEStronglyMeasurable (F n) μ :=
    (hG.aemeasurable.min (hDint n).aemeasurable).aestronglyMeasurable
  have hFbound (n : ℕ) : ∀ᵐ a ∂μ, ‖F n a‖ ≤ |G a| := by
    filter_upwards [hlower] with a ha
    exact lowerClip_sub_bound n (X a) (Y a) (G a) ha
  have hFint (n : ℕ) : Integrable (F n) μ :=
    hG.abs.mono' (hFm n) (hFbound n)
  have hDzero (n : ℕ) : ∫ a, D n a ∂μ = 0 := by
    rw [show D n = (fun a => lowerClip n (Y a) - lowerClip n (X a)) from rfl,
      integral_sub (hDY n) (hDX n)]
    have hid := (hXY.comp (hclipmeas n)).integral_eq
    change (∫ a, lowerClip n (X a) ∂μ) = (∫ a, lowerClip n (Y a) ∂μ) at hid
    rw [hid, sub_self]
  have hFnonpos (n : ℕ) : ∫ a, F n a ∂μ ≤ 0 := by
    rw [← hDzero n]
    exact integral_mono_ae (hFint n) (hDint n) (Eventually.of_forall fun a => min_le_right _ _)
  have hlim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (G a)) := by
    filter_upwards [hlower] with a ha
    have hDlim := (lowerClip_tendsto (Y a)).sub (lowerClip_tendsto (X a))
    simpa only [min_eq_left ha] using (tendsto_const_nhds (x := G a)).min hDlim
  exact le_of_tendsto
    (tendsto_integral_of_dominated_convergence (fun a => |G a|) hFm hG.abs hFbound hlim)
    (Eventually.of_forall hFnonpos)

def prefixMax (z : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => max (prefixMax z n) (z n)

lemma prefixMax_nonneg (z : ℕ → ℝ) (n : ℕ) : 0 ≤ prefixMax z n := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih.trans (le_max_left _ _)

lemma prefixMax_le_truncation (z : ℕ → ℝ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    prefixMax z n ≤ T + ∑ j ∈ Finset.range n, max (z j - T) 0 := by
  induction n with
  | zero => simpa [prefixMax] using hT
  | succ n ih =>
    rw [prefixMax, Finset.sum_range_succ]
    apply max_le
    · linarith [le_max_right (z n - T) 0]
    · have hsum : 0 ≤ ∑ j ∈ Finset.range n, max (z j - T) 0 :=
        Finset.sum_nonneg fun j _ => le_max_right _ _
      linarith [le_max_left (z n - T) 0]

lemma integrable_prefixMax
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {Z : ℕ → α → ℝ} (hZ : ∀ j, Integrable (Z j) μ) (n : ℕ) :
    Integrable (fun a => prefixMax (fun j => Z j a) n) μ := by
  induction n with
  | zero => exact integrable_zero α ℝ μ
  | succ n ih => exact ih.sup (hZ n)

lemma integral_prefixMax_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {Z : ℕ → α → ℝ} (hZ : Integrable (Z 0) μ)
    (hid : ∀ j, IdentDistrib (Z j) (Z 0) μ μ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    (∫ a, prefixMax (fun j => Z j a) n ∂μ) ≤
      T + n * ∫ a, max (Z 0 a - T) 0 ∂μ := by
  have hint (j : ℕ) : Integrable (Z j) μ := (hid j).integrable_iff.mpr hZ
  have htail (j : ℕ) : Integrable (fun a => max (Z j a - T) 0) μ :=
    ((hint j).sub (integrable_const _)).sup (integrable_const _)
  calc
    (∫ a, prefixMax (fun j => Z j a) n ∂μ)
        ≤ ∫ a, T + ∑ j ∈ Finset.range n, max (Z j a - T) 0 ∂μ := by
      apply integral_mono (integrable_prefixMax μ hint n)
        ((integrable_const T).add (integrable_finsetSum _ fun j _ => htail j))
      intro a
      exact prefixMax_le_truncation _ hT _
    _ = T + ∑ j ∈ Finset.range n, ∫ a, max (Z j a - T) 0 ∂μ := by
      rw [integral_add (integrable_const T)
        (integrable_finsetSum _ fun j _ => htail j), integral_const,
        integral_finsetSum _ fun j _ => htail j]
      simp
    _ = T + n * ∫ a, max (Z 0 a - T) 0 ∂μ := by
      congr 1
      have heq (j : ℕ) : (∫ a, max (Z j a - T) 0 ∂μ) =
          ∫ a, max (Z 0 a - T) 0 ∂μ :=
        ((hid j).comp ((measurable_id.sub_const T).max measurable_const)).integral_eq
      simp_rw [heq]
      simp

lemma integral_prefixMax_div_tendsto_zero
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {Z : ℕ → α → ℝ} (hZ : Integrable (Z 0) μ)
    (hid : ∀ j, IdentDistrib (Z j) (Z 0) μ μ) :
    Tendsto (fun n : ℕ => (∫ a, prefixMax (fun j => Z j a) n ∂μ) / n)
      atTop (𝓝 0) := by
  have htail : Tendsto (fun T : ℕ => ∫ a, max (Z 0 a - T) 0 ∂μ) atTop (𝓝 0) := by
    have hbound (T : ℕ) : ∀ᵐ a ∂μ, ‖max (Z 0 a - T) 0‖ ≤ |Z 0 a| := by
      apply Eventually.of_forall
      intro a
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      apply max_le
      · linarith [le_abs_self (Z 0 a), Nat.cast_nonneg (α := ℝ) T]
      · exact abs_nonneg _
    have hlim : ∀ᵐ a ∂μ,
        Tendsto (fun T : ℕ => max (Z 0 a - T) 0) atTop (𝓝 0) := by
      apply Eventually.of_forall
      intro a
      obtain ⟨N, hN⟩ := exists_nat_ge (Z 0 a)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
      exact (max_eq_right (by linarith)).symm
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
      (fun a => |Z 0 a|)
      (fun T => (hZ.aemeasurable.sub_const T |>.max aemeasurable_const).aestronglyMeasurable)
      hZ.abs hbound hlim
  have hnonneg (n : ℕ) : 0 ≤ (∫ a, prefixMax (fun j => Z j a) n ∂μ) / n :=
    div_nonneg (integral_nonneg fun a => prefixMax_nonneg _ _) (Nat.cast_nonneg _)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (hnonneg n)
  · intro ε hε
    obtain ⟨T, hT⟩ := (htail.eventually (gt_mem_nhds (half_pos hε))).exists
    have hdiv : Tendsto (fun n : ℕ => (T : ℝ) / n) atTop (𝓝 0) :=
      tendsto_natCast_atTop_atTop.const_div_atTop _
    filter_upwards [hdiv.eventually (gt_mem_nhds (half_pos hε)),
      eventually_ge_atTop 1] with n hn hn1
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn1
    have hbd := div_le_div_of_nonneg_right
      (integral_prefixMax_le μ hZ hid (Nat.cast_nonneg T) n) hnpos.le
    rw [add_div, mul_div_cancel_left₀ _ hnpos.ne'] at hbd
    linarith

lemma le_prefixMax (z : ℕ → ℝ) {j n : ℕ} (hj : j < n) : z j ≤ prefixMax z n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | rfl
    · exact (ih h).trans (le_max_left _ _)
    · exact le_max_right _ _

lemma log_sum_le_log_add_prefixMax (h : ℕ → ℝ) (hh : ∀ j, 0 ≤ h j)
    {n : ℕ} (hn : 0 < n) :
    Real.log (1 + ∑ j ∈ Finset.range n, h j) ≤
      Real.log n + prefixMax (fun j => Real.log (1 + h j)) n := by
  let M := prefixMax (fun j => Real.log (1 + h j)) n
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsum : 0 ≤ ∑ j ∈ Finset.range n, h j := Finset.sum_nonneg fun j _ => hh j
  apply (Real.log_le_iff_le_exp (by linarith)).mpr
  rw [Real.exp_add, Real.exp_log hnR]
  have hterm : ∀ j ∈ Finset.range n, 1 + h j ≤ Real.exp M := by
    intro j hj
    exact (Real.log_le_iff_le_exp (by linarith [hh j])).mp
      (le_prefixMax (fun j => Real.log (1 + h j)) (Finset.mem_range.mp hj))
  have hbd := Finset.sum_le_sum hterm
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] at hbd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

lemma integral_log_sum_div_tendsto_zero
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {h : ℕ → α → ℝ} (hh : ∀ᵐ a ∂μ, ∀ j, 0 ≤ h j a)
    (hid : ∀ j, IdentDistrib (h j) (h 0) μ μ)
    (hint : Integrable (fun a => Real.log (1 + h 0 a)) μ) :
    Tendsto (fun n : ℕ => (∫ a, Real.log (1 + ∑ j ∈ Finset.range n, h j a) ∂μ) / n)
      atTop (𝓝 0) := by
  let Z : ℕ → α → ℝ := fun j a => Real.log (1 + h j a)
  have hZid (j : ℕ) : IdentDistrib (Z j) (Z 0) μ μ :=
    (hid j).comp (Real.measurable_log.comp (measurable_const.add measurable_id))
  have hZint (j : ℕ) : Integrable (Z j) μ := (hZid j).integrable_iff.mpr hint
  have hnonneg (n : ℕ) :
      0 ≤ (∫ a, Real.log (1 + ∑ j ∈ Finset.range n, h j a) ∂μ) / n := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply integral_nonneg_of_ae
    filter_upwards [hh] with a ha
    apply Real.log_nonneg
    have := Finset.sum_nonneg (s := Finset.range n) (fun j _ => ha j)
    linarith
  have hupper : ∀ᶠ n : ℕ in atTop,
      (∫ a, Real.log (1 + ∑ j ∈ Finset.range n, h j a) ∂μ) / n ≤
        Real.log n / n + (∫ a, prefixMax (fun j => Z j a) n ∂μ) / n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : 0 < n := by omega
    have hm : AEStronglyMeasurable
        (fun a => Real.log (1 + ∑ j ∈ Finset.range n, h j a)) μ :=
      (Real.measurable_log.comp_aemeasurable
        (aemeasurable_const.add (Finset.aemeasurable_fun_sum _ fun j _ => (hid j).aemeasurable_fst))).aestronglyMeasurable
    have hbd : ∀ᵐ a ∂μ,
        Real.log (1 + ∑ j ∈ Finset.range n, h j a) ≤
          Real.log n + prefixMax (fun j => Z j a) n := by
      filter_upwards [hh] with a ha
      exact log_sum_le_log_add_prefixMax _ ha hn0
    have hubint : Integrable (fun a => Real.log n + prefixMax (fun j => Z j a) n) μ :=
      (integrable_const _).add (integrable_prefixMax μ hZint n)
    have hsint : Integrable (fun a => Real.log (1 + ∑ j ∈ Finset.range n, h j a)) μ := by
      apply hubint.mono' hm
      filter_upwards [hh, hbd] with a ha hb
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by
        have := Finset.sum_nonneg (s := Finset.range n) (fun j _ => ha j)
        linarith))]
      exact hb
    have hbint := integral_mono_ae hsint hubint hbd
    rw [integral_add (integrable_const _) (integrable_prefixMax μ hZint n)] at hbint
    simp only [integral_const] at hbint
    simp at hbint
    have hd := div_le_div_of_nonneg_right hbint (Nat.cast_nonneg n)
    simpa only [add_div] using hd
  apply squeeze_zero' (Eventually.of_forall hnonneg) hupper
  have hlog : Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero, Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa using hlog.add (integral_prefixMax_div_tendsto_zero μ hint hZid)

end DirectionalTransience
end
end

end OAI
