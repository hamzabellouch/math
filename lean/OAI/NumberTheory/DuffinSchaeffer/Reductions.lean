import Mathlib

namespace OAI

/-! Preliminary reductions for inhomogeneous Diophantine approximation. -/

noncomputable section

open Filter MeasureTheory Set Metric
open scoped BigOperators Topology

namespace WeakInhomogeneousDS

def approximationSet (γ : ℝ) (ψ : ℕ → ℝ) (q : ℕ) : Set ℝ :=
  {x | ‖(((q : ℝ) * x - γ : ℝ) : UnitAddCircle)‖ < ψ q}

def wellApproximated (γ : ℝ) (ψ : ℕ → ℝ) : Set ℝ :=
  {x | Set.Infinite {q : ℕ | 0 < q ∧ x ∈ approximationSet γ ψ q}}

def rowCenters (γ : ℝ) (q : ℕ) : Set ℝ :=
  Set.range fun a : ℤ => ((a : ℝ) + γ) / (q : ℝ)

def rowRadius (ψ : ℕ → ℝ) (q : ℕ) : ℝ := ψ q / (q : ℝ)

def totientMass (ψ : ℕ → ℝ) (q : ℕ) : ℝ :=
  (Nat.totient q : ℝ) / (q : ℝ) * ψ q

theorem totientMass_eq_totient_mul_rowRadius (ψ : ℕ → ℝ) (q : ℕ) :
    totientMass ψ q = (Nat.totient q : ℝ) * rowRadius ψ q := by
  unfold totientMass rowRadius
  ring

theorem mul_rowRadius (ψ : ℕ → ℝ) {q : ℕ} (hq : 0 < q) :
    (q : ℝ) * rowRadius ψ q = ψ q := by
  unfold rowRadius
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq))

theorem norm_coe_lt_iff_exists_int (t ε : ℝ) :
    ‖(t : UnitAddCircle)‖ < ε ↔ ∃ a : ℤ, |t - (a : ℝ)| < ε := by
  rw [UnitAddCircle.norm_eq]
  constructor
  · intro h
    exact ⟨round t, h⟩
  · rintro ⟨a, ha⟩
    exact (round_le t a).trans_lt ha

theorem mem_approximationSet_iff (γ : ℝ) (ψ : ℕ → ℝ) (q : ℕ) (x : ℝ) :
    x ∈ approximationSet γ ψ q ↔
      ∃ a : ℤ, |(q : ℝ) * x - γ - (a : ℝ)| < ψ q :=
  norm_coe_lt_iff_exists_int _ _

theorem approximationSet_eq_thickening (γ : ℝ) (ψ : ℕ → ℝ)
    {q : ℕ} (hq : 0 < q) :
    approximationSet γ ψ q = thickening (rowRadius ψ q) (rowCenters γ q) := by
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  ext x
  rw [mem_approximationSet_iff, thickening_eq_biUnion_ball]
  simp only [rowCenters, rowRadius, mem_iUnion, Set.mem_range, mem_ball, Real.dist_eq]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨((a : ℝ) + γ) / (q : ℝ), ⟨a, rfl⟩, ?_⟩
    have heq : x - ((a : ℝ) + γ) / (q : ℝ) =
        ((q : ℝ) * x - γ - (a : ℝ)) / (q : ℝ) := by
      field_simp
      ring
    rw [heq, abs_div, abs_of_pos hqR]
    exact (div_lt_div_iff_of_pos_right hqR).mpr ha
  · rintro ⟨y, ⟨a, rfl⟩, ha⟩
    refine ⟨a, ?_⟩
    have heq : x - ((a : ℝ) + γ) / (q : ℝ) =
        ((q : ℝ) * x - γ - (a : ℝ)) / (q : ℝ) := by
      field_simp
      ring
    rw [heq, abs_div, abs_of_pos hqR] at ha
    exact (div_lt_div_iff_of_pos_right hqR).mp ha

theorem approximationSet_eq_iUnion_Ioo (γ : ℝ) (ψ : ℕ → ℝ)
    {q : ℕ} (hq : 0 < q) :
    approximationSet γ ψ q = ⋃ a : ℤ,
      Ioo (((a : ℝ) + γ) / (q : ℝ) - rowRadius ψ q)
        (((a : ℝ) + γ) / (q : ℝ) + rowRadius ψ q) := by
  rw [approximationSet_eq_thickening γ ψ hq, thickening_eq_biUnion_ball]
  simp [rowCenters, Real.ball_eq_Ioo]

theorem isOpen_approximationSet (γ : ℝ) (ψ : ℕ → ℝ) (q : ℕ) :
    IsOpen (approximationSet γ ψ q) := by
  apply isOpen_lt _ continuous_const
  exact ((AddCircle.continuous_mk' (1 : ℝ)).comp
    ((continuous_const.mul continuous_id).sub continuous_const)).norm

theorem approximationSet_empty_of_nonpos (γ : ℝ) (ψ : ℕ → ℝ)
    {q : ℕ} (h : ψ q ≤ 0) : approximationSet γ ψ q = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact (not_lt_of_ge (norm_nonneg _)) (hx.trans_le h)

theorem approximationSet_mono (γ : ℝ) {ψ χ : ℕ → ℝ} {q : ℕ}
    (h : ψ q ≤ χ q) : approximationSet γ ψ q ⊆ approximationSet γ χ q := by
  intro x hx
  exact hx.trans_le h

theorem wellApproximated_eq_blimsup (γ : ℝ) (ψ : ℕ → ℝ) :
    wellApproximated γ ψ =
      blimsup (approximationSet γ ψ) atTop (fun q => 0 < q) := by
  rw [← Nat.cofinite_eq_atTop, cofinite.blimsup_set_eq]
  rfl

theorem measurableSet_wellApproximated (γ : ℝ) (ψ : ℕ → ℝ) :
    MeasurableSet (wellApproximated γ ψ) := by
  rw [wellApproximated_eq_blimsup]
  exact MeasurableSet.measurableSet_blimsup
    (fun q _ => (isOpen_approximationSet γ ψ q).measurableSet)

theorem wellApproximated_mono (γ : ℝ) {ψ χ : ℕ → ℝ} (h : ∀ q, ψ q ≤ χ q) :
    wellApproximated γ ψ ⊆ wellApproximated γ χ := by
  intro x hx
  exact hx.mono (fun q hq => ⟨hq.1, approximationSet_mono γ (h q) hq.2⟩)

theorem approximationSet_eq_univ_of_half_lt (γ : ℝ) (ψ : ℕ → ℝ) {q : ℕ}
    (h : (1 : ℝ) / 2 < ψ q) : approximationSet γ ψ q = univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hb : ‖(((q : ℝ) * x - γ : ℝ) : UnitAddCircle)‖ ≤ (1 : ℝ) / 2 := by
    simpa only [abs_one] using
      (AddCircle.norm_le_half_period (1 : ℝ)
        (x := (((q : ℝ) * x - γ : ℝ) : UnitAddCircle)) one_ne_zero)
  exact hb.trans_lt h

theorem thickening_rowCenters_one_div (γ : ℝ) {q : ℕ} (hq : 0 < q) :
    thickening (1 / (q : ℝ)) (rowCenters γ q) = univ := by
  change thickening (rowRadius (fun _ => 1) q) (rowCenters γ q) = univ
  rw [← approximationSet_eq_thickening γ (fun _ => 1) hq]
  exact approximationSet_eq_univ_of_half_lt γ _ (by norm_num)

theorem ae_wellApproximated_of_infinite_large_widths (γ : ℝ) (ψ : ℕ → ℝ)
    {c : ℝ} (hc : 0 < c)
    (hinf : Set.Infinite {q : ℕ | 0 < q ∧ c ≤ ψ q}) :
    ∀ᵐ x : ℝ ∂volume, x ∈ wellApproximated γ ψ := by
  let p : ℕ → Prop := fun q => 0 < q ∧ c ≤ ψ q
  have hfull : blimsup (fun q : ℕ => thickening (1 / (q : ℝ)) (rowCenters γ q))
      atTop p = univ := by
    rw [← Nat.cofinite_eq_atTop, cofinite.blimsup_set_eq]
    apply Set.eq_univ_of_forall
    intro x
    apply hinf.mono
    intro q hq
    exact ⟨hq, by rw [thickening_rowCenters_one_div γ hq.1]; trivial⟩
  have hscale := blimsup_thickening_mul_ae_eq volume p (rowCenters γ) hc
    (fun q : ℕ => 1 / (q : ℝ)) tendsto_one_div_atTop_nhds_zero_nat
  rw [hfull] at hscale
  filter_upwards [hscale] with x hx
  have hmem : x ∈ blimsup
      (fun q : ℕ => thickening (c * (1 / (q : ℝ))) (rowCenters γ q)) atTop p := by
    exact (eq_iff_iff.mp hx).mpr (mem_univ x)
  rw [← Nat.cofinite_eq_atTop, cofinite.blimsup_set_eq] at hmem
  apply hmem.mono
  rintro q ⟨hq, hqx⟩
  refine ⟨hq.1, approximationSet_mono γ (ψ := fun _ => c) hq.2 ?_⟩
  rw [approximationSet_eq_thickening γ (fun _ => c) hq.1]
  simpa only [rowRadius, mul_one_div] using hqx

theorem exists_infinite_large_widths_of_not_tendsto {ψ : ℕ → ℝ}
    (hψ : ∀ q, 0 ≤ ψ q) (hnot : ¬ Tendsto ψ atTop (𝓝 0)) :
    ∃ c : ℝ, 0 < c ∧ Set.Infinite {q : ℕ | 0 < q ∧ c ≤ ψ q} := by
  by_contra h
  apply hnot
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun q => ha.trans_le (hψ q))
  · intro c hc
    have hn : ¬ ∃ᶠ q in atTop, 0 < q ∧ c ≤ ψ q := by
      rw [Nat.frequently_atTop_iff_infinite]
      exact fun hi => h ⟨c, hc, hi⟩
    have he : ∀ᶠ q in atTop, ¬ (0 < q ∧ c ≤ ψ q) := not_frequently.mp hn
    filter_upwards [he, Nat.eventually_pos] with q heq hq
    exact lt_of_not_ge (fun hcq => heq ⟨hq, hcq⟩)

theorem ae_wellApproximated_of_not_tendsto_zero (γ : ℝ) (ψ : ℕ → ℝ)
    (hψ : ∀ q, 0 ≤ ψ q) (hnot : ¬ Tendsto ψ atTop (𝓝 0)) :
    ∀ᵐ x : ℝ ∂volume, x ∈ wellApproximated γ ψ := by
  obtain ⟨c, hc, hinf⟩ := exists_infinite_large_widths_of_not_tendsto hψ hnot
  exact ae_wellApproximated_of_infinite_large_widths γ ψ hc hinf

theorem totientMass_nonneg {ψ : ℕ → ℝ} (hψ : ∀ q, 0 ≤ ψ q) (q : ℕ) :
    0 ≤ totientMass ψ q := by
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hψ q)

theorem totientMass_le {ψ : ℕ → ℝ} (hψ : ∀ q, 0 ≤ ψ q) (q : ℕ) :
    totientMass ψ q ≤ ψ q := by
  by_cases hq : q = 0
  · simpa [totientMass, hq] using hψ 0
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hq)
  have hφ : (Nat.totient q : ℝ) / (q : ℝ) ≤ 1 := by
    rw [div_le_one hqR]
    exact_mod_cast Nat.totient_le q
  exact (mul_le_mul_of_nonneg_right hφ (hψ q)).trans_eq (one_mul _)

theorem tendsto_totientMass_zero {ψ : ℕ → ℝ} (hψ : ∀ q, 0 ≤ ψ q)
    (hsmall : Tendsto ψ atTop (𝓝 0)) :
    Tendsto (totientMass ψ) atTop (𝓝 0) :=
  squeeze_zero (totientMass_nonneg hψ) (totientMass_le hψ) hsmall

theorem rowRadius_bounds {ψ : ℕ → ℝ} (hψ : ∀ q, 0 ≤ ψ q) (q : ℕ) :
    0 ≤ rowRadius ψ q ∧ rowRadius ψ q ≤ ψ q := by
  constructor
  · exact div_nonneg (hψ q) (Nat.cast_nonneg q)
  · by_cases hq : q = 0
    · simpa [rowRadius, hq] using hψ 0
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
    exact div_le_self (hψ q) hq1

theorem tendsto_rowRadius_zero {ψ : ℕ → ℝ} (hψ : ∀ q, 0 ≤ ψ q)
    (hsmall : Tendsto ψ atTop (𝓝 0)) :
    Tendsto (rowRadius ψ) atTop (𝓝 0) :=
  squeeze_zero (fun q => (rowRadius_bounds hψ q).1)
    (fun q => (rowRadius_bounds hψ q).2) hsmall

theorem exists_fixed_mass_block {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hsmall : Tendsto a atTop (𝓝 0))
    (hdiv : Tendsto (fun K : ℕ => ∑ q ∈ Finset.Icc 1 K, a q) atTop atTop)
    {w : ℝ} (hw : 0 < w) (N : ℕ) :
    ∃ B : Finset ℕ, (∀ q ∈ B, N ≤ q ∧ 0 < q ∧ 0 < a q) ∧
      w ≤ ∑ q ∈ B, a q ∧ (∑ q ∈ B, a q) ≤ 2 * w := by
  classical
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp (hsmall.eventually (gt_mem_nhds hw))
  let M := max (max N 1) M₀
  have hNM : N ≤ M := (le_max_left N 1).trans (le_max_left _ _)
  have h1M : 1 ≤ M := (le_max_right N 1).trans (le_max_left _ _)
  have hM₀M : M₀ ≤ M := le_max_right _ _
  have ha_small : ∀ q, M ≤ q → a q ≤ w := by
    intro q hq
    exact (hM₀ q (hM₀M.trans hq)).le
  have hex : ∃ K : ℕ, w ≤ ∑ q ∈ Finset.Icc M K, a q := by
    obtain ⟨K, hMK, hbig⟩ := ((eventually_ge_atTop M).and
      (hdiv.eventually_ge_atTop (w + ∑ q ∈ Finset.Ico 1 M, a q))).exists
    have hsum := Finset.sum_Ico_consecutive a h1M (hMK.trans (Nat.le_succ K))
    simp only [Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc] at hsum
    exact ⟨K, by linarith⟩
  let K := Nat.find hex
  have hK : w ≤ ∑ q ∈ Finset.Icc M K, a q := Nat.find_spec hex
  have hMK : M ≤ K := by
    by_contra h
    have hz : Finset.Icc M K = ∅ := Finset.Icc_eq_empty_of_lt (lt_of_not_ge h)
    rw [hz, Finset.sum_empty] at hK
    exact (not_le_of_gt hw) hK
  have hKpos : 0 < K := lt_of_lt_of_le (by omega : 0 < M) hMK
  have hupper : (∑ q ∈ Finset.Icc M K, a q) ≤ 2 * w := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hKpos)
    have hprev : (∑ q ∈ Finset.Icc M k, a q) < w := by
      exact lt_of_not_ge (Nat.find_min hex (by change k < K; omega))
    have hlast := ha_small K hMK
    rw [hk, Nat.succ_eq_add_one, Finset.sum_Icc_succ_top (by omega)]
    rw [hk] at hlast
    linarith
  let B := {q ∈ Finset.Icc M K | 0 < a q}
  have hsum : (∑ q ∈ B, a q) = ∑ q ∈ Finset.Icc M K, a q := by
    apply Finset.sum_filter_of_ne
    intro q _ hq
    exact lt_of_le_of_ne (ha q) (Ne.symm hq)
  refine ⟨B, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨hq, hpos⟩ := Finset.mem_filter.mp hq
    have hMq := (Finset.mem_Icc.mp hq).1
    exact ⟨hNM.trans hMq, lt_of_lt_of_le (by omega : 0 < M) hMq, hpos⟩
  · rwa [hsum]
  · rwa [hsum]

theorem exists_late_totient_mass_block {ψ : ℕ → ℝ} (hψ : ∀ q, 0 ≤ ψ q)
    (hsmall : Tendsto ψ atTop (𝓝 0))
    (hdiv : Tendsto (fun K : ℕ => ∑ q ∈ Finset.Icc 1 K, totientMass ψ q)
      atTop atTop)
    {w : ℝ} (hw : 0 < w) (N : ℕ) :
    ∃ B : Finset ℕ, (∀ q ∈ B, N ≤ q ∧ 0 < q ∧ 0 < ψ q) ∧
      w ≤ ∑ q ∈ B, totientMass ψ q ∧ (∑ q ∈ B, totientMass ψ q) ≤ 2 * w := by
  obtain ⟨B, hB, hlow, hupp⟩ := exists_fixed_mass_block
    (totientMass_nonneg hψ) (tendsto_totientMass_zero hψ hsmall) hdiv hw N
  refine ⟨B, ?_, hlow, hupp⟩
  intro q hq
  obtain ⟨hNq, hqpos, hmass⟩ := hB q hq
  exact ⟨hNq, hqpos, hmass.trans_le (totientMass_le hψ q)⟩

theorem exists_late_small_totient_mass_block {ψ : ℕ → ℝ} (hψ : ∀ q, 0 ≤ ψ q)
    (hsmall : Tendsto ψ atTop (𝓝 0))
    (hdiv : Tendsto (fun K : ℕ => ∑ q ∈ Finset.Icc 1 K, totientMass ψ q)
      atTop atTop)
    {w ε : ℝ} (hw : 0 < w) (hε : 0 < ε) (N : ℕ) :
    ∃ B : Finset ℕ,
      (∀ q ∈ B, N ≤ q ∧ 0 < q ∧ 0 < ψ q ∧ rowRadius ψ q < ε) ∧
      w ≤ ∑ q ∈ B, totientMass ψ q ∧ (∑ q ∈ B, totientMass ψ q) ≤ 2 * w := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    ((tendsto_rowRadius_zero hψ hsmall).eventually (gt_mem_nhds hε))
  obtain ⟨B, hB, hlow, hupp⟩ := exists_late_totient_mass_block hψ hsmall hdiv hw (max N M)
  refine ⟨B, ?_, hlow, hupp⟩
  intro q hq
  obtain ⟨hNq, hqpos, hψq⟩ := hB q hq
  exact ⟨(le_max_left N M).trans hNq, hqpos, hψq, hM q ((le_max_right N M).trans hNq)⟩

theorem exists_dyadic_tolerance (q : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    ∃ v : ℝ, u / 2 ≤ v ∧ v ≤ u ∧
      (v / (q : ℝ) = 0 ∨ ∃ k : ℤ, v / (q : ℝ) = (2 : ℝ) ^ k) := by
  by_cases hq : q = 0
  · refine ⟨u, by linarith, le_rfl, Or.inl ?_⟩
    simp [hq]
  by_cases hu0 : u = 0
  · subst u
    exact ⟨0, by simp, le_rfl, Or.inl (by simp)⟩
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hq)
  have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  obtain ⟨k, hlow, hupp⟩ := exists_mem_Ico_zpow (div_pos hu' hqR) (by norm_num : (1 : ℝ) < 2)
  rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)] at hupp
  have hlow' := (le_div_iff₀ hqR).mp hlow
  have hupp' := (div_lt_iff₀ hqR).mp hupp
  refine ⟨(q : ℝ) * (2 : ℝ) ^ k, by nlinarith, by nlinarith, Or.inr ⟨k, ?_⟩⟩
  exact mul_div_cancel_left₀ _ hqR.ne'

theorem totient_divergence_of_mul_le {ψ χ : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∀ q, c * ψ q ≤ χ q)
    (hdiv : Tendsto (fun K : ℕ => ∑ q ∈ Finset.Icc 1 K, totientMass ψ q)
      atTop atTop) :
    Tendsto (fun K : ℕ => ∑ q ∈ Finset.Icc 1 K, totientMass χ q) atTop atTop := by
  apply tendsto_atTop_mono (f := fun K => c * ∑ q ∈ Finset.Icc 1 K, totientMass ψ q)
    ?_ (Tendsto.const_mul_atTop hc hdiv)
  intro K
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  unfold totientMass
  calc
    c * ((Nat.totient q : ℝ) / (q : ℝ) * ψ q) =
        (Nat.totient q : ℝ) / (q : ℝ) * (c * ψ q) := by ring
    _ ≤ (Nat.totient q : ℝ) / (q : ℝ) * χ q :=
      mul_le_mul_of_nonneg_left (h q)
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem exists_dyadic_reduction {ψ : ℕ → ℝ} (hψ : ∀ q, 0 ≤ ψ q)
    (hsmall : Tendsto ψ atTop (𝓝 0))
    (hdiv : Tendsto (fun K : ℕ => ∑ q ∈ Finset.Icc 1 K, totientMass ψ q)
      atTop atTop) :
    ∃ χ : ℕ → ℝ, (∀ q, 0 ≤ χ q) ∧
      (∀ q, ψ q / 2 ≤ χ q ∧ χ q ≤ ψ q) ∧
      (∀ q, rowRadius χ q = 0 ∨ ∃ k : ℤ, rowRadius χ q = (2 : ℝ) ^ k) ∧
      Tendsto χ atTop (𝓝 0) ∧
      Tendsto (fun K : ℕ => ∑ q ∈ Finset.Icc 1 K, totientMass χ q) atTop atTop ∧
      ∀ γ : ℝ, wellApproximated γ χ ⊆ wellApproximated γ ψ := by
  choose χ hhalf hle hdyadic using fun q => exists_dyadic_tolerance q (hψ q)
  have hχ : ∀ q, 0 ≤ χ q := fun q => (div_nonneg (hψ q) (by norm_num)).trans (hhalf q)
  refine ⟨χ, hχ, (fun q => ⟨hhalf q, hle q⟩), hdyadic,
    squeeze_zero hχ hle hsmall, ?_, fun γ => wellApproximated_mono γ hle⟩
  apply totient_divergence_of_mul_le (c := (1 : ℝ) / 2) (by norm_num) ?_ hdiv
  intro q
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hhalf q

def avoidedTail (γ : ℝ) (ψ : ℕ → ℝ) (N : ℕ) : Set ℝ :=
  ⋂ q : ℕ, ⋂ (_ : N ≤ q), ⋂ (_ : 0 < q), (approximationSet γ ψ q)ᶜ

@[simp]
theorem mem_avoidedTail (γ : ℝ) (ψ : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    x ∈ avoidedTail γ ψ N ↔ ∀ q, N ≤ q → 0 < q → x ∉ approximationSet γ ψ q := by
  simp [avoidedTail]

theorem measurableSet_avoidedTail (γ : ℝ) (ψ : ℕ → ℝ) (N : ℕ) :
    MeasurableSet (avoidedTail γ ψ N) := by
  exact MeasurableSet.iInter (fun q => MeasurableSet.iInter (fun _ =>
    MeasurableSet.iInter (fun _ => (isOpen_approximationSet γ ψ q).measurableSet.compl)))

theorem compl_wellApproximated (γ : ℝ) (ψ : ℕ → ℝ) :
    (wellApproximated γ ψ)ᶜ = ⋃ N : ℕ, avoidedTail γ ψ N := by
  ext x
  constructor
  · intro hx
    have hfin : Set.Finite {q : ℕ | 0 < q ∧ x ∈ approximationSet γ ψ q} :=
      Set.not_infinite.mp hx
    obtain ⟨N, hN⟩ := hfin.exists_le
    refine mem_iUnion.mpr ⟨N + 1, (mem_avoidedTail γ ψ (N + 1) x).mpr ?_⟩
    intro q hq hpos hmem
    have hupp := hN q ⟨hpos, hmem⟩
    omega
  · intro hx
    obtain ⟨N, hN⟩ := mem_iUnion.mp hx
    have hfin : Set.Finite {q : ℕ | 0 < q ∧ x ∈ approximationSet γ ψ q} := by
      apply (finite_lt_nat N).subset
      rintro q ⟨hq, hmem⟩
      exact lt_of_not_ge (fun hNq => (mem_avoidedTail γ ψ N x).mp hN q hNq hq hmem)
    exact hfin.not_infinite

theorem exists_positive_avoidedTail (γ : ℝ) (ψ : ℕ → ℝ)
    (hfail : ¬ ∀ᵐ x : ℝ ∂volume, x ∈ wellApproximated γ ψ) :
    ∃ N : ℕ, 0 < volume (avoidedTail γ ψ N) := by
  by_contra hn
  apply hfail
  rw [ae_iff]
  change volume ((wellApproximated γ ψ)ᶜ) = 0
  rw [compl_wellApproximated]
  apply measure_iUnion_null
  intro N
  apply nonpos_iff_eq_zero.mp
  exact le_of_not_gt (fun hN => hn ⟨N, hN⟩)

theorem exists_finite_measure_avoided_set (γ : ℝ) (ψ : ℕ → ℝ)
    (hfail : ¬ ∀ᵐ x : ℝ ∂volume, x ∈ wellApproximated γ ψ) :
    ∃ N : ℕ, ∃ A : Set ℝ, MeasurableSet A ∧ 0 < volume A ∧ volume A < ⊤ ∧
      ∀ x ∈ A, ∀ q, N ≤ q → 0 < q → x ∉ approximationSet γ ψ q := by
  obtain ⟨N, hN⟩ := exists_positive_avoidedTail γ ψ hfail
  have hcover : avoidedTail γ ψ N = ⋃ m : ℕ,
      avoidedTail γ ψ N ∩ Icc (-(m : ℝ)) (m : ℝ) := by
    ext x
    constructor
    · intro hx
      obtain ⟨m, hm⟩ := exists_nat_gt |x|
      exact mem_iUnion.mpr ⟨m, hx, (abs_le.mp hm.le)⟩
    · intro hx
      obtain ⟨m, hx, _⟩ := mem_iUnion.mp hx
      exact hx
  have hex : ∃ m : ℕ,
      0 < volume (avoidedTail γ ψ N ∩ Icc (-(m : ℝ)) (m : ℝ)) := by
    by_contra h
    have hz : volume (avoidedTail γ ψ N) = 0 := by
      rw [hcover]
      apply measure_iUnion_null
      intro m
      exact nonpos_iff_eq_zero.mp (le_of_not_gt (fun hm => h ⟨m, hm⟩))
    exact (ne_of_gt hN) hz
  obtain ⟨m, hm⟩ := hex
  refine ⟨N, avoidedTail γ ψ N ∩ Icc (-(m : ℝ)) (m : ℝ),
    (measurableSet_avoidedTail γ ψ N).inter measurableSet_Icc, hm, ?_, ?_⟩
  · exact (measure_mono inter_subset_right).trans_lt isCompact_Icc.measure_lt_top
  · intro x hx
    exact (mem_avoidedTail γ ψ N x).mp hx.1

theorem exists_disjoint_totient_mass_blocks {ψ : ℕ → ℝ} (hψ : ∀ q, 0 ≤ ψ q)
    (hsmall : Tendsto ψ atTop (𝓝 0))
    (hdiv : Tendsto (fun K : ℕ => ∑ q ∈ Finset.Icc 1 K, totientMass ψ q)
      atTop atTop)
    {w : ℝ} (hw : 0 < w) (N : ℕ) :
    ∃ B : ℕ → Finset ℕ,
      (∀ j, (B j).Nonempty ∧ (∀ q ∈ B j, N ≤ q ∧ j ≤ q ∧ 0 < q ∧ 0 < ψ q) ∧
        w ≤ ∑ q ∈ B j, totientMass ψ q ∧ (∑ q ∈ B j, totientMass ψ q) ≤ 2 * w) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ q ∈ B j, rowRadius ψ q < ε := by
  classical
  choose C hC hlow hupp using fun M => exists_late_totient_mass_block hψ hsmall hdiv hw M
  let t : ℕ → ℕ := Nat.rec N (fun _ k => max (k + 1) ((C k).sup id + 1))
  have ht_succ (j : ℕ) : t (j + 1) = max (t j + 1) ((C (t j)).sup id + 1) := rfl
  have ht : StrictMono t := by
    apply strictMono_nat_of_lt_succ
    intro j
    rw [ht_succ]
    exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)
  have htN (j : ℕ) : N ≤ t j := ht.monotone (Nat.zero_le j)
  have htj (j : ℕ) : j ≤ t j := ht.id_le j
  have hsep : ∀ i j, i < j → ∀ p ∈ C (t i), ∀ q ∈ C (t j), p < q := by
    intro i j hij p hp q hq
    calc
      p ≤ (C (t i)).sup id := Finset.le_sup (f := id) hp
      _ < t (i + 1) := by
        rw [ht_succ]
        exact (Nat.lt_succ_self _).trans_le (le_max_right _ _)
      _ ≤ t j := ht.monotone (Nat.succ_le_of_lt hij)
      _ ≤ q := (hC (t j) q hq).1
  refine ⟨fun j => C (t j), ?_, ?_, ?_⟩
  · intro j
    refine ⟨?_, ?_, hlow (t j), hupp (t j)⟩
    · apply Finset.nonempty_iff_ne_empty.mpr
      intro hz
      change C (t j) = ∅ at hz
      have h := hlow (t j)
      rw [hz, Finset.sum_empty] at h
      exact (not_le_of_gt hw) h
    · intro q hq
      obtain ⟨htq, hpos, hψq⟩ := hC (t j) q hq
      exact ⟨(htN j).trans htq, (htj j).trans htq, hpos, hψq⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro q hqi hqj
    rcases lt_or_gt_of_ne hij with hij | hij
    · exact lt_irrefl q (hsep i j hij q hqi q hqj)
    · exact lt_irrefl q (hsep j i hij q hqj q hqi)
  · intro ε hε
    obtain ⟨M, hM⟩ := eventually_atTop.mp
      ((tendsto_rowRadius_zero hψ hsmall).eventually (gt_mem_nhds hε))
    filter_upwards [eventually_ge_atTop M] with j hj
    intro q hq
    exact hM q (hj.trans ((htj j).trans (hC (t j) q hq).1))

theorem counterexample_reduction (γ : ℝ) (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q)
    (hdiv : Tendsto (fun K : ℕ => ∑ q ∈ Finset.Icc 1 K, totientMass ψ q)
      atTop atTop)
    (hfail : ¬ ∀ᵐ x : ℝ ∂volume, x ∈ wellApproximated γ ψ)
    {w : ℝ} (hw : 0 < w) :
    ∃ χ : ℕ → ℝ,
      (∀ q, 0 ≤ χ q) ∧ (∀ q, ψ q / 2 ≤ χ q ∧ χ q ≤ ψ q) ∧
      (∀ q, rowRadius χ q = 0 ∨ ∃ k : ℤ, rowRadius χ q = (2 : ℝ) ^ k) ∧
      Tendsto χ atTop (𝓝 0) ∧
      Tendsto (fun K : ℕ => ∑ q ∈ Finset.Icc 1 K, totientMass χ q) atTop atTop ∧
      ∃ A : Set ℝ, ∃ B : ℕ → Finset ℕ,
        MeasurableSet A ∧ 0 < volume A ∧ volume A < ⊤ ∧
        (∀ j, (B j).Nonempty ∧ (∀ q ∈ B j, j ≤ q ∧ 0 < q ∧ 0 < χ q) ∧
          w ≤ ∑ q ∈ B j, totientMass χ q ∧ (∑ q ∈ B j, totientMass χ q) ≤ 2 * w) ∧
        Pairwise (fun i j => Disjoint (B i) (B j)) ∧
        (∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ q ∈ B j, rowRadius χ q < ε) ∧
        ∀ x ∈ A, ∀ j, ∀ q ∈ B j, x ∉ approximationSet γ χ q := by
  have hsmall : Tendsto ψ atTop (𝓝 0) := by
    by_contra hs
    exact hfail (ae_wellApproximated_of_not_tendsto_zero γ ψ hψ hs)
  obtain ⟨χ, hχ, hbounds, hdyadic, hχsmall, hχdiv, hsubset⟩ :=
    exists_dyadic_reduction hψ hsmall hdiv
  have hχfail : ¬ ∀ᵐ x : ℝ ∂volume, x ∈ wellApproximated γ χ := by
    intro ha
    exact hfail (ha.mono (fun _ hx => hsubset γ hx))
  obtain ⟨N, A, hA, hApos, hAfin, havoid⟩ :=
    exists_finite_measure_avoided_set γ χ hχfail
  obtain ⟨B, hB, hdisj, hwidth⟩ :=
    exists_disjoint_totient_mass_blocks hχ hχsmall hχdiv hw N
  refine ⟨χ, hχ, hbounds, hdyadic, hχsmall, hχdiv, A, B,
    hA, hApos, hAfin, ?_, hdisj, hwidth, ?_⟩
  · intro j
    obtain ⟨hne, hrows, hl, hu⟩ := hB j
    exact ⟨hne, (fun q hq => (hrows q hq).2), hl, hu⟩
  · intro x hx j q hq
    obtain ⟨hNq, _, hqpos, _⟩ := (hB j).2.1 q hq
    exact havoid x hx q hNq hqpos

end WeakInhomogeneousDS

end

end OAI
