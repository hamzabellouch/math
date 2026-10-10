import OAI.NumberTheory.TotientAsymptotic.Renewal

namespace OAI

/-! Cofinal logarithmic phases and convergence of the coefficient approximants. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma self_sub_log_tendsto :
    Tendsto (fun t : ℝ => t - Real.log t) atTop atTop := by
  have hlog : Tendsto (fun t : ℝ => Real.log t / t) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hone : Tendsto (fun t : ℝ => 1 - Real.log t / t) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hlog
  have hmul : Tendsto (fun t : ℝ => t * (1-Real.log t / t)) atTop atTop :=
    Filter.Tendsto.atTop_mul_pos zero_lt_one tendsto_id hone
  apply hmul.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
  field_simp

lemma psi_tendsto : Tendsto psi atTop atTop := by
  exact (self_sub_log_tendsto.comp Real.tendsto_log_atTop).atTop_div_const lam_pos

lemma psi_continuousOn {b : ℝ} (hb : 1 < b) : ContinuousOn psi (Set.Ici b) := by
  intro y hy
  have hy1 : 1 < y := hb.trans_le hy
  have hy0 : 0 < y := zero_lt_one.trans hy1
  have hlog : 0 < Real.log y := Real.log_pos hy1
  exact (((Real.continuousAt_log hy0.ne').sub
    ((Real.continuousAt_log hlog.ne').comp (Real.continuousAt_log hy0.ne'))).div_const
      lam).continuousWithinAt

lemma B_exp_exp (b : ℝ) : B (Real.exp (Real.exp b)) = b := by
  simp only [B, Real.log_exp]

lemma theta_of_phase {x s : ℝ} {n : ℕ} (hs : s ∈ Set.Ico (0 : ℝ) 1)
    (hx : psi (B x) = n+s) : m x = n ∧ theta x = s := by
  have hh : m x = n := by
    unfold m
    rw [hx, Nat.floor_eq_iff (add_nonneg (Nat.cast_nonneg n) hs.1)]
    constructor <;> linarith [hs.1, hs.2]
  exact ⟨hh, by simp only [theta, hx, hh]; ring⟩

theorem exact_phase_cofinal {s : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1) (X : ℝ) :
    ∃ x : ℝ, X ≤ x ∧ theta x = s := by
  let b₀ : ℝ := max 2 X
  have hb₀ : 1 < b₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  obtain ⟨n, hn⟩ := exists_nat_gt (psi b₀-s)
  have hnmem : (n : ℝ)+s ∈ Set.Ici (psi b₀) := by
    change psi b₀ ≤ (n : ℝ)+s
    linarith
  obtain ⟨b, hb, hphase⟩ :=
    intermediate_value_Ici (psi_continuousOn hb₀) psi_tendsto hnmem
  refine ⟨Real.exp (Real.exp b), ?_, ?_⟩
  · have h₁ := Real.add_one_le_exp b
    have h₂ := Real.add_one_le_exp (Real.exp b)
    have hxb : X ≤ b := (le_max_right 2 X).trans hb
    linarith
  · apply (theta_of_phase hs (n := n) _).2
    simpa only [B_exp_exp] using hphase



lemma theta_eventually_mem : ∀ᶠ x : ℝ in atTop, theta x ∈ Set.Ico (0 : ℝ) 1 := by
  have hp : Tendsto (fun x => psi (B x)) atTop atTop :=
    psi_tendsto.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  filter_upwards [hp.eventually (eventually_ge_atTop (0 : ℝ))] with x hx
  constructor
  · exact sub_nonneg.mpr (Nat.floor_le hx)
  · have h := Nat.lt_floor_add_one (psi (B x))
    change psi (B x) - (⌊psi (B x)⌋₊ : ℕ) < 1
    linarith

theorem coefficient_convergence_from_phase_comparison (f C : ℝ → ℝ)
    (hcomp : ∀ ε : ℝ, 0 < ε → ∃ H₀ : ℕ, ∀ H ≥ H₀,
      ∀ᶠ x : ℝ in atTop, |C x - AH H f (theta x)| ≤ ε) :
    TendstoUniformlyOn (fun H => AH H f) (A f) atTop (Set.Ico (0 : ℝ) 1) ∧
    Tendsto (fun x : ℝ => C x - A f (theta x)) atTop (nhds 0) := by
  have hcauchy : UniformCauchySeqOn (fun H => AH H f) atTop (Set.Ico (0 : ℝ) 1) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨H₀, hH₀⟩ := hcomp (ε/3) (by positivity)
    refine ⟨H₀, ?_⟩
    intro H hH K hK s hs
    obtain ⟨XH, hXH⟩ := eventually_atTop.mp (hH₀ H hH)
    obtain ⟨XK, hXK⟩ := eventually_atTop.mp (hH₀ K hK)
    obtain ⟨x, hx, hphase⟩ := exact_phase_cofinal hs (max XH XK)
    have hh := hXH x ((le_max_left XH XK).trans hx)
    have hk := hXK x ((le_max_right XH XK).trans hx)
    rw [hphase] at hh hk
    rw [Real.dist_eq]
    calc |AH H f s - AH K f s| ≤ |AH H f s - C x| + |C x - AH K f s| :=
      abs_sub_le _ _ _
      _ ≤ ε/3 + ε/3 := add_le_add (by simpa only [abs_sub_comm] using hh) hk
      _ < ε := by linarith
  have hunif : TendstoUniformlyOn (fun H => AH H f) (A f) atTop (Set.Ico (0 : ℝ) 1) := by
    apply hcauchy.tendstoUniformlyOn_of_tendsto
    intro s hs
    exact (hcauchy.cauchySeq hs).tendsto_limUnder
  refine ⟨hunif, ?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨H₀, hH₀⟩ := hcomp (ε/3) (by positivity)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp
    (Metric.tendstoUniformlyOn_iff.mp hunif (ε/3) (by positivity))
  let H := max H₀ J
  filter_upwards [hH₀ H (le_max_left _ _), theta_eventually_mem] with x hx hθ
  have hu := hJ H (le_max_right _ _) (theta x) hθ
  rw [Real.dist_eq] at hu ⊢
  rw [sub_zero]
  calc |C x - A f (theta x)| ≤
      |C x - AH H f (theta x)| + |AH H f (theta x) - A f (theta x)| := abs_sub_le _ _ _
    _ < ε/3 + ε/3 := add_lt_add_of_le_of_lt hx (by simpa only [abs_sub_comm] using hu)
    _ < ε := by linarith

theorem coefficient_bounds_of_comparison (f C : ℝ → ℝ)
    (herror : Tendsto (fun x : ℝ => C x - A f (theta x)) atTop (nhds 0))
    (cMinus cPlus : ℝ) (hb : ∀ᶠ x : ℝ in atTop, cMinus ≤ C x ∧ C x ≤ cPlus) :
    ∀ s ∈ Set.Ico (0 : ℝ) 1, cMinus ≤ A f s ∧ A f s ≤ cPlus := by
  intro s hs
  have hfind (ε : ℝ) (hε : 0 < ε) :
      ∃ x : ℝ, cMinus ≤ C x ∧ C x ≤ cPlus ∧ |C x - A f s| < ε := by
    have he := Metric.tendsto_nhds.mp herror ε hε
    obtain ⟨X, hX⟩ := eventually_atTop.mp (hb.and he)
    obtain ⟨x, hx, hphase⟩ := exact_phase_cofinal hs X
    have h := hX x hx
    refine ⟨x, h.1.1, h.1.2, ?_⟩
    simpa only [hphase, Real.dist_eq, sub_zero] using h.2
  constructor
  · by_contra h
    have hgap := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨x, hx, _, he⟩ := hfind (cMinus - A f s) hgap
    have habs := (abs_lt.mp he).2
    linarith
  · by_contra h
    have hgap := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨x, _, hx, he⟩ := hfind (A f s - cPlus) hgap
    have habs := (abs_lt.mp he).1
    linarith

end TotientAsymptotic

end

end OAI
