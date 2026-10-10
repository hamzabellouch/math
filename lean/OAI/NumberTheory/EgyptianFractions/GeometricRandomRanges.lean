import OAI.NumberTheory.EgyptianFractions.ResidueLevels

namespace OAI
noncomputable section
open Filter

namespace Problem337.GeometricRandomRanges

/-- The common geometric cutoffs used in the random middle-level selection. -/
def cutoff (D S : ℝ) (j : ℕ) : ℝ :=
  ResidueLevels.level (D * S) (ResidueLevels.scale S) (1 / 10000) j

/-- Only levels whose denominator factor is one need a random block. -/
def middleTests (D S : ℝ) : Finset ℕ :=
  (Finset.range (ResidueLevels.depth (D * S) (ResidueLevels.scale S) (1 / 10000))).filter
    (fun j => cutoff D S j ≤ Real.exp S)

/-- Positive integers in the open-closed interval between adjacent cutoffs. -/
def middleLevel (D S : ℝ) (j : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊cutoff D S j⌋₊).filter
    (fun u => cutoff D S (j + 1) < (u : ℝ))

/-- The terminal numerators not covered by the binary factor. -/
def terminalRange (S : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊Real.exp (ResidueLevels.scale S)⌋₊).filter
    (fun u => S ^ 100000 < (u : ℝ))

/-- The floor prime-product scale eventually dominates any fixed multiple of
`log S`. This simultaneously handles the number of levels and the random
product theorem's lower logarithmic cutoff. -/
theorem eventually_log_mul_le_scale (K : ℝ) :
    ∀ᶠ S : ℝ in atTop, K * Real.log S ≤ (ResidueLevels.scale S : ℝ) := by
  let C : ℝ := max K 1
  have hC : 0 < C := by dsimp [C]; positivity
  have ht : Tendsto (fun S : ℝ => Real.log S ^ 2 / S) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have heps : 0 < 1 / (2 * C) := by positivity
  filter_upwards [ht.eventually (gt_mem_nhds heps),
    ResidueLevels.eventually_scale_bounds, eventually_gt_atTop (1 : ℝ)] with S hsmall hm hS
  have hSpos : 0 < S := by linarith
  have hlog : 0 < Real.log S := Real.log_pos hS
  have hcross : 2 * C * Real.log S ^ 2 < S := by
    have h := (div_lt_div_iff₀ hSpos (by positivity : 0 < 2 * C)).mp hsmall
    nlinarith
  have hfloor := (div_le_iff₀ (by positivity : 0 < 2 * Real.log S)).mp hm.2.2.1
  have hCle : C * Real.log S ≤ (ResidueLevels.scale S : ℝ) := by
    nlinarith
  exact (mul_le_mul_of_nonneg_right (le_max_left K 1) hlog.le).trans hCle

theorem mem_middleTests {D S : ℝ} {j : ℕ} (hj : j ∈ middleTests D S) :
    j < ResidueLevels.depth (D * S) (ResidueLevels.scale S) (1 / 10000) ∧
      cutoff D S j ≤ Real.exp S := by
  simpa only [middleTests, Finset.mem_filter, Finset.mem_range] using hj

theorem mem_middleLevel {D S : ℝ} {j u : ℕ} (hu : u ∈ middleLevel D S j) :
    0 < u ∧ cutoff D S (j + 1) < (u : ℝ) ∧ (u : ℝ) ≤ cutoff D S j := by
  obtain ⟨huI, hlo⟩ := Finset.mem_filter.mp hu
  obtain ⟨hupos, huhi⟩ := Finset.mem_Icc.mp huI
  refine ⟨hupos, hlo, ?_⟩
  exact (Nat.cast_le.mpr huhi).trans
    (Nat.floor_le (ResidueLevels.level_pos _ _ _ _).le)

theorem middleLevel_card_le (D S : ℝ) (j : ℕ) :
    ((middleLevel D S j).card : ℝ) ≤ cutoff D S j := by
  have hcard : (middleLevel D S j).card ≤ ⌊cutoff D S j⌋₊ := by
    apply le_trans (Finset.card_filter_le _ _)
    simp
  exact (Nat.cast_le.mpr hcard).trans
    (Nat.floor_le (ResidueLevels.level_pos _ _ _ _).le)

/-- The exact logarithmic window, including the slight overlap of the middle
level with numerators below `exp m`. -/
theorem middle_log_bounds {D S : ℝ}
    (hm : 0 < (ResidueLevels.scale S : ℝ)) {j u : ℕ}
    (hj : j ∈ middleTests D S) (hu : u ∈ middleLevel D S j) :
    (9999 / 10000 : ℝ) * (ResidueLevels.scale S : ℝ) < Real.log (u : ℝ) ∧
      Real.log (u : ℝ) ≤ S := by
  obtain ⟨hjdepth, hjtop⟩ := mem_middleTests hj
  obtain ⟨hupos, hulow, huhi⟩ := mem_middleLevel hu
  have hur : (0 : ℝ) < u := by exact_mod_cast hupos
  have hbefore := (ResidueLevels.before_depth_iff hm
    (by norm_num : (0 : ℝ) < 1 / 10000) j).mp hjdepth
  have hloglower : D * S - (1 / 10000 : ℝ) * ResidueLevels.scale S * (j + 1 : ℕ) <
      Real.log (u : ℝ) := by
    exact (Real.lt_log_iff_exp_lt hur).mpr hulow
  have hnext : (9999 / 10000 : ℝ) * (ResidueLevels.scale S : ℝ) <
      D * S - (1 / 10000 : ℝ) * ResidueLevels.scale S * (j + 1 : ℕ) := by
    push_cast
    nlinarith
  refine ⟨hnext.trans hloglower, ?_⟩
  exact (Real.log_le_iff_le_exp hur).mpr (huhi.trans hjtop)

theorem mem_terminalRange {S : ℝ} {u : ℕ} (hu : u ∈ terminalRange S) :
    0 < u ∧ S ^ 100000 < (u : ℝ) ∧
      (u : ℝ) ≤ Real.exp (ResidueLevels.scale S) := by
  obtain ⟨huI, hlo⟩ := Finset.mem_filter.mp hu
  obtain ⟨hupos, huhi⟩ := Finset.mem_Icc.mp huI
  exact ⟨hupos, hlo, (Nat.cast_le.mpr huhi).trans
    (Nat.floor_le (Real.exp_pos _).le)⟩

/-- The terminal range has exactly the log window required by random products. -/
theorem terminal_log_bounds {S : ℝ} (hS : 0 < S) {u : ℕ}
    (hu : u ∈ terminalRange S) :
    100000 * Real.log S < Real.log (u : ℝ) ∧
      Real.log (u : ℝ) ≤ (ResidueLevels.scale S : ℝ) := by
  obtain ⟨hupos, hlo, hhi⟩ := mem_terminalRange hu
  have hur : (0 : ℝ) < u := by exact_mod_cast hupos
  constructor
  · have hlog := Real.log_lt_log (pow_pos hS 100000) hlo
    simpa only [Real.log_pow, Nat.cast_ofNat] using hlog
  · exact (Real.log_le_iff_le_exp hur).mpr hhi

/-- All non-arithmetic hypotheses of the common sampled-Fourier selection,
for the actual geometric middle levels and terminal interval. The finite
indices retain multiplicity; no residue or cancellation bound is assumed. -/
structure SelectionRanges (D S : ℝ) (N : ℕ) : Prop where
  parameter_large : 8 ≤ S
  scale_large : 500000 ≤ (ResidueLevels.scale S : ℝ)
  tests_card : ((middleTests D S).card : ℝ) ≤ (ResidueLevels.scale S : ℝ)
  cutoff_positive : ∀ j ∈ middleTests D S, 0 < cutoff D S j
  level_card : ∀ j ∈ middleTests D S, ((middleLevel D S j).card : ℝ) ≤ cutoff D S j
  middle_window : ∀ j ∈ middleTests D S, ∀ u ∈ middleLevel D S j,
    100000 * Real.log S ≤ Real.log (u : ℝ) ∧ Real.log (u : ℝ) ≤ S ∧
      (9999 / 10000 : ℝ) * (ResidueLevels.scale S : ℝ) ≤ Real.log (u : ℝ)
  terminal_threshold : ∀ u ∈ terminalRange S, N ≤ u
  terminal_window : ∀ u ∈ terminalRange S,
    100000 * Real.log S ≤ Real.log (u : ℝ) ∧
      Real.log (u : ℝ) ≤ (ResidueLevels.scale S : ℝ)

/-- A single onset works for all middle levels and terminal numerators.
In particular the abstract random-selection range premises are satisfied
by the explicit geometric cutoffs, not assumed separately. -/
theorem eventually_selectionRanges (D : ℝ) (hD : 1 ≤ D) (N : ℕ) :
    ∀ᶠ S : ℝ in atTop, SelectionRanges D S N := by
  filter_upwards [ResidueLevels.eventually_scale_bounds,
    ResidueLevels.eventually_depth_log_bound hD (by norm_num : (0 : ℝ) < 1 / 10000)
      (by norm_num : (1 / 10000 : ℝ) ≤ 1),
    eventually_log_mul_le_scale (3 * D / (1 / 10000)),
    eventually_log_mul_le_scale 200000,
    ResidueLevels.tendsto_scale.eventually (eventually_ge_atTop (500000 : ℝ)),
    eventually_ge_atTop (8 : ℝ), eventually_ge_atTop (N : ℝ)]
    with S hscale hdepth hcount hlogscale hlarge hS8 hN
  have hS : 1 < S := by linarith
  have hm : 0 < (ResidueLevels.scale S : ℝ) := by linarith
  have hlog : 0 ≤ Real.log S := (Real.log_pos hS).le
  refine ⟨hS8, hlarge, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hcard : (middleTests D S).card ≤
        ResidueLevels.depth (D * S) (ResidueLevels.scale S) (1 / 10000) := by
      apply le_trans (Finset.card_filter_le _ _)
      simp
    exact (Nat.cast_le.mpr hcard).trans (hdepth.trans hcount)
  · intro j hj
    exact ResidueLevels.level_pos _ _ _ _
  · intro j hj
    exact middleLevel_card_le D S j
  · intro j hj u hu
    obtain ⟨hlo, hhi⟩ := middle_log_bounds hm hj hu
    exact ⟨by nlinarith, hhi, hlo.le⟩
  · intro u hu
    obtain ⟨_, hlo, _⟩ := mem_terminalRange hu
    have hpow : S ≤ S ^ 100000 := le_self_pow₀ hS.le (by norm_num)
    have hNu : (N : ℝ) ≤ u := hN.trans (hpow.trans hlo.le)
    exact_mod_cast hNu
  · intro u hu
    obtain ⟨hlo, hhi⟩ := terminal_log_bounds (by linarith : 0 < S) hu
    exact ⟨hlo.le, hhi⟩

/-- Characterization for applying a selected finite-level conclusion to an
arbitrary integer in the geometric interval. -/
theorem mem_middleLevel_iff {D S : ℝ} {j u : ℕ} :
    u ∈ middleLevel D S j ↔
      0 < u ∧ cutoff D S (j + 1) < (u : ℝ) ∧ (u : ℝ) ≤ cutoff D S j := by
  constructor
  · exact mem_middleLevel
  · rintro ⟨hu, hlo, hhi⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hu, Nat.le_floor hhi⟩, hlo⟩

/-- Characterization for applying the terminal conclusion outside the binary
range. It retains the open lower endpoint and the closed upper endpoint. -/
theorem mem_terminalRange_iff {S : ℝ} {u : ℕ} :
    u ∈ terminalRange S ↔ 0 < u ∧ S ^ 100000 < (u : ℝ) ∧
      (u : ℝ) ≤ Real.exp (ResidueLevels.scale S) := by
  constructor
  · exact mem_terminalRange
  · rintro ⟨hu, hlo, hhi⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hu, Nat.le_floor hhi⟩, hlo⟩

theorem mem_middleTests_iff {D S : ℝ} {j : ℕ} :
    j ∈ middleTests D S ↔
      j < ResidueLevels.depth (D * S) (ResidueLevels.scale S) (1 / 10000) ∧
        cutoff D S j ≤ Real.exp S := by
  simp only [middleTests, Finset.mem_filter, Finset.mem_range]

end Problem337.GeometricRandomRanges

end

end OAI
