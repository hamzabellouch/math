import Mathlib

namespace OAI
noncomputable section

open Filter

namespace Problem337.ResidueLevels

/-- The first index at which a geometric scale reaches `exp m`. -/
def depth (A m η : ℝ) : ℕ := ⌈(A - m) / (η * m)⌉₊

/-- A geometric scale, kept in logarithmic coordinates. -/
def level (A m η : ℝ) (j : ℕ) : ℝ := Real.exp (A - η * m * j)

theorem before_depth_iff {A m η : ℝ} (hm : 0 < m) (hη : 0 < η) (j : ℕ) :
    j < depth A m η ↔ m < A - η * m * j := by
  rw [depth, Nat.lt_ceil, lt_div_iff₀ (mul_pos hη hm)]
  constructor <;> intro h <;> nlinarith

theorem depth_pos {A m η : ℝ} (hm : 0 < m) (hη : 0 < η) (hA : m < A) :
    0 < depth A m η := by
  rw [before_depth_iff hm hη]
  simpa using hA

theorem level_pos (A m η : ℝ) (j : ℕ) : 0 < level A m η j :=
  Real.exp_pos _

theorem level_strictAnti {A m η : ℝ} (hm : 0 < m) (hη : 0 < η) :
    StrictAnti (level A m η) := by
  intro i j hij
  apply Real.exp_lt_exp.mpr
  have hijR : (i : ℝ) < j := by exact_mod_cast hij
  have := mul_lt_mul_of_pos_left hijR (mul_pos hη hm)
  linarith

theorem level_above_cutoff {A m η : ℝ} (hm : 0 < m) (hη : 0 < η) (j : ℕ) :
    Real.exp m < level A m η j ↔ j < depth A m η := by
  rw [level, Real.exp_lt_exp, before_depth_iff hm hη]

theorem final_level_bounds {A m η : ℝ} (hm : 0 < m) (hη : 0 < η)
    (hA : m ≤ A) :
    Real.exp ((1 - η) * m) < level A m η (depth A m η) ∧
      level A m η (depth A m η) ≤ Real.exp m := by
  have hp : 0 < η * m := mul_pos hη hm
  have hx : 0 ≤ (A - m) / (η * m) := div_nonneg (sub_nonneg.mpr hA) hp.le
  have hl := Nat.le_ceil ((A - m) / (η * m))
  have hu := Nat.ceil_lt_add_one hx
  change (A - m) / (η * m) ≤ (depth A m η : ℝ) at hl
  change (depth A m η : ℝ) < (A - m) / (η * m) + 1 at hu
  have hl' := (div_le_iff₀ hp).1 hl
  have hu' := mul_lt_mul_of_pos_right hu hp
  rw [add_mul, div_mul_cancel₀ _ hp.ne'] at hu'
  constructor
  · apply Real.exp_lt_exp.mpr
    nlinarith
  · apply Real.exp_le_exp.mpr
    nlinarith

theorem half_log_le_next {A m η : ℝ} (hm : 0 < m) (hη : 0 < η)
    (hηhalf : η ≤ 1 / 2) {j : ℕ} (hj : j < depth A m η) :
    (A - η * m * j) / 2 ≤ A - η * m * (j + 1 : ℕ) := by
  have hj' := (before_depth_iff hm hη j).1 hj
  have hηm := mul_le_mul_of_nonneg_right hηhalf hm.le
  push_cast
  nlinarith

theorem exp_half_le_next {A m η : ℝ} (hm : 0 < m) (hη : 0 < η)
    (hηhalf : η ≤ 1 / 2) {j : ℕ} (hj : j < depth A m η) :
    Real.exp ((A - η * m * j) / 2) ≤ level A m η (j + 1) := by
  exact Real.exp_le_exp.mpr (half_log_le_next hm hη hηhalf hj)

theorem sqrt_level_le_next {A m η : ℝ} (hm : 0 < m) (hη : 0 < η)
    (hηhalf : η ≤ 1 / 2) {j : ℕ} (hj : j < depth A m η) :
    Real.sqrt (level A m η j) ≤ level A m η (j + 1) := by
  rw [Real.sqrt_le_left (level_pos A m η (j + 1)).le]
  simp only [level, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h := half_log_le_next hm hη hηhalf hj
  norm_num at *
  linarith

theorem depth_upper {A m η : ℝ} (hm : 0 < m) (hη : 0 < η)
    (hA : m ≤ A) :
    (depth A m η : ℝ) < A / (η * m) + 1 := by
  have hp : 0 < η * m := mul_pos hη hm
  have hx : 0 ≤ (A - m) / (η * m) := div_nonneg (sub_nonneg.mpr hA) hp.le
  have hu := Nat.ceil_lt_add_one hx
  change (depth A m η : ℝ) < (A - m) / (η * m) + 1 at hu
  have hle : (A - m) / (η * m) ≤ A / (η * m) :=
    div_le_div_of_nonneg_right (by linarith) hp.le
  linarith

theorem depth_log_bound {S D m η : ℝ} (_hS : 0 < S) (hlog : 1 ≤ Real.log S)
    (hD : 1 ≤ D) (hm : 0 < m) (hη : 0 < η) (hηone : η ≤ 1)
    (hmlo : S / (2 * Real.log S) ≤ m) (hmhi : m ≤ D * S) :
    (depth (D * S) m η : ℝ) ≤ (3 * D / η) * Real.log S := by
  have hp : 0 < η * m := mul_pos hη hm
  have hlogpos : 0 < Real.log S := by linarith
  have hmlo' : S ≤ m * (2 * Real.log S) :=
    (div_le_iff₀ (by positivity : 0 < 2 * Real.log S)).1 hmlo
  have hratio : D * S / (η * m) ≤ (2 * D / η) * Real.log S := by
    apply (div_le_iff₀ hp).2
    have hmul := mul_le_mul_of_nonneg_left hmlo' (show 0 ≤ D by linarith)
    have heq : (2 * D / η) * Real.log S * (η * m) = D * (m * (2 * Real.log S)) := by
      field_simp
    rw [heq]
    exact hmul
  have hDone : 1 ≤ D / η := (le_div_iff₀ hη).2 (by linarith)
  have hbudget : 1 ≤ (D / η) * Real.log S := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hDone) (sub_nonneg.mpr hlog)]
  have hu := depth_upper hm hη hmhi
  have heq : (3 * D / η) * Real.log S =
      (2 * D / η) * Real.log S + (D / η) * Real.log S := by ring
  rw [heq]
  linarith

/-- The auxiliary denominator factor changes only from `C` to `1`. -/
def factor (A m η S : ℝ) (C j : ℕ) : ℕ :=
  if Real.exp S < level A m η j then C else 1

theorem next_factor_dvd {A m η S : ℝ} (hm : 0 < m) (hη : 0 < η)
    (C j : ℕ) : factor A m η S C (j + 1) ∣ factor A m η S C j := by
  unfold factor
  split_ifs with hnext hcur hcur
  · exact dvd_refl C
  · have hdec := level_strictAnti (A := A) hm hη (Nat.lt_succ_self j)
    exact False.elim (hcur (hnext.trans hdec))
  · exact one_dvd C
  · exact dvd_refl 1

/-- The integer number of prime factors used at scale `S`. -/
def scale (S : ℝ) : ℕ := ⌊S / Real.log S⌋₊

theorem tendsto_div_log : Tendsto (fun S : ℝ => S / Real.log S) atTop atTop := by
  have ht : Tendsto (fun S : ℝ => Real.log S / S) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  apply tendsto_atTop.2
  intro b
  let c : ℝ := max b 1
  have hc : 0 < c := by dsimp [c]; positivity
  filter_upwards [ht.eventually (gt_mem_nhds (one_div_pos.mpr hc)),
    eventually_gt_atTop (1 : ℝ)] with S hratio hS
  have hSp : 0 < S := by linarith
  have hlogp : 0 < Real.log S := Real.log_pos hS
  have hprod := (div_lt_div_iff₀ hSp hc).1 hratio
  have hlt : c < S / Real.log S := (lt_div_iff₀ hlogp).2 (by nlinarith)
  exact (le_max_left b 1).trans hlt.le

theorem scale_bounds {S : ℝ} (hS : 0 < S) (hlog : 0 < Real.log S)
    (hratio : 2 ≤ S / Real.log S) :
    S / (2 * Real.log S) ≤ (scale S : ℝ) ∧
      (scale S : ℝ) ≤ S / Real.log S := by
  have hx : 0 ≤ S / Real.log S := div_nonneg hS.le hlog.le
  have hfloor := Nat.lt_floor_add_one (S / Real.log S)
  have hle := Nat.floor_le hx
  change S / Real.log S < (scale S : ℝ) + 1 at hfloor
  change (scale S : ℝ) ≤ S / Real.log S at hle
  have heq : S / (2 * Real.log S) = (S / Real.log S) / 2 := by ring
  refine ⟨?_, hle⟩
  rw [heq]
  linarith

theorem eventually_scale_bounds : ∀ᶠ S : ℝ in atTop,
    1 ≤ Real.log S ∧ 2 ≤ scale S ∧
    S / (2 * Real.log S) ≤ (scale S : ℝ) ∧
    (scale S : ℝ) ≤ S / Real.log S := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_div_log.eventually (eventually_ge_atTop (2 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with S hlog hratio hS
  refine ⟨hlog, Nat.le_floor hratio, ?_⟩
  exact scale_bounds (by linarith) (by linarith) hratio

theorem tendsto_scale : Tendsto (fun S : ℝ => (scale S : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (tendsto_div_log.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  filter_upwards [eventually_scale_bounds] with S hS
  have heq : (S / Real.log S) / 2 = S / (2 * Real.log S) := by ring
  simpa only [heq] using hS.2.2.1

theorem tendsto_div_scale : Tendsto (fun S : ℝ => S / (scale S : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ Real.tendsto_log_atTop
  filter_upwards [eventually_scale_bounds] with S hS
  have hscale : (0 : ℝ) < scale S := by exact_mod_cast (show 0 < scale S by omega)
  have hlog : 0 < Real.log S := by linarith [hS.1]
  apply (le_div_iff₀ hscale).2
  have hprod := (le_div_iff₀ hlog).1 hS.2.2.2
  nlinarith

theorem eventually_depth_log_bound {D η : ℝ} (hD : 1 ≤ D) (hη : 0 < η)
    (hηone : η ≤ 1) : ∀ᶠ S : ℝ in atTop,
    (depth (D * S) (scale S) η : ℝ) ≤ (3 * D / η) * Real.log S := by
  filter_upwards [eventually_scale_bounds, eventually_gt_atTop (1 : ℝ)] with S hS hSp
  have hm : (0 : ℝ) < scale S := by exact_mod_cast (show 0 < scale S by omega)
  have hlog : 0 < Real.log S := by linarith [hS.1]
  have hratio : S / Real.log S ≤ S := by
    apply (div_le_iff₀ hlog).2
    nlinarith [hS.1]
  have hDS : S ≤ D * S := by nlinarith
  exact depth_log_bound (by linarith) hS.1 hD hm hη hηone hS.2.2.1
    (hS.2.2.2.trans (hratio.trans hDS))

/-- An error exponential in `S` is negligible beside any fixed exponential
in the smaller prime-product scale. -/
theorem eventually_exp_absorb {a b c C : ℝ} (hab : a < b) (hc : 0 < c)
    (hC : 0 ≤ C) : ∀ᶠ S : ℝ in atTop,
    Real.exp (-b * scale S) + C * Real.exp (-c * S) ≤
      Real.exp (-a * scale S) := by
  have ht₁ : Tendsto (fun S : ℝ => Real.exp (-((b - a) * scale S))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_scale.const_mul_atTop (sub_pos.mpr hab))
  have ht₂ : Tendsto (fun S : ℝ => C * Real.exp (-(scale S : ℝ))) atTop (nhds 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_scale).const_mul C
  have hsmall : ∀ᶠ S : ℝ in atTop,
      Real.exp (-((b - a) * scale S)) + C * Real.exp (-(scale S : ℝ)) ≤ 1 := by
    apply Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1)
    simpa using ht₁.add ht₂
  filter_upwards [hsmall, eventually_scale_bounds,
    tendsto_div_scale.eventually (eventually_ge_atTop ((a + 1) / c))] with S hs hm hr
  have hmp : (0 : ℝ) < scale S := by exact_mod_cast (show 0 < scale S by omega)
  have hr' := (le_div_iff₀ hmp).1 hr
  have hr'' := mul_le_mul_of_nonneg_left hr' hc.le
  have heq : c * ((a + 1) / c * (scale S : ℝ)) = (a + 1) * scale S := by
    field_simp
  rw [heq] at hr''
  have hexp : Real.exp (-c * S) ≤ Real.exp (-(a + 1) * scale S) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have heq₁ : Real.exp (-b * scale S) =
      Real.exp (-a * scale S) * Real.exp (-((b - a) * scale S)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have heq₂ : Real.exp (-(a + 1) * scale S) =
      Real.exp (-a * scale S) * Real.exp (-(scale S : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (-b * scale S) + C * Real.exp (-c * S) ≤
        Real.exp (-b * scale S) + C * Real.exp (-(a + 1) * scale S) := by
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hexp hC)
    _ = Real.exp (-a * scale S) *
        (Real.exp (-((b - a) * scale S)) + C * Real.exp (-(scale S : ℝ))) := by
      rw [heq₁, heq₂]
      ring
    _ ≤ Real.exp (-a * scale S) := by
      simpa using mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le

theorem eventually_deterministic_mean_bound {a c C : ℝ}
    (ha : a < Real.log 2) (hc : 0 < c) (hC : 0 ≤ C) :
    ∀ᶠ S : ℝ in atTop,
      (1 / 2 : ℝ) ^ scale S + C * Real.exp (-c * S) ≤
        Real.exp (-a * scale S) := by
  filter_upwards [eventually_exp_absorb ha hc hC] with S hS
  have heq : Real.exp (-Real.log 2 * (scale S : ℝ)) = (1 / 2 : ℝ) ^ scale S := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp only [one_div]
  simpa only [heq] using hS

@[simp] theorem level_zero (A m η : ℝ) : level A m η 0 = Real.exp A := by
  simp [level]

theorem level_succ (A m η : ℝ) (j : ℕ) :
    level A m η (j + 1) = Real.exp (-η * m) * level A m η j := by
  simp only [level, Nat.cast_add, Nat.cast_one, ← Real.exp_add]
  congr 1
  ring

theorem final_factor_one {A m η S : ℝ} (hm : 0 < m) (hη : 0 < η)
    (hA : m ≤ A) (hmS : m ≤ S) (C : ℕ) :
    factor A m η S C (depth A m η) = 1 := by
  have hfinal := (final_level_bounds hm hη hA).2
  have hle : level A m η (depth A m η) ≤ Real.exp S :=
    hfinal.trans (Real.exp_le_exp.mpr hmS)
  simp only [factor, not_lt.mpr hle, ↓reduceIte]

/-- Finite adjacent descending intervals cover the region between the endpoints.
No continuity or integrality of interval endpoints is required. -/
theorem exists_interval_index {f : ℕ → ℝ} {d : ℕ} {u : ℝ}
    (hlo : f d < u) (hhi : u ≤ f 0) :
    ∃ j : ℕ, j < d ∧ f (j + 1) < u ∧ u ≤ f j := by
  induction d with
  | zero => exact False.elim (not_lt_of_ge hhi hlo)
  | succ d ih =>
      by_cases hdu : f d < u
      · obtain ⟨j, hj, hjlo, hjhi⟩ := ih hdu
        exact ⟨j, by omega, hjlo, hjhi⟩
      · exact ⟨d, Nat.lt_succ_self d, hlo, le_of_not_gt hdu⟩

theorem interval_index_unique {f : ℕ → ℝ} (hf : StrictAnti f)
    {u : ℝ} {i j : ℕ} (hi : f (i + 1) < u ∧ u ≤ f i)
    (hj : f (j + 1) < u ∧ u ≤ f j) : i = j := by
  apply Nat.le_antisymm
  · by_contra h
    have hji : j + 1 ≤ i := by omega
    have hle := hf.antitone hji
    linarith [hj.1, hi.2]
  · by_contra h
    have hij : i + 1 ≤ j := by omega
    have hle := hf.antitone hij
    linarith [hi.1, hj.2]

theorem exists_unique_level_interval {A m η : ℝ} (hm : 0 < m) (hη : 0 < η)
    {u : ℝ} (hlo : level A m η (depth A m η) < u) (hhi : u ≤ Real.exp A) :
    ∃! j : ℕ, j < depth A m η ∧ level A m η (j + 1) < u ∧
      u ≤ level A m η j := by
  obtain ⟨j, hj, hjlo, hjhi⟩ := exists_interval_index hlo (by simpa using hhi)
  refine ⟨j, ⟨hj, hjlo, hjhi⟩, ?_⟩
  intro i hi
  exact interval_index_unique (level_strictAnti hm hη) hi.2 ⟨hjlo, hjhi⟩

/-- Every auxiliary factor is positive once the initial factor is. -/
theorem factor_pos {A m η S : ℝ} {C : ℕ} (hC : 0 < C) (j : ℕ) :
    0 < factor A m η S C j := by
  unfold factor
  split_ifs <;> omega

theorem factor_le {A m η S : ℝ} {C : ℕ} (hC : 0 < C) (j : ℕ) :
    factor A m η S C j ≤ C := by
  unfold factor
  split_ifs <;> omega

theorem factor_zero {D S m η : ℝ} (hD : 1 < D) (hS : 0 < S) (C : ℕ) :
    factor (D * S) m η S C 0 = C := by
  have hlog : S < D * S := by nlinarith
  simp only [factor, level_zero, Real.exp_lt_exp.mpr hlog, ↓reduceIte]

theorem factor_eq_of_large_numerator {A m η S u : ℝ} {C j : ℕ}
    (hu : Real.exp S < u) (huj : u ≤ level A m η j) :
    factor A m η S C j = C := by
  simp only [factor, hu.trans_le huj, ↓reduceIte]

/-- The floor scale lies below the original scale; this is the missing
comparison needed to certify that the terminal auxiliary factor equals one. -/
theorem scale_le_self {S : ℝ} (hS : 0 ≤ S) (hlog : 1 ≤ Real.log S) :
    (scale S : ℝ) ≤ S := by
  have hlogpos : 0 < Real.log S := by linarith
  have hratio : 0 ≤ S / Real.log S := div_nonneg hS hlogpos.le
  apply (Nat.floor_le hratio).trans
  apply (div_le_iff₀ hlogpos).2
  nlinarith

end Problem337.ResidueLevels

end

end OAI
