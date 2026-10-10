import OAI.Analysis.PeriodicLattice.Signals

namespace OAI

/-! Locally finite smooth profiles and their parameter estimates. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingProfiles {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace Profiles

open scoped ContDiff Topology
open Filter Set

def clock (t : ℝ) : ℝ :=
  letI := threeAtLeastTwo
  Real.smoothTransition (3 * t - 1)

def bump (x : ℝ) : ℝ :=
  letI := threeAtLeastTwo
  letI := eightAtLeastTwo
  Real.smoothTransition (8 * x + 3) * Real.smoothTransition (3 - 8 * x)

theorem clock_contDiff : ContDiff ℝ ∞ clock := by
  unfold clock
  fun_prop

theorem clock_nonneg (t : ℝ) : 0 ≤ clock t := Real.smoothTransition.nonneg _

theorem clock_le_one (t : ℝ) : clock t ≤ 1 := Real.smoothTransition.le_one _

theorem clock_zero {t : ℝ} (ht : t ≤ 1 / 3) : clock t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

theorem clock_one {t : ℝ} (ht : 2 / 3 ≤ t) : clock t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

theorem clock_monotone : Monotone clock := by
  intro t s h
  exact Real.smoothTransition.monotone (by linarith)

theorem bump_contDiff : ContDiff ℝ ∞ bump := by
  unfold bump
  fun_prop

theorem bump_nonneg (x : ℝ) : 0 ≤ bump x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem bump_le_one (x : ℝ) : bump x ≤ 1 := by
  unfold bump
  exact (mul_le_of_le_one_left (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _)

theorem bump_one {x : ℝ} (hx : |x| ≤ 1 / 4) : bump x = 1 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hx
  rw [bump, Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), one_mul]

theorem bump_zero {x : ℝ} (hx : 3 / 8 ≤ |x|) : bump x = 0 := by
  rcases le_abs.mp hx with h | h
  · rw [bump, Real.smoothTransition.zero_of_nonpos (x := 3 - 8 * x) (by linarith), mul_zero]
  · rw [bump, Real.smoothTransition.zero_of_nonpos (x := 8 * x + 3) (by linarith), zero_mul]

theorem bump_support : Function.support bump ⊆ Set.Icc (-(3 / 8 : ℝ)) (3 / 8) := by
  intro x hx
  have h : |x| < 3 / 8 := lt_of_not_ge (fun h => hx (bump_zero h))
  exact ⟨by have := (abs_lt.mp h).1; linarith, (abs_lt.mp h).2.le⟩

theorem clock_deriv_eq_zero {t : ℝ} (ht : t < 1 / 3 ∨ 2 / 3 < t) :
    deriv clock t = 0 := by
  rcases ht with ht | ht
  · have hev : clock =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact clock_zero hs.le
    simpa using hev.deriv_eq
  · have hev : clock =ᶠ[𝓝 t] (fun _ => (1 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact clock_one hs.le
    simpa using hev.deriv_eq

theorem clock_deriv_contDiff : ContDiff ℝ ∞ (deriv clock) :=
  (contDiff_infty_iff_deriv.mp clock_contDiff).2

theorem lattice_intervals_locallyFinite :
    LocallyFinite (fun j : ℤ => Set.Icc ((j : ℝ) - 3 / 8) ((j : ℝ) + 3 / 8)) := by
  apply locallyFinite_Icc_of_tendsto
  · simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-(3 / 8 : ℝ))
        (tendsto_intCast_atTop_atTop : Tendsto (fun j : ℤ => (j : ℝ)) atTop atTop)
  · exact tendsto_atBot_add_const_right atBot (3 / 8 : ℝ)
      (tendsto_intCast_atBot_iff.mpr tendsto_id)

def latticeBump (e : ℝ) (j : ℤ) (y : ℝ) : ℝ :=
  letI := twoAtLeastTwo
  bump ((y - 1 / 2) / e - j)

theorem latticeBump_contDiff (e : ℝ) (j : ℤ) : ContDiff ℝ ∞ (latticeBump e j) := by
  unfold latticeBump
  exact bump_contDiff.comp ((contDiff_id.sub contDiff_const).div_const e |>.sub contDiff_const)

theorem latticeBump_locallyFinite (e : ℝ) :
    LocallyFinite (fun j : ℤ => Function.support (latticeBump e j)) := by
  have hc : Continuous (fun y : ℝ => (y - 1 / 2) / e) := by fun_prop
  apply (lattice_intervals_locallyFinite.preimage_continuous hc).subset
  intro j y hy
  have h := bump_support hy
  simp only [Set.mem_preimage, Set.mem_Icc] at *
  change -(3 / 8) ≤ (y - 1 / 2) / e - (j : ℝ) ∧
    (y - 1 / 2) / e - (j : ℝ) ≤ 3 / 8 at h
  constructor <;> linarith

def selector (e : ℝ) (A : ℤ → ℝ) (y : ℝ) : ℝ := ∑ᶠ j : ℤ, A j * latticeBump e j y

theorem selector_contDiff (e : ℝ) (A : ℤ → ℝ) : ContDiff ℝ ∞ (selector e A) := by
  apply contMDiff_iff_contDiff.mp
  apply contMDiff_finsum
  · intro j
    exact contMDiff_iff_contDiff.mpr (contDiff_const.mul (latticeBump_contDiff e j))
  · apply (latticeBump_locallyFinite e).subset
    intro j y hy
    exact fun hz => hy (by simp [hz])

theorem other_bump_zero (e : ℝ) {y : ℝ} {j k : ℤ}
    (hj : |(y - 1 / 2) / e - j| ≤ 1 / 4) (hkj : k ≠ j) : latticeBump e k y = 0 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hj
  apply bump_zero
  rcases lt_or_gt_of_ne hkj with hk | hk
  · have hk' : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ j)
    apply (le_abs).mpr (Or.inl ?_)
    linarith
  · have hk' : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (by omega : j + 1 ≤ k)
    apply (le_abs).mpr (Or.inr ?_)
    linarith

theorem selector_plateau (e : ℝ) (A : ℤ → ℝ) {y : ℝ} {j : ℤ}
    (hj : |(y - 1 / 2) / e - j| ≤ 1 / 4) : selector e A y = A j := by
  unfold selector
  rw [finsum_eq_single _ j (fun k hk => by rw [other_bump_zero e hj hk, mul_zero])]
  rw [latticeBump, bump_one hj, mul_one]

theorem selector_shift (e : ℝ) (he : e ≠ 0) (A : ℤ → ℝ) (N : ℤ)
    (hA : Function.Periodic A N) (y : ℝ) :
    selector e A (y + e * N) = selector e A y := by
  unfold selector
  rw [← finsum_comp_equiv (Equiv.addRight N)]
  apply finsum_congr
  intro j
  simp only [Equiv.coe_addRight, latticeBump, Int.cast_add]
  rw [hA j]
  congr 2
  field_simp
  ring

theorem selector_single {e y : ℝ} (A : ℤ → ℝ) {j : ℤ}
    (hj : |(y - 1 / 2) / e - j| < 5 / 8) :
    selector e A y = A j * latticeBump e j y := by
  unfold selector
  apply finsum_eq_single
  intro k hk
  have hz : latticeBump e k y = 0 := by
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hj
    apply bump_zero
    rcases lt_or_gt_of_ne hk with h | h
    · have h' : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ j)
      apply (le_abs).mpr (Or.inl ?_)
      linarith
    · have h' : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (by omega : j + 1 ≤ k)
      apply (le_abs).mpr (Or.inr ?_)
      linarith
  rw [hz, mul_zero]

theorem selector_eventually_single {e y : ℝ} (A : ℤ → ℝ) {j : ℤ}
    (hj : |(y - 1 / 2) / e - j| ≤ 1 / 2) :
    selector e A =ᶠ[𝓝 y] (fun z => A j * latticeBump e j z) := by
  have hc : Continuous (fun z : ℝ => |(z - 1 / 2) / e - (j : ℝ)|) := by fun_prop
  have hy : |(y - 1 / 2) / e - j| < 5 / 8 := by linarith
  filter_upwards [hc.continuousAt.eventually (gt_mem_nhds hy)] with z hz
  exact selector_single A hz

theorem latticeBump_iteratedDeriv (e : ℝ) (j : ℤ) (k : ℕ) :
    iteratedDeriv k (latticeBump e j) =
      fun y => (e⁻¹) ^ k * iteratedDeriv k bump ((y - 1 / 2) / e - j) := by
  have ih : ContDiff ℝ k (fun z : ℝ => bump (z - j)) :=
    (bump_contDiff.comp (contDiff_id.sub contDiff_const)).of_le (WithTop.coe_le_coe.mpr le_top)
  have heq : latticeBump e j = (fun z : ℝ =>
      (fun w : ℝ => bump (w - j)) (e⁻¹ * (z - 1 / 2))) := by
    ext z
    simp only [latticeBump, div_eq_mul_inv, mul_comm]
  rw [heq, iteratedDeriv_comp_sub_const k (fun w => bump (e⁻¹ * w - j)) (1 / 2),
    iteratedDeriv_comp_const_mul ih e⁻¹, iteratedDeriv_comp_sub_const]
  simp only [div_eq_mul_inv, mul_comm]

theorem selector_iteratedDeriv {e y : ℝ} (A : ℤ → ℝ) {j : ℤ}
    (hj : |(y - 1 / 2) / e - j| ≤ 1 / 2) (k : ℕ) :
    iteratedDeriv k (selector e A) y =
      A j * (e⁻¹) ^ k * iteratedDeriv k bump ((y - 1 / 2) / e - j) := by
  rw [(selector_eventually_single A hj).iteratedDeriv_eq,
    iteratedDeriv_const_mul_field, latticeBump_iteratedDeriv]
  exact (mul_assoc _ _ _).symm

theorem selector_derivative_bound {e B D : ℝ} (he : 0 < e) (A : ℤ → ℝ) (k : ℕ)
    (hA : ∀ j, |A j| ≤ B) (hD : ∀ z, |iteratedDeriv k bump z| ≤ D) (y : ℝ) :
    |iteratedDeriv k (selector e A) y| ≤ B * (e⁻¹) ^ k * D := by
  let z : ℝ := (y - 1 / 2) / e
  let j : ℤ := ⌊z + 1 / 2⌋
  have hj₁ := Int.floor_le (z + 1 / 2)
  have hj₂ := Int.lt_floor_add_one (z + 1 / 2)
  have hj : |(y - 1 / 2) / e - (j : ℝ)| ≤ 1 / 2 := by
    apply abs_le.mpr
    dsimp [z, j] at *
    constructor <;> linarith
  rw [selector_iteratedDeriv A hj, abs_mul, abs_mul,
    abs_of_nonneg (pow_nonneg (inv_nonneg.mpr he.le) k)]
  have hB : 0 ≤ B := (abs_nonneg _).trans (hA j)
  exact mul_le_mul (mul_le_mul_of_nonneg_right (hA j) (by positivity))
    (hD _) (abs_nonneg _) (by positivity)

def shiftedClock (n : ℕ) (t : ℝ) : ℝ := clock (t - n)

def pulse (n : ℕ) (t : ℝ) : ℝ := deriv clock (t - n)

theorem shiftedClock_contDiff (n : ℕ) : ContDiff ℝ ∞ (shiftedClock n) :=
  clock_contDiff.comp (contDiff_id.sub contDiff_const)

theorem pulse_contDiff (n : ℕ) : ContDiff ℝ ∞ (pulse n) :=
  clock_deriv_contDiff.comp (contDiff_id.sub contDiff_const)

theorem shiftedClock_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (shiftedClock n) (pulse n t) t := by
  have hd := ((contDiff_infty_iff_deriv.mp clock_contDiff).1 (t - n)).hasDerivAt
  exact hd.comp_sub_const t (n : ℝ)

theorem pulse_eq_zero {n : ℕ} {t : ℝ} (ht : t < n + 1 / 3 ∨ n + 2 / 3 < t) :
    pulse n t = 0 := by
  apply clock_deriv_eq_zero
  rcases ht with ht | ht
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

theorem pulse_support (n : ℕ) :
    Function.support (pulse n) ⊆ Icc ((n : ℝ) + 1 / 3) (n + 2 / 3) := by
  intro t ht
  constructor
  · by_contra h
    exact ht (pulse_eq_zero (Or.inl (lt_of_not_ge h)))
  · by_contra h
    exact ht (pulse_eq_zero (Or.inr (lt_of_not_ge h)))

theorem time_tails_locallyFinite : LocallyFinite (fun n : ℕ => Ici (n : ℝ)) := by
  intro t
  refine ⟨Iio (t + 1), Iio_mem_nhds (by linarith), ?_⟩
  apply (finite_Iic ⌈t + 1⌉₊).subset
  rintro n ⟨s, hs, hs'⟩
  have hn : (n : ℝ) ≤ (⌈t + 1⌉₊ : ℝ) :=
    hs.trans ((le_of_lt hs').trans (Nat.le_ceil _))
  exact_mod_cast hn

theorem shiftedClock_locallyFinite :
    LocallyFinite (fun n : ℕ => Function.support (shiftedClock n)) := by
  apply time_tails_locallyFinite.subset
  intro n t ht
  by_contra h
  have hn : t < (n : ℝ) := lt_of_not_ge h
  exact ht (clock_zero (by linarith))

theorem pulse_locallyFinite : LocallyFinite (fun n : ℕ => Function.support (pulse n)) := by
  apply time_tails_locallyFinite.subset
  intro n t ht
  have := (pulse_support n ht).1
  change (n : ℝ) ≤ t
  linarith

theorem other_pulse_zero {n m : ℕ} (hne : m ≠ n) {t : ℝ}
    (ht : (n : ℝ) ≤ t) (ht' : t ≤ n + 1) : pulse m t = 0 := by
  apply pulse_eq_zero
  rcases lt_or_gt_of_ne hne with h | h
  · have h' : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h
    exact Or.inr (by linarith)
  · have h' : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h
    exact Or.inl (by linarith)

def schedule {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : ℕ → ℝ → E) (t y : ℝ) : E := ∑ᶠ n : ℕ, pulse n t • V n y

theorem schedule_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : ℕ → ℝ → E) (hV : ∀ n, ContDiff ℝ ∞ (V n)) :
    ContDiff ℝ ∞ (fun ty : ℝ × ℝ => schedule V ty.1 ty.2) := by
  apply contMDiff_iff_contDiff.mp
  apply contMDiff_finsum
  · intro n
    exact contMDiff_iff_contDiff.mpr
      (((pulse_contDiff n).comp contDiff_fst).smul ((hV n).comp contDiff_snd))
  · apply (pulse_locallyFinite.preimage_continuous continuous_fst).subset
    intro n ty hty
    exact fun hz => hty (by simp [hz])

theorem schedule_on_slot {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : ℕ → ℝ → E) (n : ℕ) {t : ℝ} (ht : (n : ℝ) ≤ t) (ht' : t ≤ n + 1)
    (y : ℝ) : schedule V t y = pulse n t • V n y := by
  apply finsum_eq_single
  intro m hm
  rw [other_pulse_zero hm ht ht', zero_smul]

theorem schedule_zero_at_start {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : ℕ → ℝ → E) (y : ℝ) : schedule V 0 y = 0 := by
  rw [schedule_on_slot V 0 (by norm_num) (by norm_num),
    pulse_eq_zero (Or.inl (by norm_num)), zero_smul]

theorem selector_unit_periodic {b : ℕ} (hb : 2 ≤ b) (L n : ℕ)
    (A : ℤ → ℝ) (hA : Function.Periodic A (Scales.capacity b L n : ℤ)) :
    Function.Periodic (selector (Scales.epsilon b L n) A) 1 := by
  obtain ⟨m, hm⟩ := Scales.capacity_dvd_inverseScale b L n
  have hp : Function.Periodic A (b ^ Scales.exponent L n : ℕ) := by
    rw [hm, Nat.cast_mul, mul_comm]
    exact hA.nat_mul m
  have he := Scales.epsilon_pos hb L n
  have hscale : Scales.epsilon b L n * ((b ^ Scales.exponent L n : ℕ) : ℤ) = (1 : ℝ) := by
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
    simpa [Scales.epsilon] using inv_mul_cancel₀ (pow_ne_zero (Scales.exponent L n) hb0)
  intro y
  simpa only [hscale] using selector_shift _ (ne_of_gt he) A _ hp y

theorem schedule_eventually_on_slot {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : ℕ → ℝ → E) (n : ℕ) {t : ℝ} (ht : (n : ℝ) ≤ t) (ht' : t ≤ n + 1) :
    (fun s => schedule V s) =ᶠ[𝓝 t] (fun s y => pulse n s • V n y) := by
  filter_upwards [Ioo_mem_nhds (show (n : ℝ) - 1 / 3 < t by linarith)
    (show t < n + 4 / 3 by linarith)] with s hs
  funext y
  apply finsum_eq_single
  intro m hm
  have hz : pulse m s = 0 := by
    apply pulse_eq_zero
    rcases lt_or_gt_of_ne hm with h | h
    · have h' : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h
      exact Or.inr (by linarith [hs.1])
    · have h' : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h
      exact Or.inl (by linarith [hs.2])
  rw [hz, zero_smul]

def mixedPartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r k : ℕ) (v : ℝ → ℝ → E) (t y : ℝ) : E :=
  iteratedDeriv r (fun s => iteratedDeriv k (v s) y) t

theorem schedule_mixedPartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : ℕ → ℝ → E) (r k n : ℕ) {t : ℝ} (ht : (n : ℝ) ≤ t) (ht' : t ≤ n + 1)
    (y : ℝ) :
    mixedPartial r k (schedule V) t y =
      iteratedDeriv r (pulse n) t • iteratedDeriv k (V n) y := by
  have heq : (fun s => iteratedDeriv k (schedule V s) y) =ᶠ[𝓝 t]
      (fun s => pulse n s • iteratedDeriv k (V n) y) := by
    filter_upwards [schedule_eventually_on_slot V n ht ht'] with s hs
    rw [hs, iteratedDeriv_fun_const_smul_field]
  rw [mixedPartial, heq.iteratedDeriv_eq r]
  exact iteratedDeriv_smul_const
    ((pulse_contDiff n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt _

theorem pulse_iteratedDeriv (n r : ℕ) (t : ℝ) :
    iteratedDeriv r (pulse n) t = iteratedDeriv r (deriv clock) (t - n) := by
  exact congrFun (iteratedDeriv_comp_sub_const r (deriv clock) (n : ℝ)) t

theorem compact_iteratedDeriv {f : ℝ → ℝ} (h : HasCompactSupport f) (k : ℕ) :
    HasCompactSupport (iteratedDeriv k f) := by
  induction k with
  | zero => simpa using h
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem bump_hasCompactSupport : HasCompactSupport bump :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc bump_support

theorem clock_deriv_hasCompactSupport : HasCompactSupport (deriv clock) := by
  apply HasCompactSupport.intro (K := Icc (1 / 3 : ℝ) (2 / 3)) isCompact_Icc
  intro t ht
  apply clock_deriv_eq_zero
  simpa only [mem_Icc, not_and_or, not_le] using ht

theorem profile_derivative_bounds (r k : ℕ) :
    ∃ T D : ℕ, (∀ t, |iteratedDeriv r (deriv clock) t| ≤ T) ∧
      (∀ y, |iteratedDeriv k bump y| ≤ D) := by
  obtain ⟨T, hT⟩ := (clock_deriv_contDiff.continuous_iteratedDeriv r
    (WithTop.coe_le_coe.mpr le_top)).bounded_above_of_compact_support
      (compact_iteratedDeriv clock_deriv_hasCompactSupport r)
  obtain ⟨D, hD⟩ := (bump_contDiff.continuous_iteratedDeriv k
    (WithTop.coe_le_coe.mpr le_top)).bounded_above_of_compact_support
      (compact_iteratedDeriv bump_hasCompactSupport k)
  obtain ⟨T', hT'⟩ := exists_nat_gt T
  obtain ⟨D', hD'⟩ := exists_nat_gt D
  exact ⟨T', D', fun t => (hT t).trans hT'.le, fun y => (hD y).trans hD'.le⟩

end Profiles

end
end PeriodicLattice

end OAI
