import OAI.Dynamics.EntropyCounterexample.Clock
import OAI.Dynamics.EntropyCounterexample.ClockDynamics

namespace OAI

open Filter Set
open scoped Topology OnePoint

namespace Problem340.Clock

structure LiftedOrbit (t e : ℕ → ℝ) : Prop where
  cutoff_nonneg : ∀ n, 0 ≤ e n
  cutoff_le_one : ∀ n, e n ≤ 1
  update : ∀ n, t (n + 1) = t n + increment (t n) (e n)

namespace LiftedOrbit

variable {t e : ℕ → ℝ} (h : LiftedOrbit t e)
include h

lemma monotone : Monotone t := by
  apply monotone_nat_of_le_succ
  intro n
  rw [h.update]
  exact le_add_of_nonneg_right (increment_nonneg _ (h.cutoff_nonneg n))

lemma increments_le_one (n : ℕ) : t (n + 1) - t n ≤ 1 := by
  rw [h.update]
  simpa using increment_le_one (t n) (h.cutoff_le_one n)

lemma barrier_le_difference (n : ℕ) : barrier (t n) ≤ t (n + 1) - t n := by
  rw [h.update]
  simpa using barrier_le_increment (t n) (h.cutoff_nonneg n)

theorem bounded_limit (hbounded : BddAbove (Set.range t)) :
    ∃ k : ℤ, Tendsto t atTop (𝓝 (50 + 100 * (k : ℝ))) := by
  apply ClockDynamics.bounded_clock_limit_lattice h.monotone hbounded
    (contDiff_barrier (n := 0)).continuous barrier_nonneg h.barrier_le_difference
  intro x hx
  exact (barrier_eq_zero_iff x).mp hx

theorem bounded_circle_limit (hbounded : BddAbove (Set.range t)) :
    Tendsto (fun n => (t n : AddCircle (100 : ℝ))) atTop
      (𝓝 ((50 : ℝ) : AddCircle (100 : ℝ))) := by
  obtain ⟨k, hlimit⟩ := h.bounded_limit hbounded
  have hperiod : (((50 + 100 * (k : ℝ)) : ℝ) : AddCircle (100 : ℝ)) =
      ((50 : ℝ) : AddCircle (100 : ℝ)) := by
    have heq : (100 : ℝ) * (k : ℝ) = k • (100 : ℝ) := by
      simp [zsmul_eq_mul, mul_comm]
    rw [heq, AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period,
      smul_zero, add_zero]
  have hcircle : Tendsto (fun n => (t n : AddCircle (100 : ℝ))) atTop
      (𝓝 (((50 + 100 * (k : ℝ)) : ℝ) : AddCircle (100 : ℝ))) :=
    ((AddCircle.continuous_mk' (100 : ℝ)).tendsto (50 + 100 * (k : ℝ))).comp hlimit
  simpa only [hperiod] using hcircle

lemma cutoff_le_difference (n : ℕ) : e n ≤ t (n + 1) - t n := by
  rw [h.update]
  have hp := mul_nonneg (barrier_nonneg (t n)) (sub_nonneg.mpr (h.cutoff_le_one n))
  unfold increment
  nlinarith

theorem cutoff_tendsto_zero (hbounded : BddAbove (Set.range t)) :
    Tendsto e atTop (𝓝 0) := by
  obtain ⟨_, _, hdifference⟩ := ClockDynamics.bounded_clock_limit h.monotone hbounded
  exact squeeze_zero h.cutoff_nonneg h.cutoff_le_difference hdifference

theorem eventually_observation_zero {β : ℝ → ℝ}
    (hbounded : BddAbove (Set.range t)) (hperiodic : Function.Periodic β 100)
    (hzero : ∀ x ∈ Set.Ioo (48 : ℝ) 52, β x = 0) :
    ∀ᶠ n in atTop, β (t n) = 0 := by
  obtain ⟨k, hlimit⟩ := h.bounded_limit hbounded
  have hshift : Tendsto (fun n => t n - (k : ℝ) * 100) atTop (𝓝 50) := by
    have heq : 50 + 100 * (k : ℝ) - (k : ℝ) * 100 = 50 := by ring
    simpa only [heq] using hlimit.sub_const ((k : ℝ) * 100)
  have hnear : ∀ᶠ n in atTop, t n - (k : ℝ) * 100 ∈ Set.Ioo (48 : ℝ) 52 :=
    hshift.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hnear] with n hn
  have hz := hzero _ hn
  rwa [hperiodic.sub_int_mul_eq k] at hz

theorem eventually_norm_lt {V : Type*} [SeminormedAddCommGroup V]
    {z : ℕ → V} {r : ℝ} (hbounded : BddAbove (Set.range t))
    (hcutoff : ∀ n, r ≤ ‖z n‖ → e n = 1) :
    ∀ᶠ n in atTop, ‖z n‖ < r := by
  apply ClockDynamics.eventually_small_of_bounded_clock h.monotone hbounded
    (show (0 : ℝ) < 1 by norm_num)
  intro n hn
  rw [h.update, hcutoff n hn, increment_one]
  linarith

theorem main_tendsto_zero {R : Type*} [SeminormedRing R] {z : ℕ → R}
    {r : ℝ} (hbounded : BddAbove (Set.range t)) (hr : r ≤ 1)
    (hcutoff : ∀ n, r ≤ ‖z n‖ → e n = 1)
    (hsquare : ∀ᶠ n in atTop, z (n + 1) = z n ^ 2) :
    Tendsto z atTop (𝓝 0) := by
  apply ClockDynamics.eventually_squaring_tendsto_zero hsquare
  filter_upwards [h.eventually_norm_lt hbounded hcutoff] with n hn
  exact hn.trans_le hr

theorem main_tendsto_zero_of_readouts {ι : Type*} [Fintype ι]
    {z : ℕ → ℂ} (hbounded : BddAbove (Set.range t))
    (hcutoff : ∀ n, 3 / 4 ≤ ‖z n‖ → e n = 1)
    (β : ι → ℝ → ℝ) (u : ℕ → ι → ℂ)
    (hperiodic : ∀ i, Function.Periodic (β i) 100)
    (hzero : ∀ i x, x ∈ Set.Ioo (48 : ℝ) 52 → β i x = 0)
    (hupdate : ∀ n, z (n + 1) = z n ^ 2 + ∑ i, β i (t n) • u n i) :
    Tendsto z atTop (𝓝 0) := by
  have hcoeff : ∀ᶠ n in atTop, ∀ i, β i (t n) = 0 :=
    eventually_all.mpr (fun i => h.eventually_observation_zero hbounded
      (hperiodic i) (hzero i))
  apply h.main_tendsto_zero hbounded (show (3 / 4 : ℝ) ≤ 1 by norm_num) hcutoff
  filter_upwards [hcoeff] with n hn
  rw [hupdate]
  simp [hn]

theorem bounded_or_tendsto_atTop :
    BddAbove (Set.range t) ∨ Tendsto t atTop atTop := by
  by_cases hb : BddAbove (Set.range t)
  · exact Or.inl hb
  · exact Or.inr (tendsto_atTop_atTop_of_monotone' h.monotone hb)

theorem avoids_invariant_fast_set {X : Type*} {z : ℕ → X} {S : Set X}
    (hbounded : BddAbove (Set.range t))
    (hstable : ∀ n, z n ∈ S → z (n + 1) ∈ S)
    (hfast : ∀ n, z n ∈ S → e n = 1) : ∀ n, z n ∉ S := by
  intro N hN
  have hforever : ∀ n, N ≤ n → z n ∈ S := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hN
    | succ n _ ih => exact hstable n ih
  have hsmall : ∀ᶠ n in atTop, e n < 1 :=
    (h.cutoff_tendsto_zero hbounded).eventually (gt_mem_nhds (by norm_num))
  obtain ⟨M, hM⟩ := eventually_atTop.mp hsmall
  have hlt := hM (N + M) (by omega)
  rw [hfast (N + M) (hforever _ (by omega))] at hlt
  exact lt_irrefl _ hlt

theorem onePoint_main_tendsto_zero_of_readouts {ι : Type*} [Fintype ι]
    {z : ℕ → OnePoint ℂ} (hbounded : BddAbove (Set.range t))
    (hpole : ∀ n, z n = ∞ → z (n + 1) = ∞)
    (hfast_pole : ∀ n, z n = ∞ → e n = 1)
    (hcutoff : ∀ n (w : ℂ), z n = (w : OnePoint ℂ) → 3 / 4 ≤ ‖w‖ → e n = 1)
    (β : ι → ℝ → ℝ) (u : ℕ → ι → ℂ)
    (hperiodic : ∀ i, Function.Periodic (β i) 100)
    (hzero : ∀ i x, x ∈ Set.Ioo (48 : ℝ) 52 → β i x = 0)
    (hupdate : ∀ n (w : ℂ), z n = (w : OnePoint ℂ) →
      z (n + 1) = ((w ^ 2 + ∑ i, β i (t n) • u n i : ℂ) : OnePoint ℂ)) :
    Tendsto z atTop (𝓝 ((0 : ℂ) : OnePoint ℂ)) := by
  have hfinite : ∀ n, z n ≠ ∞ :=
    h.avoids_invariant_fast_set (S := {∞}) hbounded hpole hfast_pole
  choose w hw using fun n => OnePoint.ne_infty_iff_exists.mp (hfinite n)
  have hrec : ∀ n, w (n + 1) = w n ^ 2 + ∑ i, β i (t n) • u n i := by
    intro n
    apply OnePoint.coe_injective
    rw [hw (n + 1)]
    exact hupdate n (w n) (hw n).symm
  have hlim : Tendsto w atTop (𝓝 0) :=
    h.main_tendsto_zero_of_readouts hbounded
      (fun n hn => hcutoff n (w n) (hw n).symm hn) β u hperiodic hzero hrec
  have hcoe := (OnePoint.continuous_coe.tendsto (0 : ℂ)).comp hlim
  exact hcoe.congr hw

end LiftedOrbit
end Problem340.Clock

end OAI
