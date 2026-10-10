import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring

namespace OAI

/-! # From a decaying time step to continuous-time decay

Strong continuity gives the bounded propagation on one compact time interval.
The remaining estimate is a division of time into integral steps and one
bounded remainder interval.
-/

open Set
open scoped NNReal

namespace DefocusingNLS

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem stronglyContinuous_family_compact_bound (S : ℝ≥0 → E →L[ℂ] E)
    (hS : ∀ x : E, Continuous (fun t => S t x)) (τ : ℝ≥0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ≥0, t ≤ τ → ‖S t‖ ≤ M := by
  obtain ⟨M, hM⟩ := banach_steinhaus (g := fun t : Icc (0 : ℝ≥0) τ => S t) (by
    intro x
    obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) τ)).exists_bound_of_continuousOn
      (hS x).continuousOn
    exact ⟨C, fun t => hC t t.property⟩)
  exact ⟨max M 0, le_max_right _ _, fun t ht =>
    (hM ⟨t, bot_le, ht⟩).trans (le_max_left _ _)⟩

omit [CompleteSpace E] in
theorem semigroup_nat_mul (S : ℝ≥0 → E →L[ℂ] E)
    (hzero : S 0 = 1)
    (hadd : ∀ s t, S (s + t) = S t * S s) (τ : ℝ≥0) (n : ℕ) :
    S ((n : ℝ≥0) * τ) = (S τ) ^ n := by
  induction n with
  | zero => simpa only [Nat.cast_zero, zero_mul, pow_zero] using hzero
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, hadd, ih, pow_succ']

theorem continuous_decay_of_step_decay (S : ℝ≥0 → E →L[ℂ] E)
    (hzero : S 0 = 1) (hadd : ∀ s t, S (s + t) = S t * S s)
    (hS : ∀ x : E, Continuous (fun t => S t x))
    (V : Set E) (τ : ℝ≥0) (hτ : 0 < τ) (r C : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hC : 0 ≤ C)
    (hstep : ∀ n : ℕ, ∀ x ∈ V, ‖((S τ) ^ n) x‖ ≤ C * r ^ n * ‖x‖) :
    ∃ D δ : ℝ, 0 ≤ D ∧ 0 < δ ∧ ∀ t : ℝ≥0, ∀ x ∈ V,
      ‖S t x‖ ≤ D * Real.exp (-δ * (t : ℝ)) * ‖x‖ := by
  obtain ⟨M, hM, hbound⟩ := stronglyContinuous_family_compact_bound S hS τ
  have hτR : 0 < (τ : ℝ) := hτ
  let δ : ℝ := -Real.log r / τ
  have hlog : Real.log r < 0 := Real.log_neg hr hr1
  have hδ : 0 < δ := div_pos (neg_pos.mpr hlog) hτR
  refine ⟨M * C / r, δ, by positivity, hδ, ?_⟩
  intro t x hx
  let n : ℕ := ⌊(t : ℝ) / τ⌋₊
  have hn : (n : ℝ) ≤ (t : ℝ) / τ := Nat.floor_le (div_nonneg t.2 hτR.le)
  have hn' : (t : ℝ) / τ < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hnτ : (n : ℝ) * τ ≤ (t : ℝ) := (le_div_iff₀ hτR).mp hn
  let u : ℝ≥0 := ⟨(t : ℝ) - (n : ℝ) * τ, sub_nonneg.mpr hnτ⟩
  have hu : u ≤ τ := by
    change (t : ℝ) - (n : ℝ) * τ ≤ (τ : ℝ)
    have h := (div_lt_iff₀ hτR).mp hn'
    nlinarith
  have ht : t = (n : ℝ≥0) * τ + u := by
    apply Subtype.ext
    change (t : ℝ) = (n : ℝ) * τ + ((t : ℝ) - (n : ℝ) * τ)
    ring
  have hsplit : S t = S u * (S τ) ^ n := by
    rw [ht, hadd, semigroup_nat_mul S hzero hadd]
  have hgeom : r ^ n ≤ Real.exp (-δ * (t : ℝ)) / r := by
    have hh : (n : ℝ) * Real.log r ≤ ((t : ℝ) / τ - 1) * Real.log r :=
      mul_le_mul_of_nonpos_right (by linarith : (t : ℝ) / τ - 1 ≤ (n : ℝ)) hlog.le
    have he : ((t : ℝ) / τ - 1) * Real.log r = -δ * (t : ℝ) - Real.log r := by
      dsimp only [δ]
      field_simp
    calc
      r ^ n = Real.exp ((n : ℝ) * Real.log r) := by
        rw [Real.exp_nat_mul, Real.exp_log hr]
      _ ≤ Real.exp (((t : ℝ) / τ - 1) * Real.log r) := Real.exp_le_exp.mpr hh
      _ = Real.exp (-δ * (t : ℝ)) / r := by rw [he, Real.exp_sub, Real.exp_log hr]
  calc
    ‖S t x‖ = ‖S u (((S τ) ^ n) x)‖ := by rw [hsplit]; rfl
    _ ≤ ‖S u‖ * ‖((S τ) ^ n) x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ M * (C * r ^ n * ‖x‖) :=
      mul_le_mul (hbound u hu) (hstep n x hx) (norm_nonneg _) hM
    _ ≤ M * (C * (Real.exp (-δ * (t : ℝ)) / r) * ‖x‖) := by
      gcongr
    _ = M * C / r * Real.exp (-δ * (t : ℝ)) * ‖x‖ := by ring

end

end DefocusingNLS

end OAI
