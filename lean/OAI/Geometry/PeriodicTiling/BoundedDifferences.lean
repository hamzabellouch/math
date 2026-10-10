import OAI.Geometry.PeriodicTiling.ConfigurationDifferences
import OAI.Geometry.PeriodicTiling.ForwardDifference
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

namespace OAI

universe uG uA

namespace PeriodicTilingThree

variable {G : Type uG} [AddCommGroup G]

theorem configDiff_bounded (v : G) (f : G → ℝ)
    (hf : ∃ B : ℝ, ∀ x, |f x| ≤ B) :
    ∃ B : ℝ, ∀ x, |configDiff v f x| ≤ B := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨B + B, fun x => ?_⟩
  calc
    |configDiff v f x| = |f (x + v) + -f x| := rfl
    _ ≤ |f (x + v)| + |-f x| := abs_add_le _ _
    _ = |f (x + v)| + |f x| := by rw [abs_neg]
    _ ≤ B + B := add_le_add (hB _) (hB _)

theorem configDiff_eq_zero_of_second (v : G) (f : G → ℝ)
    (hf : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hsecond : configDiff v (configDiff v f) = 0) : configDiff v f = 0 := by
  obtain ⟨B, hB⟩ := hf
  let g := configDiff v f
  have hg : Function.Periodic g v := (configDiff_eq_zero_iff v g).mp hsecond
  ext x
  have hg_nat : ∀ n : ℕ, g (x + n • v) = g x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        simpa only [succ_nsmul, ← add_assoc] using (hg (x + n • v)).trans ih
  have hf_nat : ∀ n : ℕ, f (x + n • v) = f x + (n : ℝ) * g x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hd := hg_nat n
        change f (x + n • v + v) - f (x + n • v) = g x at hd
        simp only [succ_nsmul, ← add_assoc, Nat.cast_add, Nat.cast_one]
        linarith
  have hx := abs_le.mp (hB x)
  have hz : g x = 0 := by
    rcases lt_trichotomy (g x) 0 with hneg | hzero | hpos
    · obtain ⟨n, hn⟩ := exists_nat_gt (2 * B / (-g x))
      have hn' : 2 * B < (n : ℝ) * (-g x) :=
        (div_lt_iff₀ (neg_pos.mpr hneg)).mp hn
      have hy := abs_le.mp (hB (x + n • v))
      have he := hf_nat n
      nlinarith
    · exact hzero
    · obtain ⟨n, hn⟩ := exists_nat_gt (2 * B / g x)
      have hn' : 2 * B < (n : ℝ) * g x := (div_lt_iff₀ hpos).mp hn
      have hy := abs_le.mp (hB (x + n • v))
      have he := hf_nat n
      nlinarith
  exact hz

theorem configDiff_eq_zero_of_iterate (v : G) (n : ℕ) (f : G → ℝ)
    (hf : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hn : 0 < n) (hiter : (configDiff v)^[n] f = 0) :
    configDiff v f = 0 := by
  induction n generalizing f with
  | zero => exact (Nat.not_lt_zero _ hn).elim
  | succ n ih =>
      cases n with
      | zero =>
          change configDiff v f = 0 at hiter
          exact hiter
      | succ n =>
          have hnext : (configDiff v)^[n + 1] (configDiff v f) = 0 := by
            simpa only [Function.iterate_succ_apply] using hiter
          have hsecond : configDiff v (configDiff v f) = 0 :=
            ih (configDiff v f) (configDiff_bounded v f hf) (Nat.succ_pos _) hnext
          exact configDiff_eq_zero_of_second v f hf hsecond

theorem periodic_of_bounded_configDiff_iterate (v : G) (n : ℕ) (f : G → ℝ)
    (hf : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hn : 0 < n) (hiter : (configDiff v)^[n] f = 0) :
    Function.Periodic f v :=
  (configDiff_eq_zero_iff v f).mp (configDiff_eq_zero_of_iterate v n f hf hn hiter)

theorem forwardDiff_eq_configDiff {A : Type uA} [AddCommGroup A] :
    (forwardDiff : (ℤ → A) → ℤ → A) = configDiff (1 : ℤ) := rfl

theorem forwardDiff_eq_zero_of_bounded_iterate (n : ℕ) (f : ℤ → ℝ)
    (hf : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hn : 0 < n) (hiter : (forwardDiff^[n]) f = 0) : forwardDiff f = 0 := by
  rw [forwardDiff_eq_configDiff] at hiter ⊢
  exact configDiff_eq_zero_of_iterate 1 n f hf hn hiter

end PeriodicTilingThree

end OAI
