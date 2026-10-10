import OAI.NumberTheory.Ostmann.Arithmetic.ResidueIntervals

namespace OAI

/-! # The giant cells are above every prime factor of the common modulus -/

namespace Ostmann

theorem giant_interval_gt_modulus (L : ℝ) (hL : 0 < L) (M : ℕ) (hM : 0 < M)
    (hlog : Real.log (M : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L))
    (u v : ℝ) (hu : Real.exp ((49 / 1000 : ℝ) * L) ≤ u)
    (p : ℕ) (hp : p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊) : M < p := by
  have hgap : Real.exp ((12 / 1000 : ℝ) * L) < Real.exp ((49 / 1000 : ℝ) * L) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hlogp : Real.log (M : ℝ) < Real.log (p : ℝ) :=
    (hlog.trans_lt hgap).trans_le (hu.trans (log_mem_of_mem_exp_interval hp).1.le)
  have hp0 : (0 : ℝ) < p := (Real.exp_pos u).trans (Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hp).1)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have he := Real.exp_lt_exp.mpr hlogp
  rw [Real.exp_log hM0, Real.exp_log hp0] at he
  exact_mod_cast he

end Ostmann

end OAI
