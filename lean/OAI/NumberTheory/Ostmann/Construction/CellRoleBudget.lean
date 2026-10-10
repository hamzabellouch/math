import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-!
# Absorption of the cell-role count

Section 4 fixes `ε = 1/10000`, bounds the number of selected cell roles by
`C (k+1) exp(2 ε k)`, and uses the scale `z = exp(3 ε k)`.  Their ratio tends
to zero, so every fixed positive proportion of `z` eventually absorbs the
role count. This is an elementary numerical step, with no published input.
-/

namespace Ostmann

open Filter
open scoped Topology

/-- The fixed small parameter used in the character selection. -/
noncomputable def cellRoleEpsilon : ℝ := 1 / 10000

/-- Upper bound for all selected cell roles, including the anchors. -/
noncomputable def cellRoleCountBound (C : ℝ) (k : ℕ) : ℝ :=
  C * ((k : ℝ) + 1) * Real.exp (2 * cellRoleEpsilon * k)

/-- The larger exponential scale which absorbs the cell-role count. -/
noncomputable def cellRoleScale (k : ℕ) : ℝ :=
  Real.exp (3 * cellRoleEpsilon * k)

theorem cellRoleScale_pos (k : ℕ) : 0 < cellRoleScale k := Real.exp_pos _

theorem cellRoleCountBound_nonneg {C : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    0 ≤ cellRoleCountBound C k := by
  unfold cellRoleCountBound
  positivity

theorem cellRoleCountBound_div_scale (C : ℝ) (k : ℕ) :
    cellRoleCountBound C k / cellRoleScale k =
      C * (((k : ℝ) + 1) / Real.exp (cellRoleEpsilon * k)) := by
  unfold cellRoleCountBound cellRoleScale
  rw [show 3 * cellRoleEpsilon * (k : ℝ) =
    2 * cellRoleEpsilon * k + cellRoleEpsilon * k by ring, Real.exp_add]
  field_simp

/-- The manuscript's `n_max / z → 0`, with its fixed value of epsilon. -/
theorem tendsto_cellRoleCountBound_div_scale (C : ℝ) :
    Tendsto (fun k : ℕ => cellRoleCountBound C k / cellRoleScale k)
      atTop (𝓝 0) := by
  have hε : 0 < cellRoleEpsilon := by norm_num [cellRoleEpsilon]
  have h1 := (isLittleO_pow_exp_pos_mul_atTop 1 hε).tendsto_div_nhds_zero
  have h0 := (isLittleO_pow_exp_pos_mul_atTop 0 hε).tendsto_div_nhds_zero
  have hreal : Tendsto (fun x : ℝ => C * ((x + 1) / Real.exp (cellRoleEpsilon * x)))
      atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, ← add_div, add_zero, mul_zero]
      using (h1.add h0).const_mul C
  have hnat := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, cellRoleCountBound_div_scale] using hnat

/-- Any prescribed positive budget eventually absorbs the entire role count. -/
theorem eventually_cellRoleCountBound_le (C b : ℝ) (hb : 0 < b) :
    ∀ᶠ k : ℕ in atTop, cellRoleCountBound C k ≤ b * cellRoleScale k := by
  filter_upwards [(tendsto_cellRoleCountBound_div_scale C).eventually_lt_const hb]
    with k hk
  exact ((div_lt_iff₀ (cellRoleScale_pos k)).mp hk).le

/-- A single cutoff works for every actual list whose number of roles obeys
the manuscript's upper bound. -/
theorem exists_cellRoleCount_cutoff (C b : ℝ) (hb : 0 < b) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ n : ℕ,
      (n : ℝ) ≤ cellRoleCountBound C k → (n : ℝ) ≤ b * cellRoleScale k := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp (eventually_cellRoleCountBound_le C b hb)
  exact ⟨K, fun k hk n hn => hn.trans (hK k hk)⟩

end Ostmann

end OAI
