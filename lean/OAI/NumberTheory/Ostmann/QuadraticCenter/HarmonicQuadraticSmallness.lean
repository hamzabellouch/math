import OAI.NumberTheory.Ostmann.Construction.DyadicHarmonicBias

namespace OAI

/-! # The harmonic-band consequence of the quadratic proposition -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem mem_iteratedLogPrimeBand_iff (α β L : ℝ) (p : ℕ) :
    p ∈ iteratedLogPrimeBand α β L ↔
      p.Prime ∧ α * L ≤ Real.log (Real.log (p : ℝ)) ∧
        Real.log (Real.log (p : ℝ)) ≤ β * L := by
  simp only [iteratedLogPrimeBand, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hp, hprime⟩, hlo⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hprime.one_lt)
    refine ⟨hprime, (Real.le_log_iff_exp_le hlog).mpr hlo, ?_⟩
    apply (Real.log_le_iff_le_exp hlog).mpr
    apply (Real.log_le_iff_le_exp hp0).mpr
    exact (by exact_mod_cast hp : (p : ℝ) ≤ ⌊Real.exp (Real.exp (β * L))⌋₊).trans (Nat.floor_le (Real.exp_nonneg _))
  · rintro ⟨hprime, hlo, hhi⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hprime.one_lt)
    refine ⟨⟨Nat.le_floor ?_, hprime⟩, (Real.le_log_iff_exp_le hlog).mp hlo⟩
    exact (Real.log_le_iff_le_exp hp0).mp ((Real.log_le_iff_le_exp hlog).mp hhi)

theorem harmonicQuadraticBandMass_nonneg (A : Set ℕ) (N : ℕ) (α β L : ℝ) :
    0 ≤ harmonicQuadraticBandMass A N α β L :=
  Finset.sum_nonneg (fun p _ => harmonicQuadraticBias_nonneg A N p)

private theorem dyadic_shell_count (β L : ℝ) (hβ : 0 ≤ β) (hL : 1 ≤ L) :
    let n := ⌈β * L / Real.log 2⌉₊
    Real.exp (β * L) ≤ (2 : ℝ) ^ n ∧
      (n : ℝ) + 1 ≤ (β / Real.log 2 + 2) * L := by
  intro n
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hn : β * L / Real.log 2 ≤ (n : ℝ) := Nat.le_ceil _
  have hu : (n : ℝ) < β * L / Real.log 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have he : Real.exp ((n : ℝ) * Real.log 2) = (2 : ℝ) ^ n := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  refine ⟨?_, ?_⟩
  · rw [← he]
    exact Real.exp_le_exp.mpr ((div_le_iff₀ hlog).mp hn)
  · have heq : β * L / Real.log 2 = (β / Real.log 2) * L := by ring
    rw [heq] at hu
    nlinarith

theorem harmonicQuadraticBandMass_isLittleO (A : Set ℕ) (N : ℕ) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hsmall : (fun T => closedQuadraticBandMass A N T) =o[atTop] (fun T : ℝ => T)) :
    (fun L => harmonicQuadraticBandMass A N α β L) =o[atTop] (fun L : ℝ => L) := by
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  let C := β / Real.log 2 + 2
  let ε := c / C
  have hC : 0 < C := by dsimp [C]; positivity
  have hε : 0 < ε := div_pos hc hC
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hsmall.bound hε)
  have hgrowth : Tendsto (fun L : ℝ => Real.exp (α * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hα)
  filter_upwards [hgrowth.eventually_ge_atTop T₀, eventually_ge_atTop (1 : ℝ)] with L hlarge hL
  let n := ⌈β * L / Real.log 2⌉₊
  obtain ⟨hexp, hcount⟩ := dyadic_shell_count β L hβ.le hL
  have hstart : 1 ≤ Real.exp (α * L) := Real.one_le_exp (by positivity)
  have hcover : Real.exp (β * L) ≤ (2 : ℝ) ^ n * Real.exp (α * L) :=
    hexp.trans (le_mul_of_one_le_right (by positivity) hstart)
  have hlocal : ∀ j ≤ n, closedQuadraticBandMass A N ((2 : ℝ) ^ j * Real.exp (α * L)) ≤
      ε * ((2 : ℝ) ^ j * Real.exp (α * L)) := by
    intro j _
    have hstartj : Real.exp (α * L) ≤ (2 : ℝ) ^ j * Real.exp (α * L) :=
      le_mul_of_one_le_left (Real.exp_nonneg _) (one_le_pow₀ (by norm_num))
    have hh := hT₀ _ (hlarge.trans hstartj)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (closedQuadraticBandMass_nonneg A N _),
      abs_of_pos (by positivity : 0 < (2 : ℝ) ^ j * Real.exp (α * L))] using hh
  have hmass := harmonicQuadraticBandMass_dyadic_bound A N n α β L ε hcover hlocal
  rw [Real.norm_eq_abs, abs_of_nonneg (harmonicQuadraticBandMass_nonneg A N α β L),
    Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ L)]
  apply hmass.trans
  calc
    _ ≤ (C * L) * ε := mul_le_mul_of_nonneg_right hcount hε.le
    _ = c * L := by dsimp [ε]; field_simp

end Ostmann

end OAI
