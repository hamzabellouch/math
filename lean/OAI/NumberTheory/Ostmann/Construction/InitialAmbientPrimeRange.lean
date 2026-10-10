import OAI.NumberTheory.Ostmann.Construction.InitialCellPriors
import OAI.NumberTheory.Ostmann.Construction.FavorableBlockEndpoint

namespace OAI

/-! # The actual collision cutoff contains the complete initial prime space -/
namespace Ostmann
open Filter

theorem eventual_initial_regular_prime_range :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ Y → Y ≤ Real.exp L →
      initialRegularPrimeRange L ⊆ Nat.primesLE (tailCollisionCutoff Y) := by
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (eventual_tailCollisionCutoff 0)
  have ht : Tendsto (fun L : ℝ => Real.exp ((4 / 100 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [eventual_tail_cell_window 1 0 0,
    ht.eventually (eventually_ge_atTop Y₀), eventually_ge_atTop (0 : ℝ)]
    with L hwindow hlarge hL
  intro Y hYlo hYhi p hp
  have hcut := hY₀ Y (hlarge.trans hYlo)
  have hQ := tailCollisionCutoff_bounds Y hcut.1 hcut.2.1
  have hD : 0 ≤ tailDefectBudget 1 0 Y := by
    dsimp [tailDefectBudget]
    positivity [Real.log_nonneg hcut.1, Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num),
      Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
  have hw := (hwindow Y (Real.exp ((11 / 1000 : ℝ) * L)) hYlo hYhi
    (Real.exp_le_exp.mpr (by linarith)) le_rfl).2.1
  have hlog : Real.exp ((11 / 1000 : ℝ) * L) ≤
      Real.log (tailCollisionCutoff Y : ℝ) := by linarith
  have hQ0 : (0 : ℝ) < tailCollisionCutoff Y := by exact_mod_cast hQ.1
  have hbound : Real.exp (Real.exp ((11 / 1000 : ℝ) * L)) ≤
      (tailCollisionCutoff Y : ℝ) := by
    simpa only [Real.exp_log hQ0] using Real.exp_le_exp.mpr hlog
  obtain ⟨hpbound, hpprime⟩ := Nat.mem_primesLE.mp hp
  apply Nat.mem_primesLE.mpr
  refine ⟨?_, hpprime⟩
  exact_mod_cast (show (p : ℝ) ≤ (tailCollisionCutoff Y : ℝ) from
    (Nat.cast_le.mpr hpbound).trans ((Nat.floor_le (Real.exp_nonneg _)).trans hbound))

theorem eventual_initial_giant_prime_range (k : ℕ) (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop, ∀ lo Y G : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ Y → Y ≤ Real.exp L →
      2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y →
      G ≤ lo - 2 + 12 * Real.exp ((1 / 100 : ℝ) * L) →
      smoothGiantPrimeRange G ⊆ Nat.primesLE (tailCollisionCutoff Y) := by
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (eventual_tailCollisionCutoff 0)
  have ht : Tendsto (fun L : ℝ => Real.exp ((4 / 100 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [eventual_polynomial_log_budget (8 + |Real.log 2|) 1 (1 / 100) 1 1
      (by positivity) (by norm_num) (by norm_num) (by norm_num),
    ht.eventually (eventually_ge_atTop Y₀), eventually_ge_atTop (1 : ℝ)]
    with L hmargin hlarge hL
  intro lo Y G hYlo hYhi hYlower hG p hp
  have hcut := hY₀ Y (hlarge.trans hYlo)
  have hQ := tailCollisionCutoff_bounds Y hcut.1 hcut.2.1
  have hlogY : Real.log Y ≤ L := (Real.log_le_iff_le_exp (by linarith [hcut.1])).mpr hYhi
  have hm := hmargin L (by linarith) (by simp)
  simp only [pow_one, one_mul] at hm
  have hmargin' : 5 * L + Real.log 2 ≤ Real.exp ((1 / 100 : ℝ) * L) := by
    have hab := le_abs_self (Real.log 2)
    have ha0 := abs_nonneg (Real.log 2)
    nlinarith
  have hpow : (2 : ℝ) ≤ 2 ^ k := by
    calc
      2 = (2 : ℝ) ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [pow_succ] at hYlower
  have hpw := mul_le_mul_of_nonneg_right hpow
    (Real.exp_nonneg ((1 / 100 : ℝ) * L))
  have hlogcut : G + 1 ≤ Real.log (tailCollisionCutoff Y : ℝ) := by
    nlinarith only [hQ.2.2, hlogY, hmargin', hYlower, hG, hpw,
      Real.exp_nonneg ((1 / 100 : ℝ) * L)]
  have hQ0 : (0 : ℝ) < tailCollisionCutoff Y := by exact_mod_cast hQ.1
  have hceil : ⌈Real.exp (G + 1)⌉₊ ≤ tailCollisionCutoff Y := by
    apply Nat.ceil_le.mpr
    simpa only [Real.exp_log hQ0] using Real.exp_le_exp.mpr hlogcut
  have hp' := Finset.mem_filter.mp hp
  exact Nat.mem_primesLE.mpr ⟨(Finset.mem_Icc.mp hp'.1).2.trans hceil, hp'.2⟩

end Ostmann

end OAI
