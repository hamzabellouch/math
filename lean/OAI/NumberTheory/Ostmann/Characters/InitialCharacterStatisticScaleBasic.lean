import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Order.Floor

namespace OAI

noncomputable section
namespace Ostmann.Characters.InitialCharacterScale
open Filter
open scoped Topology

def depthScale (k : ℕ) : ℝ := Real.exp ((3/10000 : ℝ)*k)

def wordSize (k : ℕ) (L : ℝ) : ℕ := ⌊depthScale k*L⌋₊

def initialGap (BD : ℝ) (k : ℕ) (L : ℝ) : ℝ :=
  (BD+20*Real.log (depthScale k))*(wordSize k L : ℝ)

def maxCells (C : ℝ) (k : ℕ) : ℝ := C*((k : ℝ)+1)*Real.exp ((2/10000 : ℝ)*k)

theorem depthScale_pos (k : ℕ) : 0 < depthScale k := Real.exp_pos _

theorem one_le_depthScale (k : ℕ) : 1 ≤ depthScale k := by
  exact Real.one_le_exp_iff.mpr (by positivity)

theorem wordSize_bounds (k : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    depthScale k*L-1 < (wordSize k L : ℝ) ∧ (wordSize k L : ℝ) ≤ depthScale k*L := by
  have hh := Nat.lt_floor_add_one (depthScale k*L)
  have hl := Nat.floor_le (mul_nonneg (depthScale_pos k).le hL)
  change depthScale k*L < (wordSize k L : ℝ)+1 at hh
  exact ⟨by linarith,hl⟩

theorem wordSize_tendsto (k : ℕ) : Tendsto (fun L : ℝ => (wordSize k L : ℝ)) atTop atTop := by
  have ht : Tendsto (fun L : ℝ => depthScale k*L-1) atTop atTop := by
    simpa only [id_eq, sub_eq_add_neg] using
      (tendsto_id.const_mul_atTop (depthScale_pos k)).atTop_add (tendsto_const_nhds (x := -(1 : ℝ)))
  apply tendsto_atTop_mono' atTop _ ht
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  exact (wordSize_bounds k hL).1.le

theorem fixed_power_eventually (k r : ℕ) :
    ∀ᶠ L : ℝ in atTop, (3*(wordSize k L : ℝ))^r ≤ Real.exp (wordSize k L : ℝ) := by
  have ht : Tendsto (fun L : ℝ => (3*(wordSize k L : ℝ))^r *
      Real.exp (-(wordSize k L : ℝ))) atTop (𝓝 0) := by
    have hh := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero r).comp
      (wordSize_tendsto k)).const_mul ((3 : ℝ)^r)
    simpa only [Function.comp_def, mul_pow, mul_assoc, mul_zero] using hh
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with L hL
  have hh := (le_div_iff₀ (Real.exp_pos (-(wordSize k L : ℝ)))).mpr hL.le
  simpa only [one_div, ← Real.exp_neg, neg_neg] using hh

theorem maxCells_div_depthScale_tendsto (C : ℝ) :
    Tendsto (fun k : ℕ => maxCells C k/depthScale k) atTop (𝓝 0) := by
  have hn : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hp := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/10000)
    (by norm_num)).comp hn
  simp only [Function.comp_def, Real.rpow_one] at hp
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (hn.const_mul_atTop (by norm_num : (0 : ℝ) < 1/10000))
  have hh := (hp.add he).const_mul C
  simp only [add_zero, mul_zero] at hh
  convert hh using 1
  funext k
  dsimp only [maxCells, depthScale, Function.comp_def]
  rw [mul_div_assoc, ← Real.exp_sub]
  have hexp : (2/10000 : ℝ)*k-(3/10000 : ℝ)*k=-(1/10000 : ℝ)*k := by ring
  rw [hexp]
  ring_nf

theorem eventually_maxCells_le_depthScale (C : ℝ) :
    ∀ᶠ k : ℕ in atTop, maxCells C k ≤ depthScale k := by
  filter_upwards [(maxCells_div_depthScale_tendsto C).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with k hk
  exact (div_le_one (depthScale_pos k)).mp hk.le

end Ostmann.Characters.InitialCharacterScale

end

end OAI
