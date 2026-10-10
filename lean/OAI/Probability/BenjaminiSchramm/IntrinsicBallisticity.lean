import OAI.Probability.BenjaminiSchramm.IntrinsicConnectionAverage
import OAI.Probability.BenjaminiSchramm.ExponentialDecay

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem longConnectionEvent_antitone (G : BondGraph V E) (x y : V)
    {m n : ℕ} (hmn : m ≤ n) : longConnectionEvent G x y n ⊆ longConnectionEvent G x y m := by
  rintro ω ⟨hc,hd⟩
  exact ⟨hc,hmn.trans hd⟩

theorem longConnection_block_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (M k n : ℕ) (hM : 0 < M) (x y : V) (hd : k*M ≤ n) :
    (law p).real (longConnectionEvent G x y n) ≤ ‖T‖ * (‖T‖ / M)^k := by
  have hpow := longConnection_power_bound G hloc p T hT M k x y
  have hreal : (M : ℝ)^k * (law p).real (longConnectionEvent G x y (k*M)) ≤
      (matrixCoeff (T^(k+1)) x y).re := by
    change (M : ℝ)^k * (law p (longConnectionEvent G x y (k*M))).toReal ≤ _
    have hh := ENNReal.toReal_mono (by unfold ennMatrixCoeff; exact ENNReal.ofReal_ne_top) hpow
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_natCast,
      ennMatrixCoeff,ENNReal.toReal_ofReal ((hT.positiveRealMatrix G p T).pow (k+1) x y).2] using hh
  have hcoeff : (matrixCoeff (T ^ (k + 1)) x y).re ≤ ‖T‖ ^ (k + 1) := by
    apply (Complex.re_le_norm _).trans
    have hc : ‖matrixCoeff (T ^ (k + 1)) x y‖ ≤ ‖T ^ (k + 1)‖ := by
      change ‖(T ^ (k + 1)) (lp.single 2 y (1 : ℂ)) x‖ ≤ _
      apply (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
        ((T ^ (k + 1)) (lp.single 2 y (1 : ℂ))) x).trans
      simpa only [lp.norm_single (by norm_num : 0 < (2 : ENNReal)), norm_one, mul_one] using
        (T ^ (k + 1)).le_opNorm (lp.single 2 y (1 : ℂ))
    exact hc.trans (norm_pow_le' T (Nat.zero_lt_succ k))
  have hc : (0 : ℝ) < M := by exact_mod_cast hM
  calc
    _ ≤ (law p).real (longConnectionEvent G x y (k*M)) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (longConnectionEvent_antitone G x y hd))
    _ ≤ ‖T‖^(k+1) / (M : ℝ)^k :=
      (le_div_iff₀ (pow_pos hc k)).mpr (by simpa only [mul_comm] using hreal.trans hcoeff)
    _ = _ := by rw [div_pow,pow_succ]; ring

theorem longConnection_exponential_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (x y : V) (n : ℕ) :
    (law p).real (longConnectionEvent G x y n) ≤ 2 * ‖T‖ *
      Real.exp (-(Real.log 2 / (3 * ‖T‖)) * n) := by
  have hM : 1 ≤ ‖T‖ := hT.norm_one_le G p T
  have hMp : 0 < ‖T‖ := lt_of_lt_of_le zero_lt_one hM
  let m : ℕ := ⌈2 * ‖T‖⌉₊
  have hml : 2 * ‖T‖ ≤ (m : ℝ) := Nat.le_ceil _
  have hmu : (m : ℝ) ≤ 3 * ‖T‖ := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 2 * ‖T‖ by positivity)
    dsimp [m]
    linarith
  have hmp : 0 < m := by
    have : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hml
    exact_mod_cast this
  let k := n / m
  have hk : k * m ≤ n := Nat.div_mul_le_self _ _
  have hxy : n < (k + 1) * m := by
    simpa only [k, Nat.mul_comm] using Nat.lt_mul_div_succ (n) hmp
  have hr : ‖T‖ / m ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < m)).mpr
    linarith
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ‖T‖ / m) hr k
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcast : (n : ℝ) ≤ ((k : ℝ) + 1) * (3 * ‖T‖) := by
    have h1 : (n : ℝ) ≤ ((k : ℝ) + 1) * m := by
      exact_mod_cast hxy.le
    exact h1.trans (mul_le_mul_of_nonneg_left hmu (by positivity))
  have hexponent : -(Real.log 2) * k ≤
      Real.log 2 - (Real.log 2 / (3 * ‖T‖)) * n := by
    have hdiv : (n : ℝ) / (3 * ‖T‖) ≤ (k : ℝ) + 1 :=
      (div_le_iff₀ (by positivity)).mpr hcast
    have hh := mul_le_mul_of_nonneg_left hdiv hlog.le
    nlinarith [show (Real.log 2 / (3 * ‖T‖)) * n =
      Real.log 2 * ((n : ℝ) / (3 * ‖T‖)) by ring]
  have hhalf : (1 / 2 : ℝ) ^ k = Real.exp (-(Real.log 2) * k) := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp only [one_div]
  calc
    _ ≤ ‖T‖ * (‖T‖ / m) ^ k :=
      longConnection_block_bound G hloc p T hT m k n hmp x y hk
    _ ≤ ‖T‖ * (1 / 2 : ℝ) ^ k := mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ = ‖T‖ * Real.exp (-(Real.log 2) * k) := by rw [hhalf]
    _ ≤ ‖T‖ * Real.exp (Real.log 2 -
        (Real.log 2 / (3 * ‖T‖)) * n) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (norm_nonneg _)
    _ = _ := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2),
        neg_mul, Real.exp_neg, div_eq_mul_inv]
      ring

end Percolation.BenjaminiSchramm

end OAI
