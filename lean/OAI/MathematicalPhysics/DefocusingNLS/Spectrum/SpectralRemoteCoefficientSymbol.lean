import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteSymbolBilinear

namespace OAI

/-! Uniform logarithmic jets of the scaled angular and spectral coefficients. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

theorem spectralRemote_scaled_exponential_jet (a c : ℝ) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => c*Real.exp (a*t)) =
      fun t => a^k*c*Real.exp (a*t) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ,ih]
      funext t
      have hd := ((((hasDerivAt_id t).const_mul a).exp).const_mul (a^k*c))
      simp only [id_eq,mul_one] at hd
      rw [hd.deriv]
      simp only [pow_succ]
      ring

theorem spectralRemote_scaled_exponential_symbol
    {L c : ℕ → ℝ} {a C : ℝ} (ha : a ≤ 0) (hC : 0 ≤ C)
    (hc : ∀ᶠ n in atTop, |c n| *Real.exp (a*L n) ≤ C) :
    HasUniformLogJetBound L 0 (fun n t => c n*Real.exp (a*t)) := by
  refine ⟨Eventually.of_forall (fun n =>
    (contDiff_const.mul (contDiff_const.mul contDiff_id).exp).contDiffOn),?_⟩
  intro k
  refine ⟨|a|^k*C,mul_nonneg (pow_nonneg (abs_nonneg _) _) hC,?_⟩
  filter_upwards [hc] with n hn
  intro t ht
  rw [spectralRemote_scaled_exponential_jet]
  simp only [Real.norm_eq_abs,abs_mul,abs_pow,abs_of_pos (Real.exp_pos _),
    zero_mul,Real.exp_zero,mul_one]
  calc
    |a|^k*|c n| *Real.exp (a*t) = |a|^k*(|c n| *Real.exp (a*t)) := by ring
    _ ≤ |a|^k*(|c n| *Real.exp (a*L n)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (abs_nonneg a) k)
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg (c n))
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht.le ha)
    _ ≤ |a|^k*C := mul_le_mul_of_nonneg_left hn (pow_nonneg (abs_nonneg _) _)

theorem spectralRemote_actual_coefficient_symbol
    {L omega eta : ℕ → ℝ} (h : ℝ) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (homega : ∀ᶠ n in atTop, |omega n| *Real.exp (-2*L n) ≤ C)
    (heta : ∀ᶠ n in atTop, |eta n| *Real.exp (-4*L n) ≤ D) :
    HasUniformLogJetBound L 0
      (fun n t => h*omega n*Real.exp (-2*t)+eta n*Real.exp (-4*t)) := by
  have hw : ∀ᶠ n in atTop, |h*omega n| *Real.exp (-2*L n) ≤ |h| *C := by
    filter_upwards [homega] with n hn
    simpa only [abs_mul,mul_assoc] using mul_le_mul_of_nonneg_left hn (abs_nonneg h)
  exact (spectralRemote_scaled_exponential_symbol (by norm_num)
    (mul_nonneg (abs_nonneg h) hC) hw).add
    (spectralRemote_scaled_exponential_symbol (by norm_num) hD heta)

end DefocusingNLS

end OAI
