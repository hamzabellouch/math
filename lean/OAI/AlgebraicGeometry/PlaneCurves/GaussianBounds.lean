import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import OAI.AlgebraicGeometry.PlaneCurves.ThetaSeries

namespace OAI

/-!
# Gaussian bounds and fixed-parameter theta convergence
-/

section

/-! Fixed-parameter Gaussian bounds. A global completed-square estimate removes
any small-parameter restriction; all real linear coefficients are allowed. -/
noncomputable section
namespace Nagata.W02

def gaussianConstant (c C : ℝ) : ℝ := (C + 1) ^ 2 / (4 * c)

/-- Completed square with a spare linear decay of slope one. -/
theorem gaussian_exponent_le (c C t : ℝ) (hc : 0 < c) :
    -c * t ^ 2 + C * t ≤ gaussianConstant c C - t := by
  have hid : c * gaussianConstant c C = (C + 1) ^ 2 / 4 := by
    unfold gaussianConstant
    field_simp
  apply le_of_mul_le_mul_left (a := c) _ hc
  nlinarith [sq_nonneg (c * t - (C + 1) / 2)]

/-- Global explicit exponential majorant, independent of the index. -/
theorem gaussian_exp_le (c C t : ℝ) (hc : 0 < c) :
    Real.exp (-c * t ^ 2 + C * t) ≤
      Real.exp (gaussianConstant c C) * Real.exp (-t) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by simpa [sub_eq_add_neg] using gaussian_exponent_le c C t hc)

/-- Any polynomially weighted Gaussian with arbitrary linear perturbation is
summable on natural numbers; the index zero is included. -/
theorem summable_pow_mul_gaussian (c C : ℝ) (N : ℕ) (hc : 0 < c) :
    Summable (fun t : ℕ => (t : ℝ) ^ N * Real.exp (-c * (t : ℝ) ^ 2 + C * t)) := by
  have hsum := (Real.summable_pow_mul_exp_neg_nat_mul N (show (0 : ℝ) < 1 by norm_num)).mul_left
    (Real.exp (gaussianConstant c C))
  apply hsum.of_nonneg_of_le
  · intro t
    positivity
  · intro t
    have hb := mul_le_mul_of_nonneg_left (gaussian_exp_le c C (t : ℝ) hc)
      (pow_nonneg (Nat.cast_nonneg t) N)
    simpa only [one_mul, neg_mul, mul_neg_one, neg_one_mul, mul_comm, mul_left_comm, mul_assoc] using hb

end Nagata.W02

end
end

section

/-! Gaussian disk bounds for the literal normalized theta summands. All fixed
0<τ<1 are covered, and the multiplier may be any nonzero complex number. -/
noncomputable section
namespace Nagata.W02
open Nagata.W07

def thetaGaussianDecay (n τ : ℝ) : ℝ := -Real.log τ * n / 2

def thetaGaussianLinear (n a τ R : ℝ) (ε : ℂ) : ℝ :=
  Real.log τ * (thetaMargin n a - n / 2) + n * R + |Real.log ‖ε‖|

def thetaGaussianMajorant (n a K τ R : ℝ) (ε : ℂ) (N : ℕ) (p : ℤ) : ℝ :=
  Real.exp (|K| * R) * (|K| + n) ^ N *
    Real.exp (-thetaGaussianDecay n τ * (p.natAbs : ℝ) ^ 2 +
      (thetaGaussianLinear n a τ R ε + N) * (p.natAbs : ℝ))

theorem thetaGaussianDecay_pos {n τ : ℝ} (hn : 0 < n) (hτ : 0 < τ) (hτ1 : τ < 1) :
    0 < thetaGaussianDecay n τ := by
  have hl : Real.log τ < 0 := Real.log_neg hτ hτ1
  exact div_pos (mul_pos (neg_pos.mpr hl) hn) (by norm_num)

/-- General nonzero multipliers cost only a linear exponential in |p|. -/
theorem norm_zpow_le_exp_natAbs (ε : ℂ) (hε : ε ≠ 0) (p : ℤ) :
    ‖ε ^ (-p)‖ ≤ Real.exp (|Real.log ‖ε‖| * (p.natAbs : ℝ)) := by
  rw [norm_zpow, ← Real.rpow_intCast, Real.rpow_def_of_pos (norm_pos_iff.mpr hε)]
  apply Real.exp_le_exp.mpr
  rw [Int.cast_neg, natAbs_real]
  calc
    Real.log ‖ε‖ * -(p : ℝ) ≤ |Real.log ‖ε‖ * -(p : ℝ)| := le_abs_self _
    _ = |Real.log ‖ε‖| * |(p : ℝ)| := by rw [abs_mul, abs_neg]

/-- Affine frequency weights are absorbed into a linear exponential. -/
theorem affine_frequency_pow_le (A n t : ℝ) (N : ℕ)
    (hA : 0 ≤ A) (hn : 0 ≤ n) (ht : 0 ≤ t) :
    (A + n * t) ^ N ≤ (A + n) ^ N * Real.exp ((N : ℝ) * t) := by
  have hbase : A + n * t ≤ (A + n) * Real.exp t := by
    calc
      A + n * t ≤ (A + n) * (t + 1) := by nlinarith
      _ ≤ (A + n) * Real.exp t :=
        mul_le_mul_of_nonneg_left (Real.add_one_le_exp t) (add_nonneg hA hn)
  have hp := pow_le_pow_left₀ (add_nonneg hA (mul_nonneg hn ht)) hbase N
  simpa only [mul_pow, ← Real.exp_nat_mul] using hp

/-- The exact derivative summands have a disk-uniform Gaussian majorant. -/
theorem norm_normalizedThetaDerivativeTerm_le_gaussian
    {n a K τ R : ℝ} {ε x : ℂ} (hn : 0 < n) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hε : ε ≠ 0) (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) (N : ℕ) (p : ℤ) :
    ‖normalizedThetaDerivativeTerm n a K ε τ N p x‖ ≤
      thetaGaussianMajorant n a K τ R ε N p := by
  let t : ℝ := p.natAbs
  let A : ℝ := |K| + n * t
  let Q : ℝ := thetaMargin n a * t + n * t * (t - 1) / 2
  have ht : 0 ≤ t := Nat.cast_nonneg _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hfreq : |K + n * (p : ℝ)| ≤ A := theta_frequency_le hn.le K p
  have hεbound := norm_zpow_le_exp_natAbs ε hε p
  have hlog : Real.log τ < 0 := Real.log_neg hτ hτ1
  have hquad : Q ≤ thetaExponent n a (p : ℝ) := by
    simpa only [Q, t, natAbs_real] using thetaExponent_quadratic_lower n a (p : ℝ)
  have hpower : τ ^ thetaExponent n a (p : ℝ) ≤ Real.exp (Real.log τ * Q) := by
    rw [Real.rpow_def_of_pos hτ]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hquad hlog.le)
  have hexp : ‖Complex.exp (((K + n * (p : ℝ) : ℝ) : ℂ) * x)‖ ≤ Real.exp (A * R) := by
    apply (Complex.norm_exp_le_exp_norm _).trans
    apply Real.exp_le_exp.mpr
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hx (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hfreq hR)
  have hfreqpow := pow_le_pow_left₀ (abs_nonneg _) hfreq N
  have hnorm : ‖normalizedThetaDerivativeTerm n a K ε τ N p x‖ =
      |K + n * (p : ℝ)| ^ N * ‖ε ^ (-p)‖ * τ ^ thetaExponent n a (p : ℝ) *
        ‖Complex.exp (((K + n * (p : ℝ) : ℝ) : ℂ) * x)‖ := by
    simp only [normalizedThetaDerivativeTerm, normalizedThetaTerm, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hτ.le _), mul_assoc]
  have hmain : ‖normalizedThetaDerivativeTerm n a K ε τ N p x‖ ≤
      A ^ N * Real.exp (|Real.log ‖ε‖| * t) * Real.exp (Real.log τ * Q) *
        Real.exp (A * R) := by
    rw [hnorm]
    gcongr
  have hfreq2 := affine_frequency_pow_le |K| n t N (abs_nonneg K) hn.le ht
  calc
    _ ≤ A ^ N * Real.exp (|Real.log ‖ε‖| * t) * Real.exp (Real.log τ * Q) *
        Real.exp (A * R) := hmain
    _ ≤ ((|K| + n) ^ N * Real.exp ((N : ℝ) * t)) *
        Real.exp (|Real.log ‖ε‖| * t) * Real.exp (Real.log τ * Q) *
        Real.exp (A * R) := by gcongr
    _ = thetaGaussianMajorant n a K τ R ε N p := by
      unfold thetaGaussianMajorant thetaGaussianDecay thetaGaussianLinear
      rw [mul_comm (Real.exp (|K| * R)) ((|K| + n) ^ N)]
      simp only [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [Q, A, t]
      ring

end Nagata.W02

end
end

section

/-! All-parameter normal convergence and holomorphy for the actual source theta
series. No Jacobi identification and no small-τ restriction is used. -/
noncomputable section
open Filter Topology
namespace Nagata.W02
open Nagata.W07 Nagata.W22

/-- Transfer an absolutely summable natural sequence to symmetric integer indices. -/
theorem summable_natAbs {f : ℕ → ℝ} (hf : Summable f) :
    Summable (fun p : ℤ => f p.natAbs) := by
  have hp : Summable (fun t : ℕ => f (t : ℤ).natAbs) := by simpa using hf
  have hm : Summable (fun t : ℕ => f (-(t + 1 : ℤ)).natAbs) := by
    have hh := (summable_nat_add_iff (f := f) 1).mpr hf
    simpa only [Int.natAbs_neg, ← Nat.cast_one (R := ℤ), ← Nat.cast_add,
      Int.natAbs_natCast] using hh
  exact hp.of_nat_of_neg_add_one hm

/-- The same explicit majorant is summable on the entire integer lattice. -/
theorem summable_thetaGaussianMajorant {n τ : ℝ} (hn : 0 < n)
    (hτ : 0 < τ) (hτ1 : τ < 1) (a K R : ℝ) (ε : ℂ) (N : ℕ) :
    Summable (thetaGaussianMajorant n a K τ R ε N) := by
  have hc := thetaGaussianDecay_pos hn hτ hτ1
  have hs : Summable (fun t : ℕ => Real.exp (-thetaGaussianDecay n τ * (t : ℝ) ^ 2 +
      (thetaGaussianLinear n a τ R ε + N) * (t : ℝ))) := by
    simpa using summable_pow_mul_gaussian (thetaGaussianDecay n τ)
      (thetaGaussianLinear n a τ R ε + N) 0 hc
  exact (summable_natAbs hs).mul_left (Real.exp (|K| * R) * (|K| + n) ^ N)

/-- Absolute summability at every point, for every fixed 0<τ<1 and ε≠0. -/
theorem summable_normalizedThetaDerivativeTerm_allTau
    {n a K τ : ℝ} {ε : ℂ} (hn : 0 < n) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hε : ε ≠ 0) (N : ℕ) (x : ℂ) :
    Summable (fun p : ℤ => ‖normalizedThetaDerivativeTerm n a K ε τ N p x‖) := by
  exact (summable_thetaGaussianMajorant hn hτ hτ1 a K ‖x‖ ε N).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun p => norm_normalizedThetaDerivativeTerm_le_gaussian
      hn hτ hτ1 hε (norm_nonneg x) le_rfl N p)

/-- Normal convergence of actual derivative-series finite sums on every closed disk. -/
theorem tendstoUniformlyOn_normalizedThetaDerivativeSeries_allTau
    {n a K τ R : ℝ} {ε : ℂ} (hn : 0 < n) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hε : ε ≠ 0) (hR : 0 ≤ R) (N : ℕ) :
    TendstoUniformlyOn
      (fun S : Finset ℤ => fun x => ∑ p ∈ S, normalizedThetaDerivativeTerm n a K ε τ N p x)
      (normalizedThetaDerivativeSeries n a K ε τ N) atTop {x : ℂ | ‖x‖ ≤ R} := by
  apply tendstoUniformlyOn_tsum (summable_thetaGaussianMajorant hn hτ hτ1 a K R ε N)
  intro p x hx
  exact norm_normalizedThetaDerivativeTerm_le_gaussian hn hτ hτ1 hε hR hx N p

/-- Every formal derivative series is entire, obtained from its actual finite
sums on a disk around each point. -/
theorem differentiable_normalizedThetaDerivativeSeries_allTau
    {n a K τ : ℝ} {ε : ℂ} (hn : 0 < n) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hε : ε ≠ 0) (N : ℕ) :
    Differentiable ℂ (normalizedThetaDerivativeSeries n a K ε τ N) := by
  intro x
  let R : ℝ := ‖x‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hu := tendstoUniformlyOn_normalizedThetaDerivativeSeries_allTau
    (a := a) (K := K) hn hτ hτ1 hε hR N
  have hlocal := (hu.mono (show {z : ℂ | ‖z‖ < R} ⊆ {z : ℂ | ‖z‖ ≤ R}
    from fun z hz => (show ‖z‖ < R from hz).le)).tendstoLocallyUniformlyOn
  have hfinite : ∀ S : Finset ℤ, DifferentiableOn ℂ
      (fun z => ∑ p ∈ S, normalizedThetaDerivativeTerm n a K ε τ N p z)
      {z : ℂ | ‖z‖ < R} := by
    intro S
    apply DifferentiableOn.fun_sum
    intro p hp
    have hd : Differentiable ℂ (normalizedThetaDerivativeTerm n a K ε τ N p) := by
      unfold normalizedThetaDerivativeTerm normalizedThetaTerm
      exact (differentiable_const _).mul
        ((differentiable_const _).mul ((differentiable_const _).mul differentiable_id).cexp)
    exact hd.differentiableOn
  have hU : IsOpen {z : ℂ | ‖z‖ < R} := isOpen_lt continuous_norm continuous_const
  have hdiff := hlocal.differentiableOn (Eventually.of_forall hfinite) hU
  exact hdiff.differentiableAt (hU.mem_nhds (by dsimp [R]; simp))

/-- The literal source theta series is entire for every fixed allowed parameter
and arbitrary nonzero multiplier, without invoking Jacobi theta. -/
theorem differentiable_normalizedThetaSeries_allTau
    {n a K τ : ℝ} {ε : ℂ} (hn : 0 < n) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hε : ε ≠ 0) : Differentiable ℂ (normalizedThetaSeries n a K ε τ) := by
  have he : normalizedThetaDerivativeSeries n a K ε τ 0 = normalizedThetaSeries n a K ε τ := by
    funext x
    exact normalizedThetaDerivativeSeries_zero n a K ε τ x
  rw [← he]
  exact differentiable_normalizedThetaDerivativeSeries_allTau (a := a) (K := K) hn hτ hτ1 hε 0

end Nagata.W02

end
end

end OAI
