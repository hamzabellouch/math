import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSubunitDifference
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFieldOperator

namespace OAI

/-! The normalized coefficient error tends to zero in the bounded-function
norm when the profile's weighted expansion remainder stays bounded. -/

open Filter Topology
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem exists_spectral_weighted_coefficient_limit
    (m : ℕ → ℕ) (hm : ∀ n, 1 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (q p : ℕ → ℝ → ℂ) (hq : ∀ n, Continuous (q n)) (hp : ∀ n, Continuous (p n))
    (κ T ρ C : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C)
    (e : ℕ → ℝ →ᵇ ℂ) (he : ∀ n, ‖e n‖ ≤ C)
    (hqb : ∀ n t, T ≤ t → ‖q n t‖ ≤ ρ)
    (hpb : ∀ n t, T ≤ t → ‖p n t‖ ≤ ρ)
    (hqp : ∀ n t, T ≤ t → q n t-p n t=(Real.exp (-κ*t) : ℂ)*e n t) :
    ∃ A B : ℕ → ℝ →ᵇ ℂ, Tendsto A atTop (𝓝 0) ∧ Tendsto B atTop (𝓝 0) ∧
      ∀ n t, T ≤ t →
        A n t=(Real.exp (κ*t) : ℂ)*
          (spectralDiagonalCoefficient (m n) (q n t)-spectralDiagonalCoefficient (m n) (p n t)) ∧
        B n t=(Real.exp (κ*t) : ℂ)*
          (spectralCrossCoefficient (m n) (q n t)-spectralCrossCoefficient (m n) (p n t)) := by
  let δ := fun n => 2*(m n : ℝ)*(2*(m n : ℝ)+1)*ρ^(2*m n)/ρ
  have hδ (n : ℕ) : 0 ≤ δ n := by dsimp [δ]; positivity
  have hδ0 : Tendsto δ atTop (𝓝 0) :=
    (spectralCoefficient_difference_rate_tendsto ρ hρ hρ1).comp hmTop
  let f := fun n t => (Real.exp (κ*max T t) : ℂ)*
    (spectralDiagonalCoefficient (m n) (q n (max T t))-
      spectralDiagonalCoefficient (m n) (p n (max T t)))
  let g := fun n t => (Real.exp (κ*max T t) : ℂ)*
    (spectralCrossCoefficient (m n) (q n (max T t))-
      spectralCrossCoefficient (m n) (p n (max T t)))
  have hf (n : ℕ) : Continuous (f n) := by
    dsimp [f,spectralDiagonalCoefficient]
    fun_prop
  have hg (n : ℕ) : Continuous (g n) := by
    dsimp [g,spectralCrossCoefficient]
    fun_prop
  have hb (n : ℕ) (t : ℝ) : ‖f n t‖+‖g n t‖ ≤ δ n*C := by
    have ht : T ≤ max T t := le_max_left _ _
    have hh := spectralCoefficient_weighted_difference (m n) (hm n) ρ hρ
      (q n (max T t)) (p n (max T t)) (e n (max T t)) κ (max T t)
      (hqb n _ ht) (hpb n _ ht) (hqp n _ ht)
    exact hh.trans (mul_le_mul_of_nonneg_left ((e n).norm_coe_le_norm (max T t) |>.trans (he n)) (hδ n))
  let A := fun n => BoundedContinuousFunction.ofNormedAddCommGroup
    (f n) (hf n) (δ n*C) (fun t => (le_add_of_nonneg_right (norm_nonneg (g n t))).trans (hb n t))
  let B := fun n => BoundedContinuousFunction.ofNormedAddCommGroup
    (g n) (hg n) (δ n*C) (fun t => (le_add_of_nonneg_left (norm_nonneg (f n t))).trans (hb n t))
  have hA (n : ℕ) : ‖A n‖ ≤ δ n*C := by
    apply (BoundedContinuousFunction.norm_le (mul_nonneg (hδ n) hC)).mpr
    intro t
    exact (le_add_of_nonneg_right (norm_nonneg (g n t))).trans (hb n t)
  have hB (n : ℕ) : ‖B n‖ ≤ δ n*C := by
    apply (BoundedContinuousFunction.norm_le (mul_nonneg (hδ n) hC)).mpr
    intro t
    exact (le_add_of_nonneg_left (norm_nonneg (f n t))).trans (hb n t)
  have hlim : Tendsto (fun n => δ n*C) atTop (𝓝 0) := by
    simpa only [zero_mul] using hδ0.mul_const C
  refine ⟨A,B,squeeze_zero_norm hA hlim,squeeze_zero_norm hB hlim,?_⟩
  intro n t ht
  constructor
  · change f n t = _
    dsimp only [f]
    rw [max_eq_right ht]
  · change g n t = _
    dsimp only [g]
    rw [max_eq_right ht]

end DefocusingNLS

end OAI
