import OAI.Geometry.RCD.Sobolev.HarmonicEnergyCompactness
import Mathlib.Analysis.Calculus.FDeriv.Basic

namespace OAI

/-! # Differentiability controls probability means on shrinking balls -/

open Set Filter MeasureTheory Metric Asymptotics
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem differentiable_mean_remainder {n : ℕ} {g : Euclidean n → ℝ}
    {D : Euclidean n →L[ℝ] ℝ} {x : Euclidean n} (hd : HasFDerivAt g D x)
    {A : ℝ} (hA : 0≤A) (r : ℕ → ℝ) (hr : ∀ k, 0<r k)
    (hrlim : Tendsto r atTop (𝓝 0)) (P : ℕ → ProbabilityMeasure (Euclidean n))
    (hs : ∀ k, ∀ᵐ y ∂(P k : Measure (Euclidean n)), dist y x≤A*r k) :
    Tendsto (fun k => (∫ y, g y-g x-D (y-x) ∂(P k : Measure (Euclidean n)))/r k)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/(2*(A+1))
  have hδ : 0<δ := div_pos hε (by positivity)
  have he : ∀ᶠ y in 𝓝 x, ‖g y-g x-D (y-x)‖≤δ*‖y-x‖ :=
    isLittleO_iff.mp (hasFDerivAt_iff_isLittleO.mp hd) hδ
  obtain ⟨s,hspos,hse⟩ := Metric.mem_nhds_iff.mp he
  have hsmall : ∀ᶠ k in atTop, A*r k<s := by
    have hh : Tendsto (fun k => A*r k) atTop (𝓝 0) := by
      simpa only [mul_zero] using hrlim.const_mul A
    exact hh.eventually (Iio_mem_nhds hspos)
  filter_upwards [hsmall] with k hk
  have hb : ∀ᵐ y ∂(P k : Measure (Euclidean n)), ‖g y-g x-D (y-x)‖≤δ*(A*r k) := by
    filter_upwards [hs k] with y hy
    have hys : y∈ball x s := hy.trans_lt hk
    exact (hse hys).trans (mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hy) hδ.le)
  have hi := norm_integral_le_of_norm_le_const hb
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one] at hi
  rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos (hr k)]
  have hib : |∫ y, g y-g x-D (y-x) ∂(P k : Measure (Euclidean n))|/r k≤δ*A := by
    apply (div_le_iff₀ (hr k)).mpr
    simpa only [Real.norm_eq_abs,mul_assoc] using hi
  apply hib.trans_lt
  have hδA : δ*A<ε := by
    dsimp only [δ]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0<2*(A+1))).mpr
    nlinarith
  exact hδA

end RegularPointCoordinates

end

end OAI
