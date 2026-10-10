import OAI.Analysis.LipschitzHilbert.Estimates.FiniteAmplitudeGeometric

namespace OAI

/-! The numerical small- and large-measure tails for the amplitude
levels after bin projection. The constants are independent of dimension
and of the finite set of retained levels. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem amplitude_small_mass_tail (I : Finset ℤ) (mass : ℤ → ℝ) (M0 Q eps : ℝ)
    (hM0 : 0<M0) (hQ : 0≤Q) (_heps : 0≤eps)
    (hamp : ∀ i∈I, (2:ℝ)^i≤2*Q)
    (hmass : ∀ i∈I, mass i≤eps*M0) :
    (∑ i∈I, (2:ℝ)^i*Real.sqrt (mass i/M0))≤8*Q*Real.sqrt eps := by
  have hsum := finite_zpow_sum_bound I 2 (2*Q) (by norm_num) (by positivity) hamp
  have hsum' : (∑ i∈I, (2:ℝ)^i)≤8*Q := by norm_num at hsum; linarith
  calc
    _ ≤ ∑ i∈I, (2:ℝ)^i*Real.sqrt eps := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ((div_le_iff₀ hM0).mpr (hmass i hi)))
      positivity
    _ = (∑ i∈I, (2:ℝ)^i)*Real.sqrt eps := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hsum' (Real.sqrt_nonneg _)

theorem amplitude_large_mass_tail (I : Finset ℤ) (mass : ℤ → ℝ) (M0 Q eps : ℝ)
    (hM0 : 0<M0) (hQ : 0≤Q) (heps : 0<eps)
    (hmass : ∀ i∈I, 0≤mass i)
    (hlarge : ∀ i∈I, M0≤eps*mass i)
    (hL1 : ∀ i∈I, (2:ℝ)^i*mass i≤2*Q*M0) :
    (∑ i∈I, (2:ℝ)^i*Real.sqrt (mass i/M0))≤
      2*(2/(1-(Real.sqrt 2)⁻¹))*Q*Real.sqrt eps := by
  have hbase : 1<Real.sqrt 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    have hp := Real.sqrt_nonneg (2:ℝ)
    nlinarith
  have hamp (i : ℤ) (hi : i∈I) : (2:ℝ)^i≤2*Q*eps := by
    have hpow : 0≤(2:ℝ)^i := (zpow_pos (by norm_num) _).le
    have h1 := mul_le_mul_of_nonneg_left (hlarge i hi) hpow
    have h2 := mul_le_mul_of_nonneg_left (hL1 i hi) heps.le
    have he : (2:ℝ)^i*M0≤(2*Q*eps)*M0 := by nlinarith
    nlinarith
  have hsum := finite_zpow_sum_bound I (Real.sqrt 2) (Real.sqrt (2*Q*eps)) hbase
    (Real.sqrt_nonneg _) (fun i hi => by rw [sqrt_two_zpow]; exact Real.sqrt_le_sqrt (hamp i hi))
  have hpoint (i : ℤ) (hi : i∈I) :
      (2:ℝ)^i*Real.sqrt (mass i/M0)≤Real.sqrt (2*Q)*(Real.sqrt 2)^i := by
    rw [sqrt_two_zpow]
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,mul_pow,Real.sq_sqrt (div_nonneg (hmass i hi) hM0.le),
      Real.sq_sqrt (by positivity : 0≤2*Q),Real.sq_sqrt (by positivity : 0≤(2:ℝ)^i)]
    have hh : (2:ℝ)^i*(mass i/M0)≤2*Q := by
      rw [←mul_div_assoc]
      exact (div_le_iff₀ hM0).mpr (hL1 i hi)
    nlinarith [mul_le_mul_of_nonneg_left hh (zpow_pos (by norm_num : (0:ℝ)<2) i).le]
  calc
    _ ≤ ∑ i∈I, Real.sqrt (2*Q)*(Real.sqrt 2)^i := Finset.sum_le_sum hpoint
    _ = Real.sqrt (2*Q)*(∑ i∈I, (Real.sqrt 2)^i) := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.sqrt (2*Q)*((2/(1-(Real.sqrt 2)⁻¹))*Real.sqrt (2*Q*eps)) :=
      mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul (by positivity : 0≤2*Q)]
      have hs := Real.sq_sqrt (by positivity : 0≤2*Q)
      calc
        _ = (2/(1-(Real.sqrt 2)⁻¹))*Real.sqrt eps*(Real.sqrt (2*Q))^2 := by ring
        _ = _ := by rw [hs]; ring

end LipschitzHilbert

end

end OAI
