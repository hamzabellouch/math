import OAI.Probability.FreeIsing.Critical.GlobalEndgame
import OAI.Probability.FreeIsing.Estimates.CoupledSmallLogLoss

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace Problem367

theorem log_reciprocal_ge_of_le_exp {J t : ℝ} (ht : 0 < t)
    (hsmall : t ≤ Real.exp (-32 * J)) :
    32 * J ≤ Real.log (1 / t) := by
  have hlog : Real.log t ≤ -32 * J := (Real.log_le_iff_le_exp ht).2 hsmall
  rw [one_div, Real.log_inv]
  linarith

theorem eq_zero_of_coupled_cavity_spatial_bounds
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ξ} [IsProbabilityMeasure ν]
    {theta T M J C : ℝ}
    {X Y X' Y' H N H' N' : ℝ → Ω → ℝ} {R : ℝ → Ξ → ℝ}
    {V S Q L Z : ℝ → ℝ}
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hT : 0 ≤ T) (hM : 0 ≤ M) (hJ : 0 < J)
    (hC : 1 ≤ C) (hcoef : cavityLogVarianceCoefficient theta ≤ C)
    (hX : ∀ t, Measurable (X t)) (hX' : ∀ t, Measurable (X' t))
    (hH : ∀ t ∈ Icc 0 T, Integrable (fun ω => (H t ω - H' t ω) ^ 2) μ)
    (hN : ∀ t ∈ Icc 0 T, Integrable (fun ω => (N t ω - N' t ω) ^ 2) μ)
    (hpair : ∀ t ∈ Ioc 0 T, ∀ᵐ ω ∂μ,
      X t ω + cavityMessage theta (Y t ω) = H t ω ∧
      Y t ω + cavityMessage theta (X t ω) = N t ω ∧
      X' t ω + cavityMessage theta (Y' t ω) = H' t ω ∧
      Y' t ω + cavityMessage theta (X' t ω) = N' t ω)
    (hbound : ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂μ,
      |H t ω - H' t ω| ≤ M ∧ |N t ω - N' t ω| ≤ M)
    (hVeq : ∀ t, V t = ∫ ω, (H t ω - H' t ω) ^ 2 ∂μ)
    (hSeq : ∀ t, S t = ∫ ω,
      (Real.log (responseAttenuation theta (X t ω)) -
        Real.log (responseAttenuation theta (X' t ω))) ^ 2 ∂μ)
    (hNV : ∀ t ∈ Ioc 0 T, (∫ ω, (N t ω - N' t ω) ^ 2 ∂μ) ≤ V t)
    (hLaw : ∀ t ∈ Ioc 0 T, IdentDistrib (X t) (R t) μ ν)
    (hLaw' : ∀ t ∈ Ioc 0 T, IdentDistrib (X' t) (R t) μ ν)
    (hmom : ∀ t ∈ Ioc 0 T, t ≤ Real.exp (-32 * J) →
      ∀ p : ℕ, 1 ≤ p → Integrable (fun ξ => |R t ξ| ^ p) ν ∧
        (∫ ξ, |R t ξ| ^ p ∂ν) ≤
          Real.exp (J * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4))
    (hV : AbsolutelyContinuousOnInterval V 0 T) (hzero : V 0 = 0)
    (hspatial : ∀ᵐ t ∂volume.restrict (Ioc 0 T), 0 < V t →
      Q t ≤ C * (S t * (((min (Real.sqrt t) 1)⁻¹) ^ 2 +
        (Real.log (1 + Real.log ((1 + M ^ 2) / V t))) ^ 2) + V t ^ 2) ∧
      L t ≤ C * (V t * ((min (Real.sqrt t) 1)⁻¹ +
        Real.log (1 + Real.log ((1 + M ^ 2) / V t))) + V t ^ 2) ∧
      Z t ≤ C * (Real.sqrt (S t) *
        ((min (Real.sqrt t) 1)⁻¹ * Real.sqrt ((min (Real.sqrt t) 1)⁻¹) +
          (Real.log (1 + Real.log ((1 + M ^ 2) / V t))) ^ ((3 : ℝ) / 2)) + V t) ∧
      deriv V t ≤ C * (V t + Q t + L t + Real.sqrt (V t) * Z t)) :
    ∀ t ∈ Icc 0 T, V t = 0 := by
  have hcutoff : Real.exp (-32 * J) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hVnonneg (t : ℝ) : 0 ≤ V t := by
    rw [hVeq]
    exact integral_nonneg (fun _ => sq_nonneg _)
  have hSnonneg (t : ℝ) : 0 ≤ S t := by
    rw [hSeq]
    exact integral_nonneg (fun _ => sq_nonneg _)
  have hVupper (t : ℝ) (ht : t ∈ Icc 0 T) : V t ≤ 1 + M ^ 2 := by
    calc
      V t = ∫ ω, (H t ω - H' t ω) ^ 2 ∂μ := hVeq t
      _ ≤ ∫ _ : Ω, M ^ 2 ∂μ := by
        apply integral_mono_ae (hH t ht) (integrable_const _)
        filter_upwards [hbound t ht] with ω hω
        have hs := (sq_le_sq₀ (abs_nonneg _) hM).2 hω.1
        simpa only [sq_abs] using hs
      _ = M ^ 2 := by simp
      _ ≤ 1 + M ^ 2 := by linarith
  have hnoise (t : ℝ) (ht : t ∈ Ioc 0 T) : S t ≤ C * V t := by
    have htcc : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    calc
      S t = _ := hSeq t
      _ ≤ cavityLogVarianceCoefficient theta * V t := by
        exact integral_cavity_log_discrepancy_sq_le hθ0 hθ1 (hX t) (hX' t)
          (hH t htcc) (hN t htcc) (hpair t ht) (le_of_eq (hVeq t).symm) (hNV t ht)
      _ ≤ C * V t := mul_le_mul_of_nonneg_right hcoef (hVnonneg t)
  apply eq_zero_of_ae_critical_spatial_endpoint_bounds
    (cutoff := Real.exp (-32 * J)) (C := C) (H := 1 + M ^ 2)
    (A := cavityLogVarianceCoefficient theta) (B := cavityLogTailCoefficient theta M)
    (c := 1 / (512 * J)) (K := 1 + M ^ 2)
    hT (Real.exp_pos _) hcutoff hC (by nlinarith [sq_nonneg M])
    (cavityLogVarianceCoefficient_nonneg theta) (cavityLogTailCoefficient_nonneg theta M)
    (by positivity) (by nlinarith [sq_nonneg M]) hV hzero
    (fun t _ => hVnonneg t) hVupper hVupper
  · filter_upwards [hspatial, ae_restrict_mem measurableSet_Ioc] with t hs ht
    intro hv
    obtain ⟨hq, hl, hz, hd⟩ := hs hv
    exact ⟨hSnonneg t, hnoise t ht, hq, hl, hz, hd⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro htc _
    have htcc : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    have hlog := log_reciprocal_ge_of_le_exp ht.1 htc
    have htail : ν {ξ | t ^ (1 / 8 : ℝ) < |R t ξ|} ≤
        ENNReal.ofReal (Real.exp (-(1 / (512 * J)) * (Real.log (1 / t)) ^ 2)) := by
      have he : -(1 / (512 * J)) * (Real.log (1 / t)) ^ 2 =
          -((Real.log (1 / t)) ^ 2) / (512 * J) := by ring
      rw [he]
      exact measure_abs_gt_rpow_le_of_moments hJ ht.1 hlog
        (fun p hp => (hmom t ht htc p hp).1) (fun p hp => (hmom t ht htc p hp).2)
    rw [hSeq]
    exact integral_cavity_log_discrepancy_small_time_of_common_law
      hθ0 hθ1 (hX t) (hX' t) (hH t htcc) (hN t htcc) (hpair t ht)
      hM ht.1 (hbound t htcc) (le_of_eq (hVeq t).symm) (hNV t ht)
      (hLaw t ht) (hLaw' t ht) htail

end Problem367

end

end OAI
