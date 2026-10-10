import OAI.Probability.FreeIsing.Energy.CoupledAttenuation
import OAI.Probability.FreeIsing.Energy.MomentTail
import OAI.Probability.FreeIsing.Estimates.LogInterpolation

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

def cavityLogVarianceCoefficient (theta : ℝ) : ℝ :=
  4 / (1 - theta) ^ 2

def cavityLogTailCoefficient (theta M : ℝ) : ℝ :=
  8 * (M / (1 - theta)) ^ 2

theorem cavityLogVarianceCoefficient_nonneg (theta : ℝ) :
    0 ≤ cavityLogVarianceCoefficient theta := by
  unfold cavityLogVarianceCoefficient
  positivity

theorem cavityLogTailCoefficient_nonneg (theta M : ℝ) :
    0 ≤ cavityLogTailCoefficient theta M := by
  unfold cavityLogTailCoefficient
  positivity

section Coupling

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {theta : ℝ} {X Y X' Y' H K H' K' : Ω → ℝ}

theorem integral_cavity_log_discrepancy_sq_le_of_marginal_tails
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hX : Measurable X) (hX' : Measurable X')
    (hH : Integrable (fun ω => (H ω - H' ω) ^ 2) μ)
    (hK : Integrable (fun ω => (K ω - K' ω) ^ 2) μ)
    (heq : ∀ᵐ ω ∂μ,
      X ω + cavityMessage theta (Y ω) = H ω ∧
      Y ω + cavityMessage theta (X ω) = K ω ∧
      X' ω + cavityMessage theta (Y' ω) = H' ω ∧
      Y' ω + cavityMessage theta (X' ω) = K' ω)
    {V M R B₁ B₂ : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐ ω ∂μ, |H ω - H' ω| ≤ M ∧ |K ω - K' ω| ≤ M)
    (hHV : (∫ ω, (H ω - H' ω) ^ 2 ∂μ) ≤ V)
    (hKV : (∫ ω, (K ω - K' ω) ^ 2 ∂μ) ≤ V)
    (hTail : μ.real {ω | R < |X ω|} ≤ B₁)
    (hTail' : μ.real {ω | R < |X' ω|} ≤ B₂) :
    (∫ ω, (Real.log (responseAttenuation theta (X ω)) -
        Real.log (responseAttenuation theta (X' ω))) ^ 2 ∂μ) ≤
      cavityLogVarianceCoefficient theta * R ^ 2 * V +
        min (cavityLogVarianceCoefficient theta * V)
          (4 * (M / (1 - theta)) ^ 2 * (B₁ + B₂)) := by
  have hθsq : theta ^ 2 ≤ 1 := by nlinarith
  have hInt := integrable_cavity_pair_sub_sq hθ0 hθ1 hX hX' hH hK heq
  have hVar := integral_cavity_pair_sub_sq_le hθ0 hθ1 hX hX' hH hK heq hHV hKV
  have hBound : ∀ᵐ ω ∂μ, |X ω - X' ω| ≤ M / (1 - theta) := by
    filter_upwards [heq, hbound] with ω he hb
    exact cavity_pair_sub_abs_le hθ0 hθ1 he.1 he.2.1 he.2.2.1 he.2.2.2 hb.1 hb.2
  have h := integral_log_responseAttenuation_sub_sq_le_of_marginal_tails
    hθsq hX hX' hInt (div_nonneg hM (by linarith)) hBound hVar hTail hTail'
  have hfirst : 4 * R ^ 2 * (V / (1 - theta) ^ 2) =
      cavityLogVarianceCoefficient theta * R ^ 2 * V := by
    unfold cavityLogVarianceCoefficient
    ring
  have hsecond : 4 * (V / (1 - theta) ^ 2) =
      cavityLogVarianceCoefficient theta * V := by
    unfold cavityLogVarianceCoefficient
    ring
  simpa only [hfirst, hsecond] using h

theorem integral_cavity_log_discrepancy_small_time
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hX : Measurable X) (hX' : Measurable X')
    (hH : Integrable (fun ω => (H ω - H' ω) ^ 2) μ)
    (hK : Integrable (fun ω => (K ω - K' ω) ^ 2) μ)
    (heq : ∀ᵐ ω ∂μ,
      X ω + cavityMessage theta (Y ω) = H ω ∧
      Y ω + cavityMessage theta (X ω) = K ω ∧
      X' ω + cavityMessage theta (Y' ω) = H' ω ∧
      Y' ω + cavityMessage theta (X' ω) = K' ω)
    {V M t c : ℝ} (hM : 0 ≤ M) (ht : 0 < t)
    (hbound : ∀ᵐ ω ∂μ, |H ω - H' ω| ≤ M ∧ |K ω - K' ω| ≤ M)
    (hHV : (∫ ω, (H ω - H' ω) ^ 2 ∂μ) ≤ V)
    (hKV : (∫ ω, (K ω - K' ω) ^ 2 ∂μ) ≤ V)
    (hTail : μ.real {ω | t ^ (1 / 8 : ℝ) < |X ω|} ≤
      Real.exp (-c * (Real.log (1 / t)) ^ 2))
    (hTail' : μ.real {ω | t ^ (1 / 8 : ℝ) < |X' ω|} ≤
      Real.exp (-c * (Real.log (1 / t)) ^ 2)) :
    (∫ ω, (Real.log (responseAttenuation theta (X ω)) -
        Real.log (responseAttenuation theta (X' ω))) ^ 2 ∂μ) ≤
      cavityLogVarianceCoefficient theta * t ^ (1 / 4 : ℝ) * V +
        min (cavityLogVarianceCoefficient theta * V)
          (cavityLogTailCoefficient theta M * Real.exp (-c * (Real.log (1 / t)) ^ 2)) := by
  have h := integral_cavity_log_discrepancy_sq_le_of_marginal_tails
    hθ0 hθ1 hX hX' hH hK heq hM hbound hHV hKV hTail hTail'
  have hr : (t ^ (1 / 8 : ℝ)) ^ 2 = t ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  have htail : 4 * (M / (1 - theta)) ^ 2 *
      (Real.exp (-c * (Real.log (1 / t)) ^ 2) + Real.exp (-c * (Real.log (1 / t)) ^ 2)) =
      cavityLogTailCoefficient theta M * Real.exp (-c * (Real.log (1 / t)) ^ 2) := by
    unfold cavityLogTailCoefficient
    ring
  simpa only [hr, htail] using h

theorem integral_cavity_log_discrepancy_small_time_of_moments
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hX : Measurable X) (hX' : Measurable X')
    (hH : Integrable (fun ω => (H ω - H' ω) ^ 2) μ)
    (hK : Integrable (fun ω => (K ω - K' ω) ^ 2) μ)
    (heq : ∀ᵐ ω ∂μ,
      X ω + cavityMessage theta (Y ω) = H ω ∧
      Y ω + cavityMessage theta (X ω) = K ω ∧
      X' ω + cavityMessage theta (Y' ω) = H' ω ∧
      Y' ω + cavityMessage theta (X' ω) = K' ω)
    {V M t A : ℝ} (hM : 0 ≤ M) (ht : 0 < t) (hA : 0 < A)
    (hsmall : 32 * A ≤ Real.log (1 / t))
    (hbound : ∀ᵐ ω ∂μ, |H ω - H' ω| ≤ M ∧ |K ω - K' ω| ≤ M)
    (hHV : (∫ ω, (H ω - H' ω) ^ 2 ∂μ) ≤ V)
    (hKV : (∫ ω, (K ω - K' ω) ^ 2 ∂μ) ≤ V)
    (hInt : ∀ p : ℕ, 1 ≤ p → Integrable (fun ω => |X ω| ^ p) μ)
    (hInt' : ∀ p : ℕ, 1 ≤ p → Integrable (fun ω => |X' ω| ^ p) μ)
    (hmom : ∀ p : ℕ, 1 ≤ p → (∫ ω, |X ω| ^ p ∂μ) ≤
      Real.exp (A * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4))
    (hmom' : ∀ p : ℕ, 1 ≤ p → (∫ ω, |X' ω| ^ p ∂μ) ≤
      Real.exp (A * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4)) :
    (∫ ω, (Real.log (responseAttenuation theta (X ω)) -
        Real.log (responseAttenuation theta (X' ω))) ^ 2 ∂μ) ≤
      cavityLogVarianceCoefficient theta * t ^ (1 / 4 : ℝ) * V +
        min (cavityLogVarianceCoefficient theta * V)
          (cavityLogTailCoefficient theta M *
            Real.exp (-(1 / (512 * A)) * (Real.log (1 / t)) ^ 2)) := by
  have he : -(1 / (512 * A)) * (Real.log (1 / t)) ^ 2 =
      -((Real.log (1 / t)) ^ 2) / (512 * A) := by ring
  apply integral_cavity_log_discrepancy_small_time hθ0 hθ1 hX hX' hH hK heq
    hM ht hbound hHV hKV
  · rw [he]
    exact measureReal_abs_gt_rpow_le_of_moments hA ht hsmall hInt hmom
  · rw [he]
    exact measureReal_abs_gt_rpow_le_of_moments hA ht hsmall hInt' hmom'

theorem integral_cavity_log_discrepancy_small_time_of_common_law
    {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ} {Z : Ξ → ℝ}
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hX : Measurable X) (hX' : Measurable X')
    (hH : Integrable (fun ω => (H ω - H' ω) ^ 2) μ)
    (hK : Integrable (fun ω => (K ω - K' ω) ^ 2) μ)
    (heq : ∀ᵐ ω ∂μ,
      X ω + cavityMessage theta (Y ω) = H ω ∧
      Y ω + cavityMessage theta (X ω) = K ω ∧
      X' ω + cavityMessage theta (Y' ω) = H' ω ∧
      Y' ω + cavityMessage theta (X' ω) = K' ω)
    {V M t c : ℝ} (hM : 0 ≤ M) (ht : 0 < t)
    (hbound : ∀ᵐ ω ∂μ, |H ω - H' ω| ≤ M ∧ |K ω - K' ω| ≤ M)
    (hHV : (∫ ω, (H ω - H' ω) ^ 2 ∂μ) ≤ V)
    (hKV : (∫ ω, (K ω - K' ω) ^ 2 ∂μ) ≤ V)
    (hLaw : IdentDistrib X Z μ ν) (hLaw' : IdentDistrib X' Z μ ν)
    (hTail : ν {z | t ^ (1 / 8 : ℝ) < |Z z|} ≤
      ENNReal.ofReal (Real.exp (-c * (Real.log (1 / t)) ^ 2))) :
    (∫ ω, (Real.log (responseAttenuation theta (X ω)) -
        Real.log (responseAttenuation theta (X' ω))) ^ 2 ∂μ) ≤
      cavityLogVarianceCoefficient theta * t ^ (1 / 4 : ℝ) * V +
        min (cavityLogVarianceCoefficient theta * V)
          (cavityLogTailCoefficient theta M * Real.exp (-c * (Real.log (1 / t)) ^ 2)) := by
  have transfer {W : Ω → ℝ} (hW : IdentDistrib W Z μ ν) :
      μ.real {ω | t ^ (1 / 8 : ℝ) < |W ω|} ≤
        Real.exp (-c * (Real.log (1 / t)) ^ 2) := by
    apply ENNReal.toReal_le_of_le_ofReal (Real.exp_nonneg _)
    have hm := (hW.comp measurable_abs).measure_mem_eq
      (measurableSet_Ioi : MeasurableSet (Set.Ioi (t ^ (1 / 8 : ℝ))))
    change μ {ω | t ^ (1 / 8 : ℝ) < |W ω|} =
      ν {z | t ^ (1 / 8 : ℝ) < |Z z|} at hm
    rw [hm]
    exact hTail
  exact integral_cavity_log_discrepancy_small_time hθ0 hθ1 hX hX' hH hK heq
    hM ht hbound hHV hKV (transfer hLaw) (transfer hLaw')

omit [IsProbabilityMeasure μ] in

theorem integral_cavity_log_discrepancy_osgood_of_small_time
    {V M t c L : ℝ} (hc : 0 < c) (hL : 1 ≤ L)
    (hV : 0 < V) (hVL : V ≤ L) (ht : 0 < t) (ht1 : t < 1)
    (hsmall : (∫ ω, (Real.log (responseAttenuation theta (X ω)) -
        Real.log (responseAttenuation theta (X' ω))) ^ 2 ∂μ) ≤
      cavityLogVarianceCoefficient theta * t ^ (1 / 4 : ℝ) * V +
        min (cavityLogVarianceCoefficient theta * V)
          (cavityLogTailCoefficient theta M * Real.exp (-c * (Real.log (1 / t)) ^ 2))) :
    (∫ ω, (Real.log (responseAttenuation theta (X ω)) -
        Real.log (responseAttenuation theta (X' ω))) ^ 2 ∂μ) ≤
      (cavityLogVarianceCoefficient theta +
        2 * (cavityLogVarianceCoefficient theta + cavityLogTailCoefficient theta M) / c) *
        V * (t ^ (1 / 4 : ℝ) + (1 + Real.log (L / V)) / (Real.log (1 / t)) ^ 2) := by
  exact small_time_log_loss_of_minimum (cavityLogVarianceCoefficient_nonneg theta)
    (cavityLogTailCoefficient_nonneg theta M) hc hL hV hVL ht ht1 hsmall

end Coupling

end Problem367

end

end OAI
