import OAI.Probability.FreeIsing.Cavity.Pair
import OAI.Probability.FreeIsing.Energy.AttenuationMoments
import OAI.Probability.FreeIsing.Energy.AttenuationProduct
import OAI.Probability.FreeIsing.Estimates.MessageFunction

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367

theorem cavity_pair_sub_sq_le
    {theta x y x' y' H K H' K' : ℝ}
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hx : x + cavityMessage theta y = H)
    (hy : y + cavityMessage theta x = K)
    (hx' : x' + cavityMessage theta y' = H')
    (hy' : y' + cavityMessage theta x' = K') :
    (x - x') ^ 2 ≤
      ((1 + theta) / (1 - theta ^ 2) ^ 2) *
        ((H - H') ^ 2 + theta * (K - K') ^ 2) := by
  have hden : 0 < 1 - theta ^ 2 := by nlinarith
  have hdist := CavityPair.stability_fst
    (lipschitzWith_cavityMessage hθ0 hθ1.le)
    (show (⟨theta, hθ0⟩ : ℝ≥0) < 1 from hθ1) hx hy hx' hy'
  change dist x x' ≤ (dist H H' + theta * dist K K') / (1 - theta ^ 2) at hdist
  have habs : |x - x'| ≤
      (|H - H'| + theta * |K - K'|) / (1 - theta ^ 2) := by
    simpa only [Real.dist_eq, NNReal.coe_mk] using hdist
  have hsquare := (sq_le_sq₀ (abs_nonneg (x - x'))
    (show 0 ≤ (|H - H'| + theta * |K - K'|) / (1 - theta ^ 2) by positivity)).2 habs
  rw [sq_abs, div_pow] at hsquare
  have hweighted : (|H - H'| + theta * |K - K'|) ^ 2 ≤
      (1 + theta) * ((H - H') ^ 2 + theta * (K - K') ^ 2) := by
    have h := mul_nonneg hθ0 (sq_nonneg (|H - H'| - |K - K'|))
    nlinarith [sq_abs (H - H'), sq_abs (K - K')]
  calc
    (x - x') ^ 2 ≤ (|H - H'| + theta * |K - K'|) ^ 2 /
        (1 - theta ^ 2) ^ 2 := hsquare
    _ ≤ ((1 + theta) * ((H - H') ^ 2 + theta * (K - K') ^ 2)) /
        (1 - theta ^ 2) ^ 2 :=
      div_le_div_of_nonneg_right hweighted (sq_nonneg _)
    _ = _ := by ring

theorem cavity_pair_sub_abs_le
    {theta x y x' y' H K H' K' M : ℝ}
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hx : x + cavityMessage theta y = H)
    (hy : y + cavityMessage theta x = K)
    (hx' : x' + cavityMessage theta y' = H')
    (hy' : y' + cavityMessage theta x' = K')
    (hH : |H - H'| ≤ M) (hK : |K - K'| ≤ M) :
    |x - x'| ≤ M / (1 - theta) := by
  have hden : 0 < 1 - theta ^ 2 := by nlinarith
  have hminus : 1 - theta ≠ 0 := by linarith
  have hplus : 1 + theta ≠ 0 := by linarith
  have hdist := CavityPair.stability_fst
    (lipschitzWith_cavityMessage hθ0 hθ1.le)
    (show (⟨theta, hθ0⟩ : ℝ≥0) < 1 from hθ1) hx hy hx' hy'
  change dist x x' ≤ (dist H H' + theta * dist K K') / (1 - theta ^ 2) at hdist
  have habs : |x - x'| ≤
      (|H - H'| + theta * |K - K'|) / (1 - theta ^ 2) := by
    simpa only [Real.dist_eq, NNReal.coe_mk] using hdist
  calc
    |x - x'| ≤ (|H - H'| + theta * |K - K'|) / (1 - theta ^ 2) := habs
    _ ≤ (M + theta * M) / (1 - theta ^ 2) := by gcongr
    _ = M / (1 - theta) := by
      field_simp
      ring

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {theta : ℝ} {X Y X' Y' H K H' K' : Ω → ℝ}

theorem memLp_log_responseAttenuation {p : ENNReal}
    (hθ : theta ^ 2 ≤ 1) (hX : MemLp X p μ) :
    MemLp (fun ω => Real.log (responseAttenuation theta (X ω))) p μ := by
  simpa only [Function.comp_def] using
    (lipschitzWith_log_responseAttenuation hθ).comp_memLp
      (by simp only [responseAttenuation_zero, Real.log_one]) hX

theorem centered_log_response_discrepancy_of_identDistrib [IsFiniteMeasure μ]
    (hθ : theta ^ 2 ≤ 1) (hX : MemLp X 2 μ)
    (hlaw : ProbabilityTheory.IdentDistrib X X' μ μ) :
    MemLp (fun ω => Real.log (responseAttenuation theta (X ω)) -
      Real.log (responseAttenuation theta (X' ω))) 2 μ ∧
      (∫ ω, Real.log (responseAttenuation theta (X ω)) -
        Real.log (responseAttenuation theta (X' ω)) ∂μ) = 0 := by
  have hLX := memLp_log_responseAttenuation hθ hX
  have hLLaw := hlaw.comp (lipschitzWith_log_responseAttenuation hθ).continuous.measurable
  simp only [Function.comp_def] at hLLaw
  have hLX' := hLLaw.memLp_snd hLX
  have hI := MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) hLX
  have hI' := MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) hLX'
  refine ⟨hLX.sub hLX', ?_⟩
  rw [integral_sub hI hI', hLLaw.integral_eq, sub_self]

theorem integrable_cavity_pair_sub_sq
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hX : Measurable X) (hX' : Measurable X')
    (hH : Integrable (fun ω => (H ω - H' ω) ^ 2) μ)
    (hK : Integrable (fun ω => (K ω - K' ω) ^ 2) μ)
    (heq : ∀ᵐ ω ∂μ,
      X ω + cavityMessage theta (Y ω) = H ω ∧
      Y ω + cavityMessage theta (X ω) = K ω ∧
      X' ω + cavityMessage theta (Y' ω) = H' ω ∧
      Y' ω + cavityMessage theta (X' ω) = K' ω) :
    Integrable (fun ω => (X ω - X' ω) ^ 2) μ := by
  apply ((hH.add (hK.const_mul theta)).const_mul
    ((1 + theta) / (1 - theta ^ 2) ^ 2)).mono'
    (((hX.sub hX').pow_const 2).aestronglyMeasurable)
  filter_upwards [heq] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact cavity_pair_sub_sq_le hθ0 hθ1 hω.1 hω.2.1 hω.2.2.1 hω.2.2.2

theorem integral_cavity_pair_sub_sq_le
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hX : Measurable X) (hX' : Measurable X')
    (hH : Integrable (fun ω => (H ω - H' ω) ^ 2) μ)
    (hK : Integrable (fun ω => (K ω - K' ω) ^ 2) μ)
    (heq : ∀ᵐ ω ∂μ,
      X ω + cavityMessage theta (Y ω) = H ω ∧
      Y ω + cavityMessage theta (X ω) = K ω ∧
      X' ω + cavityMessage theta (Y' ω) = H' ω ∧
      Y' ω + cavityMessage theta (X' ω) = K' ω)
    {V : ℝ}
    (hHV : (∫ ω, (H ω - H' ω) ^ 2 ∂μ) ≤ V)
    (hKV : (∫ ω, (K ω - K' ω) ^ 2 ∂μ) ≤ V) :
    (∫ ω, (X ω - X' ω) ^ 2 ∂μ) ≤ V / (1 - theta) ^ 2 := by
  have hXint := integrable_cavity_pair_sub_sq hθ0 hθ1 hX hX' hH hK heq
  have hden : 0 < 1 - theta ^ 2 := by nlinarith
  have hminus : 1 - theta ≠ 0 := by linarith
  have hplus : 1 + theta ≠ 0 := by linarith
  have hcoef : 0 ≤ (1 + theta) / (1 - theta ^ 2) ^ 2 := by positivity
  calc
    (∫ ω, (X ω - X' ω) ^ 2 ∂μ) ≤
        ∫ ω, ((1 + theta) / (1 - theta ^ 2) ^ 2) *
          ((H ω - H' ω) ^ 2 + theta * (K ω - K' ω) ^ 2) ∂μ := by
      apply integral_mono_ae hXint
        ((hH.add (hK.const_mul theta)).const_mul _)
      filter_upwards [heq] with ω hω
      exact cavity_pair_sub_sq_le hθ0 hθ1 hω.1 hω.2.1 hω.2.2.1 hω.2.2.2
    _ = ((1 + theta) / (1 - theta ^ 2) ^ 2) *
        ((∫ ω, (H ω - H' ω) ^ 2 ∂μ) +
          theta * ∫ ω, (K ω - K' ω) ^ 2 ∂μ) := by
      rw [integral_const_mul, integral_add hH (hK.const_mul theta), integral_const_mul]
    _ ≤ ((1 + theta) / (1 - theta ^ 2) ^ 2) * (V + theta * V) := by
      gcongr
    _ = V / (1 - theta) ^ 2 := by
      field_simp
      ring

theorem integral_cavity_log_discrepancy_sq_le
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hX : Measurable X) (hX' : Measurable X')
    (hH : Integrable (fun ω => (H ω - H' ω) ^ 2) μ)
    (hK : Integrable (fun ω => (K ω - K' ω) ^ 2) μ)
    (heq : ∀ᵐ ω ∂μ,
      X ω + cavityMessage theta (Y ω) = H ω ∧
      Y ω + cavityMessage theta (X ω) = K ω ∧
      X' ω + cavityMessage theta (Y' ω) = H' ω ∧
      Y' ω + cavityMessage theta (X' ω) = K' ω)
    {V : ℝ}
    (hHV : (∫ ω, (H ω - H' ω) ^ 2 ∂μ) ≤ V)
    (hKV : (∫ ω, (K ω - K' ω) ^ 2 ∂μ) ≤ V) :
    (∫ ω, (Real.log (responseAttenuation theta (X ω)) -
        Real.log (responseAttenuation theta (X' ω))) ^ 2 ∂μ) ≤
      4 / (1 - theta) ^ 2 * V := by
  have hθsq : theta ^ 2 ≤ 1 := by nlinarith
  have hXint := integrable_cavity_pair_sub_sq hθ0 hθ1 hX hX' hH hK heq
  calc
    (∫ ω, (Real.log (responseAttenuation theta (X ω)) -
        Real.log (responseAttenuation theta (X' ω))) ^ 2 ∂μ) ≤
        ∫ ω, 4 * (X ω - X' ω) ^ 2 ∂μ :=
      integral_mono
        (integrable_log_responseAttenuation_sub_sq hθsq hX hX' hXint)
        (hXint.const_mul 4) (fun _ => log_responseAttenuation_sub_sq_le hθsq)
    _ = 4 * ∫ ω, (X ω - X' ω) ^ 2 ∂μ := integral_const_mul _ _
    _ ≤ 4 * (V / (1 - theta) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (integral_cavity_pair_sub_sq_le hθ0 hθ1 hX hX' hH hK heq hHV hKV)
        (by norm_num)
    _ = 4 / (1 - theta) ^ 2 * V := by ring

end Probability

end Problem367

end

end OAI
