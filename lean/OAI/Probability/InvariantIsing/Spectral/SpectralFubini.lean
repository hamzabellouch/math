import OAI.Probability.InvariantIsing.Spectral.SpectralDensityContinuity
import OAI.Probability.InvariantIsing.Spectral.SpectralPrimitive
import OAI.Probability.InvariantIsing.Spectral.SpectralSymbols

namespace OAI

/-! Fubini identification of reconstructed spectral-group symbols. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

/-- The layer-cake calculation in manuscript `rot:function-path`. -/
theorem integral_spectralDensity_CDF_fubini (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) {q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) :
    (∫ r in q..1, spectralPathDensity ρ eig hρ hρsum p a r *
      pathMeasure.real {u | p u ≤ r}) =
      ∫ u, (∫ r in max q (p u)..1, spectralPathDensity ρ eig hρ hρsum p a r) ∂pathMeasure := by
  let h := spectralPathDensity ρ eig hρ hρsum p a
  let K : ℝ → ℝ → ℝ := fun r u => if p u ≤ r then h r else 0
  let : IsFiniteMeasure (volume.restrict (uIoc q 1)) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min q 1) (max q 1)))
    infer_instance
  have hm : Measurable (Function.uncurry K) := by
    exact Measurable.ite
      (measurableSet_le (p.measurable.comp measurable_snd) measurable_fst)
      ((continuous_spectralPathDensity ρ eig hρ hρsum p a).measurable.comp measurable_fst)
      measurable_const
  have hK : Integrable (Function.uncurry K)
      ((volume.restrict (uIoc q 1)).prod pathMeasure) := by
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    exact ae_of_all _ fun z => by
      dsimp [Function.uncurry, K]
      split_ifs
      · rw [abs_of_nonneg (spectralPathDensity_nonneg ρ eig hρ hρsum p a z.1)]
        exact spectralPathDensity_le_one ρ eig hρ hρsum p a z.1
      · simp
  have hinner_u : ∀ r, (∫ u, K r u ∂pathMeasure) = h r * pathMeasure.real {u | p u ≤ r} := by
    intro r
    change (∫ u, ({u | p u ≤ r}).indicator (fun _ => h r) u ∂pathMeasure) = _
    rw [integral_indicator_const (h r) (measurableSet_le p.measurable measurable_const)]
    simp only [smul_eq_mul, mul_comm]
  have hinner_r : ∀ u, (∫ r in q..1, K r u) = ∫ r in max q (p u)..1, h r := by
    intro u
    rw [intervalIntegral.integral_of_le hq.2,
      intervalIntegral.integral_of_le (max_le hq.2 (p.le_one u))]
    change (∫ r, (Ici (p u)).indicator h r ∂volume.restrict (Ioc q 1)) = _
    rw [integral_indicator measurableSet_Ici,
      ← restrict_Ioi_eq_restrict_Ici,
      Measure.restrict_restrict measurableSet_Ioi, inter_comm, Ioc_inter_Ioi]
  have hswap := intervalIntegral_integral_swap hK
  simp_rw [hinner_u, hinner_r] at hswap
  exact hswap

theorem spectralGroupSymbol_eq_CDF_integral (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    pathSymbol (spectralGroupDiagonal ρ eig hρ hρsum p a)
      (spectralGroupPath ρ eig hρ hρsum p a) s =
      ∫ r in p s..1, spectralPathDensity ρ eig hρ hρsum p a r *
        pathMeasure.real {u | p u ≤ r} := by
  let h := spectralPathDensity ρ eig hρ hρsum p a
  let G : ℝ → ℝ := fun q => ∫ r in 0..q, h r
  have hc : Continuous h := continuous_spectralPathDensity ρ eig hρ hρsum p a
  have hG : Monotone G := by
    intro q r hqr
    have hi := intervalIntegral.integral_nonneg_of_forall (μ := volume) hqr
      (spectralPathDensity_nonneg ρ eig hρ hρsum p a)
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ := volume) 0 q) (hc.intervalIntegrable (μ := volume) q r)
    dsimp [G]
    linarith
  let H : ℝ → ℝ := fun u => G (max (p s) (p u))
  have hH : Monotone H := by
    intro u v huv
    exact hG (max_le_max le_rfl (p.monotone huv))
  have hHbounds : ∀ u, 0 ≤ H u ∧ H u ≤ spectralGroupDiagonal ρ eig hρ hρsum p a := by
    intro u
    have h0 : G 0 = 0 := by simp [G]
    constructor
    · rw [← h0]
      exact hG (le_max_of_le_left (p.nonneg s))
    · exact hG (max_le (p.le_one s) (p.le_one u))
  have hHi : Integrable H pathMeasure := by
    apply (integrable_const (spectralGroupDiagonal ρ eig hρ hρsum p a)).mono'
      hH.measurable.aestronglyMeasurable
    exact ae_of_all _ fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hHbounds u).1]
      exact (hHbounds u).2
  have htail : ∀ u, (∫ r in max (p s) (p u)..1, h r) =
      spectralGroupDiagonal ρ eig hρ hρsum p a - H u := by
    intro u
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ := volume) 0 (max (p s) (p u)))
      (hc.intervalIntegrable (μ := volume) (max (p s) (p u)) 1)
    change _ = (∫ r in 0..1, h r) - (∫ r in 0..max (p s) (p u), h r)
    linarith
  have hlow : (∫ u in 0..s, H u) = s * spectralGroupPath ρ eig hρ hρsum p a s := by
    calc
      _ = ∫ _ in 0..s, spectralGroupPath ρ eig hρ hρsum p a s := by
        apply intervalIntegral.integral_congr_Ioo_of_le hs.1
        intro u hu
        dsimp [H]
        rw [max_eq_left (p.monotone hu.2.le)]
        rfl
      _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hhigh : (∫ u in s..1, H u) = ∫ u in s..1, spectralGroupPath ρ eig hρ hρsum p a u := by
    apply intervalIntegral.integral_congr_Ioo_of_le hs.2
    intro u hu
    dsimp [H]
    rw [max_eq_right (p.monotone hu.1.le)]
    rfl
  have hHmean : (∫ u, H u ∂pathMeasure) =
      s * spectralGroupPath ρ eig hρ hρsum p a s +
        ∫ u in s..1, spectralGroupPath ρ eig hρ hρsum p a u := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hH.intervalIntegrable (μ := volume) (a := 0) (b := s))
      (hH.intervalIntegrable (μ := volume) (a := s) (b := 1))
    rw [hlow, hhigh] at hadd
    change (∫ u in Ioo 0 1, H u) = _
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    exact hadd.symm
  rw [integral_spectralDensity_CDF_fubini ρ eig hρ hρsum p a ⟨p.nonneg s, p.le_one s⟩]
  change _ = ∫ u, (∫ r in max (p s) (p u)..1, h r) ∂pathMeasure
  simp_rw [htail]
  rw [integral_sub (integrable_const _) hHi]
  simp only [integral_const, measureReal_def, pathMeasure_univ, ENNReal.toReal_one, one_smul]
  rw [hHmean]
  unfold pathSymbol
  ring

/-- The full reconstructed-symbol identity in manuscript `rot:function-path`. -/
theorem spectralGroupSymbol_eq_projectedResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    pathSymbol (spectralGroupDiagonal ρ eig hρ hρsum p a)
      (spectralGroupPath ρ eig hρ hρsum p a) s =
      projectedResolvent ρ eig hρ hρsum a (deficit p (p s)) := by
  rw [spectralGroupSymbol_eq_CDF_integral ρ eig hρ hρsum p a hs]
  exact integral_spectralDensity_mul_CDF ρ eig hρ hρsum p a ⟨p.nonneg s, p.le_one s⟩

end InvariantIsing

end

end OAI
