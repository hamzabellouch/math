import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMellinWeights

namespace OAI

/-! The exact Dirichlet-series Mellin expression of the constructed cubic
cusp expansion, justified by absolute integration on the initial half-plane. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaDirichlet (a : Eisenstein → ℂ) (u : ℂ) : ℂ :=
  ∑' n : Eisenstein, if n = 0 then 0 else
    a n*(‖cubicThetaFrequency n‖:ℂ)^(-u)

lemma cubicThetaDirichlet_summable {a : Eisenstein → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, ‖a n‖ ≤ C)
    {u : ℂ} (hu : 2 < u.re) :
    Summable (fun n : Eisenstein => if n = 0 then (0:ℂ) else
      a n*(‖cubicThetaFrequency n‖:ℂ)^(-u)) := by
  apply summable_norm_iff.mp
  convert cubicTheta_mellin_weight_summable hC ha hu using 1
  funext n
  by_cases hn : n = 0
  · simp only [hn,ite_true,norm_zero]
  · simp only [hn,ite_false,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (cubicThetaFrequency_pos hn),Complex.neg_re]

/-- The Gamma product and the frequency Dirichlet series arise from the
actual Fourier expansion; only its modular inversion remains separate. -/
theorem cubicThetaNonconstant_mellin {a : Eisenstein → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, ‖a n‖ ≤ C)
    {u : ℂ} (hu : 2 < u.re) :
    mellin (fun v : ℝ => cubicThetaNonconstant a (0,v)) u =
      mellin cubicThetaWhittaker u*cubicThetaDirichlet a u := by
  let : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  let F (n : Eisenstein) (v : ℝ) : ℂ :=
    (v:ℂ)^(u-1)*cubicThetaSeriesTerm a 0 v n
  have hhalf : (1/6:ℝ) < ((u+1)/2).re := by
    simp only [Complex.div_ofNat_re,Complex.add_re,Complex.one_re]
    linarith
  have heu : 2*((u+1)/2)-1 = u := by ring
  have hFi (n : Eisenstein) : IntegrableOn (F n) (Ioi 0) := by
    by_cases hn : n = 0
    · simp [F,cubicThetaSeriesTerm,hn]
    · have h := cubicThetaWhittaker_scaled_mellinConvergent hhalf
        (cubicThetaFrequency_pos hn) (a n)
      rw [heu] at h
      simpa [F,MellinConvergent,cubicThetaSeriesTerm,hn,tracePair] using h
  have hmass (n : Eisenstein) : (∫ v in Ioi (0:ℝ), ‖F n v‖) =
      (if n = 0 then (0:ℝ) else ‖a n‖*‖cubicThetaFrequency n‖^(-u.re))*
        cubicWhittakerNormMass u.re := by
    by_cases hn : n = 0
    · simp [F,cubicThetaSeriesTerm,hn]
    · simpa [F,cubicThetaSeriesTerm,hn,tracePair,mul_assoc] using
        cubicWhittaker_norm_integral_scale u (a n) (cubicThetaFrequency_pos hn)
  have hsum : Summable (fun n : Eisenstein => ∫ v in Ioi (0:ℝ), ‖F n v‖) := by
    simp_rw [hmass]
    exact (cubicTheta_mellin_weight_summable hC ha hu).mul_right _
  have hinter := integral_tsum_of_summable_integral_norm hFi hsum
  have hsingle (n : Eisenstein) : (∫ v in Ioi (0:ℝ), F n v) =
      mellin cubicThetaWhittaker u*(if n = 0 then 0 else
        a n*(‖cubicThetaFrequency n‖:ℂ)^(-u)) := by
    by_cases hn : n = 0
    · simp [F,cubicThetaSeriesTerm,hn]
    · have he : (∫ v in Ioi (0:ℝ), F n v) =
          mellin (fun v : ℝ => a n • cubicThetaWhittaker (‖cubicThetaFrequency n‖*v)) u := by
        unfold mellin
        apply setIntegral_congr_fun measurableSet_Ioi
        intro v _
        simp [F,cubicThetaSeriesTerm,hn,tracePair]
      rw [he,mellin_const_smul,mellin_comp_mul_left _ _ (cubicThetaFrequency_pos hn)]
      simp only [hn,ite_false,smul_eq_mul]
      ring
  calc
    _ = ∫ v in Ioi (0:ℝ), ∑' n : Eisenstein, F n v := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v _
      dsimp [F,cubicThetaNonconstant]
      rw [tsum_mul_left]
    _ = ∑' n : Eisenstein, ∫ v in Ioi (0:ℝ), F n v := hinter.symm
    _ = _ := by simp_rw [hsingle]; rw [tsum_mul_left]; rfl

end CubicFirstMoment

end

end OAI
