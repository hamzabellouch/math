import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularPowers

namespace OAI

/-! The exact shifted Mellin identity for every fixed angular mode.
Absolute integration is proved using the original bounded coefficient mass. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- The frequency derivative and the shifted Mellin exponent cancel before
summation. This is the analytic origin of the shifted Gamma factors. -/
theorem cubicThetaAngular_mellin {a : Eisenstein → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, ‖a n‖ ≤ C)
    (ℓ : ℤ) {s : ℂ} (hs : 3/2 < s.re) :
    mellin (fun v : ℝ => cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ) (0,v))
      (2*s+(ℓ.natAbs:ℂ)-1) =
      mellin cubicThetaWhittaker (2*s+(ℓ.natAbs:ℂ)-1)*
        cubicThetaDirichlet (fun n => theta ℓ n*a n) (2*s-1) := by
  let : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  let u : ℂ := 2*s+(ℓ.natAbs:ℂ)-1
  let F (n : Eisenstein) (v : ℝ) : ℂ :=
    (v:ℂ)^(u-1)*cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) 0 v n
  have hhalf : (1/6:ℝ) < (s+(ℓ.natAbs:ℂ)/2).re := by
    simp only [Complex.add_re,Complex.div_ofNat_re,Complex.natCast_re]
    have hk : (0:ℝ) ≤ ℓ.natAbs := Nat.cast_nonneg _
    linarith
  have heu : 2*(s+(ℓ.natAbs:ℂ)/2)-1 = u := by dsimp [u]; ring
  have hu0 : 2 < (2*s-1).re := by norm_num [Complex.mul_re,Complex.sub_re]; linarith
  have hFi (n : Eisenstein) : IntegrableOn (F n) (Ioi 0) := by
    by_cases hn : n = 0
    · simp [F,cubicThetaSeriesTerm,hn]
    · have h := cubicThetaWhittaker_scaled_mellinConvergent hhalf
        (cubicThetaFrequency_pos hn) (cubicThetaAngularCoefficient a ℓ n)
      rw [heu] at h
      simpa [F,MellinConvergent,cubicThetaSeriesTerm,hn,tracePair] using h
  have hmass (n : Eisenstein) : (∫ v in Ioi (0:ℝ), ‖F n v‖) =
      (if n = 0 then (0:ℝ) else ‖a n‖*‖cubicThetaFrequency n‖^(-(2*s-1).re))*
        cubicWhittakerNormMass u.re := by
    by_cases hn : n = 0
    · simp [F,cubicThetaSeriesTerm,hn]
    · have h := cubicWhittaker_norm_integral_scale u (cubicThetaAngularCoefficient a ℓ n)
        (cubicThetaFrequency_pos hn)
      have h' : (∫ v in Ioi (0:ℝ), ‖F n v‖) =
          ‖cubicThetaAngularCoefficient a ℓ n‖*‖cubicThetaFrequency n‖^(-u.re)*
            cubicWhittakerNormMass u.re := by
        simpa [F,cubicThetaSeriesTerm,hn,tracePair,mul_assoc] using h
      rw [h',ite_eq_right hn]
      dsimp only [u]
      rw [cubicThetaAngular_weight ℓ hn]
  have hsum : Summable (fun n : Eisenstein => ∫ v in Ioi (0:ℝ), ‖F n v‖) := by
    simp_rw [hmass]
    exact (cubicTheta_mellin_weight_summable hC ha hu0).mul_right _
  have hinter := integral_tsum_of_summable_integral_norm hFi hsum
  have hsingle (n : Eisenstein) : (∫ v in Ioi (0:ℝ), F n v) =
      mellin cubicThetaWhittaker u*(if n = 0 then 0 else
        theta ℓ n*a n*(‖cubicThetaFrequency n‖:ℂ)^(-(2*s-1))) := by
    by_cases hn : n = 0
    · simp [F,cubicThetaSeriesTerm,hn]
    · have he : (∫ v in Ioi (0:ℝ), F n v) =
          mellin (fun v : ℝ => cubicThetaAngularCoefficient a ℓ n •
            cubicThetaWhittaker (‖cubicThetaFrequency n‖*v)) u := by
        unfold mellin
        apply setIntegral_congr_fun measurableSet_Ioi
        intro v _
        simp [F,cubicThetaSeriesTerm,hn,tracePair]
      rw [he,mellin_const_smul,mellin_comp_mul_left _ _ (cubicThetaFrequency_pos hn)]
      simp only [hn,ite_false,smul_eq_mul]
      calc
        _ = mellin cubicThetaWhittaker u*(cubicThetaAngularCoefficient a ℓ n*
            (‖cubicThetaFrequency n‖:ℂ)^(-u)) := by ring
        _ = _ := by dsimp only [u]; rw [cubicThetaAngular_dirichlet_term ℓ hn]
  calc
    _ = ∫ v in Ioi (0:ℝ), ∑' n : Eisenstein, F n v := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v _
      dsimp [F,cubicThetaNonconstant]
      rw [tsum_mul_left]
    _ = ∑' n : Eisenstein, ∫ v in Ioi (0:ℝ), F n v := hinter.symm
    _ = _ := by simp_rw [hsingle]; rw [tsum_mul_left]; rfl

/-- The literal shifted Gamma product for fixed signed angular frequency. -/
theorem cubicThetaAngular_completed {a : Eisenstein → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, ‖a n‖ ≤ C)
    (ℓ : ℤ) {s : ℂ} (hs : 3/2 < s.re) :
    mellin (fun v : ℝ => cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ) (0,v))
      (2*s+(ℓ.natAbs:ℂ)-1) =
      (1/4:ℂ)*((2*Real.pi:ℝ):ℂ)^(-2*(s+(ℓ.natAbs:ℂ)/2))*
        Complex.Gamma (s+(ℓ.natAbs:ℂ)/2+1/6)*Complex.Gamma (s+(ℓ.natAbs:ℂ)/2-1/6)*
        cubicThetaDirichlet (fun n => theta ℓ n*a n) (2*s-1) := by
  rw [cubicThetaAngular_mellin hC ha ℓ hs]
  have hhalf : (1/6:ℝ) < (s+(ℓ.natAbs:ℂ)/2).re := by
    simp only [Complex.add_re,Complex.div_ofNat_re,Complex.natCast_re]
    have hk : (0:ℝ) ≤ ℓ.natAbs := Nat.cast_nonneg _
    linarith
  have he : 2*s+(ℓ.natAbs:ℂ)-1 = 2*(s+(ℓ.natAbs:ℂ)/2)-1 := by ring
  rw [he,cubicThetaWhittaker_mellin hhalf]

end CubicFirstMoment

end

end OAI
