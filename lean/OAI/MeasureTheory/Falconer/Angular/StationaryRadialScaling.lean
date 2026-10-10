import OAI.MeasureTheory.Falconer.Angular.StationaryRadialCoefficient

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

 theorem stationary_radial_power (j k : ℕ) {s : ℝ} (hs : 0 < s) :
    (s^(-1/2:ℝ)*s^(-1/2:ℝ)) * ((s⁻¹)^j*(s⁻¹)^k) = s^(-((j:ℝ)+(k:ℝ)+1)) := by
  rw [← Real.rpow_add hs]
  have hj : (s⁻¹)^j = s^(-(j:ℝ)) := by rw [Real.rpow_neg hs.le,Real.rpow_natCast,inv_pow]
  have hk : (s⁻¹)^k = s^(-(k:ℝ)) := by rw [Real.rpow_neg hs.le,Real.rpow_natCast,inv_pow]
  rw [hj,hk,← Real.rpow_add hs,← Real.rpow_add hs]
  congr 1
  ring

 theorem stationaryRadialCoefficient_eq (Ψ : ℝ → ℝ) (j k : ℕ) (f g : ℝ → ℂ)
    (θ φ : ℝ) {A B s : ℝ} (hA : 0 < A) (hB : 0 < B) (hs : 0 < s) :
    stationaryRadialCoefficient Ψ j k f g θ φ A B s =
      (Ψ s : ℂ) *
        (((A*s)^(-1/2:ℝ):ℝ):ℂ) * normalizedStationaryJet j f θ (A*s) *
        (((B*s)^(-1/2:ℝ):ℝ):ℂ) * normalizedStationaryJet k g φ (B*s) := by
  have hp := congrArg (fun t : ℝ => (t:ℂ)) (stationary_radial_power j k hs)
  simp only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_inv] at hp
  simp only [stationaryRadialCoefficient,normalizedStationaryJet,radialStationaryProfile,
    Real.mul_rpow hA.le hs.le,Real.mul_rpow hB.le hs.le,Complex.ofReal_mul,
    mul_inv_rev,Complex.ofReal_inv,mul_pow]
  rw [← hp]
  ring

end PlanarFalconer

end OAI
