import OAI.MeasureTheory.Falconer.Angular.FullCircleStationaryPower

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology ComplexConjugate

 theorem stationaryJet_congr {f g : ℝ → ℂ} (h : f =ᶠ[𝓝 0] g) (n : ℕ) :
    stationaryJet n f = stationaryJet n g := by
  unfold stationaryJet
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  rw [Filter.EventuallyEq.iteratedDeriv_eq c.length h]

 theorem stationaryJet_zero_germ {f : ℝ → ℂ} (h : f =ᶠ[𝓝 0] (fun _ => 0)) (n : ℕ) :
    stationaryJet n f = 0 := by
  rw [stationaryJet_congr h]
  simp [stationaryJet]

 theorem directStationaryOperator_congr {f g : ℝ → ℂ} {θ : ℝ}
    (h : f =ᶠ[𝓝 θ] g) (j : ℕ) : directStationaryOperator j f θ = directStationaryOperator j g θ := by
  have ht : Filter.Tendsto (fun u : ℝ => u+θ) (𝓝 0) (𝓝 θ) := by
    simpa only [ContinuousAt, zero_add] using (show Continuous (fun u : ℝ => u+θ) from
      continuous_id.add continuous_const).continuousAt (x := (0:ℝ))
  have he : (fun u => f (u+θ)) =ᶠ[𝓝 0] (fun u => g (u+θ)) := h.comp_tendsto ht
  unfold directStationaryOperator
  rw [stationaryJet_congr he]

 theorem stationaryDerivativeExpansion_zero_germ {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (h : f =ᶠ[𝓝 0] (fun _ => 0)) (n : ℕ) (Λ : ℝ) : stationaryDerivativeExpansion f n Λ = 0 := by
  unfold stationaryDerivativeExpansion
  apply Finset.sum_eq_zero
  intro k _
  rw [stationaryAmplitude_jet (2*k) hf,stationaryJet_zero_germ h]
  simp

 theorem fullCircleStationaryExpansion_one_sided {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (h : f =ᶠ[𝓝 Real.pi] (fun _ => 0)) (n : ℕ) (Λ : ℝ) :
    fullCircleStationaryExpansion Λ f n =
      Complex.exp (Complex.I*(Λ:ℂ))*(fresnelCoefficient (Λ/2)*stationaryDerivativeExpansion f n Λ) := by
  have ht : Filter.Tendsto (fun u : ℝ => u+Real.pi) (𝓝 0) (𝓝 Real.pi) := by
    simpa only [ContinuousAt, zero_add] using (show Continuous (fun u : ℝ => u+Real.pi) from
      continuous_id.add continuous_const).continuousAt (x := (0:ℝ))
  have he : (fun u => conj (f (u+Real.pi))) =ᶠ[𝓝 0] (fun _ => 0) := by
    filter_upwards [h.comp_tendsto ht] with u hu
    simp only [Function.comp_apply] at hu
    simp [hu]
  have hfs : ContDiff ℝ ∞ (fun u => conj (f (u+Real.pi))) :=
    Complex.conjCLE.contDiff.comp (hf.comp (contDiff_id.add contDiff_const))
  simp only [fullCircleStationaryExpansion,stationaryDerivativeExpansion_zero_germ hfs he,
    mul_zero,map_zero,add_zero]

end PlanarFalconer

end OAI
