import OAI.Analysis.HenonEmden.IntegratedRecovery

namespace OAI

universe uE uΩ

section AngularIntegration

open MeasureTheory Set Metric
noncomputable section
namespace HenonLaneEmden.Angular
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
open LineComponents

def rayConstant (n : ℕ) : ℝ := 2^(n+1)*(n:ℝ)

lemma long_component_measure_le {f : E → ℝ} {x : E} (hx : ‖x‖ ≤ 2)
    {t l M : ℝ} (ht : 0 < t) (hl : 0 < l) (hl1 : l ≤ 1) (hM : 0 ≤ M)
    (hU : IsOpen {z : sphere (0:E) 1 × ℝ | t < f (x+z.2 • z.1.1)})
    (hm : (∫⁻ z in ball (0:E) 4, ENNReal.ofReal (f z) ∂μ) ≤ ENNReal.ofReal M) :
    μ.toSphere.real {e | ENNReal.ofReal l < componentLength
      {z : sphere (0:E) 1 × ℝ | t < f (x+z.2 • z.1.1)} e} ≤
      rayConstant (Module.finrank ℝ E)*M/(t*l^(Module.finrank ℝ E)) := by
  let n := Module.finrank ℝ E
  have hn : 0 < (n:ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  have hh := (long_component_local_mass_le μ hx hl hl1 hU).trans
    (mul_le_mul_right hm 2)
  have hh' := ENNReal.toReal_mono (by finiteness) hh
  have hf : 0 ≤ (l/2)^(Module.finrank ℝ E)/(Module.finrank ℝ E:ℝ) := by positivity
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal ht.le,ENNReal.toReal_ofReal hf,
    ENNReal.toReal_ofNat,ENNReal.toReal_ofReal hM] at hh'
  rw [le_div_iff₀ (mul_pos ht (pow_pos hl _))]
  unfold rayConstant
  have he : t*((l/2)^n/(n:ℝ)) = (t*l^n)/(2^n*(n:ℝ)) := by
    rw [div_pow]; field_simp
  rw [he] at hh'
  have hd : 0 < (2^n:ℝ)*(n:ℝ) := mul_pos (by positivity) hn
  have hh'' := (div_le_iff₀ hd).mp (show μ.toSphere.real _*(t*l^n)/(2^n*(n:ℝ)) ≤ 2*M by
    convert hh' using 1; unfold Measure.real at *; ring)
  convert hh'' using 1; dsimp [n]; rw [pow_succ]; ring

end HenonLaneEmden.Angular

namespace HenonLaneEmden
lemma integral_le_constant_add_event {Ω : Type uΩ} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsFiniteMeasure ν] {S : Set Ω} (hS : MeasurableSet S) {F : Ω → ℝ}
    (hF : Measurable F) {a H : ℝ} (ha : 0 ≤ a) (_hH : 0 ≤ H)
    (hFn : ∀ z, 0 ≤ F z) (hFH : ∀ z, F z ≤ H) (hout : ∀ z ∉ S, F z ≤ a) :
    (∫ z, F z ∂ν) ≤ a*ν.real univ+H*ν.real S := by
  have hFi : Integrable F ν := (integrable_const H).mono' hF.aestronglyMeasurable
    (ae_of_all _ (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (hFn z)]; exact hFH z))
  have hIi : Integrable (S.indicator (fun _ => H)) ν := (integrable_const H).indicator hS
  have hh := integral_mono hFi ((integrable_const a).add hIi) (fun z => ?_)
  · simpa [integral_add (integrable_const a) hIi,integral_indicator hS,integral_const,
      smul_eq_mul,mul_comm] using hh
  · change F z ≤ a + S.indicator (fun _ => H) z
    by_cases hz : z ∈ S
    · rw [indicator_of_mem hz]; linarith [hFH z]
    · rw [indicator_of_notMem hz]; simpa only [add_zero] using hout z hz

end HenonLaneEmden
end
end AngularIntegration

end OAI
