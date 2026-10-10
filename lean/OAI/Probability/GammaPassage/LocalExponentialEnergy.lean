import OAI.Probability.GammaPassage.LocalResamplingExponential
import OAI.Probability.GammaPassage.LocalRegularity
import OAI.Probability.GammaPassage.ResamplingEnergyIdentity
import OAI.Probability.GammaPassage.FiniteTilt

namespace OAI

namespace GammaFPP.FiniteLocal
open MeasureTheory ProbabilityTheory PlanarFPP Real Finset
open scoped ENNReal

lemma finite_coordinates_nonnegative {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) :
    ∀ᵐ v ∂finiteGammaMeasure (ι := ↥(localEdges p q R)) shape rate, ∀ e, 0 ≤ v e := by
  let : IsProbabilityMeasure (gammaMeasure shape rate) := isProbabilityMeasure_gammaMeasure hs hr
  rw [ae_all_iff]
  intro e
  exact ((measurePreserving_eval
    (fun _ : ↥(localEdges p q R) => gammaMeasure shape rate) e).quasiMeasurePreserving.ae
      (gamma_ae_pos shape rate)).mono (fun _ hu => hu.le)

/-- The forward resampling energy is bounded after weighting by the exponential
of the passage time in the initial environment. -/
theorem finite_exponential_forward_energy {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R)
    (a : ℝ) (ha : |a| ≤ rate/4) :
    (∑ e : ↥(localEdges p q R), ∫⁻ z : Coordinates p q R × Coordinates p q R,
      ENNReal.ofReal (exp (a*finitePassageTime p q R z.1) *
        (exp (a*max (finitePassageTime p q R (Function.update z.1 e (z.2 e))-
          finitePassageTime p q R z.1) 0/2)-1)^2)
      ∂(finiteGammaMeasure shape rate).prod (finiteGammaMeasure shape rate)) ≤
      (ENNReal.ofReal ((8*(2 : ℝ)^shape/rate^2)*a^2)*R) *
        ∫⁻ v, ENNReal.ofReal (exp (a*finitePassageTime p q R v))
          ∂finiteGammaMeasure shape rate := by
  classical
  let : IsProbabilityMeasure (gammaMeasure shape rate) := isProbabilityMeasure_gammaMeasure hs hr
  let P := finiteGammaMeasure (ι := ↥(localEdges p q R)) shape rate
  let : IsProbabilityMeasure P := by
    dsimp only [P, finiteGammaMeasure]
    infer_instance
  let F := finitePassageTime p q R
  have hF : Measurable F := measurable_finitePassageTime p q R hR
  let K := fun v e u => ENNReal.ofReal ((exp (a*max (F (Function.update v e u)-F v) 0/2)-1)^2)
  have he : ∀ e : ↥(localEdges p q R),
      (∫⁻ z : Coordinates p q R × Coordinates p q R,
        ENNReal.ofReal (exp (a*F z.1))*K z.1 e (z.2 e) ∂P.prod P) =
      ∫⁻ v, ENNReal.ofReal (exp (a*F v))*(∫⁻ u, K v e u ∂gammaMeasure shape rate) ∂P := by
    intro e
    rw [lintegral_prod _ (by dsimp [K]; fun_prop)]
    apply lintegral_congr
    intro v
    dsimp only
    rw [lintegral_const_mul _ (show Measurable (fun w : Coordinates p q R => K v e (w e))
      from by dsimp [K]; fun_prop)]
    congr 1
    have hm := lintegral_map (μ := P) (show Measurable (K v e) from by dsimp [K]; fun_prop)
      (measurable_pi_apply e)
    dsimp only [P, finiteGammaMeasure] at hm
    rw [(measurePreserving_eval
      (fun _ : ↥(localEdges p q R) => gammaMeasure shape rate) e).map_eq] at hm
    exact hm.symm
  simp_rw [ENNReal.ofReal_mul (exp_pos _).le]
  change (∑ e, ∫⁻ z : Coordinates p q R × Coordinates p q R,
    ENNReal.ofReal (exp (a*F z.1))*K z.1 e (z.2 e) ∂P.prod P) ≤ _
  simp_rw [he]
  rw [← lintegral_finsetSum _ (fun e _ => by dsimp [K]; fun_prop)]
  simp_rw [← mul_sum]
  calc
    _ ≤ ∫⁻ v, ENNReal.ofReal (exp (a*F v))*
        (ENNReal.ofReal ((8*(2 : ℝ)^shape/rate^2)*a^2)*R) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [finite_coordinates_nonnegative hs hr p q R] with v hv
      gcongr
      exact finite_upward_exponential_sum hs hr p q R hR v hv a ha
    _ = _ := by
      simp_rw [mul_comm _ (ENNReal.ofReal ((8*(2 : ℝ)^shape/rate^2)*a^2)*R)]
      exact lintegral_const_mul _ (by fun_prop)

/-- Exchanging the initial and resampled coordinates bounds the total exponential
resampling energy by twice the forward energy, for either sign of `a`. -/
theorem finite_exponential_resampling_energy {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R)
    (a : ℝ) (ha : |a| ≤ rate/4) :
    (∑ e : ↥(localEdges p q R), ∫⁻ z : Coordinates p q R × Coordinates p q R,
      ENNReal.ofReal ((exp (a*finitePassageTime p q R (Function.update z.1 e (z.2 e))/2) -
        exp (a*finitePassageTime p q R z.1/2))^2)
      ∂(finiteGammaMeasure shape rate).prod (finiteGammaMeasure shape rate)) ≤
      (ENNReal.ofReal ((16*(2 : ℝ)^shape/rate^2)*a^2)*R) *
        ∫⁻ v, ENNReal.ofReal (exp (a*finitePassageTime p q R v))
          ∂finiteGammaMeasure shape rate := by
  classical
  let : IsProbabilityMeasure (gammaMeasure shape rate) := isProbabilityMeasure_gammaMeasure hs hr
  simp only [finiteGammaMeasure]
  simp_rw [EnergyIdentity.exponential_resampling_energy_split (gammaMeasure shape rate)
    (finitePassageTime p q R) (measurable_finitePassageTime p q R hR), ← mul_sum]
  have hb := finite_exponential_forward_energy hs hr p q R hR a ha
  simp only [finiteGammaMeasure] at hb
  calc
    _ ≤ 2*((ENNReal.ofReal ((8*(2 : ℝ)^shape/rate^2)*a^2)*R)*
        ∫⁻ v, ENNReal.ofReal (exp (a*finitePassageTime p q R v))
          ∂Measure.pi (fun _ : ↥(localEdges p q R) => gammaMeasure shape rate)) := by
      exact _root_.mul_le_mul_right hb 2
    _ = _ := by
      have he : (2 : ℝ≥0∞)*ENNReal.ofReal ((8*(2 : ℝ)^shape/rate^2)*a^2) =
          ENNReal.ofReal ((16*(2 : ℝ)^shape/rate^2)*a^2) := by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      simp only [← mul_assoc, he]

end GammaFPP.FiniteLocal

end OAI
