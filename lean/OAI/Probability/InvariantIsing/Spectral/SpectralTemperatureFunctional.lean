import OAI.Probability.InvariantIsing.Spectral.SpectralEnergyPrimitive

namespace OAI

/-! The finite-spectrum temperature functional is a differentiable primitive
of the interaction energy, including at temperature zero. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem continuous_finiteInteractionEnergy_temperature (ρ eig : ι → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) :
    Continuous (fun t => finiteInteractionEnergy ρ eig hρ hρsum t p) := by
  let K := ∑ a, |eig a|
  have heig (a : ι) : |eig a| ≤ K :=
    Finset.single_le_sum (fun a _ => abs_nonneg (eig a)) (Finset.mem_univ a)
  have hbound (t r : ℝ) : |finiteSpectralSlope ρ eig hρ hρsum (t * deficit p r)| ≤ K :=
    abs_le.mpr (finiteSpectralSlope_bounds ρ eig hρ hρsum
      (fun a => (abs_le.mp (heig a)).1) (fun a => (abs_le.mp (heig a)).2) _)
  have hc : Continuous (fun t => ∫ r, finiteSpectralSlope ρ eig hρ hρsum (t * deficit p r)
      ∂pathMeasure) := by
    apply continuous_of_dominated (bound := fun _ => K)
    · intro t
      exact ((continuous_finiteSpectralSlope ρ eig hρ hρsum).comp
        (continuous_const.mul (continuous_deficit p))).aestronglyMeasurable
    · intro t
      exact ae_of_all _ fun r => by simpa only [Real.norm_eq_abs] using hbound t r
    · exact integrable_const K
    · exact ae_of_all _ fun r => (continuous_finiteSpectralSlope ρ eig hρ hρsum).comp
        (continuous_id.mul continuous_const)
  exact continuous_const.mul hc

/-- An everywhere-defined primitive; at nonnegative temperatures it is exactly
the manuscript's finite-spectrum interaction functional. -/
def finiteTemperatureFunctional (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (t : ℝ) : ℝ :=
  ∫ u in 0..t, finiteInteractionEnergy ρ eig hρ hρsum u p

theorem finiteTemperatureFunctional_eq (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) {t : ℝ} (ht : 0 ≤ t) :
    finiteTemperatureFunctional ρ eig hρ hρsum p t =
      spectralFunctional (fun x => t * finiteR ρ eig hρ hρsum (t * x)) p :=
  integral_finiteInteractionEnergy ρ eig hρ hρsum ht p

@[simp] theorem finiteTemperatureFunctional_zero (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) :
    finiteTemperatureFunctional ρ eig hρ hρsum p 0 = 0 := by
  simp only [finiteTemperatureFunctional, intervalIntegral.integral_same]

theorem continuous_finiteTemperatureFunctional (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) :
    Continuous (finiteTemperatureFunctional ρ eig hρ hρsum p) :=
  intervalIntegral.continuous_primitive
    (continuous_finiteInteractionEnergy_temperature ρ eig hρ hρsum p).intervalIntegrable 0

theorem hasDerivAt_finiteTemperatureFunctional (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (t : ℝ) :
    HasDerivAt (finiteTemperatureFunctional ρ eig hρ hρsum p)
      (finiteInteractionEnergy ρ eig hρ hρsum t p) t := by
  have hc := continuous_finiteInteractionEnergy_temperature ρ eig hρ hρsum p
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt


lemma finiteTemperatureFunctional_modulus (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (K : ℝ) (hK : ∀ a, |eig a| ≤ K)
    (s t : ℝ) :
    |finiteTemperatureFunctional ρ eig hρ hρsum p s -
      finiteTemperatureFunctional ρ eig hρ hρsum p t| ≤ (K / 2) * |s - t| := by
  have hd (a : ℝ) (_ : a ∈ (univ : Set ℝ)) :=
    (hasDerivAt_finiteTemperatureFunctional ρ eig hρ hρsum p a).hasDerivWithinAt (s := univ)
  have hb (a : ℝ) (_ : a ∈ (univ : Set ℝ)) :
      ‖finiteInteractionEnergy ρ eig hρ hρsum a p‖ ≤ K / 2 := by
    simpa only [Real.norm_eq_abs] using abs_finiteInteractionEnergy_le ρ eig hρ hρsum hK a p
  simpa only [Real.norm_eq_abs] using
    (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      hd hb (mem_univ t) (mem_univ s)

end InvariantIsing

end

end OAI
