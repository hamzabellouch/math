import OAI.Combinatorics.HoneycombChords.ConfluentInterpolation
import OAI.Combinatorics.HoneycombChords.FunctionalTransforms

namespace OAI

/-! Construction of the finite strip functional from physical spectral interpolation. -/

namespace CriticalHoneycomb.FiniteFunctional
open Real Filter Topology MeasureTheory Analytic

theorem source_physical_finite_functional : PhysicalFiniteFunctional := by
  intro N hN
  obtain ⟨B,ρ,P,hB,hMass,hdeg,h₀,h₃,h₅,hzero,hangle⟩ :=
    source_physical_spectral_interpolation N hN
  obtain ⟨F,f,hF,hf,hrep,hT⟩ := density_transform_surjective N P hdeg
  have hu₀ : |(0:ℝ)|+2*angle < Real.pi/2 := by
    rw [abs_zero]; unfold angle; linarith [Real.pi_pos]
  have huL : |angle|+2*angle < Real.pi/2 := by
    rw [angle_abs]; unfold angle; linarith [Real.pi_pos]
  have hz : ∀ j < 2*N, iteratedDeriv j (integralFusion angle ρ f) 0 = 0 := by
    intro j hj
    rw [← (interpolant_fusion_eq_integral_eventually hf hT hu₀).iteratedDeriv_eq j]
    exact hzero j hj
  have hL : ∀ j < N, iteratedDeriv j (integralFusion angle ρ f) angle = 0 := by
    intro j hj
    rw [← (interpolant_fusion_eq_integral_eventually hf hT huL).iteratedDeriv_eq j]
    exact hangle j hj
  have hm := M_integrable_and_annihilated hrep hf ρ hz hL
  have hI₃ : integralInterpolant ρ f (3*angle/2) = 0 := by
    rw [← interpolant_eq_integralInterpolant (ρ := ρ) hT (by
      rw [abs_of_pos (by linarith [angle_pos] : 0 < 3*angle/2)]; unfold angle; linarith [Real.pi_pos])]
    exact h₃
  have hI₅ : integralInterpolant ρ f (5*angle/2) = 0 := by
    rw [← interpolant_eq_integralInterpolant (ρ := ρ) hT (by
      rw [abs_of_pos (by linarith [angle_pos] : 0 < 5*angle/2)]; unfold angle; linarith [Real.pi_pos])]
    exact h₅
  obtain ⟨hc₁,hc₃⟩ := finite_endpoint_constraints hrep hf ρ hI₃ hI₅
  refine ⟨B,ρ,F,hB,hMass,hF,(fun H hH => (hm H hH).2),hc₁,hc₃,?_⟩
  rw [value_inv_D_eq_interpolant hrep,← interpolant_eq_integralInterpolant (ρ := ρ) hT (by
    rw [abs_zero,zero_add]; exact angle_lt_pi_half)]
  exact h₀.symm

end CriticalHoneycomb.FiniteFunctional


end OAI
