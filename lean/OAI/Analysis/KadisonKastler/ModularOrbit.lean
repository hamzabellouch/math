import OAI.Analysis.KadisonKastler.ModularRootCommutation
import OAI.Analysis.KadisonKastler.RegularCoreIntersection
import OAI.Analysis.KadisonKastler.StripAverageMembership

namespace OAI

/-! # Strongly continuous bounded modular orbits and their scalar averages -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

def modularOrbit (Y : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd (-t)) : H →L[ℂ] H) * Y *
    (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)

theorem modularOrbit_continuous (Y : H →L[ℂ] H) (x : H) :
    Continuous (fun t => modularOrbit J Ω hsep hcyc Y t x) := by
  exact continuous_unitary_field_apply
    (fun t : ℝ => modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd (-t)))
    (fun v => (modularStrongGroup_continuous J Ω hsep hcyc v).comp continuous_neg)
    (fun t => Y ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (Y.continuous.comp (modularStrongGroup_continuous J Ω hsep hcyc x))

theorem modularOrbit_norm_le (Y : H →L[ℂ] H) (t : ℝ) :
    ‖modularOrbit J Ω hsep hcyc Y t‖ ≤ ‖Y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Y)
  intro x
  change ‖(modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd (-t)) : H →L[ℂ] H)
    (Y ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) x))‖ ≤ _
  rw [Unitary.norm_map]
  simpa only [Unitary.norm_map] using Y.le_opNorm
    ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) x)

def modularOrbitAverage (Y : H →L[ℂ] H) (φ : ℝ) (hφ : |φ| < Real.pi) : H →L[ℂ] H :=
  weightedOperatorIntegral volume (stripAverageKernel Real.pi (φ : ℂ))
    (stripAverageKernel_integrable (by simpa using hφ)) (modularOrbit J Ω hsep hcyc Y)
    (fun x => (modularOrbit_continuous J Ω hsep hcyc Y x).aestronglyMeasurable) ‖Y‖
    (Filter.Eventually.of_forall (modularOrbit_norm_le J Ω hsep hcyc Y))

end

end KadisonKastler

end OAI
