import Mathlib
import OAI.Geometry.PrescribedPotential.CommutatorSupport
import OAI.Geometry.PrescribedPotential.NonlinearCoreCommutator
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.RealSobolev

namespace OAI

/-! Global Nonlinear Commutator. -/

section

 
noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff Classical Matrix.Norms.Elementwise
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

lemma nonlinear_commutator_core_strong (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (v : EC d) (φ : SmoothRealFunction A) (x : X) :
    D.localizers.strong (k : ℝ)
      (fderiv ℝ (D.completedVolume k hk) (D.localizers.embed ((k : ℝ)+2) (Smooth.ofReal φ))
        (D.localizers.embed ((k : ℝ)+2) (D.localizedDerivative p v (Smooth.ofReal φ)))) x =
      D.localizedDerivative p v (Smooth.ofReal (g.potentialDensity φ)) x +
      D.localizers.strong (k : ℝ)
        (D.nonlinearRemainder k hk p v (D.localizers.embed ((k : ℝ)+2) (Smooth.ofReal φ))) x := by
  by_cases hx : x ∈ D.derivativeSupport p
  · obtain ⟨hs,hκ⟩ := D.derivativeSupport_source hx
    exact D.nonlinear_commutator_on_support k hk p v φ hs hκ
  · obtain ⟨q,hq⟩ := A.covers x
    let ψ := (D.realLocalizedDerivative p v (RealSmooth.ofReal φ)).source
    have hψ : Smooth.ofReal ψ = D.localizedDerivative p v (Smooth.ofReal φ) :=
      RealSmooth.ofReal_source _
    rw [← hψ,D.completedVolumeDerivative_source k hk φ ψ q hq,
      D.localizedDerivative_source_hessian_zero hx v φ q hq,
      map_zero,mul_zero,D.localizedDerivative_zero hx,D.nonlinearRemainder_zero hx,add_zero]

lemma nonlinear_commutator_core (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (v : EC d) (φ : SmoothRealFunction A) :
    fderiv ℝ (D.completedVolume k hk) (D.localizers.embed ((k : ℝ)+2) (Smooth.ofReal φ))
        (D.localizers.embed ((k : ℝ)+2) (D.localizedDerivative p v (Smooth.ofReal φ))) =
      D.localizers.embed (k : ℝ) (D.localizedDerivative p v (Smooth.ofReal (g.potentialDensity φ))) +
      D.nonlinearRemainder k hk p v (D.localizers.embed ((k : ℝ)+2) (Smooth.ofReal φ)) := by
  have hs : (Module.finrank ℝ (EC d) : ℝ) < 2*(k : ℝ) := by
    have hh : (Module.finrank ℝ (EC d) : ℝ) < (k : ℝ) := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α := ℝ) k]
  apply D.localizers.strong_injective (k : ℝ) hs
  ext x
  rw [map_add,D.localizers.strong_embed _ hs]
  exact D.nonlinear_commutator_core_strong k hk p v φ x

end GluingData
end GlobalElliptic

end
end

end OAI
