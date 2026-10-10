import OAI.Geometry.RCD.Sobolev.LocalWeakSourceUniqueness
import OAI.Geometry.RCD.Heat.LocalLogarithmicLaplacian
import OAI.Geometry.RCD.Sobolev.WeakLaplacianDomain

namespace OAI

/-! # The source of any local scaled logarithm

The local L2 source is independent of the chosen extension. In particular
a lower bound for that source applies to the original heat representative.
-/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] (μ : Measure X)
  [IsFiniteMeasureOnCompacts μ] (Q : QuadraticCheegerEnergy μ)

theorem local_scaled_log_source {Ω S : Set X} (hΩ : IsCompact Ω)
    (hS : MeasurableSet S) (hSΩ : S ⊆ Ω)
    (u w : SobolevSpace μ Q) (d q : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ Q u d) (hq : IsWeakLaplacian μ Q w q)
    (L : ℝ≥0) (hL : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ Q u x ≤ L)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hu : ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.toLp μ Q u x ∈ Icc a b)
    (κ : ℝ) (hw : SobolevSpace.toLp μ Q w =ᵐ[μ.restrict Ω]
      fun x => κ*Real.log (SobolevSpace.toLp μ Q u x))
    (χ : X →ᵇ ℝ) {C : ℝ≥0} (hχ : LipschitzWith C χ)
    (hχc : HasCompactSupport (χ : X → ℝ)) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : 0 ≤ χ) (hχ1 : ∀ x ∈ S, χ x = 1) :
    q =ᵐ[μ.restrict S] fun x => κ*(d x/SobolevSpace.toLp μ Q u x-
      localGamma μ Q u u x/(SobolevSpace.toLp μ Q u x)^2) := by
  obtain ⟨v,e,he,hv,heq,_⟩ := exists_local_logarithmic_laplacian μ Q u d hd L hL ha hab hu
  have hrep : SobolevSpace.toLp μ Q (κ • v) =ᵐ[μ.restrict Ω]
      SobolevSpace.toLp μ Q w := by
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul κ (SobolevSpace.toLp μ Q v)),hv,hw]
      with x hx hy hz
    change SobolevSpace.toLp μ Q (κ • v) x = κ*SobolevSpace.toLp μ Q v x at hx
    rw [hx,hy,hz]
  have heq' := (he.smul μ Q κ).local_source_eq μ Q hΩ hS hSΩ hq hrep
    χ hχ hχc hχΩ hχ0 hχ1
  filter_upwards [heq',ae_restrict_of_ae (Lp.coeFn_smul κ e),
    ae_restrict_of_ae_restrict_of_subset hSΩ heq] with x hx hy hz
  change (κ • e) x = κ*e x at hy
  rw [← hx,hy,hz]

end RegularPointCoordinates

end

end OAI
