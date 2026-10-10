import OAI.Analysis.CircleDomains.Reflection.ReflectionPrincipalSolution
import OAI.Analysis.CircleDomains.Selection.FiniteRoundComparison

namespace OAI

/-! Actual data for finite analytic uniformization by invariant Beltrami
coefficients. Conformality of the straightened comparison and roundness of
its boundary images are not fields and remain to be proved. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer CannonBeltrami
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

structure AnalyticReflectionData {I : Type*} [Finite I] (C : FiniteJordanConfiguration I) where
  comparison : ℂ ≃ₜ ℂ
  center : I → ℂ
  radius : I → ℝ
  radius_pos : ∀i,0<radius i
  comparison_smooth : ContDiff ℝ ∞ (comparison : ℂ → ℂ)
  comparison_inverse_smooth : ContDiff ℝ ∞ (comparison.symm : ℂ → ℂ)
  cap_image : ∀i,comparison '' closure (jordanInterior (C.hole i))=closedBall (center i) (radius i)
  baseCoefficient : ℂ → ℂ
  bound : ℝ
  bound_nonneg : 0≤bound
  bound_lt_one : bound<1
  base_bound : ∀z,‖baseCoefficient z‖≤bound
  base_equation : ∀z,partialBar comparison.symm z=baseCoefficient z*partialZ comparison.symm z
  extension : Sphere → ℂ
  extension_measurable : Measurable extension
  extension_bound : ∀p,‖extension p‖≤bound
  extension_base : EqOn extension (sphereCoefficient 0 baseCoefficient) (comparison.onePointCongr '' C.region)
  extension_invariant : ∀i p,extension p=roundReflectionCoefficient (center i) p
    (extension (roundDiskReflection (center i) (radius i) (radius_pos i) p))
  density : PlaneL2
  supportRadius : ℝ
  extension_zero : ∀z : ℂ,supportRadius≤‖z‖ → extension (z : Sphere)=0
  approximation : PrincipalSmoothApproximation density bound supportRadius
  limitData : PrincipalMapLimit approximation
  density_equation : ∀ᵐz ∂volume,density z=extension (z : Sphere)*(1+beurling density z)
  coefficient_tendsto : ∀ᵐz ∂volume,Tendsto (fun n => approximation.coefficient n z)
    atTop (𝓝 (extension (z : Sphere)))

namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

def principal (D : AnalyticReflectionData C) : ℂ ≃ₜ ℂ := D.limitData.map

lemma principal_decay (D : AnalyticReflectionData C) :
    Tendsto (fun z => D.principal z-z) (Bornology.cobounded ℂ) (𝓝 0) := D.limitData.principal

lemma principal_weak (D : AnalyticReflectionData C) (v : ℂ) (φ : SchwartzMap ℂ ℂ)
    (hs : HasCompactSupport (φ : ℂ → ℂ)) :
    (∫z,D.principal z*fderiv ℝ (φ : ℂ → ℂ) z v)=
      -(∫z,(v+principalDirectionalCorrection D.density v z)*φ z) := D.limitData.weak v φ hs

end AnalyticReflectionData

lemma exists_analytic_reflection_data {I : Type*} [Finite I]
    (C : FiniteJordanConfiguration I) (ha : ∀i,IsAnalyticJordanCap (C.hole i)) :
    Nonempty (AnalyticReflectionData C) := by
  obtain ⟨P,c,r,μ,k,S,hPs,hPis,hr,hcap,hμs,hk,hk1,hS,hb,hz,he⟩ :=
    exists_finite_analytic_rounding_coefficient C ha
  have hd := rounding_round_disks_disjoint C P c r hcap
  obtain ⟨E,T,g,S,L,hEm,hEz,hEb,hEf,hEinv,hg,hc⟩ := exists_round_invariant_principal_approximation_with_coefficient
    c r hr hd μ hμs.continuous.measurable hk hk1 hb hz
  refine ⟨{
    comparison := P
    center := c
    radius := r
    radius_pos := hr
    comparison_smooth := hPs
    comparison_inverse_smooth := hPis
    cap_image := hcap
    baseCoefficient := μ
    bound := k
    bound_nonneg := hk
    bound_lt_one := hk1
    base_bound := hb
    base_equation := he
    extension := E
    extension_measurable := hEm
    extension_bound := hEb
    extension_base := ?_
    extension_invariant := hEinv
    density := g
    supportRadius := T
    extension_zero := hEz
    approximation := S
    limitData := L
    density_equation := hg
    coefficient_tendsto := hc }⟩
  rwa [rounding_spherical_exterior_image C P c r hcap]

end CircleDomainRigidity

end

end OAI
