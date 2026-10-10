import OAI.Analysis.CircleDomains.Sobolev.SmoothImageScalar
import OAI.Analysis.CircleDomains.Topology.ConformalSphericalMetric

namespace OAI

/-! Conformal invariance gives the exact original energy on the open
image for the corresponding smooth scalar. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

theorem imageScalar_energy (hG : IsOpen d.physicalDomain) (i : Fin m) :
    IntegrableOn (euclideanGradientEnergy (R.imageScalar i))
      (R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)) ∧
    (∫ z in R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain),
      euclideanGradientEnergy (R.imageScalar i) z) =
      ∫ x in realChartDomain d.physicalDomain,
        gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x := by
  let f := extendAtInfinity R.limit.function
  let V := f '' d.physicalDomain
  have hV : IsOpen V := R.limit.conformal.1.isOpen_image hG hG (Subset.refl _)
  obtain ⟨fi, heq⟩ := R.limit.conformal.exists_smooth_inverse hG hV
  have hinf : OnePoint.infty ∈ d.physicalDomain :=
    R.model.core_source 0 (R.model.plane_core 0 (Or.inr rfl))
  have hfix : f OnePoint.infty = OnePoint.infty := rfl
  have hdom : ((↑) : ℂ → Sphere) ⁻¹' V =
      R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) := by
    ext z
    constructor
    · rintro ⟨p, hp, he⟩
      cases p using OnePoint.rec with
      | infty => exact (OnePoint.coe_ne_infty z he.symm).elim
      | coe x => exact ⟨x, hp, OnePoint.coe_injective he⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x : Sphere), hx, rfl⟩
  let u : ℂ → ℝ := (sphereRealFunction (Q i).physical ∘ fi) ∘ ((↑) : ℂ → Sphere)
  have he : EqOn (R.imageScalar i) u (((↑) : ℂ → Sphere) ⁻¹' V) := by
    rw [hdom]
    rintro _ ⟨x, hx, rfl⟩
    rw [R.imageScalar_apply hG i hx]
    have hi : fi (R.limit.function x) = (x : Sphere) := heq.left_inv x hx
    change (Q i).physical (Complex.equivRealProdCLM x) =
      sphereRealFunction (Q i).physical (fi (R.limit.function x))
    rw [hi]
    rfl
  have henergy := transported_real_energy heq hG hV hinf hfix (Q i).physical
    (Q i).physical_smooth
    (fun p hp => (R.limit.conformal.1 p hp).isMetricConformalAt_spherical)
    (fun x _ => Matrix.PosDef.one.smul (sphericalMetricFactor_pos x))
    (integrable_gradientEnergy_spherical_of_memLp (Q i).physical_energy)
  have hd : EqOn (euclideanGradientEnergy (R.imageScalar i)) (euclideanGradientEnergy u)
      (((↑) : ℂ → Sphere) ⁻¹' V) := by
    intro z hz
    have hl : R.imageScalar i =ᶠ[𝓝 z] u := by
      filter_upwards [(hV.preimage OnePoint.continuous_coe).mem_nhds hz] with y hy
      exact he hy
    simp only [euclideanGradientEnergy, hl.fderiv_eq]
  have hi : IntegrableOn (euclideanGradientEnergy (R.imageScalar i))
      (((↑) : ℂ → Sphere) ⁻¹' V) := by
    apply henergy.2.1.congr
    filter_upwards [ae_restrict_mem (hV.preimage OnePoint.continuous_coe).measurableSet] with z hz
    exact (hd hz).symm
  rw [hdom] at hi
  refine ⟨hi, ?_⟩
  rw [← hdom]
  exact (setIntegral_congr_fun (hV.preimage OnePoint.continuous_coe).measurableSet hd).trans henergy.2.2

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
