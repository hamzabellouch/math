import OAI.Analysis.CircleDomains.Topology.GatedQuotientMap
import OAI.Analysis.CircleDomains.Sobolev.SmoothSphereCharts

namespace OAI

/-! A globally measurable representative of the actual normalized map,
with the same values and derivatives on the physical domain. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_normalized_source_representative
    {G : Set Sphere} (hG : IsOpen G) (F : ℂ → ℂ)
    (hF : IsConformalOn (extendAtInfinity F) G) :
    ∃ F₀ : ℂ → ℂ, Measurable F₀ ∧
      ContDiffOn ℝ (⊤ : ℕ∞) F₀ (((↑) : ℂ → Sphere) ⁻¹' G) ∧
      EqOn F₀ F (((↑) : ℂ → Sphere) ⁻¹' G) := by
  classical
  let D := ((↑) : ℂ → Sphere) ⁻¹' G
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) F D := by
    intro z hz
    have ha := analyticAt_finite_map_of_conformal hG hF hz
      (by simp only [extendAtInfinity_coe]; exact OnePoint.coe_ne_infty _)
    simp only [extendAtInfinity_coe, finiteCoord_coe] at ha
    exact (ha.contDiffAt.restrict_scalars ℝ).contDiffWithinAt
  let F₀ : ℂ → ℂ := D.piecewise F (fun _ => 0)
  have hEq : EqOn F₀ F D := fun z hz => piecewise_eq_of_mem D F (fun _ => 0) hz
  exact ⟨F₀, hs.continuousOn.measurable_piecewise continuousOn_const
    (hG.preimage OnePoint.continuous_coe).measurableSet,
    hs.congr hEq, hEq⟩

 theorem quotientNormalizedMap_eq_of_eqOn {G U : Set Sphere} (e : G ≃ₜ U)
    {F₀ F : ℂ → ℂ} (hEq : EqOn F₀ F (((↑) : ℂ → Sphere) ⁻¹' G)) :
    quotientNormalizedMap e F₀ = quotientNormalizedMap e F := by
  funext x
  unfold quotientNormalizedMap
  have hy : (e.symm x).val ∈ G := (e.symm x).property
  cases h : (e.symm x).val using OnePoint.rec with
  | infty => rfl
  | coe z =>
    simp only [extendAtInfinity_coe]
    have hz : z ∈ ((↑) : ℂ → Sphere) ⁻¹' G := by
      change (z : Sphere) ∈ G
      simpa only [h] using hy
    have hval : F₀ z = F z := hEq hz
    exact congrArg ((↑) : ℂ → Sphere) hval

end CircleDomainRigidity

end

end OAI
