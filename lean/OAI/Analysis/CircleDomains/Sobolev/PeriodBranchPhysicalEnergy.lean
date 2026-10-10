import OAI.Analysis.CircleDomains.Sobolev.SmoothRealLift
import OAI.Analysis.CircleDomains.Topology.SphereLevels

namespace OAI

/-! Local branches of the constructed circle stream satisfy the exact
physical regularity hypotheses of the period generic-level theorem. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem period_branch_physical_energy
    {G U S V : Set Sphere} (e : G ≃ₜ U) (hG : IsOpen G) (hV : IsOpen V) (hVS : V ⊆ S)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (u : Sphere → ℝ) (hu : ContinuousOn u (U ∩ V))
    (w : ℂ → UnitAddCircle)
    (hw : FiniteTransfer.SmoothCircleOn w
      (((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' S))
    (hproj : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ V →
      (u (π (z : Sphere)) : UnitAddCircle) = w z)
    (henergy : (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' G ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' S,
      ENNReal.ofReal ‖FiniteTransfer.circleFDeriv w z‖ ^ 2) < ∞) :
    ContDiffOn ℝ 1 (fun z : ℂ => u (π (z : Sphere)))
        (((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' V) ∧
    (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' V,
      ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => u (π (z : Sphere))) z‖ ^ 2) < ∞ := by
  let A := ((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' V
  have hA : IsOpen A := (hG.preimage OnePoint.continuous_coe).inter
    (hV.preimage (hπ.comp OnePoint.continuous_coe))
  have hsub : A ⊆ ((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' S :=
    fun z hz => ⟨hz.1, hVS hz.2⟩
  have hcont : ContinuousOn (fun z : ℂ => u (π (z : Sphere))) A := by
    apply hu.comp (hπ.comp OnePoint.continuous_coe).continuousOn
    intro z hz
    refine ⟨?_, hz.2⟩
    change π (z : Sphere) ∈ U
    rw [← he ⟨(z : Sphere), hz.1⟩]
    exact (e ⟨(z : Sphere), hz.1⟩).property
  have hp : ∀ z ∈ A, (u (π (z : Sphere)) : UnitAddCircle) = w z :=
    fun z hz => hproj z hz.1 hz.2
  exact ⟨(FiniteTransfer.contDiffOn_real_lift hA
      (fun z hz => hw z (hsub hz)) hcont hp).of_le (by simp),
    (FiniteTransfer.real_lift_energy_le hA hsub hw hcont hp volume hA.measurableSet).trans_lt henergy⟩

end CircleDomainRigidity

end

end OAI
