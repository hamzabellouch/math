import OAI.Analysis.CircleDomains.Topology.SphereSliceChart
import OAI.Analysis.CircleDomains.Modulus.SphericalChartCost

namespace OAI

/-! A quotient neighborhood whose closure misses the image of infinity
has a bounded inverse physical chart. Domain points in it are covered
by that chart using the actual domain homeomorphism. -/

open Set Function
open scoped Topology NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem finiteCoord_lipschitz_quotient_neighborhood
    (π : Sphere → Sphere) (hπ : Continuous π) (G V : Set Sphere)
    (hinfty : π OnePoint.infty ∉ closure V) :
    ∃ L : ℝ≥0, LipschitzOnWith L finiteCoord
      (((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' G ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' V)) := by
  have hK : IsCompact (((↑) : ℂ → Sphere) ⁻¹' (π ⁻¹' closure V)) :=
    isCompact_finite_preimage (isClosed_closure.preimage hπ) hinfty
  obtain ⟨L, hL⟩ := finiteCoord_lipschitz_on_compact_chart hK
  refine ⟨L, hL.mono (image_mono ?_)⟩
  intro z hz
  exact subset_closure hz.2

theorem quotient_neighborhood_chart_covers
    {G U V : Set Sphere} (e : G ≃ₜ U) (π : Sphere → Sphere)
    (he : ∀ y : G, (e y).val = π y.val)
    (hinfty : π OnePoint.infty ∉ V) :
    ∀ x ∈ U ∩ V, ∃ z : ℂ,
      z ∈ (((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' V) ∧
      π (z : Sphere) = x := by
  intro x hx
  let y := e.symm ⟨x, hx.1⟩
  have hy : π y.val = x := by rw [← he y]; exact congrArg Subtype.val (e.apply_symm_apply _)
  have hyG : y.val ∈ G := y.property
  cases hp : y.val using OnePoint.rec with
  | infty =>
    have hyV : π y.val ∈ V := hy.symm ▸ hx.2
    exact (hinfty (by simpa only [hp] using hyV)).elim
  | coe z =>
    refine ⟨z, ⟨?_, ?_⟩, ?_⟩
    · simpa only [mem_preimage, ← hp] using hyG
    · change π (z : Sphere) ∈ V
      rw [← hp, hy]
      exact hx.2
    · rw [← hp]
      exact hy

end CircleDomainRigidity

end

end OAI
