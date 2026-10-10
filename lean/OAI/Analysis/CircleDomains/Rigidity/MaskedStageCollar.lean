import OAI.Analysis.CircleDomains.Topology.JordanHoleSelection
import OAI.Analysis.CircleDomains.Rigidity.MaskedStageEnergy
import OAI.Analysis.CircleDomains.Topology.ExteriorSeparation

namespace OAI

/-! The actual finite model carries a retained source collar to a Jordan
collar. Exactly the holes inside that image are selected, and the punctured
closed region lies in the transported coordinate's smooth mask. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedCoordinateStage.exists_collar_region
    (hsch : PlanarSchoenflies)
    {S : Type*} {n : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {C : Fin n → MaskedCoordinateData G U π σ}
    {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (l : Fin n)
    (H : ℂ ≃ₜ ℂ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆
      openCompletedRegion T.terminals.H)
    (hmask : realChartDomain (closedTerminalCap H) ⊆ interior (physicalMask π (C l).mask))
    (c : T.indices → ℂ) (r : T.indices → ℝ)
    (hext : ((↑) : ℂ → Sphere) ⁻¹' T.model.domain = (⋃ i, closedBall (c i) (r i))ᶜ) :
    ∃ (J : ℂ ≃ₜ ℂ) (m : ℕ) (κ : Fin m → T.indices),
      Injective κ ∧
      T.model.forward '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) ∧
      (∀ j, closedBall (c (κ j)) (r (κ j)) ⊆ jordanInterior J) ∧
      (∀ i, i ∈ range κ ↔ closedBall (c i) (r i) ⊆ jordanInterior J) ∧
      closure (jordanInterior J) \ ⋃ j, closedBall (c (κ j)) (r (κ j)) ⊆
        Complex.equivRealProdCLM ⁻¹' T.targetMask l := by
  classical
  let : Fintype T.indices := T.indices_finite.fintype
  let Q := openCompletedRegion T.terminals.H
  have hQ : IsOpen Q := isOpen_openCompletedRegion T.terminals.H
  have hQc : IsConnected Q :=
    isConnected_openCompletedRegion T.terminals.H T.terminals.disjoint_closures
  have hi : OnePoint.infty ∈ Q := T.core_model (infty_mem_sphericalCore T.core)
  have hf : ContinuousOn T.model.forward Q :=
    fun p hp => (T.model.equivalence.smooth p hp).1.continuousWithinAt
  obtain ⟨J, hJ⟩ := exists_jordan_image_retained_boundary hsch hf
    T.model.equivalence.bijOn.injOn hi T.model.principal.1 H hbd
  have hside := open_image_retained_jordan_side_eq hQ hQc.isPreconnected hi H J hbd
    hf (fun _ hS hSQ => T.model.equivalence.isOpen_image T.model.circle_domain.1 hS hSQ)
    T.model.equivalence.bijOn.injOn T.model.principal.1 hJ
  rw [T.model.equivalence.bijOn.image_eq] at hside
  have htargetbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) ⊆ T.model.domain := by
    rw [← hJ]
    exact (image_mono hbd).trans (image_subset_iff.mpr T.model.equivalence.mapsTo)
  obtain ⟨m, κ, hκ, hin, hexact, hregion⟩ :=
    exists_round_holes_inside_jordan c r T.model.domain hext J htargetbd
  refine ⟨J, m, κ, hκ, hJ, hin, hexact, ?_⟩
  intro z hz
  rw [hregion] at hz
  have hp : (z : Sphere) ∈ T.model.domain ∩ closedTerminalCap J :=
    ⟨hz.2, z, hz.1, rfl⟩
  obtain ⟨x, hx, hfx⟩ := target_closed_collar_subset_image H J hbd hJ hside
    (show Q ∩ closedTerminalCap H ⊆ Q ∩ closedTerminalCap H from Subset.rfl) hp
  obtain ⟨w, hw, rfl⟩ := hx.2
  refine ⟨Complex.equivRealProdCLM w, ⟨?_, ?_⟩, ?_⟩
  · change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM w) : ℂ) : Sphere) ∈
      openCompletedRegion T.terminals.H
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx.1
  · apply hmask
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM w) : ℂ) : Sphere) ∈
      closedTerminalCap H
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using
      (show (w : Sphere) ∈ closedTerminalCap H from ⟨w, hw, rfl⟩)
  · simp only [sphereRealMap, ContinuousLinearEquiv.symm_apply_apply, hfx, finiteCoord_coe]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
