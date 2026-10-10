import OAI.Analysis.CircleDomains.Selection.MixedCircuitRetention
import OAI.Analysis.CircleDomains.Rigidity.MaskedStageEnergy

namespace OAI

/-! A retained source circuit has a smooth image in the actual transported
mask. These are the domains required by the fixed-lift boundary integral. -/

open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem IsSmoothSphereAt.contDiffAt_finiteMap
    {f : Sphere → Sphere} {z : ℂ} (hf : IsSmoothSphereAt f (z : Sphere))
    (hfin : f (z : Sphere) ≠ OnePoint.infty) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ => finiteCoord (f (w : Sphere))) z := by
  have hs : IsSmoothSphereAt f
      ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hf
  have hfin' : f ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) ≠
      OnePoint.infty := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hfin
  have h := Complex.equivRealProdCLM.symm.contDiff.contDiffAt.comp z
    ((hs.contDiffAt_sphereRealMap hfin').comp z Complex.equivRealProdCLM.contDiff.contDiffAt)
  simpa only [Function.comp_def, sphereRealMap, ContinuousLinearEquiv.symm_apply_apply] using h

namespace FiniteTransfer

 theorem MixedModelExhaustion.eventually_circuit_smooth_in_mask
    {S C : Type*} [LinearOrder C]
    {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C}
    {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}
    (M : MixedModelExhaustion d data retained O ε ρ)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (hG : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) (c : C)
    (hmask : ∀ z ∈ frontier (jordanInterior H), Complex.equivRealProdCLM z ∈
      interior (physicalMask π (data c).mask)) :
    ∀ᶠ n in atTop,
      ContDiff ℝ (⊤ : ℕ∞) (fun t => finiteCoord ((M.stages n).model.forward (γ t : Sphere))) ∧
      ∀ t : ℝ, finiteCoord ((M.stages n).model.forward (γ t : Sphere)) ∈
        Complex.equivRealProdCLM ⁻¹' (M.stages n).toMaskedCoordinateStage.targetMask
          (M.coordinateIndex c n) := by
  let K := ((↑) : ℂ → Sphere) '' frontier (jordanInterior H)
  have hK : IsCompact K :=
    ((isCompact_closure_jordanInterior H).of_isClosed_subset isClosed_frontier
      frontier_subset_closure).image OnePoint.continuous_coe
  filter_upwards [M.real.eventually_core_contains hK hG, M.coordinateIndex_eventually c]
    with n hn hc
  have hpoint (t : ℝ) : (γ t : Sphere) ∈ openCompletedRegion (M.stages n).terminals.H := by
    apply (M.stages n).core_model
    apply (coe_mem_sphericalCore _ _).mpr
    apply interior_subset ((M.stages n).core_contains ?_)
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (γ t)) : ℂ) : Sphere) ∈
      M.real.cores n
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hn (mem_image_of_mem _ (hγ.mem_frontier t))
  have hi : OnePoint.infty ∈ openCompletedRegion (M.stages n).terminals.H :=
    (M.stages n).core_model (infty_mem_sphericalCore (M.stages n).core)
  have hfinite (t : ℝ) := finite_image_of_fixes_infty (M.stages n).model.equivalence.bijOn.injOn hi
    (M.stages n).model.principal.1 (hpoint t)
  constructor
  · apply contDiff_iff_contDiffAt.mpr
    intro t
    exact ((M.stages n).model.equivalence.smooth _ (hpoint t)).contDiffAt_finiteMap
      (hfinite t) |>.comp t hγ.smooth.contDiffAt
  · intro t
    refine ⟨Complex.equivRealProdCLM (γ t), ⟨?_, ?_⟩, ?_⟩
    · change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (γ t)) : ℂ) : Sphere) ∈
        openCompletedRegion (M.stages n).terminals.H
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hpoint t
    · change Complex.equivRealProdCLM (γ t) ∈
        interior (physicalMask π (data (M.label n (M.coordinateIndex c n))).mask)
      rw [hc]
      exact hmask _ (hγ.mem_frontier t)
    · simp only [sphereRealMap, ContinuousLinearEquiv.symm_apply_apply]

end FiniteTransfer
end CircleDomainRigidity

end

end OAI
