import OAI.Analysis.CircleDomains.Sobolev.MixedCircuitSmoothness
import OAI.Analysis.CircleDomains.Rigidity.MaskedCircuitLift
import OAI.Analysis.CircleDomains.Uniformization.CircuitUniformError
import OAI.Analysis.CircleDomains.Transfer.SourceStokesEventual

namespace OAI

/-! The fixed-source exclusion for an actual mixed model sequence.
Smoothness, mask containment, a common lifted coordinate and the uniform
error are derived from retention and local uniform convergence. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MixedModelExhaustion.excludes_source_stokes_limit
    {S C : Type*} [LinearOrder C]
    {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C}
    {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}
    (M : MixedModelExhaustion d data retained O ε ρ)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (hG : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) (j : C)
    (hmask : ∀ z ∈ frontier (jordanInterior H), Complex.equivRealProdCLM z ∈
      interior (physicalMask π (data j).mask))
    (v : ℝ → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hproj : ∀ t, (v t : UnitAddCircle) = (data j).physical (Complex.equivRealProdCLM (γ t)))
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (hlim : TendstoLocallyUniformlyOn
      (fun n (z : ℂ) => finiteCoord ((M.stages (k n)).model.forward (z : Sphere))) F atTop
      (((↑) : ℂ → Sphere) ⁻¹' G))
    (c : ℕ → ℂ) (c₀ : ℂ) (hc : Tendsto c atTop (𝓝 c₀))
    (r : ℕ → ℝ) (r₀ : ℝ≥0) (hr : ∀ n, 0 ≤ r n) (hrr : Tendsto r atTop (𝓝 (r₀ : ℝ)))
    (L I B : ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop,
      |circleFormIntegral (fun z => infDist z (closedBall (c n) (r n)))
        (fun z => sphereRealFunction ((M.stages (k n)).model.functions (M.coordinateIndex j (k n)))
          ((M.stages (k n)).model.inverse (z : Sphere)))
        (fun t => finiteCoord ((M.stages (k n)).model.forward (γ t : Sphere)))| ≤
      Real.sqrt Real.pi * L * Real.sqrt (I + ε (k n)) + 2 * Real.pi * L * (B + ε (k n))) :
    (boundaryCurveTrace (F ∘ γ) (hF.comp_continuous hγ.smooth.continuous
      (fun t => hG (mem_image_of_mem _ (hγ.mem_frontier t)))), c₀, r₀) ∉
      boundaryExclusionSet v (Real.sqrt Real.pi * L * Real.sqrt I + 2 * Real.pi * L * B) := by
  let γn := fun n t => finiteCoord ((M.stages (k n)).model.forward (γ t : Sphere))
  let un := fun n (z : ℂ) => sphereRealFunction
    ((M.stages (k n)).model.functions (M.coordinateIndex j (k n)))
    ((M.stages (k n)).model.inverse (z : Sphere))
  let W := fun n => Complex.equivRealProdCLM ⁻¹'
    (M.stages (k n)).toMaskedCoordinateStage.targetMask (M.coordinateIndex j (k n))
  have hg₀ := hF.comp_continuous hγ.smooth.continuous
    (fun t => hG (mem_image_of_mem _ (hγ.mem_frontier t)))
  obtain ⟨e, he, he0, hclose⟩ := exists_circuit_uniform_error γn (F ∘ γ)
    (tendstoUniformlyOn_retained_circuit (fun n => (M.stages (k n)).model.forward)
      F hlim H γ hγ hG)
  apply boundaryExclusionSet_excludes_eventual_source_stokes γn (F ∘ γ) hg₀ W un v hv
    c c₀ hc r r₀ hrr e he0 ?_ L I B (fun n => ε (k n)) (hε.comp hk) hbound
  filter_upwards [hk (M.eventually_circuit_smooth_in_mask H γ hγ hG j hmask),
    hk (M.eventually_circuit_values H γ hγ hG j), hclose] with n hn hvn hcn
  have ht := (M.stages (k n)).model.transported (M.coordinateIndex j (k n))
  refine ⟨hn.1.differentiable (by simp), ht.1.preimage Complex.equivRealProdCLM.continuous,
    ?_, hn.2, ?_, hr n, he n, hcn⟩
  · intro z hz a ha
    have hh := (ht.2.1 _ hz a ha).comp z Complex.equivRealProdCLM.contDiff.contDiffAt
    simpa only [un, sphereRealFunction, sphereRealMap, Function.comp_def,
      ContinuousLinearEquiv.symm_apply_apply] using hh
  · intro t
    exact (hproj t).trans (hvn t).symm

end CircleDomainRigidity.FiniteTransfer

end

end OAI
