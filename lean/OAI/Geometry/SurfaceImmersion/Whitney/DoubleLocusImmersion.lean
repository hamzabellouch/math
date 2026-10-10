import OAI.Geometry.SurfaceImmersion.Whitney.DoubleLocusProjections

namespace OAI

/-! The natural inclusion of the smooth double locus into the pair of
surfaces has injective differential. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {f : M → ProjectionTarget 3}

theorem doubleLocus_inclusion_immersion
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (p : surfaceDoublePairs f) :
    let := doubleLocusChartedSpace hf hreg
    Function.Injective
      ((mfderiv 𝓘(ℝ) planeModel (fun q : surfaceDoublePairs f => q.val.1) p).prod
        (mfderiv 𝓘(ℝ) planeModel (fun q : surfaceDoublePairs f => q.val.2) p)) := by
  let := doubleLocusChartedSpace hf hreg
  let := doubleLocus_isManifold hf hreg
  let c := transverseDoubleChart hf hreg p
  have hp : p ∈ c.coord.source := transverseDoubleChart_mem hf hreg p
  have hcp : c.coord p ∈ c.coord.target := c.coord.map_source hp
  have hc : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ c.coord p :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hp
  let A : ℝ → M := fun t => (c.coord.symm t).val.1
  let B : ℝ → M := fun t => (c.coord.symm t).val.2
  have hA : ContMDiffAt 𝓘(ℝ) planeModel ∞ A (c.coord p) :=
    c.inverse_left_smooth.contMDiffAt (c.coord.open_target.mem_nhds hcp)
  have hB : ContMDiffAt 𝓘(ℝ) planeModel ∞ B (c.coord p) :=
    c.inverse_right_smooth.contMDiffAt (c.coord.open_target.mem_nhds hcp)
  have heA : (fun q : surfaceDoublePairs f => q.val.1) =ᶠ[𝓝 p] A ∘ c.coord := by
    filter_upwards [c.coord.open_source.mem_nhds hp] with q hq
    change q.val.1 = (c.coord.symm (c.coord q)).val.1
    rw [c.coord.left_inv hq]
  have heB : (fun q : surfaceDoublePairs f => q.val.2) =ᶠ[𝓝 p] B ∘ c.coord := by
    filter_upwards [c.coord.open_source.mem_nhds hp] with q hq
    change q.val.2 = (c.coord.symm (c.coord q)).val.2
    rw [c.coord.left_inv hq]
  have hDA : mfderiv 𝓘(ℝ) planeModel (fun q : surfaceDoublePairs f => q.val.1) p =
      (mfderiv 𝓘(ℝ) planeModel A (c.coord p)).comp (mfderiv 𝓘(ℝ) 𝓘(ℝ) c.coord p) := by
    rw [heA.mfderiv_eq,mfderiv_comp p (hA.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))]
    rfl
  have hDB : mfderiv 𝓘(ℝ) planeModel (fun q : surfaceDoublePairs f => q.val.2) p =
      (mfderiv 𝓘(ℝ) planeModel B (c.coord p)).comp (mfderiv 𝓘(ℝ) 𝓘(ℝ) c.coord p) := by
    rw [heB.mfderiv_eq,mfderiv_comp p (hB.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))]
    rfl
  have hci : Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ) c.coord p) :=
    (mdifferentiable_chart (I := 𝓘(ℝ)) p).mfderiv_injective hp
  have hi := c.inverse_regular (c.coord p) hcp
  dsimp only
  intro u v huv
  apply hci
  apply hi
  rw [hDA,hDB] at huv
  exact huv

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
