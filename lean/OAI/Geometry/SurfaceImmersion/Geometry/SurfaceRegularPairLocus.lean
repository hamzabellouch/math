import OAI.Geometry.SurfaceImmersion.Whitney.SurfacePairLocalRegularization
import OAI.Geometry.SurfaceImmersion.Geometry.CriticalSetClosed

namespace OAI

/-! Regularity of a surface coincidence is an open first-jet condition. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

def regularSurfacePairs (f : M → ProjectionTarget 3) : Set (M × M) :=
  {z | f z.1 ≠ f z.2 ∨ Function.Surjective (surfacePairDerivative f z.1 z.2)}

theorem regularSurfacePairs_open {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) :
    IsOpen (regularSurfacePairs f) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  rcases hz with hz | hz
  · have ho : IsOpen {w : M × M | f w.1 ≠ f w.2} :=
      (isClosed_eq (hf.continuous.comp continuous_fst) (hf.continuous.comp continuous_snd)).isOpen_compl
    exact mem_of_superset (ho.mem_nhds hz) fun w hw => Or.inl hw
  · obtain ⟨U,F,hU,hzU,hUs,hF,heF⟩ := surface_chart_representative hf z.1
    obtain ⟨V,G,hV,hzV,hVs,hG,heG⟩ := surface_chart_representative hf z.2
    let H : Base × Base → ProjectionTarget 3 := fun w => F w.1-G w.2
    have hH : ContDiff ℝ ∞ H := (hF.comp contDiff_fst).sub (hG.comp contDiff_snd)
    have hsurj : Function.Surjective (fderiv ℝ H (chart z.1 z.1,chart z.2 z.2)) :=
      (surface_pair_coordinate_regular_iff z.1 z.2 (hUs hzU) (hVs hzV) hF hG
        (heF.eventuallyEq_of_mem (hU.mem_nhds hzU))
        (heG.eventuallyEq_of_mem (hV.mem_nhds hzV))).mp hz
    have hc : ContinuousAt (fun w : M × M => (chart z.1 w.1,chart z.2 w.2)) z :=
      ((chart z.1).continuousAt (hUs hzU)).comp continuousAt_fst |>.prodMk
        (((chart z.2).continuousAt (hVs hzV)).comp continuousAt_snd)
    have hn : ∀ᶠ w : M × M in 𝓝 z,
        Function.Surjective (fderiv ℝ H (chart z.1 w.1,chart z.2 w.2)) :=
      hc.eventually (((surjective_clm_open).preimage
        (hH.continuous_fderiv (by simp))).mem_nhds hsurj)
    filter_upwards [(hU.prod hV).mem_nhds ⟨hzU,hzV⟩,hn] with w hw hs
    right
    exact (surface_pair_coordinate_regular_iff z.1 z.2 (hUs hw.1) (hVs hw.2) hF hG
      (heF.eventuallyEq_of_mem (hU.mem_nhds hw.1))
      (heG.eventuallyEq_of_mem (hV.mem_nhds hw.2))).mpr hs

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
