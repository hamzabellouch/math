import OAI.Geometry.SurfaceImmersion.Atlas.OuterPhaseConvexity

namespace OAI

/-! The exact phase map remains an immersion on the full outer plateau. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma phaseRealChartMap_eq_real_comp (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (F : M → Space) :
    A.phaseRealChartMap i e.symm F = A.realChartMap i F ∘ (realPhaseChart e).symm := by
  funext y
  simp only [phaseRealChartMap,realChartMap,Function.comp_apply,realPhaseChart_symm_apply]
  have hb : (planeCoordinateIsometry : JetPolynomial.Base → SmallModes.Base) = baseEquiv := rfl
  have hbs : (planeCoordinateIsometry.symm : SmallModes.Base → JetPolynomial.Base) = baseEquiv.symm := rfl
  rw [hb,hbs,baseEquiv.symm_apply_apply]

lemma phase_injective_of_outer (i : A.centers)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {p : M} (hp : p ∈ (surfacePhaseChart (i : M) e).source)
    (ho : A.outer i =ᶠ[𝓝 p] (fun _ => 1)) :
    Function.Injective (fderiv ℝ (A.phaseRealChartMap i e.symm F)
      (surfacePhaseChart (i : M) e p)) := by
  let er := realPhaseChart e
  let x := surfacePhaseChart (i : M) e p
  have hx : x ∈ er.target := by
    change baseEquiv.symm (baseEquiv (e (chart (i : M) p))) ∈ e.target
    rw [baseEquiv.symm_apply_apply]
    exact e.map_source hp.2
  have hback : er.symm x = coordinateChart (i : M) p := by
    change baseEquiv (e.symm (baseEquiv.symm (baseEquiv (e (chart (i : M) p))))) = _
    rw [baseEquiv.symm_apply_apply]
    have hps : chart (i : M) p ∈ e.source := hp.2
    exact (congrArg baseEquiv (e.left_inv hps)).trans rfl
  have hI : Function.Injective (fderiv ℝ (A.realChartMap i F) (er.symm x)) := by
    rw [hback]
    exact A.realChartMap_injective_of_outer i hF hp.1 ho
  rw [A.phaseRealChartMap_eq_real_comp,fderiv_comp _
    ((A.realChartMap_smooth i hF.1).differentiable (by simp) _)
    ((realPhaseChart_symm_smooth e hi).differentiable (by simp) _)]
  exact hI.comp (inverse_chart_derivative_injective er (realPhaseChart_smooth e he)
    (realPhaseChart_symm_smooth e hi) hx)

omit [CompactSpace M] in
lemma phase_outer_neighborhood (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {T Ω : Set SmallModes.Base} (hΩ : IsOpen Ω)
    (hTΩ : T ⊆ Ω) (hΩe : Ω ⊆ (surfacePhaseChart (i : M) e).target)
    (hT : ∀ x ∈ T, A.outer i =ᶠ[𝓝 ((surfacePhaseChart (i : M) e).symm x)] (fun _ => 1)) :
    ∃ U : Set SmallModes.Base, IsOpen U ∧ T ⊆ U ∧ U ⊆ Ω ∧
      ∀ x ∈ U, A.outer i =ᶠ[𝓝 ((surfacePhaseChart (i : M) e).symm x)] (fun _ => 1) := by
  let P := {p : M | A.outer i =ᶠ[𝓝 p] (fun _ => 1)}
  have hP : IsOpen P := isOpen_setOfPred_eventually_nhds
  let E := surfacePhaseChart (i : M) e
  let U := Ω ∩ (E.target ∩ E.symm ⁻¹' P)
  have hU : IsOpen U := hΩ.inter (E.symm.isOpen_inter_preimage hP)
  exact ⟨U,hU,fun x hx => ⟨hTΩ hx,hΩe (hTΩ hx),hT x hx⟩,
    inter_subset_left,fun _ hx => hx.2.2⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
