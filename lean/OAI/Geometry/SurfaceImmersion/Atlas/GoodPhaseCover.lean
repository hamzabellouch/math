import OAI.Geometry.SurfaceImmersion.Atlas.GoodPhaseNeighborhood

namespace OAI

/-! Finite good phase charts covering the compact support of a correction. -/
noncomputable section
open Set Filter TopologicalSpace
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

/-- All geometric data of one compactly bounded local phase chart. -/
structure GoodPhaseChart (F : RField 4) (φ : Base → ℝ) where
  chart : OpenPartialHomeomorph Base Base
  phase : ∀ x, (chart x).1 = φ x
  smooth : ContDiff ℝ ∞ chart
  smoothInverse : ContDiff ℝ ∞ chart.symm
  sourceCompact : Compacts Base
  targetCompact : Compacts Base
  domain : Set Base
  sourceBound : chart.source ⊆ sourceCompact
  targetBound : chart.target ⊆ targetCompact
  targetInside : (targetCompact : Set Base) ⊆ domain
  good : RealModeDomain (F ∘ chart.symm) domain

theorem exists_goodPhaseChart {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) {p : Base}
    (hImm : Function.Injective (fderiv ℝ F p))
    (hgood : Good (realSecondTensor F p) (phaseDerivative φ p)) :
    ∃ c : GoodPhaseChart F φ, p ∈ c.chart.source := by
  obtain ⟨d,KE,KV,Ω,hp,hphase,he,hi,hKE,hKV,hsource,htarget,hinside,hdom⟩ :=
    exists_good_phase_neighborhood hF hφ hImm hgood
  exact ⟨⟨d,hphase,he,hi,⟨KE,hKE⟩,⟨KV,hKV⟩,Ω,hsource,htarget,hinside,hdom⟩,hp⟩

/-- No global coordinate chart for a mixed phase is assumed: finitely many
actual local phase charts cover its compact support. -/
theorem finite_good_phase_cover {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (K : Compacts Base)
    (hImm : ∀ p ∈ (K : Set Base), Function.Injective (fderiv ℝ F p))
    (hgood : ∀ p ∈ (K : Set Base), Good (realSecondTensor F p) (phaseDerivative φ p)) :
    ∃ (t : Finset K) (c : t → GoodPhaseChart F φ),
      (K : Set Base) ⊆ ⋃ i : t, (c i).chart.source := by
  classical
  choose c hc using fun p : K => exists_goodPhaseChart hF hφ (hImm p p.property) (hgood p p.property)
  have hcover : (K : Set Base) ⊆ ⋃ p : K, (c p).chart.source := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p,hp⟩,hc ⟨p,hp⟩⟩
  obtain ⟨t,ht⟩ := K.isCompact.elim_finite_subcover (fun p : K => (c p).chart.source)
    (fun p => (c p).chart.open_source) hcover
  refine ⟨t,fun i => c i.val,?_⟩
  intro p hp
  obtain ⟨i,hit,hi⟩ := mem_iUnion₂.mp (ht hp)
  exact mem_iUnion.mpr ⟨⟨i,hit⟩,hi⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
