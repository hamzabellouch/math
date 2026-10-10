import OAI.Geometry.SurfaceImmersion.Whitney.SmoothSurfaceDoubleChart

namespace OAI

/-! The actual double-locus charts retain smooth coordinate expressions in
both directions. Their overlap maps are ordinary smooth real functions. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

structure SmoothDoubleChart (f : M → ProjectionTarget 3) where
  left : M
  right : M
  coord : OpenPartialHomeomorph (surfaceDoublePairs f) ℝ
  expression : Base × Base → ℝ
  expression_smooth : ContDiff ℝ ∞ expression
  source_formula : ∀ z ∈ coord.source,
    z.val.1 ∈ (chart left).source ∧ z.val.2 ∈ (chart right).source ∧
      coord z = expression (chart left z.val.1,chart right z.val.2)
  inverse_left_smooth : ContMDiffOn 𝓘(ℝ) planeModel ∞ (fun t => (coord.symm t).val.1) coord.target
  inverse_right_smooth : ContMDiffOn 𝓘(ℝ) planeModel ∞ (fun t => (coord.symm t).val.2) coord.target
  inverse_regular : ∀ t ∈ coord.target, Function.Injective
    ((mfderiv 𝓘(ℝ) planeModel (fun s => (coord.symm s).val.1) t).prod
      (mfderiv 𝓘(ℝ) planeModel (fun s => (coord.symm s).val.2) t))

theorem exists_smooth_double_chart {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (p : surfaceDoublePairs f)
    (hreg : Function.Surjective (surfacePairDerivative f p.val.1 p.val.2)) :
    ∃ c : SmoothDoubleChart f, p ∈ c.coord.source := by
  obtain ⟨c,hp,hA,hB,hpair,C,hC,hform⟩ := smooth_surface_double_pair_chart_data hf
    p.val.1 p.val.2 p.property.1 p.property.2 hreg
  exact ⟨⟨p.val.1,p.val.2,c,C,hC,hform,hA,hB,hpair⟩,hp⟩

namespace SmoothDoubleChart
variable {f : M → ProjectionTarget 3}

def overlap (a b : SmoothDoubleChart f) : Set ℝ :=
  b.coord.target ∩ b.coord.symm ⁻¹' a.coord.source

def transition (a b : SmoothDoubleChart f) : ℝ → ℝ := a.coord ∘ b.coord.symm

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma overlap_open (a b : SmoothDoubleChart f) : IsOpen (a.overlap b) :=
  b.coord.continuousOn_symm.isOpen_inter_preimage b.coord.open_target a.coord.open_source

omit [T2Space M] in
theorem transition_smooth (a b : SmoothDoubleChart f) :
    ContDiffOn ℝ ∞ (a.transition b) (a.overlap b) := by
  have hA := (chart_smooth a.left).comp (b.inverse_left_smooth.mono inter_subset_left)
    (fun t (ht : t ∈ a.overlap b) => (a.source_formula (b.coord.symm t) ht.2).1)
  have hB := (chart_smooth a.right).comp (b.inverse_right_smooth.mono inter_subset_left)
    (fun t (ht : t ∈ a.overlap b) => (a.source_formula (b.coord.symm t) ht.2).2.1)
  have hC := a.expression_smooth.comp_contDiffOn (hA.contDiffOn.prodMk hB.contDiffOn)
  apply hC.congr
  intro t ht
  exact (a.source_formula (b.coord.symm t) ht.2).2.2

end SmoothDoubleChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
