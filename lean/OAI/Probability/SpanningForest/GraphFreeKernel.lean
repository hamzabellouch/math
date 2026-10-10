import OAI.Probability.SpanningForest.AlgebraicCycleSpace
import OAI.Probability.SpanningForest.GraphCoordinateTruncation

namespace OAI

noncomputable section

open Filter
open scoped Topology ENNReal

namespace Problem336.FreeKernel

open CoordinateTruncation

instance complete_closedGraphCycleSpace (G : GraphCode) :
    CompleteSpace (closedGraphCycleSpace G) := by
  unfold closedGraphCycleSpace
  infer_instance

instance projection_closedGraphCycleSpace (G : GraphCode) :
    (closedGraphCycleSpace G).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

def finiteKernel (K : FiniteSubgraphCode) : EdgeHilbert →L[ℝ] EdgeHilbert :=
  truncate (finiteEdges K) - (finiteHilbertCycleSpace K).starProjection

def graphKernel (G : GraphCode) : EdgeHilbert →L[ℝ] EdgeHilbert :=
  (supported (graphEdges G)).starProjection - (closedGraphCycleSpace G).starProjection

theorem cycle_projection_tendsto {G : GraphCode} {H : ℕ → FiniteSubgraphCode}
    (hH : IsConnectedExhaustion G H) (x : EdgeHilbert) :
    Tendsto (fun n => (finiteHilbertCycleSpace (H n)).starProjection x) atTop
      (𝓝 ((closedGraphCycleSpace G).starProjection x)) := by
  have h := Submodule.starProjection_tendsto_closure_iSup
    (fun n => finiteHilbertCycleSpace (H n)) hH.finiteHilbertCycleSpace_monotone x
  simpa only [hH.closure_iSup_finiteHilbertCycleSpace] using h

theorem finiteKernel_tendsto {G : GraphCode} {H : ℕ → FiniteSubgraphCode}
    (hH : IsConnectedExhaustion G H) (x : EdgeHilbert) :
    Tendsto (fun n => finiteKernel (H n) x) atTop (𝓝 (graphKernel G x)) := by
  simpa only [finiteKernel, graphKernel, sub_apply] using
    (graph_truncate_tendsto hH x).sub (cycle_projection_tendsto hH x)

theorem finiteKernel_inner_tendsto {G : GraphCode} {H : ℕ → FiniteSubgraphCode}
    (hH : IsConnectedExhaustion G H) (x y : EdgeHilbert) :
    Tendsto (fun n => inner ℝ x (finiteKernel (H n) y)) atTop
      (𝓝 (inner ℝ x (graphKernel G y))) :=
  tendsto_const_nhds.inner (finiteKernel_tendsto hH y)

theorem finiteKernel_minor_tendsto {G : GraphCode} {H : ℕ → FiniteSubgraphCode}
    (hH : IsConnectedExhaustion G H) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → EdgeHilbert) :
    Tendsto (fun n => Matrix.det (fun i j => inner ℝ (v i) (finiteKernel (H n) (v j))))
      atTop (𝓝 (Matrix.det (fun i j => inner ℝ (v i) (graphKernel G (v j))))) := by
  have hd : Continuous (Matrix.det : Matrix ι ι ℝ → ℝ) := continuous_id.matrix_det
  apply (hd.tendsto _).comp
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  exact finiteKernel_inner_tendsto hH (v i) (v j)

def edgeVector (e : EdgeCode) : EdgeHilbert := lp.single 2 e (1 : ℝ)

def kernelEntry (G : GraphCode) (e f : EdgeCode) : ℝ :=
  inner ℝ (edgeVector e) (graphKernel G (edgeVector f))

theorem finiteKernel_edge_minor_tendsto {G : GraphCode} {H : ℕ → FiniteSubgraphCode}
    (hH : IsConnectedExhaustion G H) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → EdgeCode) :
    Tendsto (fun n => Matrix.det (fun i j =>
      inner ℝ (edgeVector (e i)) (finiteKernel (H n) (edgeVector (e j)))))
      atTop (𝓝 (Matrix.det (fun i j => kernelEntry G (e i) (e j)))) :=
  finiteKernel_minor_tendsto hH (fun i => edgeVector (e i))

def finiteInclusionMinor (K : FiniteSubgraphCode) (A : Finset EdgeCode) : ℝ≥0∞ :=
  ENNReal.ofReal (Matrix.det (fun e f : A =>
    inner ℝ (edgeVector e.1) (finiteKernel K (edgeVector f.1))))

def inclusionMinorLimit (G : GraphCode) (A : Finset EdgeCode) : ℝ≥0∞ :=
  ENNReal.ofReal (Matrix.det (fun e f : A => kernelEntry G e.1 f.1))

theorem finiteInclusionMinor_tendsto {G : GraphCode} {H : ℕ → FiniteSubgraphCode}
    (hH : IsConnectedExhaustion G H) (A : Finset EdgeCode) :
    Tendsto (fun n => finiteInclusionMinor (H n) A) atTop
      (𝓝 (inclusionMinorLimit G A)) := by
  simpa only [finiteInclusionMinor, inclusionMinorLimit, Function.comp_def] using
    (ENNReal.continuous_ofReal.tendsto _).comp
      (finiteKernel_edge_minor_tendsto hH (fun e : A => e.1))

theorem common_inclusion_limits_of_finite_identity (G : GraphCode)
    (hfinite : ∀ K : FiniteSubgraphCode, IsFiniteConnectedSubgraph G K →
      ∀ A : Finset EdgeCode, ustCylinder K A ∅ = finiteInclusionMinor K A) :
    ∀ H : ℕ → FiniteSubgraphCode, IsConnectedExhaustion G H →
      ∀ A : Finset EdgeCode, Tendsto (fun n => ustCylinder (H n) A ∅) atTop
        (𝓝 (inclusionMinorLimit G A)) := by
  intro H hH A
  simpa only [hfinite _ (hH.1 _) A] using finiteInclusionMinor_tendsto hH A

theorem finiteCycle_le_supported (K : FiniteSubgraphCode) :
    finiteHilbertCycleSpace K ≤ supported (finiteEdges K : Set EdgeCode) := by
  rintro x ⟨f, hf, rfl⟩ e he
  rw [edgeFlowToHilbert_apply]
  apply Finsupp.notMem_support_iff.mp
  intro hes
  apply he
  exact (mem_finiteEdges K e).mpr (((mem_finiteCycleSpace K f).mp hf).1 e hes)

theorem finiteKernel_mem_supported (K : FiniteSubgraphCode) (x : EdgeHilbert) :
    finiteKernel K x ∈ supported (finiteEdges K : Set EdgeCode) :=
  (supported (finiteEdges K : Set EdgeCode)).sub_mem
    (truncate_mem_supported (finiteEdges K) x)
    (finiteCycle_le_supported K ((finiteHilbertCycleSpace K).starProjection_apply_mem x))

theorem finiteKernel_inner_edge_eq_zero_of_not_mem (K : FiniteSubgraphCode)
    (e : EdgeCode) (x : EdgeHilbert) (he : e.1 ∉ K.2) :
    inner ℝ (edgeVector e) (finiteKernel K x) = 0 := by
  rw [edgeVector, lp.inner_single_left]
  have hz := finiteKernel_mem_supported K x e
    (fun h => he ((mem_finiteEdges K e).mp h))
  simpa using hz

theorem graphCycle_le_supported (G : GraphCode) :
    closedGraphCycleSpace G ≤ supported (graphEdges G) := by
  apply Submodule.topologicalClosure_minimal
  · rintro x ⟨f, hf, rfl⟩ e he
    rw [edgeFlowToHilbert_apply]
    apply Finsupp.notMem_support_iff.mp
    intro hes
    exact he (((mem_graphCycleSpace G f).mp hf).1 e hes)
  · exact supported_isClosed _

theorem graphKernel_mem_supported (G : GraphCode) (x : EdgeHilbert) :
    graphKernel G x ∈ supported (graphEdges G) :=
  (supported (graphEdges G)).sub_mem
    ((supported (graphEdges G)).starProjection_apply_mem x)
    (graphCycle_le_supported G ((closedGraphCycleSpace G).starProjection_apply_mem x))

@[simp] theorem kernelEntry_eq_zero_of_not_adj (G : GraphCode) (e f : EdgeCode)
    (he : ¬ Adj G e.1.1 e.1.2) : kernelEntry G e f = 0 := by
  rw [kernelEntry, edgeVector, lp.inner_single_left]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_one, mul_one]
  exact graphKernel_mem_supported G (edgeVector f) e he

end Problem336.FreeKernel

end

end OAI
