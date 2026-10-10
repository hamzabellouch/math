import OAI.Probability.SpanningForest.FiniteCycleIncidence
import OAI.Probability.SpanningForest.IncidenceCirculation
import OAI.Probability.SpanningForest.TransferProjection
import OAI.Probability.SpanningForest.CodeLaplacian

namespace OAI

noncomputable section

namespace Problem336
namespace ReducedCycleKernel

def reducedFiniteIncidence (K : FiniteSubgraphCode) (root : ↥K.1) :
    Matrix {v : ↥K.1 // v ≠ root} (finiteCodeEdges K) ℝ :=
  fun v e => finiteIncidence K v.1 e

variable {G : GraphCode} {K : FiniteSubgraphCode}

def codeSource (hK : IsFiniteConnectedSubgraph G K) (e : finiteCodeEdges K) : ↥K.1 :=
  ⟨e.1.1.1, (hK.2.1 e.1.1 e.2).1⟩

def codeDestination (hK : IsFiniteConnectedSubgraph G K) (e : finiteCodeEdges K) : ↥K.1 :=
  ⟨e.1.1.2, (hK.2.1 e.1.1 e.2).2.1⟩

theorem finiteIncidence_eq_incidence (hK : IsFiniteConnectedSubgraph G K) :
    finiteIncidence K = IncidenceCirculation.incidence (codeSource hK) (codeDestination hK) := by
  classical
  ext v e
  simp only [finiteIncidence, IncidenceCirculation.incidence, codeSource, codeDestination,
    Subtype.ext_iff]

theorem reducedFiniteIncidence_eq_incidence (hK : IsFiniteConnectedSubgraph G K)
    (root : ↥K.1) :
    reducedFiniteIncidence K root =
      IncidenceCirculation.reducedIncidence (codeSource hK) (codeDestination hK) root := by
  classical
  ext v e
  exact congrFun (congrFun (finiteIncidence_eq_incidence hK) v.1) e

theorem reducedFiniteIncidence_mulVec_eq_zero_iff
    (hK : IsFiniteConnectedSubgraph G K) (root : ↥K.1)
    (x : finiteCodeEdges K → ℝ) :
    (reducedFiniteIncidence K root).mulVec x = 0 ↔ (finiteIncidence K).mulVec x = 0 := by
  classical
  rw [reducedFiniteIncidence_eq_incidence hK, finiteIncidence_eq_incidence hK]
  exact IncidenceCirculation.reduced_mulVec_eq_zero_iff _ _ _ _

theorem codeEndpoints_connected (hK : IsFiniteConnectedSubgraph G K) :
    ReducedLaplacian.Connected (codeSource hK) (codeDestination hK) := by
  intro u v
  refine Relation.ReflTransGen.mono ?_ u v (Problem336.code_endpoints_connected hK u v)
  intro a b hab
  obtain ⟨e, he⟩ := hab
  let e' : finiteCodeEdges K := ⟨⟨e.1, (hK.2.1 e.1 e.2).2.2.1⟩, e.2⟩
  refine ⟨e', ?_⟩
  simpa only [codeSource, codeDestination, Problem336.codeSource, Problem336.codeTarget, e'] using he

theorem reducedFiniteIncidence_eq_gradient_transpose
    (hK : IsFiniteConnectedSubgraph G K) (root : ↥K.1) :
    reducedFiniteIncidence K root =
      (ReducedLaplacian.reducedGradient (codeSource hK) (codeDestination hK) root).transpose := by
  classical
  rw [reducedFiniteIncidence_eq_incidence hK]
  rfl

theorem reducedFiniteIncidence_gram_isUnit
    (hK : IsFiniteConnectedSubgraph G K) (root : ↥K.1) :
    IsUnit ((reducedFiniteIncidence K root) * (reducedFiniteIncidence K root).transpose).det := by
  classical
  apply isUnit_iff_ne_zero.mpr
  have hd := ReducedLaplacian.weightedLaplacian_det_ne_zero
    (codeSource hK) (codeDestination hK) root (fun _ => 1)
    (codeEndpoints_connected hK) (fun _ => by norm_num)
  simpa [ReducedLaplacian.weightedLaplacian,
    reducedFiniteIncidence_eq_gradient_transpose hK root] using hd

theorem reducedFiniteIncidence_euclideanKernel
    (hK : IsFiniteConnectedSubgraph G K) (root : ↥K.1) :
    (reducedFiniteIncidence K root).toEuclideanLin.ker = (finiteIncidence K).toEuclideanLin.ker := by
  classical
  ext x
  simpa only [LinearMap.mem_ker, Matrix.toLpLin_apply,
    WithLp.toLp_eq_zero] using reducedFiniteIncidence_mulVec_eq_zero_iff hK root x.ofLp

theorem finiteHilbertCycleSpace_eq_reducedKernel
    (hK : IsFiniteConnectedSubgraph G K) (root : ↥K.1) :
    finiteHilbertCycleSpace K =
      ((reducedFiniteIncidence K root).toEuclideanLin.ker).map
        (finiteHilbertEmbedding K).toLinearMap := by
  rw [reducedFiniteIncidence_euclideanKernel hK]
  exact hK.finiteHilbertCycleSpace_eq_euclideanKernel

theorem finite_transfer_eq_coordinate_sub_cycle
    (hK : IsFiniteConnectedSubgraph G K) (root : ↥K.1)
    (hGram : IsUnit ((reducedFiniteIncidence K root) *
      (reducedFiniteIncidence K root).transpose).det) (x : EdgeHilbert) :
    finiteHilbertEmbedding K
      ((TransferProjection.transferMatrix (reducedFiniteIncidence K root)).toEuclideanLin
        ((finiteHilbertEmbedding K).toContinuousLinearMap.adjoint x)) =
      (finiteHilbertEmbedding K).toLinearMap.range.starProjection x -
        (finiteHilbertCycleSpace K).starProjection x := by
  classical
  rw [TransferProjection.embedded_transferMatrix_eq_difference _ hGram]
  congr 1
  congr 1
  congr 1
  exact (finiteHilbertCycleSpace_eq_reducedKernel hK root).symm

theorem finite_transfer_eq_coordinate_sub_cycle_of_connected
    (hK : IsFiniteConnectedSubgraph G K) (root : ↥K.1) (x : EdgeHilbert) :
    finiteHilbertEmbedding K
      ((TransferProjection.transferMatrix (reducedFiniteIncidence K root)).toEuclideanLin
        ((finiteHilbertEmbedding K).toContinuousLinearMap.adjoint x)) =
      (finiteHilbertEmbedding K).toLinearMap.range.starProjection x -
        (finiteHilbertCycleSpace K).starProjection x :=
  finite_transfer_eq_coordinate_sub_cycle hK root
    (reducedFiniteIncidence_gram_isUnit hK root) x

theorem finiteHilbertEmbedding_basis (K : FiniteSubgraphCode) (e : finiteCodeEdges K) :
    finiteHilbertEmbedding K (EuclideanSpace.basisFun (finiteCodeEdges K) ℝ e) =
      lp.single 2 e.1 (1 : ℝ) := by
  classical
  change finiteHilbertEmbeddingLinear K _ = _
  rw [finiteHilbertEmbeddingLinear_sum]
  simp

theorem finite_transfer_entry_eq_projection
    (hK : IsFiniteConnectedSubgraph G K) (root : ↥K.1) (e f : finiteCodeEdges K) :
    TransferProjection.transferMatrix (reducedFiniteIncidence K root) e f =
      inner ℝ (lp.single 2 e.1 (1 : ℝ))
        ((finiteHilbertEmbedding K).toLinearMap.range.starProjection (lp.single 2 f.1 (1 : ℝ)) -
          (finiteHilbertCycleSpace K).starProjection (lp.single 2 f.1 (1 : ℝ))) := by
  classical
  rw [← finite_transfer_eq_coordinate_sub_cycle_of_connected hK root]
  rw [← finiteHilbertEmbedding_basis K e, ← finiteHilbertEmbedding_basis K f]
  have hj : (finiteHilbertEmbedding K).toContinuousLinearMap.adjoint
      (finiteHilbertEmbedding K (EuclideanSpace.basisFun (finiteCodeEdges K) ℝ f)) =
      EuclideanSpace.basisFun (finiteCodeEdges K) ℝ f := by
    have hh := congrArg (fun F => F (EuclideanSpace.basisFun (finiteCodeEdges K) ℝ f))
      (finiteHilbertEmbedding K).adjoint_comp_self
    exact hh
  rw [hj, (finiteHilbertEmbedding K).inner_map_map, EuclideanSpace.basisFun_inner]
  simp [Matrix.toLpLin_apply]

theorem finite_transfer_root_independent
    (hK : IsFiniteConnectedSubgraph G K) (root root' : ↥K.1) (x : EdgeHilbert) :
    finiteHilbertEmbedding K
      ((TransferProjection.transferMatrix (reducedFiniteIncidence K root)).toEuclideanLin
        ((finiteHilbertEmbedding K).toContinuousLinearMap.adjoint x)) =
    finiteHilbertEmbedding K
      ((TransferProjection.transferMatrix (reducedFiniteIncidence K root')).toEuclideanLin
        ((finiteHilbertEmbedding K).toContinuousLinearMap.adjoint x)) := by
  rw [finite_transfer_eq_coordinate_sub_cycle_of_connected hK root,
    finite_transfer_eq_coordinate_sub_cycle_of_connected hK root']

end ReducedCycleKernel
end Problem336

end

end OAI
