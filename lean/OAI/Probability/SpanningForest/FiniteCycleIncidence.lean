import OAI.Probability.SpanningForest.AlgebraicCycleSpace

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336

instance finiteCodeEdgesFintype (K : FiniteSubgraphCode) : Fintype (finiteCodeEdges K) :=
  (finiteCodeEdges_finite K).fintype

def finiteFlowEmbedding (K : FiniteSubgraphCode) :
    (finiteCodeEdges K → ℝ) →ₗ[ℝ] EdgeFlow :=
  Fintype.linearCombination ℝ (fun e : finiteCodeEdges K => Finsupp.single e.1 1)

@[simp] theorem finiteFlowEmbedding_apply (K : FiniteSubgraphCode)
    (x : finiteCodeEdges K → ℝ) (e : finiteCodeEdges K) :
    finiteFlowEmbedding K x e.1 = x e := by
  classical
  simp only [finiteFlowEmbedding, Fintype.linearCombination_apply, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
  rw [Finset.sum_eq_single e]
  · simp
  · intro b hb hbe
    have hval : b.1 ≠ e.1 := fun h => hbe (Subtype.ext h)
    simp [hval]
  · simp

 theorem finiteFlowEmbedding_range (K : FiniteSubgraphCode) :
    LinearMap.range (finiteFlowEmbedding K) = Finsupp.supported ℝ ℝ (finiteCodeEdges K) := by
  rw [finiteFlowEmbedding, Fintype.range_linearCombination, Finsupp.supported_eq_span_single]
  congr 1
  ext f
  simp

 theorem finiteFlowEmbedding_injective (K : FiniteSubgraphCode) :
    Function.Injective (finiteFlowEmbedding K) := by
  intro x y h
  funext e
  simpa only [finiteFlowEmbedding_apply] using congrArg (fun f : EdgeFlow => f e.1) h

def finiteIncidence (K : FiniteSubgraphCode) :
    Matrix ↥K.1 (finiteCodeEdges K) ℝ :=
  fun v e => (if v.1 = e.1.1.1 then 1 else 0) - (if v.1 = e.1.1.2 then 1 else 0)

 theorem finiteIncidence_mulVec (K : FiniteSubgraphCode)
    (x : finiteCodeEdges K → ℝ) (v : ↥K.1) :
    (finiteIncidence K).mulVec x v = edgeBoundary (finiteFlowEmbedding K x) v.1 := by
  classical
  simp only [finiteIncidence, Matrix.mulVec, dotProduct, finiteFlowEmbedding,
    Fintype.linearCombination_apply, map_sum, map_smul, edgeBoundary_single,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.sub_apply,
    Finsupp.single_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro e he
  simp only [eq_comm]
  ring

 theorem IsFiniteConnectedSubgraph.boundary_eq_zero_outside {G : GraphCode}
    {K : FiniteSubgraphCode} (hK : IsFiniteConnectedSubgraph G K)
    (x : finiteCodeEdges K → ℝ) {v : ℕ} (hv : v ∉ K.1) :
    edgeBoundary (finiteFlowEmbedding K x) v = 0 := by
  classical
  simp only [finiteFlowEmbedding, Fintype.linearCombination_apply,
    map_sum, map_smul, edgeBoundary_single, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.single_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro e he
  have hends := hK.2.1 e.1.1 e.2
  have hleft : e.1.1.1 ≠ v := fun h => hv (h ▸ hends.1)
  have hright : e.1.1.2 ≠ v := fun h => hv (h ▸ hends.2.1)
  simp [hleft, hright]

 theorem IsFiniteConnectedSubgraph.finiteCycleSpace_eq_incidenceKernel {G : GraphCode}
    {K : FiniteSubgraphCode} (hK : IsFiniteConnectedSubgraph G K) :
    finiteCycleSpace K =
      (LinearMap.ker (Matrix.mulVecLin (finiteIncidence K))).map (finiteFlowEmbedding K) := by
  classical
  apply le_antisymm
  · intro f hf
    have hs : f ∈ LinearMap.range (finiteFlowEmbedding K) := by
      rw [finiteFlowEmbedding_range]
      exact hf.1
    obtain ⟨x, rfl⟩ := hs
    apply Submodule.mem_map.mpr
    refine ⟨x, ?_, rfl⟩
    change (finiteIncidence K).mulVec x = 0
    funext v
    rw [finiteIncidence_mulVec]
    exact congrArg (fun f : ℕ →₀ ℝ => f v.1) hf.2
  · intro f hf
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hf
    refine ⟨?_, ?_⟩
    · rw [← finiteFlowEmbedding_range]
      exact ⟨x, rfl⟩
    · change edgeBoundary (finiteFlowEmbedding K x) = 0
      ext v
      by_cases hv : v ∈ K.1
      · have hrow := congrArg (fun y : ↥K.1 → ℝ => y ⟨v, hv⟩) hx
        simpa only [Matrix.mulVecLin_apply, finiteIncidence_mulVec, Pi.zero_apply, Finsupp.zero_apply] using hrow
      · exact hK.boundary_eq_zero_outside x hv

 theorem IsFiniteConnectedSubgraph.finiteHilbertCycleSpace_eq_incidenceKernel {G : GraphCode}
    {K : FiniteSubgraphCode} (hK : IsFiniteConnectedSubgraph G K) :
    finiteHilbertCycleSpace K =
      (LinearMap.ker (Matrix.mulVecLin (finiteIncidence K))).map
        (edgeFlowToHilbert.comp (finiteFlowEmbedding K)) := by
  rw [finiteHilbertCycleSpace, hK.finiteCycleSpace_eq_incidenceKernel, Submodule.map_comp]

def finiteHilbertEmbeddingLinear (K : FiniteSubgraphCode) :
    EuclideanSpace ℝ (finiteCodeEdges K) →ₗ[ℝ] EdgeHilbert :=
  (edgeFlowToHilbert.comp (finiteFlowEmbedding K)).comp
    (WithLp.linearEquiv 2 ℝ (finiteCodeEdges K → ℝ)).toLinearMap

@[simp] theorem finiteHilbertEmbeddingLinear_apply (K : FiniteSubgraphCode)
    (x : EuclideanSpace ℝ (finiteCodeEdges K)) (e : finiteCodeEdges K) :
    finiteHilbertEmbeddingLinear K x e.1 = x e := by
  simp [finiteHilbertEmbeddingLinear]

 theorem finiteHilbertEmbeddingLinear_sum (K : FiniteSubgraphCode)
    (x : EuclideanSpace ℝ (finiteCodeEdges K)) :
    finiteHilbertEmbeddingLinear K x =
      ∑ e : finiteCodeEdges K, x e • lp.single 2 e.1 (1 : ℝ) := by
  simp [finiteHilbertEmbeddingLinear, finiteFlowEmbedding, Fintype.linearCombination_apply,
    map_sum, ← lp.single_smul]

 theorem finiteHilbertEmbeddingLinear_inner (K : FiniteSubgraphCode)
    (x y : EuclideanSpace ℝ (finiteCodeEdges K)) :
    inner ℝ (finiteHilbertEmbeddingLinear K x) (finiteHilbertEmbeddingLinear K y) =
      inner ℝ x y := by
  classical
  rw [finiteHilbertEmbeddingLinear_sum K x]
  simp [sum_inner, inner_smul_left, lp.inner_single_left, PiLp.inner_apply,
    finiteHilbertEmbeddingLinear_apply, mul_comm]

def finiteHilbertEmbedding (K : FiniteSubgraphCode) :
    EuclideanSpace ℝ (finiteCodeEdges K) →ₗᵢ[ℝ] EdgeHilbert :=
  (finiteHilbertEmbeddingLinear K).isometryOfInner (finiteHilbertEmbeddingLinear_inner K)

@[simp] theorem finiteHilbertEmbedding_apply (K : FiniteSubgraphCode)
    (x : EuclideanSpace ℝ (finiteCodeEdges K)) (e : finiteCodeEdges K) :
    finiteHilbertEmbedding K x e.1 = x e :=
  finiteHilbertEmbeddingLinear_apply K x e

 theorem IsFiniteConnectedSubgraph.finiteHilbertCycleSpace_eq_euclideanKernel {G : GraphCode}
    {K : FiniteSubgraphCode} (hK : IsFiniteConnectedSubgraph G K) :
    finiteHilbertCycleSpace K =
      (LinearMap.ker (Matrix.toEuclideanLin (finiteIncidence K))).map
        (finiteHilbertEmbedding K).toLinearMap := by
  classical
  rw [hK.finiteHilbertCycleSpace_eq_incidenceKernel]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨WithLp.toLp 2 x, ?_, rfl⟩
    change Matrix.toEuclideanLin (finiteIncidence K) (WithLp.toLp 2 x) = 0
    change (finiteIncidence K).mulVec x = 0 at hx
    simp only [Matrix.toLpLin_apply, hx, WithLp.toLp_zero]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.ofLp, ?_, rfl⟩
    change (finiteIncidence K).mulVec x.ofLp = 0
    change Matrix.toEuclideanLin (finiteIncidence K) x = 0 at hx
    have hh := congrArg WithLp.ofLp hx
    simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_zero] using hh

end Problem336

end

end OAI
