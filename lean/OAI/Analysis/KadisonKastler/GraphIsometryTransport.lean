import OAI.Analysis.KadisonKastler.GraphIdentificationIndependence

namespace OAI

/-! # Compression of closed Tomita graphs by a Hilbert isometry -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (V : H →ₗᵢ[ℂ] K) (J : H ≃ₗᵢ⋆[ℂ] H) (L : K ≃ₗᵢ⋆[ℂ] K)

def graphIsometry : TomitaGraphHilbert H →ₗᵢ[ℂ] TomitaGraphHilbert K where
  toFun v := WithLp.toLp 2 ![V (v 0), L (V (J.symm (v 1)))]
  map_add' x y := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [map_add]
  map_smul' z v := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [map_smulₛₗ]
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [Fin.sum_univ_two]
    change ‖V (v 0)‖ ^ 2 + ‖L (V (J.symm (v 1)))‖ ^ 2 = _
    rw [V.norm_map, L.norm_map, V.norm_map, J.symm.norm_map]

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] theorem graphIsometry_zero (v : TomitaGraphHilbert H) :
    graphIsometry V J L v 0 = V (v 0) := rfl

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] theorem graphIsometry_one (v : TomitaGraphHilbert H) :
    graphIsometry V J L v 1 = L (V (J.symm (v 1))) := rfl

omit [CompleteSpace H] [CompleteSpace K] in
theorem graphIsometry_single_zero (x : H) :
    graphIsometry V J L (Generator.tupleSingle 0 x) = Generator.tupleSingle 0 (V x) := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [Generator.tupleSingle_apply]

variable {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K} (Ω : H) (ξ : K)
  (c : ℝ)

theorem graphIsometry_projection
    (hforward : ∀ a : Algebra M, graphIsometry V J L (rescaledGraphVector J Ω c a.val) ∈
      rescaledGraphSubspace N L ξ c)
    (hback : ∀ b : Algebra N,
      (graphIsometry V J L).toContinuousLinearMap.adjoint (rescaledGraphVector L ξ c b.val) ∈
        rescaledGraphSubspace M J Ω c)
    (v : TomitaGraphHilbert H) :
    rescaledGraphProjection N L ξ c (graphIsometry V J L v) =
      graphIsometry V J L (rescaledGraphProjection M J Ω c v) := by
  let W := graphIsometry V J L
  have hmap {x : TomitaGraphHilbert H} (hx : x ∈ rescaledGraphSubspace M J Ω c) :
      W x ∈ rescaledGraphSubspace N L ξ c := by
    apply closure_minimal (s := Set.range (rescaledGraphMap M J Ω c)) ?_
      ((Submodule.isClosed_topologicalClosure _).preimage W.continuous) hx
    rintro _ ⟨a, rfl⟩
    exact hforward a
  have hadj {y : TomitaGraphHilbert K} (hy : y ∈ rescaledGraphSubspace N L ξ c) :
      W.toContinuousLinearMap.adjoint y ∈ rescaledGraphSubspace M J Ω c := by
    apply closure_minimal (s := Set.range (rescaledGraphMap N L ξ c)) ?_
      ((Submodule.isClosed_topologicalClosure _).preimage
        W.toContinuousLinearMap.adjoint.continuous) hy
    rintro _ ⟨b, rfl⟩
    exact hback b
  apply (rescaledGraphSubspace N L ξ c).eq_starProjection_of_mem_of_inner_eq_zero
  · exact hmap ((rescaledGraphSubspace M J Ω c).starProjection_apply_mem v)
  · intro w hw
    change inner ℂ (W v - W (rescaledGraphProjection M J Ω c v)) w = 0
    rw [← map_sub]
    change inner ℂ (W.toContinuousLinearMap _) w = 0
    rw [← ContinuousLinearMap.adjoint_inner_right]
    exact (rescaledGraphSubspace M J Ω c).starProjection_inner_eq_zero v _ (hadj hw)

theorem graphIsometry_resolvent
    (hforward : ∀ a : Algebra M, graphIsometry V J L (rescaledGraphVector J Ω c a.val) ∈
      rescaledGraphSubspace N L ξ c)
    (hback : ∀ b : Algebra N,
      (graphIsometry V J L).toContinuousLinearMap.adjoint (rescaledGraphVector L ξ c b.val) ∈
        rescaledGraphSubspace M J Ω c)
    (x : H) :
    graphResolvent N L ξ c (V x) = V (graphResolvent M J Ω c x) := by
  have h := congrArg (fun v : TomitaGraphHilbert K => v 0)
    (graphIsometry_projection V J L Ω ξ c hforward hback (Generator.tupleSingle 0 x))
  rw [graphIsometry_single_zero, graphIsometry_zero] at h
  exact h

end

end KadisonKastler

end OAI
