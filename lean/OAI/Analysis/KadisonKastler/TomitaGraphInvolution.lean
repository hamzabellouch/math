import OAI.Analysis.KadisonKastler.TomitaClosedOperator

namespace OAI

/-! # The involution on the closed Tomita graph

Taking adjoints on the algebraic core becomes a continuous conjugate-linear
coordinate swap. Hence its involution identity survives graph closure.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

omit [CompleteSpace H] in
/-- Adjoint on graph vectors, with the fixed second-coordinate identification. -/
def tomitaGraphFlip (J : H ≃ₗᵢ⋆[ℂ] H) : TomitaGraphHilbert H ≃ₗᵢ⋆[ℂ] TomitaGraphHilbert H where
  toFun ξ := WithLp.toLp 2 ![J.symm (ξ 1), J (ξ 0)]
  invFun ξ := WithLp.toLp 2 ![J.symm (ξ 1), J (ξ 0)]
  left_inv ξ := by ext i; fin_cases i <;> simp
  right_inv ξ := by ext i; fin_cases i <;> simp
  map_add' ξ η := by ext i; fin_cases i <;> simp [map_add]
  map_smul' z ξ := by ext i; fin_cases i <;> simp [map_smulₛₗ]
  norm_map' ξ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [Fin.sum_univ_two]
    change ‖J.symm (ξ 1)‖ ^ 2 + ‖J (ξ 0)‖ ^ 2 = ‖ξ 0‖ ^ 2 + ‖ξ 1‖ ^ 2
    rw [J.symm.norm_map, J.norm_map]
    exact add_comm _ _

omit [CompleteSpace H] in
@[simp] theorem tomitaGraphFlip_zero (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : TomitaGraphHilbert H) :
    tomitaGraphFlip J ξ 0 = J.symm (ξ 1) := rfl

omit [CompleteSpace H] in
@[simp] theorem tomitaGraphFlip_one (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : TomitaGraphHilbert H) :
    tomitaGraphFlip J ξ 1 = J (ξ 0) := rfl

theorem tomitaGraphFlip_vector (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (a : Algebra M) :
    tomitaGraphFlip J (rescaledGraphVector J Ω 1 a.val) =
      rescaledGraphVector J Ω 1 (star a.val) := by
  ext i
  fin_cases i <;> simp [rescaledGraphVector]

theorem tomitaGraphFlip_mem (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {ξ : TomitaGraphHilbert H} (hξ : ξ ∈ rescaledGraphSubspace M J Ω 1) :
    tomitaGraphFlip J ξ ∈ rescaledGraphSubspace M J Ω 1 := by
  have hc : IsClosed {v : TomitaGraphHilbert H |
      tomitaGraphFlip J v ∈ rescaledGraphSubspace M J Ω 1} :=
    (rescaledGraphMap M J Ω 1).range.isClosed_topologicalClosure.preimage
      (tomitaGraphFlip J).continuous
  apply closure_minimal (s := Set.range (rescaledGraphMap M J Ω 1)) ?_ hc hξ
  rintro _ ⟨a, rfl⟩
  change tomitaGraphFlip J (rescaledGraphVector J Ω 1 a.val) ∈
    rescaledGraphSubspace M J Ω 1
  rw [tomitaGraphFlip_vector J Ω a]
  exact rescaledGraphVector_mem M J Ω 1 (star a)

theorem rescaledGraph_no_horizontal (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (ξ : TomitaGraphHilbert H) (hξ : ξ ∈ rescaledGraphSubspace M J Ω 1)
    (hzero : ξ 1 = 0) : ξ = 0 := by
  have hflip := rescaledGraph_no_vertical J Ω 1 hsep (tomitaGraphFlip J ξ)
    (tomitaGraphFlip_mem J Ω hξ) (by simp [hzero])
  exact (tomitaGraphFlip J).injective (hflip.trans (map_zero _).symm)

/-- The closed Tomita operator has no kernel. -/
theorem tomitaClosedLinearOperator_injective (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω)) :
    Function.Injective (tomitaClosedLinearOperator M J Ω 1) := by
  intro ξ η he
  have hz : (tomitaClosedLinearOperator M J Ω 1) (ξ - η) = 0 := by
    rw [LinearPMap.map_sub, he, sub_self]
  have hg := LinearPMap.mem_graph (tomitaClosedLinearOperator M J Ω 1) (ξ - η)
  rw [tomitaClosedLinearOperator_graph J Ω 1 hsep] at hg
  have hzero := rescaledGraph_no_horizontal J Ω hsep
    (tomitaProductCoordinates.symm ((ξ - η).val,
      (tomitaClosedLinearOperator M J Ω 1) (ξ - η))) hg hz
  apply sub_eq_zero.mp
  apply Subtype.ext
  exact congrArg (fun v : TomitaGraphHilbert H => v 0) hzero

end

end KadisonKastler

end OAI
