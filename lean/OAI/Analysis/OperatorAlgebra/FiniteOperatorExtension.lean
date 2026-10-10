import OAI.Analysis.Nuclearity.MatrixCPMapExtension

namespace OAI

/-! Finite-dimensional Hilbert-operator form of the matrix cpc extension
theorem. An orthonormal basis transports the matrix extension without changing
its positivity or norm. -/

noncomputable section
open scoped InnerProductSpace CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {A B E : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E] [Nontrivial E]

theorem finiteOperator_cpc_extension (ι : A →⋆ₐ[ℂ] B) (hι : Function.Injective ι)
    (φ : A →L[ℂ] (E →L[ℂ] E)) (hφ : CompletelyPositive φ) (hφn : ‖φ‖ ≤ 1) :
    ∃ Φ : B →L[ℂ] (E →L[ℂ] E), CompletelyPositive Φ ∧ ‖Φ‖ ≤ 1 ∧
      ∀ a, Φ (ι a) = φ a := by
  let n := Module.finrank ℂ E
  have hn : 0 < n := Module.finrank_pos
  let b := stdOrthonormalBasis ℂ E
  let e : (E →L[ℂ] E) ≃⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) ℂ :=
    b.repr.conjStarAlgEquiv.trans (scalarMatrixOperatorEquiv (Fin n)).symm
  let eL := starHomContinuousLinear e.toStarAlgHom.toNonUnitalStarAlgHom
  let φ' := eL.comp φ
  have hφ' : CompletelyPositive φ' := completelyPositive_comp _ _ hφ
    (starHomContinuous_completelyPositive _)
  have hφ'n : ‖φ'‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro a
    change ‖e (φ a)‖ ≤ _
    exact (NonUnitalStarAlgHom.norm_apply_le e.toStarAlgHom.toNonUnitalStarAlgHom
      (φ a)).trans ((φ.le_opNorm a).trans
        (mul_le_mul_of_nonneg_right hφn (norm_nonneg a)))
  obtain ⟨Φ', hΦ', hΦ'n, hΦ'e⟩ := matrix_cpc_extension (⟨0, hn⟩ : Fin n) ι hι φ' hφ' hφ'n
  let dL := starHomContinuousLinear e.symm.toStarAlgHom.toNonUnitalStarAlgHom
  let Φ := dL.comp Φ'
  refine ⟨Φ, completelyPositive_comp _ _ hΦ' (starHomContinuous_completelyPositive _), ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro a
    change ‖e.symm (Φ' a)‖ ≤ _
    exact (NonUnitalStarAlgHom.norm_apply_le e.symm.toStarAlgHom.toNonUnitalStarAlgHom
      (Φ' a)).trans ((Φ'.le_opNorm a).trans
        (mul_le_mul_of_nonneg_right hΦ'n (norm_nonneg a)))
  · intro a
    change e.symm (Φ' (ι a)) = φ a
    rw [hΦ'e]
    exact e.symm_apply_apply (φ a)

end WeakPureInfiniteness

end

end OAI
