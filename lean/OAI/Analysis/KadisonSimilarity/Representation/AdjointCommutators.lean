import OAI.Analysis.KadisonSimilarity.Representation.Amplification

namespace OAI

/-! The adjoint version of a scalar corner estimate, used in propagation. -/

noncomputable section

namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Taking adjoints exchanges the two commutator factors and changes the sign. -/
theorem commutator_adjoint_left (Y X : H →L[ℂ] H) :
    commutator (star Y) X = -star (commutator Y (star X)) := by
  simp only [commutator, star_sub, star_mul, star_star, neg_sub]

theorem norm_commutator_adjoint_left (Y X : H →L[ℂ] H) :
    ‖commutator (star Y) X‖ = ‖commutator Y (star X)‖ := by
  rw [commutator_adjoint_left, norm_neg]
  exact ContinuousLinearMap.adjoint.norm_map _

/-- A scalar commutator estimate on a star algebra also holds for the adjoint
operator, with precisely the same constant. -/
theorem scalarCommutatorNorm_adjoint (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H) :
    scalarCommutatorNorm P (star Y) = scalarCommutatorNorm P Y := by
  have hle (Z : H →L[ℂ] H) : scalarCommutatorNorm P (star Z) ≤ scalarCommutatorNorm P Z := by
    apply (scalarCommutatorNorm_le_iff P (star Z) (scalarCommutatorNorm_nonneg P Z)).mpr
    intro X hX
    rw [norm_commutator_adjoint_left]
    have h := norm_commutator_le_scalarCommutatorNorm P Z (star X) (star_mem hX)
    have hn : ‖star X‖ = ‖X‖ := ContinuousLinearMap.adjoint.norm_map X
    rw [hn] at h
    exact h
  exact le_antisymm (hle Y) (by simpa only [star_star] using hle (star Y))

end KadisonSimilarity

end

end OAI
