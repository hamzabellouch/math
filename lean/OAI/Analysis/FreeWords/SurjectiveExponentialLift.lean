import Mathlib
import OAI.Analysis.FreeWords.ExponentialUnitaryApprox

namespace OAI

noncomputable section

namespace KKVariableUltra

open KKTraceTransfer

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem selfAdjoint_preimage (φ : A →⋆ₐ[ℂ] B) (hsur : Function.Surjective φ)
    (b : selfAdjoint B) : ∃ a : selfAdjoint A, φ a.val=b.val := by
  obtain ⟨x,hx⟩ := hsur b.val
  let y := (2:ℂ)⁻¹ • (x+star x)
  have hy : IsSelfAdjoint y := by
    change star y=y
    simp [y,star_smul,star_add,add_comm]
  refine ⟨⟨y,hy⟩,?_⟩
  change φ ((2:ℂ)⁻¹ • (x+star x))=b.val
  rw [map_smul,map_add,map_star,hx,b.property.star_eq]
  rw [← two_smul ℂ,smul_smul]
  norm_num

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitary_dense_image (M : VonNeumannAlgebra H)
    (φ : A →⋆ₐ[ℂ] ConcreteAlgebra M) (hsur : Function.Surjective φ)
    (u : unitary (ConcreteAlgebra M)) (ε : ℝ) (hε : 0<ε) :
    ∃ v : unitary A, ‖u.val-φ v.val‖<ε := by
  obtain ⟨b,hb⟩ := unitary_exponential_approximation M u ε hε
  obtain ⟨a,ha⟩ := selfAdjoint_preimage φ hsur b
  refine ⟨(selfAdjoint.expUnitary a),?_⟩
  rw [map_expUnitary]
  have he : (⟨φ a.val,a.property.map φ⟩ : selfAdjoint (ConcreteAlgebra M))=b := Subtype.ext ha
  rw [he]
  exact hb

end

end KKVariableUltra
end

end OAI
