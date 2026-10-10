import Mathlib
import OAI.Analysis.Commutator.IntertwinerCompression

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

open ContinuousLinearMap

namespace Kadison.IntertwinerCompression

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

lemma transfer_raw_commutator (T : H →L[ℂ] G) (A : H →L[ℂ] H) (B : G →L[ℂ] G)
    (hleft : T.comp A=B.comp T) (hright : T.adjoint.comp B=A.comp T.adjoint)
    (Y : H →L[ℂ] H) :
    transfer T (Y*A-A*Y)=transfer T Y*B-B*transfer T Y := by
  have hl : transfer T (A*Y)=B*transfer T Y := by
    simp only [transfer,mul_def,←comp_assoc]
    rw [hleft]
  have hr : transfer T (Y*A)=transfer T Y*B := by
    simp only [transfer,mul_def,comp_assoc]
    rw [hright]
  rw [transfer_sub,hl,hr]

lemma transfer_raw_commutator_norm_le (T : H →L[ℂ] G) (hcon : ‖T‖≤1)
    (A : H →L[ℂ] H) (B : G →L[ℂ] G)
    (hleft : T.comp A=B.comp T) (hright : T.adjoint.comp B=A.comp T.adjoint)
    (Y : H →L[ℂ] H) :
    ‖transfer T Y*B-B*transfer T Y‖≤‖Y*A-A*Y‖ := by
  rw [←transfer_raw_commutator T A B hleft hright]
  exact transfer_norm_le T hcon _

variable {A : Type*} [CStarAlgebra A]

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G))

variable (T : H →L[ℂ] G) (hT : ∀ a,T.comp (φ a)=(ψ a).comp T)

include hT

lemma pullback_matrix_commutator_norm_le (hcon : ‖T‖≤1) (h : ℕ)
    (X : Matrix (Fin h) (Fin h) A) (Z : G →L[ℂ] G) :
    ‖diagonalAmplification h (transfer T.adjoint Z)*matrixOperator h (fun i j => φ (X i j))-
      matrixOperator h (fun i j => φ (X i j))*diagonalAmplification h (transfer T.adjoint Z)‖≤
    ‖diagonalAmplification h Z*matrixOperator h (fun i j => ψ (X i j))-
      matrixOperator h (fun i j => ψ (X i j))*diagonalAmplification h Z‖ := by
  rw [amplify_transfer]
  apply transfer_raw_commutator_norm_le
  · exact (HilbertFiniteMaps.amplify_norm_le _ _).trans (by simpa only [adjoint.norm_map] using hcon)
  · exact amplify_intertwines ψ φ T.adjoint (adjoint_intertwines φ ψ T hT) h X
  · rw [←HilbertFiniteMaps.amplify_adjoint,adjoint_adjoint]
    exact amplify_intertwines φ ψ T hT h X

omit hT

lemma transfer_back (Y : H →L[ℂ] H) :
    transfer T.adjoint (transfer T Y)=(T.adjoint.comp T)*Y*(T.adjoint.comp T) := by
  simp only [transfer,adjoint_adjoint,mul_def,comp_assoc]

end Kadison.IntertwinerCompression

end

end
end

end OAI
