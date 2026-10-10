import Mathlib
import OAI.Analysis.Commutator.HilbertFiniteMaps
import OAI.Analysis.Commutator.MainMatrix

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder

open ContinuousLinearMap

namespace Kadison.IntertwinerCompression

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable {A : Type*} [CStarAlgebra A]

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G))

variable (T : H →L[ℂ] G) (hT : ∀ a,T.comp (φ a)=(ψ a).comp T)

def transfer (Y : H →L[ℂ] H) : G →L[ℂ] G := T.comp (Y.comp T.adjoint)

include hT

lemma adjoint_intertwines (a : A) : T.adjoint.comp (ψ a)=(φ a).comp T.adjoint := by
  have h := congrArg (fun U : H →L[ℂ] G => U.adjoint) (hT (star a))
  simpa only [adjoint_comp,map_star,star_eq_adjoint,adjoint_adjoint] using h.symm

lemma transfer_left (Y : H →L[ℂ] H) (a : A) :
    transfer T (φ a*Y)=ψ a*transfer T Y := by
  simp only [transfer,mul_def,←comp_assoc]
  rw [hT a]

lemma transfer_right (Y : H →L[ℂ] H) (a : A) :
    transfer T (Y*φ a)=transfer T Y*ψ a := by
  simp only [transfer,mul_def,comp_assoc]
  rw [adjoint_intertwines φ ψ T hT]

omit hT

lemma transfer_sub (Y Z : H →L[ℂ] H) : transfer T (Y-Z)=transfer T Y-transfer T Z := by
  simp only [transfer,comp_sub,sub_comp]

lemma transfer_norm_le (hcon : ‖T‖≤1) (Y : H →L[ℂ] H) : ‖transfer T Y‖≤‖Y‖ := by
  calc
    _≤‖T‖*(‖Y‖*‖T.adjoint‖) := (opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
    _≤1*(‖Y‖*1) := mul_le_mul hcon
      (mul_le_mul_of_nonneg_left (by simpa only [adjoint.norm_map] using hcon) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _=‖Y‖ := by ring

include hT

lemma transfer_commutator (Y : H →L[ℂ] H) (a : A) :
    transfer T (Y*φ a-φ a*Y)=transfer T Y*ψ a-ψ a*transfer T Y := by
  rw [transfer_sub,transfer_left φ ψ T hT,transfer_right φ ψ T hT]

lemma transfer_commutator_norm_le (hcon : ‖T‖≤1) (Y : H →L[ℂ] H) (a : A) :
    ‖transfer T Y*ψ a-ψ a*transfer T Y‖≤‖Y*φ a-φ a*Y‖ := by
  rw [←transfer_commutator φ ψ T hT]
  exact transfer_norm_le T hcon _

include hT

lemma amplify_intertwines (h : ℕ) (X : Matrix (Fin h) (Fin h) A) :
    (HilbertFiniteMaps.amplify (Fin h) T).comp (matrixOperator h (fun i j => φ (X i j)))=
      (matrixOperator h (fun i j => ψ (X i j))).comp (HilbertFiniteMaps.amplify (Fin h) T) := by
  ext x i
  change T (matrixOperator h (fun i j => φ (X i j)) x i)=
    matrixOperator h (fun i j => ψ (X i j)) (HilbertFiniteMaps.amplify (Fin h) T x) i
  rw [@Kadison.matrixOperator_apply H _ _ h (fun i j => φ (X i j)) x i,
    @Kadison.matrixOperator_apply G _ _ h (fun i j => ψ (X i j)) (HilbertFiniteMaps.amplify (Fin h) T x) i,
    map_sum]
  simp only [HilbertFiniteMaps.amplify_apply]
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun U : H →L[ℂ] G => U (x j)) (hT (X i j))

omit hT

lemma amplify_transfer (h : ℕ) (Y : H →L[ℂ] H) :
    diagonalAmplification h (transfer T Y)=
      transfer (HilbertFiniteMaps.amplify (Fin h) T) (diagonalAmplification h Y) := by
  change HilbertFiniteMaps.amplify (Fin h) (transfer T Y)=_
  rw [transfer,HilbertFiniteMaps.amplify_comp,HilbertFiniteMaps.amplify_comp,
    HilbertFiniteMaps.amplify_adjoint]
  rfl

end Kadison.IntertwinerCompression

end

end
end

end OAI
