import OAI.Analysis.GroupDeterminants.ShearTrace

namespace OAI

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant
section TransferTrace
variable {G r m : Type} [Group G] [Fintype r] [Fintype m] [DecidableEq r] [DecidableEq m]

def topBlockIdentity : Matrix (r ⊕ m) (r ⊕ m) (MonoidAlgebra ℂ G) :=
  Matrix.fromBlocks 1 0 0 0

def bottomBlock (P : Matrix m m (MonoidAlgebra ℂ G)) :
    Matrix (r ⊕ m) (r ⊕ m) (MonoidAlgebra ℂ G) := Matrix.fromBlocks 0 0 0 P

def lowerNil (U : Matrix m r (MonoidAlgebra ℂ G)) :
    Matrix (r ⊕ m) (r ⊕ m) (MonoidAlgebra ℂ G) := Matrix.fromBlocks 0 0 U 0

def upperNil (V : Matrix r m (MonoidAlgebra ℂ G)) :
    Matrix (r ⊕ m) (r ⊕ m) (MonoidAlgebra ℂ G) := Matrix.fromBlocks 0 V 0 0

lemma lowerNil_square (U : Matrix m r (MonoidAlgebra ℂ G)) : lowerNil U * lowerNil U = 0 := by
  simp [lowerNil, Matrix.fromBlocks_multiply, Matrix.fromBlocks_zero]
lemma upperNil_square (V : Matrix r m (MonoidAlgebra ℂ G)) : upperNil V * upperNil V = 0 := by
  simp [upperNil, Matrix.fromBlocks_multiply, Matrix.fromBlocks_zero]
omit [Fintype r] [Fintype m] in
lemma lowerShear_eq_one_add (U : Matrix m r (MonoidAlgebra ℂ G)) :
    lowerShear U = 1 + lowerNil U := by
  rw [lowerShear, lowerNil, ← Matrix.fromBlocks_one, Matrix.fromBlocks_add]
  simp
omit [Fintype r] [Fintype m] in
lemma upperShear_eq_one_add (V : Matrix r m (MonoidAlgebra ℂ G)) :
    upperShear V = 1 + upperNil V := by
  rw [upperShear, upperNil, ← Matrix.fromBlocks_one, Matrix.fromBlocks_add]
  simp

lemma transfer_diagonal_weightedPair (q : ℝ) (P : Matrix m m (MonoidAlgebra ℂ G)) :
    Matrix.fromBlocks (q • (1 : Matrix r r (MonoidAlgebra ℂ G))) 0 0
      (projectionReweight P (-q⁻¹) (-1 : ℝ)) =
      weightedPair topBlockIdentity (bottomBlock P) q (-q⁻¹) (-1) := by
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · by_cases hij : i = j <;>
      simp [weightedPair, topBlockIdentity, bottomBlock, Matrix.fromBlocks, hij]
  · simp [weightedPair, topBlockIdentity, bottomBlock, Matrix.fromBlocks]
  · simp [weightedPair, topBlockIdentity, bottomBlock, Matrix.fromBlocks]
  · simp [weightedPair, topBlockIdentity, bottomBlock, projectionReweight,
      Matrix.fromBlocks, Matrix.one_apply]

lemma transfer_trace_log (q : ℝ) (hq : 0 < q)
    (P : Matrix m m (MonoidAlgebra ℂ G)) (hP : P * P = P)
    (U : Matrix m r (MonoidAlgebra ℂ G)) (V : Matrix r m (MonoidAlgebra ℂ G)) :
    let M := indexedComplexRepresentation (transferMatrix q P U V)
    groupTrace (CFC.log (star M * M)) =
      (2 * ((Fintype.card r : ℝ) - (∑ i, (P i i).coeff 1).re) * Real.log q : ℝ) := by
  let Q : Matrix (r ⊕ m) (r ⊕ m) (MonoidAlgebra ℂ G) := topBlockIdentity
  let R : Matrix (r ⊕ m) (r ⊕ m) (MonoidAlgebra ℂ G) := bottomBlock P
  have hQ : Q * Q = Q := by simp [Q, topBlockIdentity, Matrix.fromBlocks_multiply]
  have hR : R * R = R := by simp [R, bottomBlock, Matrix.fromBlocks_multiply, hP]
  have hQR : Q * R = 0 := by
    simp [Q, R, topBlockIdentity, bottomBlock, Matrix.fromBlocks_multiply, Matrix.fromBlocks_zero]
  have hRQ : R * Q = 0 := by
    simp [Q, R, topBlockIdentity, bottomBlock, Matrix.fromBlocks_multiply, Matrix.fromBlocks_zero]
  have hQs : IsSelfAdjoint Q := by
    change Matrix.conjTranspose Q = Q
    simp [Q, topBlockIdentity, Matrix.fromBlocks_conjTranspose]
  let B := weightedPair Q R q (-q⁻¹) (-1)
  have hB : IsUnit B := weightedPair_unit Q R hQ hR hQR hRQ _ _ _
    hq.ne' (neg_ne_zero.mpr (inv_ne_zero hq.ne')) (by norm_num)
  let S := lowerNil (q⁻¹ • U)
  let T := upperNil (q⁻¹ • V)
  have htS : ∑ i, (S i i).coeff 1 = 0 := by simp [S, lowerNil, Fintype.sum_sum_type]
  have htT : ∑ i, (T i i).coeff 1 = 0 := by simp [T, upperNil, Fintype.sum_sum_type]
  have hf : transferMatrix q P U V = (1 + S) * B * (1 + T) := by
    rw [← transferMatrix_factorization q hq.ne', transfer_diagonal_weightedPair,
      lowerShear_eq_one_add, upperShear_eq_one_add]
  have H := indexed_trace_log_shear B S T hB (lowerNil_square _) (upperNil_square _) htS htT
  have H' := indexed_trace_log_weightedPair Q R hQ hR hQR hRQ hQs (Real.log q)
  have hexp : Real.exp (Real.log q) = q := Real.exp_log hq
  have hexpn : Real.exp (-Real.log q) = q⁻¹ := by rw [Real.exp_neg, hexp]
  dsimp only at H H' ⊢
  rw [hf, H]
  have ht : (∑ i, ((Q - R) i i).coeff 1) =
      (Fintype.card r : ℂ) - ∑ i, (P i i).coeff 1 := by
    simp [Q, R, topBlockIdentity, bottomBlock, Fintype.sum_sum_type]
  rw [hexp, hexpn, ht] at H'
  calc
    _ = ((Real.log q * (2 * ((Fintype.card r : ℂ) - ∑ i, (P i i).coeff 1).re) : ℝ) : ℂ) := H'
    _ = _ := by congr 1; simp only [Complex.sub_re, Complex.natCast_re]; ring

end TransferTrace
end GroupRingDeterminant

end

end OAI
