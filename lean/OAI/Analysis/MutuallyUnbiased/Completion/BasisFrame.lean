import OAI.Analysis.MutuallyUnbiased.Bases.Basic
import OAI.Analysis.MutuallyUnbiased.Completion.Frame
import OAI.Analysis.MutuallyUnbiased.Completion.OrthogonalPinching

namespace OAI

/-! The rank-one frames associated with actual orthonormal and unbiased bases. -/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators

/-- Ordinary complex coordinates of an orthonormal basis. -/
noncomputable def basisCoordinates (b : MUB6.Basis) : Coord → Coord → ℂ := fun a i => b a i

def traceVector : Coord × Coord → ℂ := fun p => if p.1 = p.2 then 1 else 0

lemma basisCoordinates_unit (b : MUB6.Basis) (a : Coord) :
    ∑ i, star (basisCoordinates b a i) * basisCoordinates b a i = 1 := by
  simpa only [basisCoordinates, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, mul_comm]
    using b.inner_eq_one a

lemma basisCoordinates_complete (b : MUB6.Basis) (i j : Coord) :
    ∑ a, basisCoordinates b a i * star (basisCoordinates b a j) =
      if i = j then 1 else 0 := by
  have h := (EuclideanSpace.basisFun Coord ℂ).toMatrix_orthonormalBasis_self_mul_conjTranspose b
  have hij := congrArg (fun A : CMatrix => A i j) h
  simpa [basisCoordinates, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Module.Basis.toMatrix_apply, Matrix.one_apply] using hij

lemma basis_projectorVector_sum (b : MUB6.Basis) :
    (∑ a, projectorVector (basisCoordinates b a)) = traceVector := by
  funext p
  simpa only [Finset.sum_apply, projectorVector, traceVector] using
    basisCoordinates_complete b p.1 p.2

lemma traceVector_outer : Matrix.vecMulVec traceVector (star traceVector) =
    (traceMatrix : Matrix (Coord × Coord) (Coord × Coord) ℂ) := by
  ext p q
  by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2 <;>
    simp [Matrix.vecMulVec_apply, traceVector, traceMatrix, hp, hq]

lemma basis_projector_inner (b c : MUB6.Basis) (a d : Coord) :
    star (projectorVector (basisCoordinates b a)) ⬝ᵥ
      projectorVector (basisCoordinates c d) =
        inner ℂ (b a) (c d) * star (inner ℂ (b a) (c d)) := by
  rw [projectorVector_inner]
  have h : star (basisCoordinates b a) ⬝ᵥ basisCoordinates c d = inner ℂ (b a) (c d) := by
    change star (b a).ofLp ⬝ᵥ (c d).ofLp = inner ℂ (b a) (c d)
    rw [dotProduct_comm]
    exact (EuclideanSpace.inner_eq_star_dotProduct (b a) (c d)).symm
  rw [h]

lemma basis_pinching_idempotent (b : MUB6.Basis) :
    pinchingMatrix (basisCoordinates b) * pinchingMatrix (basisCoordinates b) =
      pinchingMatrix (basisCoordinates b) := by
  simp only [pinchingMatrix_eq_frameOperator]
  apply frameOperator_idempotent
  intro a c
  rw [basis_projector_inner]
  rw [b.inner_eq_ite]
  split_ifs <;> simp

lemma mub_pinching_mul {m : ℕ} (B : Fin m → MUB6.Basis) (hB : IsMUBFamily B)
    (r s : Fin m) (hrs : r ≠ s) :
    pinchingMatrix (basisCoordinates (B r)) * pinchingMatrix (basisCoordinates (B s)) =
      (1 / 6 : ℂ) • (traceMatrix : Matrix (Coord × Coord) (Coord × Coord) ℂ) := by
  rw [pinchingMatrix_eq_frameOperator, pinchingMatrix_eq_frameOperator]
  have hov : ∀ a b, star (projectorVector (basisCoordinates (B r) a)) ⬝ᵥ
      projectorVector (basisCoordinates (B s) b) = (1 / 6 : ℂ) := by
    intro a b
    rw [basis_projector_inner]
    rw [Complex.star_def, Complex.mul_conj, hB r s hrs a b]
    norm_num
  have h := frameOperator_mul
    (fun a => projectorVector (basisCoordinates (B r) a))
    (fun b => projectorVector (basisCoordinates (B s) b)) (1 / 6 : ℂ) hov
  rwa [basis_projectorVector_sum, basis_projectorVector_sum, traceVector_outer] at h

lemma basis_pinching_unital (b : MUB6.Basis) :
    applySuper (pinchingMatrix (basisCoordinates b)) 1 = 1 :=
  pinchingMatrix_unital (basisCoordinates b) (basisCoordinates_unit b) (basisCoordinates_complete b)

lemma basis_pinching_trace (b : MUB6.Basis) :
    (pinchingMatrix (basisCoordinates b)).trace = 6 := by
  simpa using pinchingMatrix_trace (basisCoordinates b) (basisCoordinates_unit b)

lemma basis_complement_unital (B : Fin 6 → MUB6.Basis) :
    applySuper (complementMatrix (fun r => basisCoordinates (B r))) 1 = 1 :=
  complementMatrix_unital _ (fun r => basisCoordinates_unit (B r))
    (fun r => basisCoordinates_complete (B r))

lemma basis_pinching_pair {m : ℕ} (B : Fin m → MUB6.Basis) (hB : IsMUBFamily B)
    (r s : Fin m) :
    pinchingMatrix (basisCoordinates (B r)) * pinchingMatrix (basisCoordinates (B s)) =
      if r = s then pinchingMatrix (basisCoordinates (B r))
      else (1 / 6 : ℂ) • traceMatrix := by
  split_ifs with h
  · subst s
    exact basis_pinching_idempotent (B r)
  · exact mub_pinching_mul B hB r s h

lemma basis_complement_idempotent (B : Fin 6 → MUB6.Basis) (hB : IsMUBFamily B) :
    complementMatrix (fun r => basisCoordinates (B r)) *
        complementMatrix (fun r => basisCoordinates (B r)) =
      complementMatrix (fun r => basisCoordinates (B r)) :=
  six_complement_idempotent _ (basis_pinching_pair B hB)
    (fun r => pinchingMatrix_hermitian (basisCoordinates (B r)))
    (fun r => basis_pinching_unital (B r))

/-- The Hilbert--Schmidt complement vanishes for seven unbiased bases. -/
theorem complete_basis_complement_eq_zero (B : Fin 7 → MUB6.Basis) (hB : IsMUBFamily B) :
    complementMatrix (fun r => basisCoordinates (B r)) = 0 := by
  apply hermitian_idempotent_eq_zero_of_trace_zero
  · exact complementMatrix_hermitian _
  · exact seven_complement_idempotent _ (basis_pinching_pair B hB)
      (fun r => pinchingMatrix_hermitian (basisCoordinates (B r)))
      (fun r => basis_pinching_unital (B r))
  · norm_num [complementMatrix, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_sum,
      traceMatrix_trace, basis_pinching_trace]

/-- Entrywise fourth moment of a complete family of seven orthonormal bases. -/
theorem complete_basis_fourth_moment (B : Fin 7 → MUB6.Basis) (hB : IsMUBFamily B)
    (i j k l : Coord) :
    (∑ r, ∑ a, B r a i * star (B r a j) * star (B r a k) * B r a l) =
      (if i = k ∧ j = l then 1 else 0) + (if i = j ∧ k = l then 1 else 0) := by
  have h := congrArg (fun C : SuperSix => C (i, j) (k, l))
    (complete_basis_complement_eq_zero B hB)
  simp only [complementMatrix, Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply,
    Matrix.zero_apply] at h
  simpa only [pinchingMatrix, basisCoordinates, Matrix.one_apply, Prod.mk.injEq,
    traceMatrix] using (sub_eq_zero.mp h).symm

/-- A common unitary change of coordinates preserves mutual unbiasedness. -/
lemma isMUBFamily_map {m : ℕ} (B : Fin m → MUB6.Basis) (hB : IsMUBFamily B)
    (U : Space ≃ₗᵢ[ℂ] Space) : IsMUBFamily (fun r => (B r).map U) := by
  intro r s hrs i j
  simpa only [OrthonormalBasis.map_apply, LinearIsometryEquiv.inner_map_map] using hB r s hrs i j

/-- The complete-family fourth moment in coordinates of any reference basis. -/
theorem complete_basis_fourth_moment_relative (B : Fin 7 → MUB6.Basis) (hB : IsMUBFamily B)
    (ref : MUB6.Basis) (i j k l : Coord) :
    (∑ r, ∑ a, inner ℂ (ref i) (B r a) * star (inner ℂ (ref j) (B r a)) *
      star (inner ℂ (ref k) (B r a)) * inner ℂ (ref l) (B r a)) =
      (if i = k ∧ j = l then 1 else 0) + (if i = j ∧ k = l then 1 else 0) := by
  have h := complete_basis_fourth_moment (fun r => (B r).map ref.repr)
    (isMUBFamily_map B hB ref.repr) i j k l
  simpa only [OrthonormalBasis.map_apply, OrthonormalBasis.repr_apply_apply] using h

lemma basis_projectorVector_orthonormal (b : MUB6.Basis) (a d : Coord) :
    star (projectorVector (basisCoordinates b a)) ⬝ᵥ
      projectorVector (basisCoordinates b d) = if a = d then 1 else 0 := by
  rw [basis_projector_inner, b.inner_eq_ite]
  split_ifs <;> simp

lemma basis_pinching_projectorVector (b : MUB6.Basis) (a : Coord) :
    pinchingMatrix (basisCoordinates b) *ᵥ projectorVector (basisCoordinates b a) =
      projectorVector (basisCoordinates b a) := by
  rw [pinchingMatrix_eq_frameOperator]
  exact frameOperator_mulVec_self _ (basis_projectorVector_orthonormal b) a

lemma mub_pinching_projectorVector {m : ℕ} (B : Fin m → MUB6.Basis) (hB : IsMUBFamily B)
    (r s : Fin m) (hrs : r ≠ s) (a : Coord) :
    pinchingMatrix (basisCoordinates (B r)) *ᵥ projectorVector (basisCoordinates (B s) a) =
      (1 / 6 : ℂ) • traceVector := by
  rw [pinchingMatrix_eq_frameOperator]
  have hov : ∀ d, star (projectorVector (basisCoordinates (B r) d)) ⬝ᵥ
      projectorVector (basisCoordinates (B s) a) = (1 / 6 : ℂ) := by
    intro d
    rw [basis_projector_inner, Complex.star_def, Complex.mul_conj, hB r s hrs d a]
    norm_num
  rw [frameOperator_mulVec_of_inner _ _ _ hov, basis_projectorVector_sum]

lemma traceVector_dot_projectorVector (b : MUB6.Basis) (a : Coord) :
    star traceVector ⬝ᵥ projectorVector (basisCoordinates b a) = 1 := by
  simpa [dotProduct, traceVector, projectorVector, Fintype.sum_prod_type, mul_comm] using
    basisCoordinates_unit b a

lemma traceMatrix_projectorVector (b : MUB6.Basis) (a : Coord) :
    traceMatrix *ᵥ projectorVector (basisCoordinates b a) = traceVector := by
  rw [← traceVector_outer, Matrix.vecMulVec_mulVec, traceVector_dot_projectorVector]
  simp

lemma basis_complement_projectorVector (B : Fin 6 → MUB6.Basis) (hB : IsMUBFamily B)
    (r : Fin 6) (a : Coord) :
    complementMatrix (fun s => basisCoordinates (B s)) *ᵥ
        projectorVector (basisCoordinates (B r) a) = (1 / 6 : ℂ) • traceVector := by
  let v := projectorVector (basisCoordinates (B r) a)
  let w := (1 / 6 : ℂ) • traceVector
  have hterm (s : Fin 6) : pinchingMatrix (basisCoordinates (B s)) *ᵥ v =
      (if s = r then v - w else 0) + w := by
    by_cases hsr : s = r
    · subst s
      simp [v, basis_pinching_projectorVector]
    · simp only [hsr, ite_false, zero_add]
      exact mub_pinching_projectorVector B hB s r hsr a
  change (1 + traceMatrix - ∑ s, pinchingMatrix (basisCoordinates (B s))) *ᵥ v = w
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec]
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [show traceMatrix *ᵥ v = traceVector from traceMatrix_projectorVector (B r) a]
  funext p
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, w, smul_eq_mul]
  norm_num
  ring

end MUB6.Weiner

end OAI
