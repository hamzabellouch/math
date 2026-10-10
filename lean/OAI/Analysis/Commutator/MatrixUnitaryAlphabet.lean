import Mathlib
import OAI.Analysis.Commutator.MatrixCutEmbedding

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder Matrix

namespace Kadison.MatrixCorners

attribute [local instance] Classical.propDecidable

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

def shiftMatrix (g : G) : Matrix G G ℂ := (Equiv.addLeft g).permMatrix ℂ

lemma shift_trace (g : G) : (shiftMatrix g).trace=if g=0 then (Fintype.card G:ℂ) else 0 := by
  rw [shiftMatrix,Matrix.trace_permutation]
  by_cases hg : g=0
  · subst g
    simp
  · have he : Function.fixedPoints (Equiv.addLeft g)=∅ := by
      ext x
      simp [Function.fixedPoints,Function.IsFixedPt,hg]
    simp only [he,Set.ncard_empty,Nat.cast_zero,ite_eq_right hg]

lemma shift_star_mul (g h : G) : star (shiftMatrix g)*shiftMatrix h=shiftMatrix (h-g) := by
  change (shiftMatrix g).conjTranspose*shiftMatrix h=_
  simp only [shiftMatrix,Matrix.conjTranspose_permMatrix,←Matrix.permMatrix_mul]
  congr 1
  ext x
  simp [sub_eq_add_neg]

lemma shift_mul_star (g h : G) : shiftMatrix g*star (shiftMatrix h)=shiftMatrix (g-h) := by
  change shiftMatrix g*(shiftMatrix h).conjTranspose=_
  simp only [shiftMatrix,Matrix.conjTranspose_permMatrix,←Matrix.permMatrix_mul]
  congr 1
  ext x
  simp [sub_eq_add_neg,add_comm,add_assoc]

omit [Fintype G] in
lemma shift_zero : shiftMatrix (0:G)=1 := by
  change (Equiv.addLeft (0:G)).permMatrix ℂ=1
  have he : Equiv.addLeft (0:G)=Equiv.refl G := by ext x; simp
  rw [he,Matrix.permMatrix_refl]

lemma shift_unitary (g : G) : shiftMatrix g ∈ unitary (Matrix G G ℂ) := by
  apply Unitary.mem_iff.mpr
  constructor
  · rw [shift_star_mul,sub_self,shift_zero]
  · rw [shift_mul_star,sub_self,shift_zero]

lemma shift_gram (g h : G) : (star (shiftMatrix g)*shiftMatrix h).trace=
    if g=h then (Fintype.card G:ℂ) else 0 := by
  rw [shift_star_mul,shift_trace]
  simp [sub_eq_zero,eq_comm]

def projectionAlphabet (p : Matrix I I ℂ) (hp : IsStarProjection p)
    (e : G ≃ projectionIndices p hp) (g : G) : Matrix I I ℂ :=
  projectionEmbedding p hp (reindexStarAlgEquiv e (shiftMatrix g))

lemma projectionAlphabet_trace (p : Matrix I I ℂ) (hp : IsStarProjection p)
    (e : G ≃ projectionIndices p hp) (g : G) :
    (projectionAlphabet p hp e g).trace=if g=0 then (Fintype.card G:ℂ) else 0 := by
  rw [projectionAlphabet,projectionEmbedding_trace]
  change (Matrix.reindex e e (shiftMatrix g)).trace=_
  rw [trace_reindex,shift_trace]

lemma projectionAlphabet_star_mul (p : Matrix I I ℂ) (hp : IsStarProjection p)
    (e : G ≃ projectionIndices p hp) (g : G) :
    star (projectionAlphabet p hp e g)*projectionAlphabet p hp e g=p := by
  unfold projectionAlphabet
  rw [←map_star,←map_mul,←map_star,←map_mul,shift_star_mul,sub_self,shift_zero,
    map_one,projectionEmbedding_one]

lemma projectionAlphabet_support (p : Matrix I I ℂ) (hp : IsStarProjection p)
    (e : G ≃ projectionIndices p hp) (g : G) : projectionAlphabet p hp e g*p=
      projectionAlphabet p hp e g := by
  change projectionEmbedding p hp _ * p=projectionEmbedding p hp _
  conv_lhs => rhs; rw [←projectionEmbedding_one p hp]
  rw [←map_mul,mul_one]

lemma projectionAlphabet_gram (p : Matrix I I ℂ) (hp : IsStarProjection p)
    (e : G ≃ projectionIndices p hp) (g h : G) :
    (star (projectionAlphabet p hp e g)*projectionAlphabet p hp e h).trace=
      if g=h then (Fintype.card G:ℂ) else 0 := by
  unfold projectionAlphabet
  rw [←map_star,←map_mul,projectionEmbedding_trace,←map_star,←map_mul]
  change (Matrix.reindex e e (star (shiftMatrix g)*shiftMatrix h)).trace=_
  rw [trace_reindex,shift_gram]

end Kadison.MatrixCorners

end

end
end

end OAI
