import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Algebra.Algebra.Subalgebra.Basic

namespace OAI

/-! # Algebra evaluation from an invariant reproducing-kernel quotient

The Hardy-space evaluation is a compression. Multiplicativity follows when
its kernel is invariant and the operators preserve the positive-frequency
space.
-/

namespace KadisonKastler

noncomputable section

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The compression used for Hardy evaluation. The first identity preserves
the positive-frequency space on the kernel vectors, and the second expresses
invariance of the evaluation kernel inside that space. -/
def hardyCompressionAlgHom (A : Subalgebra ℂ (E →L[ℂ] E))
    (i : H →L[ℂ] E) (j : E →L[ℂ] H) (P : E →L[ℂ] E)
    (hji : j.comp i = ContinuousLinearMap.id ℂ H)
    (hleft : ∀ T : A, P.comp (T.val.comp i) = T.val.comp i)
    (hright : ∀ T : A,
      (j.comp T.val).comp P = ((j.comp T.val).comp i).comp j) :
    A →ₐ[ℂ] (H →L[ℂ] H) where
  toFun T := (j.comp T.val).comp i
  map_one' := by
    change (j.comp (ContinuousLinearMap.id ℂ E)).comp i = ContinuousLinearMap.id ℂ H
    rw [ContinuousLinearMap.comp_id, hji]
  map_zero' := by simp
  map_add' T S := by simp [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  map_mul' T S := by
    change (j.comp (T.val.comp S.val)).comp i =
      ((j.comp T.val).comp i).comp ((j.comp S.val).comp i)
    calc
      _ = (j.comp T.val).comp (S.val.comp i) := by
        simp only [ContinuousLinearMap.comp_assoc]
      _ = (j.comp T.val).comp (P.comp (S.val.comp i)) := by rw [hleft S]
      _ = ((j.comp T.val).comp P).comp (S.val.comp i) := by
        simp only [ContinuousLinearMap.comp_assoc]
      _ = (((j.comp T.val).comp i).comp j).comp (S.val.comp i) := by rw [hright T]
      _ = _ := by simp only [ContinuousLinearMap.comp_assoc]
  commutes' z := by
    change (j.comp (z • ContinuousLinearMap.id ℂ E)).comp i =
      z • ContinuousLinearMap.id ℂ H
    simp only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id,
      ContinuousLinearMap.smul_comp, hji]

@[simp] theorem hardyCompressionAlgHom_apply (A : Subalgebra ℂ (E →L[ℂ] E))
    (i : H →L[ℂ] E) (j : E →L[ℂ] H) (P : E →L[ℂ] E)
    (hji : j.comp i = ContinuousLinearMap.id ℂ H)
    (hleft : ∀ T : A, P.comp (T.val.comp i) = T.val.comp i)
    (hright : ∀ T : A,
      (j.comp T.val).comp P = ((j.comp T.val).comp i).comp j) (T : A) :
    hardyCompressionAlgHom A i j P hji hleft hright T = (j.comp T.val).comp i := rfl

end

end KadisonKastler

end OAI
