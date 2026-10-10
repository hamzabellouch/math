import OAI.Analysis.Pureness.Stabilization.MatrixPositive
import Mathlib.Logic.Equiv.Fintype

namespace OAI
noncomputable section
open scoped CStarAlgebra
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A]

def matrixPermute {n : ℕ} (e : Equiv.Perm (Fin n)) : FinMatrix A n →⋆ₙₐ[ℂ] FinMatrix A n :=
  (CStarMatrix.reindexₐ ℂ A e).toNonUnitalStarAlgHom

@[simp] theorem matrixPermute_entry {n : ℕ} (e : Equiv.Perm (Fin n))
    (M : FinMatrix A n) (i j : Fin n) : matrixPermute e M (e i) (e j) = M i j := by
  change M (e.symm (e i)) (e.symm (e j)) = M i j
  simp

variable [PartialOrder A] [StarOrderedRing A]

private lemma exists_selfAdjoint_square_root (a : Positive A) :
    ∃ b : A, star b = b ∧ b * b = a.1 :=
  ⟨CFC.sqrt a.1, (CFC.sqrt_nonneg a.1).star_eq, CFC.sqrt_mul_sqrt_self a.1 a.2⟩

theorem matrixPermute_factorization {n : ℕ} (e : Equiv.Perm (Fin n))
    (a : Positive (FinMatrix A n)) :
    ∃ x : FinMatrix A n, star x*x = a.1 ∧ x*star x = matrixPermute e a.1 := by
  obtain ⟨b, hb, hbb⟩ := exists_selfAdjoint_square_root a
  let x : FinMatrix A n := CStarMatrix.ofMatrix (fun i j => b (e.symm i) j)
  refine ⟨x, ?_, ?_⟩
  · apply CStarMatrix.ext; intro i j
    change (∑ k : Fin n, star (b (e.symm k) i) * b (e.symm k) j) = a.1 i j
    rw [e.symm.sum_comp (fun k => star (b k i)*b k j)]
    change (star b*b) i j = a.1 i j
    rw [hb,hbb]
  · apply CStarMatrix.ext; intro i j
    obtain ⟨i,rfl⟩ := e.surjective i
    obtain ⟨j,rfl⟩ := e.surjective j
    rw [matrixPermute_entry]
    change (∑ k : Fin n, b (e.symm (e i)) k * star (b (e.symm (e j)) k)) = a.1 i j
    simp only [Equiv.symm_apply_apply]
    change (b*star b) i j = a.1 i j
    rw [hb,hbb]

theorem matrixPermute_cuntzClass {n : ℕ} (e : Equiv.Perm (Fin n))
    (a : Positive (FinMatrix A n)) :
    CuntzClass.mk (Positive.map (matrixPermute e) a) = CuntzClass.mk a := by
  obtain ⟨x,hx,hy⟩ := matrixPermute_factorization e a
  have hs : Positive.starMul x = a := Subtype.ext hx
  have ht : Positive.mulStar x = Positive.map (matrixPermute e) a := Subtype.ext hy
  apply (CuntzClass.mk_eq_mk_iff _ _).mpr
  rw [← ht,← hs]
  exact ⟨mulStar_cuntzBelow_starMul x,starMul_cuntzBelow_mulStar x⟩
end CuntzTrace

end

end OAI
