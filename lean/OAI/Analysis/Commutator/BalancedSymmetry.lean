import Mathlib
import OAI.Analysis.Commutator.BalancedDefect

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Matrix

namespace Kadison.BalancedDilation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def symmetry (x : A) : CStarMatrix (Fin 2) (Fin 2) A :=
  CStarMatrix.ofMatrix !![CFC.sqrt (1-x*star x), x; star x, -CFC.sqrt (1-star x*x)]

lemma symmetry_selfAdjoint (x : A) : IsSelfAdjoint (symmetry x) := by
  apply CStarMatrix.ext
  intro i j
  have hl := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (1-x*star x))).star_eq
  have hr := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (1-star x*x))).star_eq
  fin_cases i <;> fin_cases j <;> simp [symmetry,CStarMatrix.star_apply,hl,hr]

lemma symmetry_mul_self (x : A) (hx : ‖x‖≤1) : symmetry x*symmetry x=1 := by
  have h₁ := defect_nonneg x hx
  have h₂ : 0≤1-star x*x := by
    simpa only [star_star] using defect_nonneg (star x) (by simpa using hx)
  have hl := CFC.sqrt_mul_sqrt_self (1-x*star x) h₁
  have hr := CFC.sqrt_mul_sqrt_self (1-star x*x) h₂
  have hi := defect_intertwines x hx
  have hi' := defect_intertwines (star x) (by simpa using hx)
  simp only [star_star] at hi'
  apply CStarMatrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetry,CStarMatrix.mul_apply,Fin.sum_univ_two,hl,hr,hi,hi']

lemma symmetry_unitary (x : A) (hx : ‖x‖≤1) : symmetry x∈unitary (CStarMatrix (Fin 2) (Fin 2) A) := by
  rw [Unitary.mem_iff]
  rw [(symmetry_selfAdjoint x).star_eq,symmetry_mul_self x hx]
  exact ⟨rfl,rfl⟩

lemma symmetry_diagonal_trace (τ : A →ₚ[ℂ] ℂ)
    (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (x : A) (hx : ‖x‖≤1) :
    ∑ i : Fin 2,τ (symmetry x i i)=0 := by
  simp [Fin.sum_univ_two,symmetry,defect_trace τ hτ x hx]

end Kadison.BalancedDilation

end

end
end

end OAI
