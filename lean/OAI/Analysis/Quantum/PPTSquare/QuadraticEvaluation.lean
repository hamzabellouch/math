import OAI.Analysis.Quantum.PPTSquare.QuadraticBasis
import OAI.Analysis.Quantum.PPTSquare.Evaluation

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open Matrix PencilAlgebra PencilEvaluation
namespace QuadraticEvaluation
attribute [local instance] Classical.propDecidable
variable {K : Type*} [Field K]
lemma eval_affine (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 2) (t : Fin 3 → K) :
    p.eval ![1,t 0,t 1,t 2] =
      ∑ j : Fin 10, lowMon t (j.castLE (by decide)) * p.coeff (QuadraticBasis.exponent j) := by
  rw [QuadraticBasis.eval_expansion p hp]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  fin_cases j <;> norm_num [QuadraticBasis.powers, lowMon, lowExp, Fin.prod_univ_succ]

lemma at_most_nine (t : Fin 20 → Fin 3 → K)
    (h : ∀ j : Fin 10 → Fin 20, Function.Injective j →
      IsUnit ((evaluation t).submatrix j (fun k : Fin 10 => k.castLE (by decide)))) :
    ∀ p : MvPolynomial (Fin 4) K, p.IsHomogeneous 2 → p ≠ 0 →
      (Finset.univ.filter (fun i => p.eval ![1,t i 0,t i 1,t i 2] = 0)).card ≤ 9 := by
  classical
  intro p hp hne
  by_contra hnot
  let z := Finset.univ.filter (fun i : Fin 20 => p.eval ![1,t i 0,t i 1,t i 2] = 0)
  have hz : 10 ≤ z.card := by dsimp [z]; omega
  obtain ⟨s,hsub,hcard⟩ := Finset.exists_subset_card_eq hz
  let e : Fin 10 ≃ s := (s.equivFinOfCardEq hcard).symm
  let j : Fin 10 → Fin 20 := fun k => (e k).val
  have hj : Function.Injective j := Subtype.val_injective.comp e.injective
  let c : Fin 10 → K := fun k => p.coeff (QuadraticBasis.exponent k)
  have hc : c ≠ 0 := QuadraticBasis.coefficients_nonzero hp hne
  apply hc
  apply Matrix.mulVec_injective_iff_isUnit.mpr (h j hj)
  rw [Matrix.mulVec_zero]
  ext k
  have hh : p.eval ![1,t (j k) 0,t (j k) 1,t (j k) 2] = 0 :=
    (Finset.mem_filter.mp (hsub (e k).property)).2
  rw [eval_affine p hp] at hh
  exact hh
end QuadraticEvaluation

end

end OAI
