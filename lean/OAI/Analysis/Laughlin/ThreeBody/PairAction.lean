import OAI.Analysis.Laughlin.Fock.Hamiltonian
import OAI.Analysis.Laughlin.ThreeBody.Contraction

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def threeBodyColumn (Q p : ℕ) (k : Fin (Q+1)) : Space Q :=
  sourcePairCreateEnd Q p (create k (1 : Space Q))

theorem sourcePairCreate_apply (Q p : ℕ) (x : Space Q) :
    sourcePairCreateEnd Q p x = ∑ i, ∑ j,
      ((pairCoefficient Q p i j / Real.sqrt 2 : ℝ) : ℂ) • create i (create j x) := by
  simp [sourcePairCreateEnd,pairCreateEnd,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply]

theorem pair_weight_difference (Q p : ℕ) (i j : Fin (Q+1)) :
    pairCoefficient Q p i j / Real.sqrt 2 - pairCoefficient Q p j i / Real.sqrt 2 =
      Real.sqrt 2 * pairCoefficient Q p i j := by
  rw [pairCoefficient_swap Q p i j]
  have hne : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  calc
    _ = 2*pairCoefficient Q p i j / Real.sqrt 2 := by ring
    _ = (Real.sqrt 2*Real.sqrt 2)*pairCoefficient Q p i j / Real.sqrt 2 := by
      rw [Real.mul_self_sqrt (by norm_num)]
    _ = _ := by field_simp

theorem pair_weight_product (Q p q : ℕ) (i j k l : Fin (Q+1)) :
    ((pairCoefficient Q q i j / Real.sqrt 2 : ℝ) : ℂ) *
      (((pairCoefficient Q p k l / Real.sqrt 2 : ℝ) : ℂ) -
       ((pairCoefficient Q p l k / Real.sqrt 2 : ℝ) : ℂ)) =
      (pairCoefficient Q q i j : ℂ) * (pairCoefficient Q p k l : ℂ) := by
  rw [← Complex.ofReal_sub,pair_weight_difference]
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (show Real.sqrt (2 : ℝ) ≠ 0 by positivity)
  push_cast
  field_simp

theorem sourcePair_threeBodyColumn (Q p q : ℕ) (hQ : 2 ≤ Q) (hp : p ≤ 2*Q-2)
    (k : Fin (Q+1)) :
    sourcePairEnd Q p (threeBodyColumn Q q k) =
      (if p = q then (1 : ℂ) else 0) • create k (1 : Space Q) -
      (2 : ℂ) • (∑ i, ∑ j, ((pairCoefficient Q q i j : ℂ) * (pairCoefficient Q p i k : ℂ)) •
        create j (1 : Space Q)) := by
  let F : Space Q := ∑ i, ∑ j, ((pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p i j : ℂ)) • create k (1 : Space Q)
  let U : Space Q := ∑ i, ∑ j, ((pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p i k : ℂ)) • create j (1 : Space Q)
  let V : Space Q := ∑ i, ∑ j, ((pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p j k : ℂ)) • create i (1 : Space Q)
  have hexp : sourcePairEnd Q p (threeBodyColumn Q q k) = F-U+V := by
    rw [threeBodyColumn,sourcePairCreate_apply]
    simp only [map_sum,map_smul,sourcePairEnd,pairEnd_three_create,
      smul_add,smul_sub,smul_smul,pair_weight_product]
    simp only [F,U,V,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hF : F = (if p = q then (1 : ℂ) else 0) • create k (1 : Space Q) := by
    dsimp [F]
    simp only [← Finset.sum_smul]
    have hg := congrArg (fun r : ℝ => (r : ℂ)) (pairCoefficient_gram Q p q hQ hp)
    push_cast at hg
    rw [show (∑ i, ∑ j, (pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p i j : ℂ)) =
      (if p = q then 1 else 0) by by_cases he : p = q <;> simpa [he,mul_comm] using hg]
  have hV : V = -U := by
    dsimp [V,U]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [pairCoefficient_swap Q q i j]
    simp
  rw [hexp,hF,hV]
  change _ = _ - (2 : ℂ) • U
  module

end Laughlin.Fock

end OAI
