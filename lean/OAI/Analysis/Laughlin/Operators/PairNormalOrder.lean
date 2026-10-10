import OAI.Analysis.Laughlin.Pair.NormalOrder
import OAI.Analysis.Laughlin.ThreeBody.PhysicalKernel

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

theorem sourcePair_normal_order (Q p q : ℕ) (hQ : 2 ≤ Q) (hp : p ≤ 2*Q-2) :
    sourcePairEnd Q p * sourcePairCreateEnd Q q =
      (if p=q then (1 : ℂ) else 0) • (1 : Module.End ℂ (Space Q)) -
      (2 : ℂ) • (∑ i, ∑ j, ∑ t,
        ((pairCoefficient Q p j t : ℂ)*(pairCoefficient Q q i t : ℂ)) •
          (create i * annihilate j)) +
      sourcePairCreateEnd Q q * sourcePairEnd Q p := by
  let F : Module.End ℂ (Space Q) := ∑ i, ∑ j,
    ((pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p i j : ℂ)) • 1
  let U : Module.End ℂ (Space Q) := ∑ i, ∑ j, ∑ b,
    ((pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p i b : ℂ)) • (create j * annihilate b)
  let V : Module.End ℂ (Space Q) := ∑ i, ∑ j, ∑ b,
    ((pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p j b : ℂ)) • (create i * annihilate b)
  have hexp : sourcePairEnd Q p * sourcePairCreateEnd Q q =
      F-U+V+sourcePairCreateEnd Q q * sourcePairEnd Q p := by
    simp only [sourcePairCreateEnd,pairCreateEnd,Complex.star_def,Complex.conj_ofReal,
      Finset.mul_sum,mul_smul_comm,← mul_assoc,sourcePairEnd,pairEnd_create_create,
      smul_add,smul_sub,Finset.smul_sum,smul_smul,pair_weight_product,
      Finset.sum_add_distrib,Finset.sum_sub_distrib,
      Finset.sum_mul,smul_mul_assoc,F,U,V]
  have hF : F = (if p=q then (1 : ℂ) else 0) • (1 : Module.End ℂ (Space Q)) := by
    dsimp [F]
    simp only [← Finset.sum_smul]
    have hg := congrArg Complex.ofReal (pairCoefficient_gram Q p q hQ hp)
    push_cast at hg
    congr 1
    by_cases he : p=q <;> simpa [he,mul_comm] using hg
  have hV : V = -U := by
    dsimp [V,U]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro b hb
    rw [pairCoefficient_swap Q q i j]
    simp only [Complex.ofReal_neg,neg_mul]
    apply LinearMap.ext
    intro x
    exact neg_smul ((pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p i b : ℂ))
      ((create j * annihilate b) x)
  have hU : U = ∑ i, ∑ j, ∑ t,
      ((pairCoefficient Q p j t : ℂ)*(pairCoefficient Q q i t : ℂ)) •
        (create i * annihilate j) := by
    dsimp [U]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro t ht
    rw [pairCoefficient_swap Q q t i,pairCoefficient_swap Q p t j]
    simp [mul_comm]
  rw [hexp,hF,hV,hU]
  module

theorem complexThreeGram_sub_one_entry (Q : ℕ) (a b : Spin.PairOrbitalIndex Q) :
    (complexThreeGram Q-1) a b = -2 * ∑ t,
      (pairCoefficient Q a.1.val b.2 t : ℂ)*(pairCoefficient Q b.1.val a.2 t : ℂ) := by
  simp only [complexThreeGram,Spin.threeGram,Matrix.sub_apply,Matrix.smul_apply,
    smul_eq_mul,Spin.swapCompression_entry,Complex.ofReal_sub,Complex.ofReal_mul,
    Complex.ofReal_ofNat,Complex.ofReal_sum]
  have h : ((1 : Matrix (Spin.PairOrbitalIndex Q) (Spin.PairOrbitalIndex Q) ℝ) a b : ℂ) =
      (1 : Matrix (Spin.PairOrbitalIndex Q) (Spin.PairOrbitalIndex Q) ℂ) a b := by
    classical
    by_cases hab : a=b <;> simp [hab,Matrix.one_apply]
  rw [h]
  ring

end Laughlin.Fock

end OAI
