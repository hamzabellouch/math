import OAI.Analysis.Laughlin.Fock.EnergyRotation
import OAI.Analysis.Laughlin.Operators.PairNormalOrder
import OAI.Analysis.Laughlin.ThreeBody.FockHaar

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

theorem annihilate_create_inner (Q : ℕ) (i : Fin (Q+1)) (x y : Space Q) :
    occupationInner Q x (create i y) = occupationInner Q (annihilate i x) y := by
  have h := congrArg star (create_annihilate_adjoint Q i y x)
  simpa only [occupationInner_star] using h

theorem pair_annihilate_create_inner (Q p : ℕ) (x y : Space Q) :
    occupationInner Q x (sourcePairCreateEnd Q p y) =
      occupationInner Q (sourcePairEnd Q p x) y := by
  have h := congrArg star (pairCreate_pair_adjoint Q
    (fun i j => ((pairCoefficient Q p i j / Real.sqrt 2 : ℝ) : ℂ)) y x)
  simpa only [occupationInner_star,sourcePairCreateEnd,sourcePairEnd] using h

theorem sourcePairCreate_inner (Q : ℕ) (hQ : 2 ≤ Q)
    (p q : Fin (2*Q-2+1)) (y z : Space Q) :
    occupationInner Q (sourcePairCreateEnd Q p.val y) (sourcePairCreateEnd Q q.val z) =
      (if p=q then (1 : ℂ) else 0) * occupationInner Q y z +
      (∑ i, ∑ j, (complexThreeGram Q-1) (p,i) (q,j) *
        occupationInner Q (annihilate i y) (annihilate j z)) +
      occupationInner Q (sourcePairEnd Q q.val y) (sourcePairEnd Q p.val z) := by
  rw [sourcePairCreateEnd,pairCreate_pair_adjoint]
  change occupationInner Q y ((sourcePairEnd Q p.val * sourcePairCreateEnd Q q.val) z) = _
  rw [sourcePair_normal_order Q p.val q.val hQ (by omega)]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    Module.End.one_apply,LinearMap.sum_apply,Module.End.mul_apply,
    occupationInner_add_right,occupationInner_sub_right,occupationInner_smul_right,
    occupationInner_sum_right,annihilate_create_inner,pair_annihilate_create_inner,
    complexThreeGram_sub_one_entry,Finset.sum_mul,Finset.mul_sum]
  have he : p.val=q.val ↔ p=q := Fin.val_inj
  simp only [he]
  ring_nf
  simp only [Finset.sum_neg_distrib]
  ring

theorem sourceFockHamiltonian_normal_square (Q : ℕ) (hQ : 2 ≤ Q) (x : Space Q) :
    occupationNormSq Q (sourceFockHamiltonian Q x) = sourceFockEnergy Q x +
      (contractionForm Q (sourceThreeEnd Q) (complexThreeGram Q-1) x).re +
      ∑ p : Fin (2*Q-2+1), ∑ q : Fin (2*Q-2+1),
        occupationNormSq Q (sourcePairEnd Q q.val (sourcePairEnd Q p.val x)) := by
  have hc (p q : Fin (2*Q-2+1)) :
      sourcePairEnd Q p.val (sourcePairEnd Q q.val x) =
        sourcePairEnd Q q.val (sourcePairEnd Q p.val x) :=
    LinearMap.congr_fun (pairEnd_commute Q _ _) x
  have hH : sourceFockHamiltonian Q x = ∑ p : Fin (2*Q-2+1),
      sourcePairCreateEnd Q p.val (sourcePairEnd Q p.val x) := by
    rw [sourceFockHamiltonian_apply_fin Q (by omega)]
    simp only [sourcePairCreateEnd_mul]
  have he : (occupationNormSq Q (sourceFockHamiltonian Q x) : ℂ) =
      (sourceFockEnergy Q x : ℂ) +
      contractionForm Q (sourceThreeEnd Q) (complexThreeGram Q-1) x +
      ∑ p : Fin (2*Q-2+1), ∑ q : Fin (2*Q-2+1),
        (occupationNormSq Q (sourcePairEnd Q q.val (sourcePairEnd Q p.val x)) : ℂ) := by
    rw [← occupationInner_self,hH,occupationInner_sum_left]
    simp_rw [occupationInner_sum_right,sourcePairCreate_inner Q hQ]
    have hl (p q : Fin (2*Q-2+1)) : occupationInner Q
        (sourcePairEnd Q q.val (sourcePairEnd Q p.val x))
        (sourcePairEnd Q p.val (sourcePairEnd Q q.val x)) =
        (occupationNormSq Q (sourcePairEnd Q q.val (sourcePairEnd Q p.val x)) : ℂ) := by
      rw [hc p q,occupationInner_self]
    simp only [Finset.sum_add_distrib,hl]
    congr 1
    · congr 1
      · rw [sourceFockEnergy_eq_fin Q (by omega),Complex.ofReal_sum]
        simp [occupationInner_self]
      · simp only [contractionForm,Fintype.sum_prod_type,sourceThreeEnd,Module.End.mul_apply]
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_comm]
  have hr := congrArg Complex.re he
  simpa only [Complex.add_re,Complex.ofReal_re,Complex.re_sum] using hr

end Laughlin.Fock

end OAI
