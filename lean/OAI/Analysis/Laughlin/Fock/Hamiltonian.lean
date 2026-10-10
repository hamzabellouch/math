import OAI.Analysis.Laughlin.Fock.Inner

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def pairCreateEnd (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ) :
    Module.End ℂ (Space Q) := ∑ i, ∑ j, star (c i j) • (create i * create j)

theorem pairCreate_pair_adjoint (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (x y : Space Q) :
    occupationInner Q (pairCreateEnd Q c x) y = occupationInner Q x (pairEnd Q c y) := by
  simp only [pairCreateEnd,pairEnd,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    occupationInner_sum_left,occupationInner_sum_right,occupationInner_smul_left,
    occupationInner_smul_right,star_star,create_annihilate_adjoint]

noncomputable def sourcePairCreateEnd (Q p : ℕ) : Module.End ℂ (Space Q) :=
  pairCreateEnd Q (fun i j => ((pairCoefficient Q p i j / Real.sqrt 2 : ℝ) : ℂ))

noncomputable def sourceFockHamiltonian (Q : ℕ) : Module.End ℂ (Space Q) :=
  ∑ p ∈ Finset.range (2*Q-1), sourcePairCreateEnd Q p * sourcePairEnd Q p

noncomputable def sourceFockEnergy (Q : ℕ) (x : Space Q) : ℝ :=
  ∑ p ∈ Finset.range (2*Q-1), occupationNormSq Q (sourcePairEnd Q p x)

theorem sourceFockHamiltonian_quadratic (Q : ℕ) (x : Space Q) :
    occupationInner Q (sourceFockHamiltonian Q x) x = (sourceFockEnergy Q x : ℂ) := by
  simp only [sourceFockHamiltonian,LinearMap.sum_apply,Module.End.mul_apply,
    occupationInner_sum_left,sourcePairCreateEnd,sourcePairEnd,pairCreate_pair_adjoint,
    occupationInner_self,sourceFockEnergy,Complex.ofReal_sum]

theorem sourceFockHamiltonian_positive (Q : ℕ) (x : Space Q) :
    0 ≤ (occupationInner Q (sourceFockHamiltonian Q x) x).re := by
  rw [sourceFockHamiltonian_quadratic]
  simp only [Complex.ofReal_re]
  unfold sourceFockEnergy
  exact Finset.sum_nonneg (fun p hp => occupationNormSq_nonneg Q _)

theorem sourceFockEnergy_eq_zero (Q : ℕ) (x : Space Q) :
    sourceFockEnergy Q x = 0 ↔ ∀ p ∈ Finset.range (2*Q-1), sourcePairEnd Q p x = 0 := by
  unfold sourceFockEnergy
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun p hp => occupationNormSq_nonneg Q _)]
  simp only [occupationNormSq_eq_zero]

end Laughlin.Fock

end OAI
