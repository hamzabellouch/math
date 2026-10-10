import OAI.Combinatorics.ContingencyTables.Transport.RationalWalks
import OAI.Combinatorics.ContingencyTables.Transport.MetropolisChain

namespace OAI

/-! # Independent rational walks agree with their real finite kernels -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture CommonBasesFPRAS

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem walkLaw_cast_kernel (K : X → RationalLaw X) (C : FiniteChain X)
    (hK : ∀ x y,((K x).mass y:ℝ)=C.P x y) (n : ℕ) (x y : X) :
    ((walkLaw K x n).mass y:ℝ)=(C.kernel.power n).P x y := by
  induction n generalizing y with
  | zero =>
    simp only [walkLaw,pointLaw,FiniteKernel.power,FiniteKernel.identity]
    by_cases hxy : x=y
    · subst y; simp
    · simp [hxy,Ne.symm hxy]
  | succ n ih =>
    change ((∑ z,(walkLaw K x n).mass z*(K z).mass y:ℚ):ℝ)=_
    simp only [Rat.cast_sum,Rat.cast_mul,ih,hK,
      FiniteKernel.power,FiniteKernel.comp,FiniteChain.kernel]

end ContingencyTables.FirstSuccess

end OAI
