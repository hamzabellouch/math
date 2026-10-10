import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinWords
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieExponential
import Mathlib.Algebra.Lie.Nilpotent

namespace OAI

/-! # The precise finite BCH input

Published source: F. Baudoin, *An Introduction to the Geometry of Stochastic
Flows* (Imperial College Press, 2004), Appendix B.5, equation (B.2) and the
multiple-exponential formula on p.124; Appendix B.6, p.126, makes the formula
global for nilpotent groups. Author's copy:
https://fabricebaudoin.blog/wp-content/uploads/2019/12/source.pdf

We use only its finite-degree consequence. Grouping the terms of the
multiple-exponential formula by their ordered letter word leaves at most
`2^(d-1)` cuts of a degree-`d` word. Each coefficient before grouping has
absolute value at most one. Thus `2^c` bounds each grouped coefficient for
all degrees at most `c`. The actual exponential is characterized by its
one-parameter subgroups and their derivatives, not by an arbitrary chart.
This is an explicit published-input parameter, never a global axiom.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped BigOperators Manifold

variable (E G : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

/-- The bounded finite Dynkin expansion, specialized to the actual tangent
Lie algebra and its intrinsic exponential. No metric growth estimate is part
of this published hypothesis. -/
def NilpotentDynkinExpansionInput [T2Space G] : Prop :=
  ∀ (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G), IsGroupExponential Exp →
    ∀ c : ℕ, lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥ →
    ∀ n : ℕ, ∃ coeff : DynkinCoefficients c n,
      (∀ d w, |coeff d w| ≤ (2 : ℝ) ^ c) ∧
      ∀ X : Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G,
        (List.ofFn (fun i => Exp (X i))).prod = Exp (finiteDynkinPolynomial coeff X)

variable {E G} [T2Space G]

/-- The polynomial product estimate is proved from the finite BCH identity
and the actual coordinate bracket bounds. Its constants are independent of
the number of factors. -/
theorem exists_product_log_with_polynomial_bound
    (dynkin : NilpotentDynkinExpansionInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    {c n : ℕ} (hc : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥)
    {J : Type*} [Fintype J] (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hbracket : ∀ i j l, |b.repr ⁅b i, b j⁆ l| ≤ C)
    (X : Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G)
    (hX : ∀ i, ‖b.equivFun (X i)‖ ≤ R) :
    ∃ z : GroupLieAlgebra (𝓘(ℝ, E)) G,
      (List.ofFn (fun i => Exp (X i))).prod = Exp z ∧
      ‖b.equivFun z‖ ≤ (c : ℝ) * 2 ^ c * (1 + (Fintype.card J : ℝ) ^ 2 * C) ^ c *
        (1 + R) ^ c * (1 + (n : ℝ)) ^ c := by
  obtain ⟨coeff, hcoeff, hprod⟩ := dynkin Exp hExp c hc n
  exact ⟨finiteDynkinPolynomial coeff X, hprod X,
    norm_finiteDynkinPolynomial_le b coeff hcoeff X hC hR hbracket hX⟩

end PolycyclicRecognition

end

end OAI
