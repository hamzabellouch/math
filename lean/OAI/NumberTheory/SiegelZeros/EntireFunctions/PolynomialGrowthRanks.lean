import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.Tactic

namespace OAI

namespace SiegelZeros

section

open scoped BigOperators

namespace WeightedTorusJets.W32

def exponentBall (d n : ℕ) : Finset (Fin d →₀ ℕ) :=
  (Finset.range (n + 1)).biUnion fun m => (Finset.univ : Finset (Fin d)).finsuppAntidiag m

@[simp] theorem mem_exponentBall (d n : ℕ) (a : Fin d →₀ ℕ) :
    a ∈ exponentBall d n ↔ a.sum (fun _ e => e) ≤ n := by
  simp only [exponentBall, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_finsuppAntidiag', Finset.subset_univ, and_true]
  constructor
  · rintro ⟨m, hm, hsum⟩
    omega
  · intro h
    exact ⟨a.sum (fun _ e => e), by omega, rfl⟩

theorem card_exponentBall (d n : ℕ) : (exponentBall d n).card = (n + d).choose d := by
  classical
  have hdis : (↑(Finset.range (n + 1)) : Set ℕ).PairwiseDisjoint
      (fun m => (Finset.univ : Finset (Fin d)).finsuppAntidiag m) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro a hai haj
    have hi' := (Finset.mem_finsuppAntidiag'.mp hai).1
    have hj' := (Finset.mem_finsuppAntidiag'.mp haj).1
    exact hij (hi'.symm.trans hj')
  rw [exponentBall, Finset.card_biUnion hdis]
  simp_rw [Finset.card_finsuppAntidiag_nat_eq_multichoose, Finset.card_univ, Fintype.card_fin]
  exact Nat.sum_range_multichoose n d

theorem finrank_restrictTotalDegree (k : Type*) [Field k] (d n : ℕ) :
    Module.finrank k (MvPolynomial.restrictTotalDegree (Fin d) k n) = (n + d).choose d := by
  classical
  have hs : {a : Fin d →₀ ℕ | a.sum (fun _ e => e) ≤ n} =
      (↑(exponentBall d n) : Set (Fin d →₀ ℕ)) := by
    ext a
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, mem_exponentBall]
  change Module.finrank k (MvPolynomial.restrictSupport k
    {a : Fin d →₀ ℕ | a.sum (fun _ e => e) ≤ n}) = _
  rw [hs, ← card_exponentBall]
  let b : Module.Basis (exponentBall d n) k
      (MvPolynomial.restrictSupport k
        (↑(exponentBall d n) : Set (Fin d →₀ ℕ))) :=
    MvPolynomial.basisRestrictSupport k
      (↑(exponentBall d n) : Set (Fin d →₀ ℕ))
  exact Module.finrank_eq_card_finset_basis b

noncomputable def polynomialGrowth (d : ℕ) : Polynomial ℚ :=
  Polynomial.preHilbertPoly ℚ d 0

@[simp] theorem polynomialGrowth_eval (d n : ℕ) :
    (polynomialGrowth d).eval (n : ℚ) = ((n + d).choose d : ℚ) := by
  simpa [polynomialGrowth] using
    Polynomial.preHilbertPoly_eq_choose_add_sub ℚ d (k := 0) (n := n) (Nat.zero_le (n + d))

theorem polynomialGrowth_eval_finrank (k : Type*) [Field k] (d n : ℕ) :
    (polynomialGrowth d).eval (n : ℚ) =
      (Module.finrank k (MvPolynomial.restrictTotalDegree (Fin d) k n) : ℚ) := by
  rw [polynomialGrowth_eval, finrank_restrictTotalDegree]

@[simp] theorem polynomialGrowth_natDegree (d : ℕ) :
    (polynomialGrowth d).natDegree = d :=
  Polynomial.natDegree_preHilbertPoly ℚ d 0

theorem polynomialGrowth_leadingCoeff (d : ℕ) :
    (polynomialGrowth d).leadingCoeff = (d.factorial : ℚ)⁻¹ :=
  Polynomial.leadingCoeff_preHilbertPoly ℚ d 0

theorem polynomialGrowth_leadingCoeff_pos (d : ℕ) :
    0 < (polynomialGrowth d).leadingCoeff := by
  rw [polynomialGrowth_leadingCoeff]
  positivity

theorem exists_polynomialGrowth (k : Type*) [Field k] (d : ℕ) :
    ∃ b : Polynomial ℚ,
      (∀ n : ℕ, b.eval (n : ℚ) =
        (Module.finrank k (MvPolynomial.restrictTotalDegree (Fin d) k n) : ℚ)) ∧
      b.natDegree = d ∧ 0 < b.leadingCoeff := by
  exact ⟨polynomialGrowth d, polynomialGrowth_eval_finrank k d,
    polynomialGrowth_natDegree d, polynomialGrowth_leadingCoeff_pos d⟩

noncomputable def scaledPolynomialGrowth (c d : ℕ) : Polynomial ℚ :=
  Polynomial.C (c : ℚ) * polynomialGrowth d

theorem scaledPolynomialGrowth_natDegree_le (c d : ℕ) :
    (scaledPolynomialGrowth c d).natDegree ≤ d := by
  exact (Polynomial.natDegree_C_mul_le _ _).trans_eq (polynomialGrowth_natDegree d)

theorem scaledPolynomialGrowth_eval_finrank (k : Type*) [Field k]
    (c d n : ℕ) :
    (scaledPolynomialGrowth c d).eval (n : ℚ) =
      (c : ℚ) * (Module.finrank k
        (MvPolynomial.restrictTotalDegree (Fin d) k n) : ℚ) := by
  rw [scaledPolynomialGrowth, Polynomial.eval_C_mul, polynomialGrowth_eval_finrank k]

end WeightedTorusJets.W32

end

end SiegelZeros

end OAI
