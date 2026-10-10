import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Data.Fintype.Prod
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.Linarith
import OAI.Analysis.Laughlin.Polynomial.BracketProductDivisibility

namespace OAI

namespace Laughlin
open MvPolynomial
open scoped BigOperators

theorem bracket_isHomogeneous {N : ℕ} (i j : Fin N) :
    (bracket i j).IsHomogeneous 2 :=
  ((isHomogeneous_X ℂ (i,false)).mul (isHomogeneous_X ℂ (j,true))).sub
    ((isHomogeneous_X ℂ (j,false)).mul (isHomogeneous_X ℂ (i,true)))

theorem orderedPairs_card (N : ℕ) : (orderedPairs N).card = N.choose 2 := by
  simpa [orderedPairs] using (Fintype.card_product_filter_lt (α := Fin N))

theorem laughlinPolynomial_isHomogeneous (N : ℕ) :
    (laughlinPolynomial N).IsHomogeneous (6 * N.choose 2) := by
  rw [laughlinPolynomial_eq_orderedProduct]
  have h := IsHomogeneous.prod (orderedPairs N)
    (fun ij => bracket ij.1 ij.2 ^ 3) (fun _ => 6)
    (fun ij _ => (bracket_isHomogeneous ij.1 ij.2).pow 3)
  simpa [orderedPairs_card, Nat.mul_comm] using h

theorem laughlinPolynomial_totalDegree (N : ℕ) :
    (laughlinPolynomial N).totalDegree = 6 * N.choose 2 :=
  (laughlinPolynomial_isHomogeneous N).totalDegree (laughlinPolynomial_ne_zero N)

theorem laughlin_degree_at_flux (N : ℕ) : 6 * N.choose 2 = N * (3 * (N-1)) := by
  cases N with
  | zero => simp
  | succ n =>
    have h := Nat.add_one_mul_choose_eq n 1
    simp only [Nat.choose_one_right, Nat.reduceAdd] at h
    simp only [Nat.add_sub_cancel]
    nlinarith

theorem laughlinPolynomial_totalDegree_flux (N : ℕ) :
    (laughlinPolynomial N).totalDegree = N * (3 * (N-1)) := by
  rw [laughlinPolynomial_totalDegree, laughlin_degree_at_flux]

theorem scalar_laughlin_of_degree_and_pair_cubes {N : ℕ}
    (P : MvPolynomial (SpinorVariables N) ℂ)
    (hdegree : P.totalDegree ≤ 6 * N.choose 2)
    (hcubes : ∀ i j : Fin N, i < j → bracket i j ^ 3 ∣ P) :
    ∃ c : ℂ, P = C c * laughlinPolynomial N := by
  obtain ⟨g,hg⟩ := laughlinPolynomial_dvd_of_pair_cubes P hcubes
  by_cases hzero : g = 0
  · exact ⟨0, by simp [hg,hzero]⟩
  · have hdeg : g.totalDegree = 0 := by
      rw [hg, totalDegree_mul_of_isDomain (laughlinPolynomial_ne_zero N) hzero,
        laughlinPolynomial_totalDegree] at hdegree
      omega
    exact ⟨g.coeff 0, by rw [hg, mul_comm]; exact congrArg (fun z => z * laughlinPolynomial N) (totalDegree_eq_zero_iff_eq_C.mp hdeg)⟩

theorem scalar_laughlin_at_flux {N : ℕ}
    (P : MvPolynomial (SpinorVariables N) ℂ)
    (hdegree : P.totalDegree ≤ N * (3 * (N-1)))
    (hcubes : ∀ i j : Fin N, i < j → bracket i j ^ 3 ∣ P) :
    ∃ c : ℂ, P = C c * laughlinPolynomial N :=
  scalar_laughlin_of_degree_and_pair_cubes P
    (by simpa [laughlin_degree_at_flux] using hdegree) hcubes

end Laughlin

end OAI
