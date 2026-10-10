import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.NormNum

namespace OAI

namespace Yau
open MvPolynomial Finsupp
noncomputable section

theorem pderiv_surjective {σ K : Type*} [Field K] [CharZero K] (i : σ) :
    Function.Surjective (pderiv (R := K) i) := by
  classical
  intro p
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
    refine ⟨monomial (s + single i 1) (a / ((s i : K) + 1)), ?_⟩
    rw [pderiv_monomial]
    have hn : (s i : K) + 1 ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero (s i)
    simp [Finsupp.add_apply, hn]
  | add p q hp hq =>
    obtain ⟨P, hP⟩ := hp
    obtain ⟨Q, hQ⟩ := hq
    exact ⟨P + Q, by rw [map_add, hP, hQ]⟩

theorem complex_pderiv_surjective (i : Fin 4) :
    Function.Surjective (pderiv (R := ℂ) i) := pderiv_surjective i

def primitive {σ K : Type*} [Field K] (i : σ) (p : MvPolynomial σ K) :
    MvPolynomial σ K :=
  ∑ s ∈ p.support, monomial (s + single i 1) (p.coeff s / ((s i : K) + 1))

theorem pderiv_primitive {σ K : Type*} [Field K] [CharZero K]
    (i : σ) (p : MvPolynomial σ K) : pderiv i (primitive i p) = p := by
  classical
  unfold primitive
  rw [map_sum]
  conv_rhs => rw [p.as_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [pderiv_monomial]
  have hn : (s i : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (s i)
  simp [Finsupp.add_apply, hn]

theorem primitive_homogeneous {σ K : Type*} [Field K]
    (i : σ) {p : MvPolynomial σ K} {m : ℕ} (hp : p.IsHomogeneous m) :
    (primitive i p).IsHomogeneous (m + 1) := by
  classical
  unfold primitive
  apply IsHomogeneous.sum
  intro s hs
  apply isHomogeneous_monomial
  have hd : s.degree = m := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hs) (hp.coeff_eq_zero h)
  simp [map_add, Finsupp.degree_single, hd]

end
end Yau

end OAI
