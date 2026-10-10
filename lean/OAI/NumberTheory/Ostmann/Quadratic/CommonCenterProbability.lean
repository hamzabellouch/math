import OAI.NumberTheory.Ostmann.Construction.OriginalTupleLifts
import OAI.NumberTheory.Ostmann.QuadraticCenter.UniformDenominatorLifts
import OAI.NumberTheory.Ostmann.Preliminaries.FallingFactorialError

namespace OAI

/-! # Common-center extraction directly from the original lift probability -/

namespace Ostmann

open scoped BigOperators Classical

theorem pow_le_twice_descFactorial (J k : ℕ) (hk : 1 ≤ k) (hsize : 2 * k ^ 2 ≤ J) :
    J ^ k ≤ 2 * J.descFactorial k := by
  have hJ : 1 ≤ J := by nlinarith
  have hp : J ^ k = J * J ^ (k - 1) := by rw [← pow_succ', Nat.sub_add_cancel hk]
  have hb := pow_le_descFactorial_add J hJ k
  have hloss := Nat.mul_le_mul_right (J ^ (k - 1)) hsize
  nlinarith

/-- All combinatorial moments are computed from actual congruence lifts.
The remaining assumptions are explicit scalar inequalities. -/
theorem exists_commonCenter_of_lift_probability (P : Finset ℕ)
    (t : ℕ → ℤ) (k d K H Z Amax : ℕ) (hd : d ≤ k + 1)
    (A V ρ : ℝ) (hA : 0 < A) (hV : 0 < V) (hρ : 0 < ρ)
    (hZ : 0 < Z) (hAmax : 0 < Amax)
    (hprime : ∀ p ∈ P, p.Prime) (hap : ∀ p ∈ P, Amax < p)
    (hmin : ∀ p ∈ P, Z ≤ p) (hlog : ∀ p ∈ P, V ≤ Real.log (p : ℝ))
    (hbudget : Real.log (2 * (H : ℝ)) < (K + 1 : ℕ) * V)
    (hsmall : 2 * K * (P.card : ℝ) ≤ A ^ 2)
    (hsize : 2 * (k + 1) ^ 2 ≤ P.card)
    (hprob : ρ ≤ (Fintype.card (Fin (k + 1) ↪ P) : ℝ)⁻¹ *
      (tupleLiftFamily P (k + 1) Amax H t).card)
    (hdiscard : A ^ d * liftMomentUpper P.card (k + 1 - d) H Z ≤
      ρ * (P.card : ℝ) ^ (k + 1) / (4 * Amax)) :
    ∃ a ∈ Finset.Icc 1 Amax,
      ∃ n ∈ Finset.Ico (-(H : ℤ)) (H + 1), ∃ h : ℤ, ∃ m : ℕ,
        0 < m ∧ m ≤ Amax ∧ h.natAbs.Coprime m ∧ |h| ≤ |n| ∧
        A ≤ ((matchingPrimes P a t n).card : ℝ) ∧
        ρ * (P.card : ℝ) ^ (k + 1) / (4 * Amax) ≤
          2 * P.card * ((matchingPrimes P a t n).card : ℝ) ^ k ∧
        ∀ (p : ℕ) (hp : p ∈ matchingPrimes P a t n),
          let _ : Fact p.Prime := ⟨hprime p (Finset.mem_filter.mp hp).1⟩
          (t p : ZMod p) = (h : ZMod p) / (m : ZMod p) := by
  have hJ : 0 < P.card := by nlinarith
  have hJr : 0 < (P.card : ℝ) := by exact_mod_cast hJ
  have hAr : 0 < (Amax : ℝ) := by exact_mod_cast hAmax
  have hhalf : (P.card : ℝ) ^ (k + 1) ≤ 2 * (P.card.descFactorial (k + 1) : ℝ) := by
    exact_mod_cast pow_le_twice_descFactorial P.card (k + 1) (by omega) hsize
  have hcount : ρ * (P.card.descFactorial (k + 1) : ℝ) ≤
      (tupleLiftFamily P (k + 1) Amax H t).card := by
    rw [Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_fin] at hprob
    have hfac : (0 : ℝ) < P.card.descFactorial (k + 1) := by nlinarith [pow_pos hJr (k + 1)]
    have hh := (le_inv_mul_iff₀ hfac).mp hprob
    nlinarith
  have hcount' : ρ * (P.card : ℝ) ^ (k + 1) / (2 * Amax) ≤
      ((tupleLiftFamily P (k + 1) Amax H t).card : ℝ) / Amax := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Amax) hAr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hhalf hρ.le]
  have hratio : ρ * (P.card : ℝ) ^ (k + 1) / (2 * Amax) =
      2 * (ρ * (P.card : ℝ) ^ (k + 1) / (4 * Amax)) := by ring
  rw [hratio] at hcount'
  have hpositive : 0 < ((tupleLiftFamily P (k + 1) Amax H t).card : ℝ) / Amax -
      A ^ d * liftMomentUpper P.card (k + 1 - d) H Z := by
    have hpos : 0 < ρ * (P.card : ℝ) ^ (k + 1) / (4 * Amax) := by positivity
    linarith
  obtain ⟨a, ha, n, hn, h, m, hm, hma, hcop, hbound, hlarge, hmoment, hcenters⟩ :=
    exists_commonCenter_of_bounded_denominators P t k d K H Z Amax hd A V
      hA hV hZ hAmax hprime hap hmin hlog hbudget hsmall
      (tupleLiftFamily P (k + 1) Amax H t)
      (fun e he => (Finset.mem_filter.mp he).2) hpositive
  refine ⟨a, ha, n, hn, h, m, hm, hma, hcop, hbound, hlarge, ?_, hcenters⟩
  linarith

end Ostmann

end OAI
