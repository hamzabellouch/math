import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Tactic

namespace OAI

namespace PiExponentJets.W24

open scoped nonZeroDivisors

section QuotientDimension

variable {R : Type*} [CommRing R]

theorem proper_prime_cut_dimension_succ_le
    (P Q : Ideal R) [P.IsPrime] (f : R)
    (hfP : f ∉ P) (hPQ : P ≤ Q) (hfQ : f ∈ Q) :
    ringKrullDim (R ⧸ Q) + 1 ≤ ringKrullDim (R ⧸ P) := by
  let g : (R ⧸ P) →+* (R ⧸ Q) := Ideal.Quotient.factor hPQ
  have hf0 : Ideal.Quotient.mk P f ≠ 0 := by
    exact fun h => hfP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hreg : Ideal.Quotient.mk P f ∈ (R ⧸ P)⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hf0
  apply ringKrullDim_succ_le_of_surjective g (Ideal.Quotient.factor_surjective hPQ) hreg
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hfQ

theorem proper_prime_cut_dimension_le
    (P Q : Ideal R) [P.IsPrime] (f : R)
    (hfP : f ∉ P) (hPQ : P ≤ Q) (hfQ : f ∈ Q)
    (s : ℕ) (hdim : ringKrullDim (R ⧸ P) = (s : WithBot ℕ∞) + 2) :
    ringKrullDim (R ⧸ Q) ≤ (s : WithBot ℕ∞) + 1 := by
  apply ENat.WithBot.add_le_add_one_right_iff.mp
  have h := proper_prime_cut_dimension_succ_le P Q f hfP hPQ hfQ
  simpa only [hdim, add_assoc, one_add_one_eq_two] using h

end QuotientDimension

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

theorem proper_prime_cut_relative_height_eq_one
    (P Q : Ideal R) [P.IsPrime] (f : R) (hfP : f ∉ P)
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes) :
    (Q.map (Ideal.Quotient.mk P)).height = 1 := by
  have : Q.IsPrime := hQ.1.1
  have hPQ : P ≤ Q := le_sup_left.trans hQ.1.2
  have hfQ : f ∈ Q :=
    (Ideal.span_singleton_le_iff_mem Q).mp (le_sup_right.trans hQ.1.2)
  have : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
      rwa [Ideal.mk_ker])
  have hne : Q.map (Ideal.Quotient.mk P) ≠ ⊥ := by
    intro h
    have hQP : Q ≤ P := by
      simpa only [Ideal.mk_ker] using
        (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk P)).mp h
    exact hfP (hQP hfQ)
  have hlo : 1 ≤ (Q.map (Ideal.Quotient.mk P)).height := by
    have hlt : (⊥ : Ideal (R ⧸ P)) < Q.map (Ideal.Quotient.mk P) :=
      bot_lt_iff_ne_bot.mpr hne
    have h := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    simpa only [Ideal.height_bot, zero_add] using h
  exact le_antisymm (Ideal.map_height_le_one_of_mem_minimalPrimes hQ) hlo

theorem proper_prime_cut_relative_local_dimension
    (P Q : Ideal R) [P.IsPrime] (f : R) (hfP : f ∉ P)
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes) :
    letI : Q.IsPrime := hQ.1.1
    letI : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact le_sup_left.trans hQ.1.2)
    ringKrullDim (Localization.AtPrime (Q.map (Ideal.Quotient.mk P))) = 1 := by
  let : Q.IsPrime := hQ.1.1
  let : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact le_sup_left.trans hQ.1.2)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
      (Q.map (Ideal.Quotient.mk P))
      (Localization.AtPrime (Q.map (Ideal.Quotient.mk P))),
    proper_prime_cut_relative_height_eq_one P Q f hfP hQ]
  rfl

omit [IsNoetherianRing R] in
theorem minimal_proper_prime_cut_dimension_le
    (P Q : Ideal R) [P.IsPrime] (f : R) (hfP : f ∉ P)
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes)
    (s : ℕ) (hdim : ringKrullDim (R ⧸ P) = (s : WithBot ℕ∞) + 2) :
    ringKrullDim (R ⧸ Q) ≤ (s : WithBot ℕ∞) + 1 :=
  proper_prime_cut_dimension_le P Q f hfP (le_sup_left.trans hQ.1.2)
    ((Ideal.span_singleton_le_iff_mem Q).mp (le_sup_right.trans hQ.1.2)) s hdim

end PiExponentJets.W24

end OAI
