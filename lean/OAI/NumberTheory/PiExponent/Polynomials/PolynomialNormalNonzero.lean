import Mathlib
import OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential

namespace OAI

namespace PiExponent

open MvPolynomial

theorem totalDegree_pderiv_lt_of_ne_zero
    {C ι : Type*} [CommSemiring C] (p : MvPolynomial ι C) (i : ι)
    (hp : pderiv i p ≠ 0) : (pderiv i p).totalDegree < p.totalDegree := by
  classical
  have hshift (d : ι →₀ ℕ) (hd : d ∈ (pderiv i p).support) :
      d + Finsupp.single i 1 ∈ p.support := by
    apply mem_support_iff.mpr
    intro hz
    have hh := mem_support_iff.mp hd
    apply hh
    rw [coeff_pderiv, hz, zero_mul]
  have hdegree (d : ι →₀ ℕ) (hd : d ∈ (pderiv i p).support) :
      d.sum (fun _ e => e) < p.totalDegree := by
    have hh := le_totalDegree (hshift d hd)
    have he : (d + Finsupp.single i 1).sum (fun _ e => e) =
        d.sum (fun _ e => e) + 1 := by
      rw [Finsupp.sum_add_index']
      · simp
      · intro; rfl
      · intros; rfl
    rw [he] at hh
    omega
  have hpos : 0 < p.totalDegree := by
    obtain ⟨d, hd⟩ := (MvPolynomial.support_nonempty.mpr hp)
    exact (Nat.zero_le _).trans_lt (hdegree d hd)
  rw [MvPolynomial.totalDegree, Finset.sup_lt_iff hpos]
  exact hdegree

theorem eq_constant_of_pderiv_eq_zero
    {C ι : Type*} [Field C] [CharZero C] (p : MvPolynomial ι C)
    (hp : ∀ i, pderiv i p = 0) : p = MvPolynomial.C (p.coeff 0) := by
  classical
  ext d
  by_cases hd : d = 0
  · subst d
    simp
  · have hex : ∃ i, d i ≠ 0 := by
      by_contra! hh
      exact hd (by ext i; exact hh i)
    obtain ⟨i, hi⟩ := hex
    have he : d - Finsupp.single i 1 + Finsupp.single i 1 = d :=
      Finsupp.sub_add_single_one_cancel hi
    have hh := congrArg (fun q : MvPolynomial ι C =>
      q.coeff (d - Finsupp.single i 1)) (hp i)
    rw [coeff_pderiv, he] at hh
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at hh
    have hfactor : (((d i - 1 : ℕ) : C) + 1) ≠ 0 := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (d i - 1)) :
          (((d i - 1 + 1 : ℕ) : C)) ≠ 0)
    have hc : p.coeff d = 0 := (mul_eq_zero.mp hh).resolve_right hfactor
    simpa [coeff_C, Ne.symm hd] using hc

theorem ideal_eq_bot_of_pderiv_stable
    {C ι : Type*} [Field C] [CharZero C] (Q : Ideal (MvPolynomial ι C))
    (hproper : Q ≠ ⊤) (hstable : ∀ p ∈ Q, ∀ i, pderiv i p ∈ Q) : Q = ⊥ := by
  have hall : ∀ n : ℕ, ∀ p : MvPolynomial ι C,
      p.totalDegree = n → p ∈ Q → p = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hdegree hp
      have hderiv : ∀ i, pderiv i p = 0 := by
        intro i
        by_contra hn
        have hlt := totalDegree_pderiv_lt_of_ne_zero p i hn
        rw [hdegree] at hlt
        exact hn (ih _ hlt _ rfl (hstable p hp i))
      have hc := eq_constant_of_pderiv_eq_zero p hderiv
      have hcoeff : p.coeff 0 = 0 := by
        by_contra hne
        have hunit : IsUnit (MvPolynomial.C (p.coeff 0) : MvPolynomial ι C) :=
          (isUnit_iff_ne_zero.mpr hne).map (MvPolynomial.C : C →+* MvPolynomial ι C)
        have hmem : MvPolynomial.C (p.coeff 0) ∈ Q := by rw [← hc]; exact hp
        exact hproper (Q.eq_top_of_isUnit_mem hmem hunit)
      simpa [hcoeff] using hc
  apply le_antisymm
  · intro p hp
    exact Ideal.mem_bot.mpr (hall p.totalDegree p rfl hp)
  · exact bot_le

theorem polynomialPrimeNormal_mkQ_ne_zero
    {C ι : Type*} [Field C] [CharZero C] [Fintype ι]
    (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    (polynomialTangent (polynomialResidueMap Q) Q).mkQ ≠ 0 := by
  classical
  intro hzero
  have htop : polynomialTangent (polynomialResidueMap Q) Q = ⊤ := by
    rw [← Submodule.ker_mkQ (polynomialTangent (polynomialResidueMap Q) Q),
      hzero, LinearMap.ker_zero]
  apply hQ
  apply ideal_eq_bot_of_pderiv_stable Q (Ideal.IsPrime.ne_top inferInstance)
  intro p hp i
  apply (polynomialResidueMap_eq_zero_iff Q _).mp
  have ht : (Pi.single i 1 : ι → PolynomialResidueField Q) ∈
      polynomialTangent (polynomialResidueMap Q) Q := by
    rw [htop]
    trivial
  change polynomialJacobian (polynomialResidueMap Q) Q (Pi.single i 1) = 0 at ht
  have hh := congrFun ht ⟨p, hp⟩
  simpa [polynomialJacobian, Pi.single_apply] using hh

end PiExponent

end OAI
