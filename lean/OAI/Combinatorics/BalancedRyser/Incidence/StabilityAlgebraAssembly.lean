import Mathlib.Algebra.CharP.CharAndCard
import OAI.Combinatorics.BalancedRyser.Incidence.StabilityCoprimeReduction
import OAI.Combinatorics.BalancedRyser.Incidence.StabilityLargeFiber
import OAI.Combinatorics.BalancedRyser.Incidence.StabilityPolynomial

namespace OAI

namespace Balanced.StabilityPolynomial

open Polynomial Classical

variable {F : Type*} [Field F] [Fintype F]

theorem vertical_fiber_of_coprime_wronskian
    (hprime : Nat.Prime (Fintype.card F)) (U : Finset (Point F))
    {A f g : F[X]} (hA : A ≠ 0) (hf : f ≠ 0)
    (hcop : IsCoprime f g)
    (hfdeg : f.natDegree < Fintype.card F)
    (hgdeg : g.natDegree < Fintype.card F)
    (hW : derivative f * g - derivative g * f = 0)
    (hdiv : X ^ Fintype.card F * f + g ∣ redeiLeadingProduct U * A) :
    ∃ c : F, Fintype.card F - A.natDegree ≤
      (U.filter fun p => OnLine p (none, c)).card := by
  classical
  let : Fact (Nat.Prime (Fintype.card F)) := ⟨hprime⟩
  let : CharP F (Fintype.card F) := charP_of_card_eq_prime rfl
  obtain ⟨hfc, hgc⟩ := constants_of_coprime_wronskian_of_natDegree_lt_char
    hcop hfdeg hgdeg hW
  have ha : f.coeff 0 ≠ 0 := by
    intro hz
    apply hf
    simpa [hz] using hfc
  refine ⟨g.coeff 0 / f.coeff 0, ?_⟩
  apply redei_large_vertical_fiber U hA (f.coeff 0) (g.coeff 0) ha
  rw [hfc, hgc] at hdiv
  simpa only [redeiLeadingProduct, mul_comm] using hdiv

theorem redei_coprime_wronskian_divisor
    (U : Finset (Point F)) {A f g : F[X]}
    (hdiv : X ^ Fintype.card F * f + g ∣ redeiLeadingProduct U * A) :
    X ^ Fintype.card F * f + g ∣
      (X * f + g) * (derivative f * g - derivative g * f) * A := by
  apply redei_factor_wronskian_divisibility
    (R := redeiLeadingProduct U) (hidentity := rfl)
    (hR0 := StabilityCoprimeReduction.redeiLeadingProduct_monic U |>.ne_zero)
    (hdiv := hdiv)
  exact Splits.prod fun p _ => Splits.X_add_C p.1

omit [Fintype F] in
private theorem equal_degree_wronskian_budget (f g : F[X]) (heq : f.natDegree = g.natDegree)
    (hW : derivative f * g - derivative g * f ≠ 0) :
    (derivative f * g - derivative g * f).natDegree + 2 ≤ 2 * f.natDegree := by
  have hf : f ≠ 0 := by intro h; simp [h] at hW
  have hg : g ≠ 0 := by intro h; simp [h] at hW
  let c : F := f.leadingCoeff / g.leadingCoeff
  let h : F[X] := f - C c * g
  have hc : c ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hf) (leadingCoeff_ne_zero.mpr hg)
  have hid : derivative h * g - derivative g * h = derivative f * g - derivative g * f := by
    dsimp [h]
    rw [derivative_sub, derivative_mul, derivative_C]
    ring
  have hh : h ≠ 0 := by
    intro hz
    have := hid
    simp [hz] at this
    exact hW this.symm
  have hdrop : h.natDegree < f.natDegree := by
    apply (natDegree_lt_iff_degree_lt hh).2
    rw [← degree_eq_natDegree hf]
    apply degree_sub_lt_left
    · rw [degree_mul, degree_C hc, zero_add, degree_eq_natDegree hf,
        degree_eq_natDegree hg, heq]
    · exact hf
    · rw [leadingCoeff_mul, leadingCoeff_C]
      dsimp [c]
      exact (div_mul_cancel₀ _ (leadingCoeff_ne_zero.mpr hg)).symm
  have hident : wronskian g h = derivative f * g - derivative g * f := by
    calc
      wronskian g h = derivative h * g - derivative g * h := by
        unfold wronskian
        ring
      _ = _ := hid
  have hw : wronskian g h ≠ 0 := by
    rw [hident]
    exact hW
  have hbound := natDegree_wronskian_lt_add hw
  rw [hident, ← heq] at hbound
  omega

omit [Fintype F] in
private theorem assembled_asymmetric_degree_budget (f g : F[X]) (s : ℕ)
    (hf : f ≠ 0) (hfs : f.natDegree ≤ s) (hgs : g.natDegree ≤ s)
    (hW : derivative f * g - derivative g * f ≠ 0) :
    (X * f + g).natDegree + (derivative f * g - derivative g * f).natDegree + 1 ≤
      f.natDegree + 2 * s := by
  have hL := natDegree_add_le (X * f) g
  rw [natDegree_X_mul hf] at hL
  have hstandard : (derivative f * g - derivative g * f).natDegree <
      f.natDegree + g.natDegree := by
    have hi : wronskian g f = derivative f * g - derivative g * f := by
      unfold wronskian
      ring
    have hb := natDegree_wronskian_lt_add (show wronskian g f ≠ 0 by rwa [hi])
    rw [hi] at hb
    omega
  rcases lt_trichotomy f.natDegree g.natDegree with hlt | heq | hgt
  · rw [max_eq_right (by omega)] at hL
    omega
  · have hsharp := equal_degree_wronskian_budget f g heq hW
    rw [← heq, max_eq_left (by omega)] at hL
    omega
  · rw [max_eq_left (by omega)] at hL
    omega

omit [Fintype F] in
private theorem assembled_zero_factor (f g A : F[X]) (q s d : ℕ)
    (hf : f ≠ 0) (hA : A ≠ 0)
    (hfs : f.natDegree ≤ s) (hgs : g.natDegree ≤ s)
    (hgq : g.natDegree < q) (hAd : A.natDegree ≤ d)
    (hgap : 2 * s + d < q + 1)
    (hdiv : X ^ q * f + g ∣ (X * f + g) * (derivative f * g - derivative g * f) * A) :
    X * f + g = 0 ∨ derivative f * g - derivative g * f = 0 := by
  by_contra hn
  push Not at hn
  have hLW := mul_ne_zero hn.1 hn.2
  have hprod := mul_ne_zero hLW hA
  have hdegree := natDegree_le_of_dvd hdiv hprod
  have hH : (X ^ q * f + g).natDegree = f.natDegree + q := by
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow_mul q hf]
    rw [natDegree_X_pow_mul q hf]
    omega
  rw [hH, natDegree_mul hLW hA, natDegree_mul hn.1 hn.2] at hdegree
  have hbudget := assembled_asymmetric_degree_budget f g s hf hfs hgs hn.2
  omega

private theorem empty_columns_le_auxiliary_degree (U : Finset (Point F)) {A f g : F[X]} (hA : A ≠ 0)
    (hfirst : X * f + g = 0)
    (hdiv : X ^ Fintype.card F * f + g ∣ redeiLeadingProduct U * A) :
    (Finset.univ.filter fun c : F => ∀ p ∈ U, p.1 ≠ c).card ≤ A.natDegree := by
  classical
  let S := Finset.univ.filter fun c : F => ∀ p ∈ U, p.1 ≠ c
  have hroot : ∀ c ∈ S, A.eval (-c) = 0 := by
    intro c hc
    have hc' : ∀ p ∈ U, p.1 ≠ c := (Finset.mem_filter.mp hc).2
    have hH : (X ^ Fintype.card F * f + g).eval (-c) = 0 := by
      have hh := congrArg (fun P : F[X] => P.eval (-c)) hfirst
      simpa only [eval_add, eval_mul, eval_pow, eval_X, eval_zero,
        FiniteField.pow_card] using hh
    have hRA : (redeiLeadingProduct U * A).eval (-c) = 0 := by
      obtain ⟨Q, hQ⟩ := hdiv
      rw [hQ, eval_mul, hH, zero_mul]
    have hR : (redeiLeadingProduct U).eval (-c) ≠ 0 := by
      simp only [redeiLeadingProduct, eval_prod, eval_add, eval_X, eval_C]
      apply Finset.prod_ne_zero_iff.mpr
      intro p hp hz
      apply hc' p hp
      linear_combination hz
    rw [eval_mul] at hRA
    exact (mul_eq_zero.mp hRA).resolve_left hR
  have hcard : (S.image fun c => -c).card ≤ A.natDegree := by
    apply card_le_degree_of_subset_roots
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_roots hA).2 (hroot c hc)
  simpa only [Finset.card_image_of_injective S neg_injective] using hcard

theorem normalized_prime_stability_of_degree_budget
    (hprime : Nat.Prime (Fintype.card F)) (U : Finset (Point F)) (d s : ℕ)
    (hsize : 2 * (nonverticalSkewCodes U).card < (d + 1) * (d + 2))
    (hbudget : U.card + d - Fintype.card F ≤ s)
    (hgap : 2 * s + d < Fintype.card F + 1)
    (hempty : d < (Finset.univ.filter fun c : F => ∀ p ∈ U, p.1 ≠ c).card) :
    ∃ c : F, Fintype.card F - d ≤
      (U.filter fun p => OnLine p (none, c)).card := by
  classical
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hdq : d < Fintype.card F := by
    apply hempty.trans_le
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)
  obtain ⟨A, D, f, g, hA, hAd, _hD, hcop, hf, hfd, hgd, _heq, _hH, hdiv⟩ :=
    StabilityCoprimeReduction.exists_coprime_redei_identity U d hsize hdq
  have hfs : f.natDegree ≤ s := hfd.trans hbudget
  have hgs : g.natDegree ≤ s := hgd.trans hbudget
  have hfq : f.natDegree < Fintype.card F := by omega
  have hgq : g.natDegree < Fintype.card F := by omega
  have hdivW := redei_coprime_wronskian_divisor U hdiv
  rcases assembled_zero_factor f g A (Fintype.card F) s d hf hA hfs hgs hgq hAd
      hgap hdivW with hfirst | hW
  · have hcount := empty_columns_le_auxiliary_degree U hA hfirst hdiv
    omega
  · obtain ⟨c, hc⟩ := vertical_fiber_of_coprime_wronskian hprime U hA hf hcop hfq hgq hW hdiv
    exact ⟨c, (show Fintype.card F - d ≤ Fintype.card F - A.natDegree by omega).trans hc⟩

theorem normalized_prime_stability
    (hprime : Nat.Prime (Fintype.card F)) (U : Finset (Point F)) (d : ℕ)
    (hU : U.card ≤ Fintype.card F)
    (hsize : 2 * (nonverticalSkewCodes U).card < (d + 1) * (d + 2))
    (hgap : 3 * d < Fintype.card F + 1)
    (hempty : d < (Finset.univ.filter fun c : F => ∀ p ∈ U, p.1 ≠ c).card) :
    ∃ c : F, Fintype.card F - d ≤
      (U.filter fun p => OnLine p (none, c)).card := by
  classical
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hdq : d < Fintype.card F := by omega
  obtain ⟨A, D, f, g, hA, hAd, _hD, hcop, hf, hfd, hgd, _heq, _hH, hdiv⟩ :=
    StabilityCoprimeReduction.exists_coprime_redei_identity U d hsize hdq
  have hfs : f.natDegree ≤ d := by omega
  have hgs : g.natDegree ≤ d := by omega
  have hfq : f.natDegree < Fintype.card F := by omega
  have hgq : g.natDegree < Fintype.card F := by omega
  have hdivW := redei_coprime_wronskian_divisor U hdiv
  rcases assembled_zero_factor f g A (Fintype.card F) d d hf hA hfs hgs hgq hAd
      (by omega) hdivW with hfirst | hW
  · have hcount := empty_columns_le_auxiliary_degree U hA hfirst hdiv
    omega
  · obtain ⟨c, hc⟩ := vertical_fiber_of_coprime_wronskian hprime U hA hf hcop hfq hgq hW hdiv
    exact ⟨c, (show Fintype.card F - d ≤ Fintype.card F - A.natDegree by omega).trans hc⟩

end Balanced.StabilityPolynomial

end OAI
