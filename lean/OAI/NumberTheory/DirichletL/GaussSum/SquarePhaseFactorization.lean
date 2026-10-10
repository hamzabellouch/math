import OAI.NumberTheory.DirichletL.GaussSum.CubicTrace
import OAI.NumberTheory.DirichletL.Fourier.PositiveLogProfiles

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators

namespace ActualEisensteinCubic

theorem primary_associated_eq (x y : O) (hxy : Associated x y)
    (hx : lambda ^ 2 ∣ x - 1) (hy : lambda ^ 2 ∣ y - 1) : x = y := by
  obtain ⟨u, hu⟩ := hxy
  have huprimary : lambda ^ 2 ∣ (u : O) - 1 := by
    have heq : (u : O) - 1 = (y - 1) - (x - 1) * (u : O) := by
      rw [← hu]
      ring
    rw [heq]
    exact dvd_sub hy (dvd_mul_of_dvd_left hx _)
  have huone : (u : O) = 1 := A3_primary_unit_eq_one _ u.isUnit huprimary
  simpa only [huone, mul_one] using hu

theorem primary_multiset_prod (s : Multiset O)
    (hs : ∀ x ∈ s, lambda ^ 2 ∣ x - 1) : lambda ^ 2 ∣ s.prod - 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self _ _)
    have hb := ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx))
    rw [Multiset.prod_cons]
    have heq : a * s.prod - 1 = (a - 1) * s.prod + (s.prod - 1) := by ring
    rw [heq]
    exact dvd_add (dvd_mul_of_dvd_left ha _) hb

theorem primary_maximal_divisor_good (t : O) (ht : lambda ^ 2 ∣ t - 1)
    (P : Ideal O) [P.IsMaximal] (htP : t ∈ P) : lambda ∉ P := by
  intro hlam
  have hlam2 : lambda ^ 2 ∈ P := by
    simpa only [pow_two] using P.mul_mem_left lambda hlam
  have hsub : t - 1 ∈ P := Ideal.mem_of_dvd P ht hlam2
  have hone : (1 : O) ∈ P := by simpa using P.sub_mem htP hsub
  exact (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal))
    ((Ideal.eq_top_iff_one _).mpr hone)

theorem exists_primary_prime_factorization (t : O) (ht0 : t ≠ 0)
    (ht : lambda ^ 2 ∣ t - 1) :
    ∃ s : Multiset O, s.prod = t ∧
      ∀ r ∈ s, Prime r ∧ lambda ^ 2 ∣ r - 1 := by
  classical
  obtain ⟨f, hf, hft⟩ := UniqueFactorizationMonoid.exists_prime_factors t ht0
  have hfgood : ∀ r ∈ f, lambda ∉ (Ideal.span {r} : Ideal O) := by
    intro r hr
    have hp := hf r hr
    let : (Ideal.span {r} : Ideal O).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    apply primary_maximal_divisor_good t ht
    exact Ideal.mem_span_singleton.mpr ((Multiset.dvd_prod hr).trans hft.dvd)
  have hreplace : ∃ s : Multiset O, Associated s.prod f.prod ∧
      ∀ r ∈ s, Prime r ∧ lambda ^ 2 ∣ r - 1 := by
    clear hft
    induction f using Multiset.induction_on with
    | empty => exact ⟨0, Associated.refl _, by simp⟩
    | @cons a f ih =>
      have ha := hf a (Multiset.mem_cons_self _ _)
      let : (Ideal.span {a} : Ideal O).IsMaximal :=
        PrincipalIdealRing.isMaximal_of_irreducible ha.irreducible
      obtain ⟨r, hrspan, hrprimary, _⟩ := cubicJacobi_exists_primary_generator
        (Ideal.span {a}) (hfgood a (Multiset.mem_cons_self _ _))
      have har : Associated a r := Ideal.span_singleton_eq_span_singleton.mp hrspan
      obtain ⟨s, hsf, hs⟩ := ih
        (fun r hr => hf r (Multiset.mem_cons_of_mem hr))
        (fun r hr => hfgood r (Multiset.mem_cons_of_mem hr))
      refine ⟨r ::ₘ s, ?_, ?_⟩
      · simpa only [Multiset.prod_cons] using har.symm.mul_mul hsf
      · intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact ⟨har.prime_iff.mp ha, hrprimary⟩
        · exact hs x hx
  obtain ⟨s, hsf, hs⟩ := hreplace
  refine ⟨s, ?_, hs⟩
  exact primary_associated_eq _ _ (hsf.trans hft)
    (primary_multiset_prod s (fun r hr => (hs r hr).2)) ht

theorem residue_char_mem (P : Ideal O) :
    (ringChar (O ⧸ P) : O) ∈ P := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_natCast]
  exact CharP.cast_eq_zero (O ⧸ P) (ringChar (O ⧸ P))

theorem maximal_eq_or_eq_of_same_residue_char
    (P Q R : Ideal O) [P.IsMaximal] [Q.IsMaximal] [R.IsMaximal]
    (hne : P ≠ Q) (hPQ : ringChar (O ⧸ Q) = ringChar (O ⧸ P))
    (hRP : ringChar (O ⧸ R) = ringChar (O ⧸ P)) : R = P ∨ R = Q := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  obtain ⟨a, b, _, _, _, _, hcover⟩ := rational_prime_ideal_cover
    (ringChar (O ⧸ P)) (CharP.char_is_prime (O ⧸ P) _)
  have hp := hcover P inferInstance (residue_char_mem P)
  have hq := hcover Q inferInstance (by rw [← hPQ]; exact residue_char_mem Q)
  have hr := hcover R inferInstance (by rw [← hRP]; exact residue_char_mem R)
  rcases hp with hp | hp <;> rcases hq with hq | hq <;>
    rcases hr with hr | hr <;> simp_all

theorem prime_divisor_residue_char_ne
    (P Q R : Ideal O) [P.IsMaximal] [Q.IsMaximal] [R.IsMaximal]
    (hne : P ≠ Q) (hPQ : ringChar (O ⧸ Q) = ringChar (O ⧸ P))
    (t : O) (htP : t ∉ P) (htQ : t ∉ Q) (htR : t ∈ R) :
    ringChar (O ⧸ R) ≠ ringChar (O ⧸ P) := by
  intro hRP
  rcases maximal_eq_or_eq_of_same_residue_char P Q R hne hPQ hRP with rfl | rfl
  · exact htP htR
  · exact htQ htR

theorem lambda_sq_dvd_three : lambda ^ 2 ∣ (3 : O) := by
  have hlam : lambda ^ 2 = -3 * omega := by
    change (omega - 1) ^ 2 = -3 * omega
    linear_combination omega_sq_for_norm
  refine ⟨-omega ^ 2, ?_⟩
  rw [hlam]
  calc
    (3 : O) = 3 * omega ^ 3 := by rw [omega_primitive.pow_eq_one]; ring
    _ = -3 * omega * -omega ^ 2 := by ring

theorem neg_two_primary : lambda ^ 2 ∣ (-2 : O) - 1 := by
  convert dvd_neg.mpr lambda_sq_dvd_three using 1 ; ring

theorem neg_add_primary (p q : O)
    (hp : lambda ^ 2 ∣ p - 1) (hq : lambda ^ 2 ∣ q - 1) :
    lambda ^ 2 ∣ -(p + q) - 1 := by
  have hd := dvd_neg.mpr (dvd_add (dvd_add hp hq) lambda_sq_dvd_three)
  convert hd using 1 ; ring

theorem prime_generator_not_mem_of_ne (P Q : Ideal O)
    [P.IsMaximal] [Q.IsMaximal] (hne : P ≠ Q)
    (q : O) (hQ : Q = Ideal.span {q}) : q ∉ P := by
  intro hq
  have hle : Q ≤ P := by
    rw [hQ]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hq
  exact hne (Ideal.IsMaximal.eq_of_le (inferInstance : Q.IsMaximal)
    (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal)) hle).symm

theorem cubic_reciprocity_equal_residue_char
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (hne : P ≠ Q) (hchar : ringChar (O ⧸ Q) = ringChar (O ⧸ P))
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    cubicChar P hPgood (Ideal.Quotient.mk P q) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q p) := by
  classical
  let t : O := -(p + q)
  have hpP : p ∈ P := by rw [hP]; exact Ideal.subset_span (by simp)
  have hqQ : q ∈ Q := by rw [hQ]; exact Ideal.subset_span (by simp)
  have hqP : q ∉ P := prime_generator_not_mem_of_ne P Q hne q hQ
  have hpQ : p ∉ Q := prime_generator_not_mem_of_ne Q P hne.symm p hP
  have htP : t ∉ P := by
    intro ht
    have hs : p + q ∈ P := by simpa only [t, neg_neg] using P.neg_mem ht
    exact hqP (by simpa only [add_sub_cancel_left] using P.sub_mem hs hpP)
  have htQ : t ∉ Q := by
    intro ht
    have hs : p + q ∈ Q := by simpa only [t, neg_neg] using Q.neg_mem ht
    exact hpQ (by simpa only [add_sub_cancel_right] using Q.sub_mem hs hqQ)
  have ht0 : t ≠ 0 := fun h => htP (h ▸ P.zero_mem)
  obtain ⟨s, hst, hs⟩ := exists_primary_prime_factorization t ht0
    (neg_add_primary p q hpprimary hqprimary)
  have hlocal : ∀ r ∈ s,
      cubicChar P hPgood (Ideal.Quotient.mk P r) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q r) := by
    intro r hr
    let R : Ideal O := Ideal.span {r}
    let : R.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (hs r hr).1.irreducible
    have hrR : r ∈ R := Ideal.subset_span (by simp)
    have htR : t ∈ R := Ideal.mem_span_singleton.mpr (hst ▸ Multiset.dvd_prod hr)
    have hRgood : lambda ∉ R := primary_maximal_divisor_good t
      (neg_add_primary p q hpprimary hqprimary) R htR
    have hRP := prime_divisor_residue_char_ne P Q R hne hchar t htP htQ htR
    have hRQ : ringChar (O ⧸ R) ≠ ringChar (O ⧸ Q) := by rwa [hchar]
    rw [cubic_reciprocity_distinct_residue_char P R hPgood hRgood hRP
      p r hP rfl hpprimary (hs r hr).2,
      cubic_reciprocity_distinct_residue_char Q R hQgood hRgood hRQ
      q r hQ rfl hqprimary (hs r hr).2]
    have hsum : Ideal.Quotient.mk R p + Ideal.Quotient.mk R q = 0 := by
      have hz := Ideal.Quotient.eq_zero_iff_mem.mpr htR
      simpa only [t, map_neg, map_add, neg_eq_zero] using hz
    have heq : Ideal.Quotient.mk R p = -Ideal.Quotient.mk R q := eq_neg_of_add_eq_zero_left hsum
    rw [heq, ← neg_one_mul (Ideal.Quotient.mk R q), map_mul,
      A3_cubicChar_neg_one, one_mul]
  have hmul : ∀ f : Multiset O,
      (∀ r ∈ f, cubicChar P hPgood (Ideal.Quotient.mk P r) =
        cubicChar Q hQgood (Ideal.Quotient.mk Q r)) →
      cubicChar P hPgood (Ideal.Quotient.mk P f.prod) =
        cubicChar Q hQgood (Ideal.Quotient.mk Q f.prod) := by
    intro f
    induction f using Multiset.induction_on with
    | empty => intro _; simp
    | @cons r f ih =>
      intro hf
      simp only [Multiset.prod_cons, map_mul]
      rw [hf r (Multiset.mem_cons_self _ _), ih
        (fun x hx => hf x (Multiset.mem_cons_of_mem hx))]
  have htval := hmul s hlocal
  rw [hst] at htval
  have hpzero : Ideal.Quotient.mk P p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hpP
  have hqzero : Ideal.Quotient.mk Q q = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hqQ
  simp only [t, map_neg, map_add, hpzero, hqzero, zero_add, add_zero] at htval
  rw [← neg_one_mul (Ideal.Quotient.mk P q), map_mul, A3_cubicChar_neg_one, one_mul,
    ← neg_one_mul (Ideal.Quotient.mk Q p), map_mul, A3_cubicChar_neg_one, one_mul] at htval
  exact htval

theorem cubic_reciprocity_primary
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    cubicChar P hPgood (Ideal.Quotient.mk P q) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q p) := by
  by_cases hPQ : P = Q
  · have hqP : q ∈ P := by rw [hPQ, hQ]; exact Ideal.subset_span (by simp)
    have hpQ : p ∈ Q := by rw [← hPQ, hP]; exact Ideal.subset_span (by simp)
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hqP,
      Ideal.Quotient.eq_zero_iff_mem.mpr hpQ, MulChar.map_zero, MulChar.map_zero]
  · by_cases hchar : ringChar (O ⧸ Q) = ringChar (O ⧸ P)
    · exact cubic_reciprocity_equal_residue_char P Q hPgood hQgood hPQ hchar
        p q hP hQ hpprimary hqprimary
    · exact cubic_reciprocity_distinct_residue_char P Q hPgood hQgood hchar
        p q hP hQ hpprimary hqprimary

theorem canonicalSextic_sq_reciprocity_primary
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    (canonicalSextic P hPgood (Ideal.Quotient.mk P q)) ^ 2 =
      (canonicalSextic Q hQgood (Ideal.Quotient.mk Q p)) ^ 2 := by
  have hP2 : (canonicalSextic P hPgood (Ideal.Quotient.mk P q)) ^ 2 =
      ConcreteTraceCRT.eisEmbedding (cubicChar P hPgood (Ideal.Quotient.mk P q)) := by
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), canonicalSextic_pow_two]
    rfl
  have hQ2 : (canonicalSextic Q hQgood (Ideal.Quotient.mk Q p)) ^ 2 =
      ConcreteTraceCRT.eisEmbedding (cubicChar Q hQgood (Ideal.Quotient.mk Q p)) := by
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), canonicalSextic_pow_two]
    rfl
  rw [hP2, hQ2, cubic_reciprocity_primary P Q hPgood hQgood p q hP hQ hpprimary hqprimary]

def cubicTwoIdeal : Ideal O := Ideal.span {(-2 : O)}

instance cubicTwoIdeal_isMaximal : cubicTwoIdeal.IsMaximal := by
  rcases rational_prime_factor_cases 2 Nat.prime_two with hm |
      ⟨a, b, _, _, _, ha, _, _, _⟩
  · simpa only [cubicTwoIdeal, Ideal.span_singleton_neg, Nat.cast_ofNat] using hm
  · have hin : (Ideal.span {a} : Ideal O) ∈ {I : Ideal O | Ideal.absNorm I = 2} := by
      change Ideal.absNorm (Ideal.span {a}) = 2
      rwa [← qNat_eq_absNorm_span]
    rw [ShortDraftHeckeBridge.norm_p_fiber_inert Nat.prime_two (by decide)] at hin
    exact False.elim hin

theorem cubicTwoIdeal_good : lambda ∉ cubicTwoIdeal := by
  apply primary_maximal_divisor_good (-2 : O) neg_two_primary
  exact Ideal.subset_span (by simp)

theorem cubicTwoIdeal_residue_char : ringChar (O ⧸ cubicTwoIdeal) = 2 := by
  let : Field (O ⧸ cubicTwoIdeal) := Ideal.Quotient.field cubicTwoIdeal
  let : Fintype (O ⧸ cubicTwoIdeal) := Fintype.ofFinite _
  have hmem : (2 : O) ∈ cubicTwoIdeal := by
    rw [cubicTwoIdeal, Ideal.span_singleton_neg]
    exact Ideal.subset_span (by simp)
  have hz : (2 : O ⧸ cubicTwoIdeal) = 0 := by
    simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  exact (Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime (O ⧸ cubicTwoIdeal) _)
    Nat.prime_two).mp ((ringChar.spec (O ⧸ cubicTwoIdeal) 2).mp hz)

theorem canonicalSextic_four_eq_fixed_two
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (p : O) (hP : P = Ideal.span {p}) (hprimary : lambda ^ 2 ∣ p - 1) :
    canonicalSextic P hgood (Ideal.Quotient.mk P (4 : O)) =
      ConcreteTraceCRT.eisEmbedding
        (cubicChar cubicTwoIdeal cubicTwoIdeal_good (Ideal.Quotient.mk cubicTwoIdeal p)) := by
  have hfour : Ideal.Quotient.mk P (4 : O) = (Ideal.Quotient.mk P (-2 : O)) ^ 2 := by
    simp only [map_ofNat, map_neg]
    ring
  rw [hfour, map_pow, ← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0),
    canonicalSextic_pow_two]
  change ConcreteTraceCRT.eisEmbedding (cubicChar P hgood (Ideal.Quotient.mk P (-2 : O))) = _
  congr 1
  exact cubic_reciprocity_primary P cubicTwoIdeal hgood cubicTwoIdeal_good
    p (-2) hP rfl hprimary neg_two_primary

theorem canonicalSextic_four_prod_eq_fixed_two
    {ι : Type*} (s : Finset ι) (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (p : ι → O)
    (hP : ∀ i ∈ s, P i = Ideal.span {p i})
    (hprimary : ∀ i ∈ s, lambda ^ 2 ∣ p i - 1) :
    (∏ i ∈ s, canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) (4 : O))) =
      ConcreteTraceCRT.eisEmbedding (cubicChar cubicTwoIdeal cubicTwoIdeal_good
        (Ideal.Quotient.mk cubicTwoIdeal (∏ i ∈ s, p i))) := by
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact canonicalSextic_four_eq_fixed_two (P i) (hgood i) (p i) (hP i hi) (hprimary i hi)

theorem canonicalSextic_four_prod_eq_one_of_mod_two
    {ι : Type*} (s : Finset ι) (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (p : ι → O)
    (hP : ∀ i ∈ s, P i = Ideal.span {p i})
    (hprimary : ∀ i ∈ s, lambda ^ 2 ∣ p i - 1)
    (hmod : (2 : O) ∣ (∏ i ∈ s, p i) - 1) :
    (∏ i ∈ s, canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) (4 : O))) = 1 := by
  have hmem : (∏ i ∈ s, p i) - 1 ∈ cubicTwoIdeal := by
    rw [cubicTwoIdeal, Ideal.span_singleton_neg]
    exact Ideal.mem_span_singleton.mpr hmod
  have heq : Ideal.Quotient.mk cubicTwoIdeal (∏ i ∈ s, p i) = 1 := by
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    simpa only [map_sub, map_one, sub_eq_zero] using hz
  rw [canonicalSextic_four_prod_eq_fixed_two s P hgood p hP hprimary, heq, map_one, map_one]

end ActualEisensteinCubic

open scoped BigOperators Classical

namespace IdealGaussCRT

theorem sum_square_phase_finite_crt {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, CommRing (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i) (ψ : AddChar T ℂ) :
    (∑ x : T, ψ (x ^ 2)) =
      ∏ i, ∑ y : R i, coordinateAddChar R e ψ i (y ^ 2) := by
  calc
    _ = ∑ x : T, ∏ i, coordinateAddChar R e ψ i ((e x i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [addChar_finite_crt_factor R e ψ (x ^ 2)]
      simp only [map_pow, Pi.pow_apply]
    _ = ∑ x : ∀ i, R i, ∏ i, coordinateAddChar R e ψ i ((x i) ^ 2) :=
      Equiv.sum_comp e.toEquiv
        (fun x : ∀ i, R i => ∏ i, coordinateAddChar R e ψ i ((x i) ^ 2))
    _ = _ := (Fintype.prod_sum (fun i (x : R i) => coordinateAddChar R e ψ i (x ^ 2))).symm

theorem quadratic_gauss_finite_crt_eq_square_sum {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, Field (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i) (ψ : AddChar T ℂ)
    (hψ : ψ.IsPrimitive) (hchar : ∀ i, ringChar (R i) ≠ 2) :
    (∑ x : T, (∏ i, ((quadraticChar (R i)).ringHomComp (Int.castRingHom ℂ)) (e x i)) * ψ x) =
      ∑ x : T, ψ (x ^ 2) := by
  rw [gauss_sum_finite_crt R e
    (fun i => (quadraticChar (R i)).ringHomComp (Int.castRingHom ℂ)) ψ,
    sum_square_phase_finite_crt R e ψ]
  apply Finset.prod_congr rfl
  intro i _
  have hp := coordinateAddChar_isPrimitive R e ψ hψ i
  have hn : coordinateAddChar R e ψ i ≠ 1 := by
    simpa only [AddChar.mulShift_one] using hp (a := 1) one_ne_zero
  exact ShortDraftQuadraticGauss.quadratic_gauss_as_square_phase _ (hchar i) hn

end IdealGaussCRT

namespace QuadraticGaussRay

abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates

theorem canonicalProductGauss_three_eq_quadraticGamma
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) :
    canonicalProductGauss p hp hcop hgood (fun _ => 3) =
      quadraticGammaO (∏ i, p i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) := by
  let c := ∏ i, p i
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let (i : ι) : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ Ideal.span {p i}) := Ideal.Quotient.field _
  let e := productElementCRT p hcop
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  change (∑ x : O ⧸ Ideal.span {c},
    (∏ i, (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 3) (e x i)) * ψ x) /
      (‖eisEmbedding c‖ : ℂ) = (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) / (‖eisEmbedding c‖ : ℂ)
  congr 1
  simp_rw [canonicalSextic_pow_three_quadratic]
  exact IdealGaussCRT.quadratic_gauss_finite_crt_eq_square_sum
    (fun i => O ⧸ Ideal.span {p i}) e ψ
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc) hchar

theorem I_zpow_eq_of_mod_four {a b : ℤ} (h : (a : ZMod 4) = b) :
    Complex.I ^ a = Complex.I ^ b := by
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub b a 4).mp h.symm
  have ha : a = b + 4 * k := by omega
  rw [ha, zpow_add₀ Complex.I_ne_zero, zpow_mul]
  norm_num

theorem fourTerms_eq_of_mod_four {a b c d : ℤ}
    (ha : (a : ZMod 4) = c) (hb : (b : ZMod 4) = d) :
    breveGaussianFourTerms a b = breveGaussianFourTerms c d := by
  have hn : ((-b : ℤ) : ZMod 4) = (-d : ℤ) := by simpa using congrArg Neg.neg hb
  have hs : ((b-a : ℤ) : ZMod 4) = (d-c : ℤ) := by
    push_cast
    rw [ha, hb]
  rw [breveGaussianFourTerms_formula, breveGaussianFourTerms_formula,
    I_zpow_eq_of_mod_four ha, I_zpow_eq_of_mod_four hn, I_zpow_eq_of_mod_four hs]

def quadraticRayValue (r : EisensteinEPrimaryPhase.Coord) : ℂ :=
  breveGaussianFourTerms (r.1.val : ℤ) (r.2.val : ℤ)

theorem quadraticGammaO_eq_rayValue (c : O) (hc : c ≠ 0) :
    quadraticGammaO c hc = quadraticRayValue (residue c) := by
  have h := quadraticGammaO_eq_fourTerms (coords c).1 (coords c).2 (by rwa [eval_coords])
  have h' : quadraticGammaO c hc = breveGaussianFourTerms (coords c).1 (coords c).2 := by
    simpa only [eval_coords] using h
  rw [h']
  unfold quadraticRayValue residue
  exact fourTerms_eq_of_mod_four (by simp) (by simp)

theorem quadraticGammaO_eq_of_residue_eq (c d : O) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : residue c = residue d) : quadraticGammaO c hc = quadraticGammaO d hd := by
  rw [quadraticGammaO_eq_rayValue, quadraticGammaO_eq_rayValue, h]

theorem canonicalProductGauss_three_eq_rayValue
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) :
    canonicalProductGauss p hp hcop hgood (fun _ => 3) =
      quadraticRayValue (residue (∏ i, p i)) := by
  rw [canonicalProductGauss_three_eq_quadraticGamma p hp hcop hgood hchar,
    quadraticGammaO_eq_rayValue]

open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates

theorem fixed_two_mk_eq_residue_lift (c : O) :
    Ideal.Quotient.mk cubicTwoIdeal c =
      Ideal.Quotient.mk cubicTwoIdeal (lift (residue c)) := by
  obtain ⟨z, hz⟩ := congr_mod_four_of_residue_eq (residue_lift (residue c)).symm
  apply Ideal.Quotient.eq.mpr
  rw [cubicTwoIdeal, Ideal.mem_span_singleton]
  refine ⟨(-2 : O) * z, ?_⟩
  calc
    c - lift (residue c) = 4 * z := hz
    _ = (-2 : O) * (-2 * z) := by ring

def fixedGValue (r : EisensteinEPrimaryPhase.Coord) : ℂ :=
  (eisEmbedding (cubicChar cubicTwoIdeal cubicTwoIdeal_good
    (Ideal.Quotient.mk cubicTwoIdeal (lift r))))⁻¹ * quadraticRayValue r

theorem residue_eq_of_four_dvd_sub (c d : O) (h : (4 : O) ∣ c - d) :
    residue c = residue d := by
  obtain ⟨z, hz⟩ := h
  have he : c = eval ((coords d).1 + 4 * (coords z).1)
      ((coords d).2 + 4 * (coords z).2) := by
    calc
      c = d + 4 * z := by linear_combination hz
      _ = eval (coords d).1 (coords d).2 + 4 * eval (coords z).1 (coords z).2 := by
        rw [eval_coords, eval_coords]
      _ = _ := by simp only [eval]; push_cast; ring
  rw [he, residue_eval]
  simp only [residue, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
    show (4 : ZMod 4) = 0 by decide, zero_mul, add_zero]

theorem residue_eq_of_quotient_four_eq (c d : O)
    (h : Ideal.Quotient.mk (Ideal.span {(4 : O)}) c =
      Ideal.Quotient.mk (Ideal.span {(4 : O)}) d) : residue c = residue d :=
  residue_eq_of_four_dvd_sub c d (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h))

def residueQuotientFour : (O ⧸ Ideal.span {(4 : O)}) → EisensteinEPrimaryPhase.Coord :=
  Quotient.lift residue (fun c d h => residue_eq_of_quotient_four_eq c d (Quotient.sound h))

@[simp] theorem residueQuotientFour_mk (c : O) :
    residueQuotientFour (Ideal.Quotient.mk (Ideal.span {(4 : O)}) c) = residue c := rfl

def fixedGQuotientValue (r : O ⧸ Ideal.span {(4 : O)}) : ℂ :=
  fixedGValue (residueQuotientFour r)

theorem canonicalProductG_eq_fixedGValue
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductG p hp hcop hgood = fixedGValue (residue (∏ i, p i)) := by
  rw [canonicalProductG,
    canonicalSextic_four_prod_eq_fixed_two Finset.univ (fun i => Ideal.span {p i}) hgood p
      (fun i _ => rfl) (fun i _ => hprimary i),
    canonicalProductGauss_three_eq_rayValue p hp hcop hgood hchar,
    fixed_two_mk_eq_residue_lift]
  rfl

theorem canonicalProductG_eq_of_residue_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (q : κ → O) (hq : ∀ i, q i ≠ 0) [∀ i, (Ideal.span {q i}).IsMaximal]
    (kcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {q i})))
    (kgood : ∀ i, lambda ∉ Ideal.span {q i})
    (kchar : ∀ i, ringChar (O ⧸ Ideal.span {q i}) ≠ 2)
    (kprimary : ∀ i, lambda ^ 2 ∣ q i - 1)
    (hres : residue (∏ i, p i) = residue (∏ i, q i)) :
    canonicalProductG p hp hcop hgood = canonicalProductG q hq kcop kgood := by
  rw [canonicalProductG_eq_fixedGValue p hp hcop hgood hchar hprimary,
    canonicalProductG_eq_fixedGValue q hq kcop kgood kchar kprimary, hres]

theorem canonicalProductG_eq_fixed_quotient
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductG p hp hcop hgood =
      fixedGQuotientValue (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i, p i)) :=
  canonicalProductG_eq_fixedGValue p hp hcop hgood hchar hprimary

end QuadraticGaussRay

end

end OAI
