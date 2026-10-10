import Mathlib
import OAI.NumberTheory.CubicGram.SquarefreeGauss
import OAI.NumberTheory.CubicGram.ReciprocityKernel

namespace OAI

/-! Full cubic reciprocity and twisted multiplicativity of Gauss sums. -/

section

noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_of_mul {a b : Eisenstein} (ha : primary a) (hab : primary (a*b)) :
    primary b := by
  rw [primary_iff_residue_one] at ha hab ⊢
  rwa [map_mul, ha, one_mul] at hab

lemma primary_induction {P : Eisenstein → Prop} (h1 : P 1)
    (hmul : ∀ p b, primaryPrime p → primary b → P b → P (p*b))
    {b : Eisenstein} (hb : primary b) : P b := by
  have hall : ∀ n : ℕ, ∀ b : Eisenstein, normNat b = n → primary b → P b := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro b hnorm hb
      by_cases hu : IsUnit b
      · simpa only [primary_unit_eq_one hu hb] using h1
      obtain ⟨q,hq,hqb⟩ := WfDvdMonoid.exists_irreducible_factor hu (primary_ne_zero hb)
      let p := primaryNormalize q
      have hp : primaryPrime p := ⟨primaryNormalize_primary
        (unit_residue_of_dvd_primary hb hqb), prime_primaryNormalize hq.prime⟩
      have hpb : p ∣ b := (primaryNormalize_associated q).dvd_iff_dvd_left.mp hqb
      obtain ⟨c,rfl⟩ := hpb
      have hc := primary_of_mul hp.1 hb
      apply hmul p c hp hc
      apply ih (normNat c) _ c rfl hc
      have hpN : 1 < normNat p := by
        have hp0 := normNat_ne_zero hp.2.ne_zero
        have hp1 : normNat p ≠ 1 := by
          intro heq
          apply hp.2.not_isUnit
          apply isUnit_of_norm_eq_one
          rw [← normNat_cast, heq, Nat.cast_one]
        omega
      have hc0 := normNat_ne_zero (primary_ne_zero hc)
      rw [← hnorm, normNat_mul]
      nlinarith [Nat.pos_of_ne_zero hc0]
  exact hall _ _ rfl hb

lemma primary_one : primary (1 : Eisenstein) := by simp [primary]

lemma cubicSymbol_one_lower (v : Eisenstein) : cubicSymbol 1 v = 1 := by
  simp [cubicSymbol]

lemma cubicSymbol_neg {b : Eisenstein} (hb : primary b) (v : Eisenstein) :
    cubicSymbol b (-v) = cubicSymbol b v := by
  revert v
  apply primary_induction (b := b) ?_ ?_ hb
  · intro v
    simp only [cubicSymbol_one_lower]
  · intro p b hp hb ih v
    rw [cubicSymbol_mul_lower hp.2.ne_zero (primary_ne_zero hb),
      cubicSymbol_mul_lower hp.2.ne_zero (primary_ne_zero hb),
      cubicSymbol_prime hp, cubicSymbol_prime hp, cubicSymbolAtPrime_neg hp, ih v]

lemma cubicSymbol_conjugate {b : Eisenstein} (hb : primary b) (v : Eisenstein) :
    cubicSymbol (conjugate b) (conjugate v) = star (cubicSymbol b v) := by
  revert v
  apply primary_induction (b := b) ?_ ?_ hb
  · intro v
    simp only [map_one, cubicSymbol_one_lower, star_one]
  · intro p b hp hb ih v
    rw [map_mul, cubicSymbol_mul_lower (primaryPrime_conjugate hp).2.ne_zero
      (primary_ne_zero (primary_conjugate hb)),
      cubicSymbol_mul_lower hp.2.ne_zero (primary_ne_zero hb),
      cubicSymbol_prime (primaryPrime_conjugate hp), cubicSymbol_prime hp,
      cubicSymbolAtPrime_conjugate hp, ih v, star_mul']

lemma reciprocity_of_prime_divisor_relation {p b : Eisenstein} (hp : primaryPrime p)
    (hb : primary b)
    (hrel : ∀ q, primaryPrime q → q ∣ b →
      cubicSymbolAtPrime q p = cubicSymbolAtPrime p q) :
    cubicSymbol b p = cubicSymbolAtPrime p b := by
  revert hrel
  apply primary_induction (b := b) ?_ ?_ hb
  · intro hrel
    rw [cubicSymbol_one_lower, cubicSymbolAtPrime_one hp]
  · intro q b hq hb ih hrel
    rw [cubicSymbol_mul_lower hq.2.ne_zero (primary_ne_zero hb),
      cubicSymbol_prime hq, cubicSymbolAtPrime_mul hp,
      hrel q hq (dvd_mul_right q b), ih]
    intro r hr hrb
    exact hrel r hr (dvd_mul_of_dvd_right hrb q)

lemma same_char_primary_primes {p r : Eisenstein} (hp : primaryPrime p)
    (hr : primaryPrime r) (hchar : ringChar (Residues r) = ringChar (Residues p)) :
    r = p ∨ r = conjugate p := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : (modulus r).IsPrime := (Ideal.span_singleton_prime hr.2.ne_zero).mpr hr.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Finite (Residues r) := finite_residues hr.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Fintype (Residues r) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  let : Field (Residues r) := Fintype.fieldOfDomain _
  obtain ⟨n, hn, hcard⟩ := FiniteField.card (Residues p) (ringChar (Residues p))
  have hN : normNat p = ringChar (Residues r) ^ (n : ℕ) := by
    rw [← hchar, ← Nat.card_eq_fintype_card, residues_card hp.2.ne_zero] at hcard
    exact hcard
  have hdiv : r ∣ (normNat p : Eisenstein) := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_natCast, hN, Nat.cast_pow, CharP.cast_eq_zero, zero_pow n.ne_zero]
  rw [normNat_cast_eq_mul_conjugate] at hdiv
  rcases hr.2.dvd_or_dvd hdiv with hrp | hrp
  · exact Or.inl (primary_associated_eq hr.1 hp.1 (hr.2.associated_of_dvd hp.2 hrp))
  · exact Or.inr (primary_associated_eq hr.1 (primary_conjugate hp.1)
      (hr.2.associated_of_dvd (primaryPrime_conjugate hp).2 hrp))

lemma cubic_reciprocity_conjugate {p : Eisenstein} (hp : primaryPrime p) :
    cubicSymbolAtPrime (conjugate p) p = cubicSymbolAtPrime p (conjugate p) := by
  by_cases heq : p = conjugate p
  · rw [← heq]
  let t : Eisenstein := -(p + conjugate p)
  have ht : primary t := by
    obtain ⟨a, ha⟩ := hp.1
    obtain ⟨b, hb⟩ := primary_conjugate hp.1
    refine ⟨-a-b-1, ?_⟩
    dsimp [t]
    linear_combination -ha-hb
  have htconj : conjugate t = t := by simp [t, add_comm]
  have hnot : ¬p ∣ t := by
    intro h
    have hsum : p ∣ p + conjugate p := by simpa only [t, dvd_neg] using h
    have hpc : p ∣ conjugate p := (dvd_add_right (dvd_refl p)).mp hsum
    exact heq (primary_associated_eq hp.1 (primary_conjugate hp.1)
      (hp.2.associated_of_dvd (primaryPrime_conjugate hp).2 hpc))
  have hnotconj : ¬conjugate p ∣ t := by
    intro h
    have hh := map_dvd conjugate h
    rw [conjugate_conjugate, htconj] at hh
    exact hnot hh
  have hrec : cubicSymbol t p = cubicSymbolAtPrime p t := by
    apply reciprocity_of_prime_divisor_relation hp ht
    intro q hq hqt
    apply cubic_reciprocity_distinct_char hp hq
    intro hc
    rcases same_char_primary_primes hp hq hc with rfl | rfl
    · exact hnot hqt
    · exact hnotconj hqt
  have hA : cubicSymbolAtPrime p t = cubicSymbolAtPrime p (conjugate p) := by
    calc
      _ = cubicSymbolAtPrime p (-conjugate p) := by
        apply cubicSymbolAtPrime_congr
        apply residue_eq_of_dvd_sub
        refine ⟨-1, ?_⟩
        dsimp [t]
        ring
      _ = _ := cubicSymbolAtPrime_neg hp _
  have hfixed : cubicSymbol t p = star (cubicSymbol t p) := by
    calc
      _ = cubicSymbol t (-conjugate p) := by
        apply cubicSymbol_congr
        apply residue_eq_of_dvd_sub
        refine ⟨-1, ?_⟩
        dsimp [t]
        ring
      _ = cubicSymbol t (conjugate p) := cubicSymbol_neg ht _
      _ = cubicSymbol (conjugate t) (conjugate p) := by rw [htconj]
      _ = _ := cubicSymbol_conjugate ht p
  rw [hrec, hA] at hfixed
  calc
    _ = star (cubicSymbolAtPrime p (conjugate p)) := by
      simpa only [conjugate_conjugate] using cubicSymbolAtPrime_conjugate hp (conjugate p)
    _ = _ := hfixed.symm

theorem cubic_reciprocity_prime {p r : Eisenstein} (hp : primaryPrime p)
    (hr : primaryPrime r) : cubicSymbolAtPrime r p = cubicSymbolAtPrime p r := by
  by_cases hc : ringChar (Residues r) = ringChar (Residues p)
  · rcases same_char_primary_primes hp hr hc with rfl | rfl
    · rfl
    · exact cubic_reciprocity_conjugate hp
  · exact cubic_reciprocity_distinct_char hp hr hc

theorem cubic_reciprocity {a b : Eisenstein} (ha : primary a) (hb : primary b) :
    cubicSymbol a b = cubicSymbol b a := by
  revert b
  apply primary_induction (b := a) ?_ ?_ ha
  · intro b hb
    rw [cubicSymbol_one_lower]
    unfold cubicSymbol
    have h : ∀ p ∈ normalizedFactors b,
        cubicSymbolAtPrime (primaryNormalize p) 1 = 1 := by
      intro p hp
      apply cubicSymbolAtPrime_one
      exact ⟨primaryNormalize_primary (unit_residue_of_dvd_primary hb
        (dvd_of_mem_normalizedFactors hp)), prime_primaryNormalize (prime_of_normalized_factor p hp)⟩
    symm
    apply Multiset.prod_eq_one
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hz
    exact h p hp
  · intro p a hp ha ih b hb
    rw [cubicSymbol_mul_lower hp.2.ne_zero (primary_ne_zero ha),
      cubicSymbol_prime hp, cubicSymbol_mul_upper hb, ih hb]
    congr 1
    symm
    exact reciprocity_of_prime_divisor_relation hp hb
      (fun q hq _ => cubic_reciprocity_prime hp hq)

theorem gauss_twisted_mul {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hab : IsCoprime a b) : gauss (a*b) = gauss a * gauss b * cubicSymbol b a ^ 2 := by
  rw [gauss_mul_of_isCoprime ha hb hab, cubic_reciprocity ha hb, pow_two]

lemma cubicSymbolAtPrime_sq_eq_star {p : Eisenstein} (hp : primaryPrime p) (v : Eisenstein) :
    cubicSymbolAtPrime p v ^ 2 = star (cubicSymbolAtPrime p v) := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  have hχ : cubicResidueChar p hp ^ 2 = (cubicResidueChar p hp)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_succ, cubicResidueChar_cube hp]
  rw [← cubicResidueChar_mk p hp, ← MulChar.pow_apply' _ (by norm_num),
    hχ, MulChar.star_apply']

lemma cubicSymbol_sq_eq_star {b : Eisenstein} (hb : primary b) (v : Eisenstein) :
    cubicSymbol b v ^ 2 = star (cubicSymbol b v) := by
  revert v
  apply primary_induction (b := b) ?_ ?_ hb
  · intro v
    simp only [cubicSymbol_one_lower, one_pow, star_one]
  · intro p b hp hb ih v
    rw [cubicSymbol_mul_lower hp.2.ne_zero (primary_ne_zero hb), cubicSymbol_prime hp,
      mul_pow, cubicSymbolAtPrime_sq_eq_star hp, ih v, star_mul']

lemma cubicSymbolAtPrime_eq_zero_of_dvd {p : Eisenstein} (hp : primaryPrime p)
    {v : Eisenstein} (hv : p ∣ v) : cubicSymbolAtPrime p v = 0 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  have heq : Ideal.Quotient.mk (modulus p) v = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hv)
  rw [← cubicResidueChar_mk p hp, heq, MulChar.map_zero]

lemma cubicSymbol_eq_zero_of_not_isCoprime {b : Eisenstein} (hb : primary b)
    {v : Eisenstein} (hv : ¬IsCoprime b v) : cubicSymbol b v = 0 := by
  revert v
  apply primary_induction (b := b) ?_ ?_ hb
  · intro v hv
    exact (hv (isCoprime_one_left)).elim
  · intro p b hp hb ih v hv
    rw [cubicSymbol_mul_lower hp.2.ne_zero (primary_ne_zero hb), cubicSymbol_prime hp]
    by_cases h : IsCoprime p v
    · have h' : ¬IsCoprime b v := fun h' => hv (h.mul_left h')
      rw [ih h', mul_zero]
    · have hd : p ∣ v := by
        by_contra hd
        exact h (isRelPrime_iff_isCoprime.mp (hp.2.irreducible.isRelPrime_iff_not_dvd.mpr hd))
      rw [cubicSymbolAtPrime_eq_zero_of_dvd hp hd, zero_mul]

theorem gauss_mul {a b : Eisenstein} (ha : primary a) (hb : primary b) :
    gauss (a*b) = gauss a * gauss b * star (cubicSymbol b a) := by
  by_cases hab : IsCoprime a b
  · rw [gauss_twisted_mul ha hb hab, cubicSymbol_sq_eq_star hb]
  · have hs : ¬Squarefree (a*b) := fun hs =>
      hab (isRelPrime_iff_isCoprime.mp (IsRelPrime.of_squarefree_mul hs))
    rw [gauss_eq_zero_of_not_squarefree (primary_mul ha hb) hs,
      cubicSymbol_eq_zero_of_not_isCoprime hb (fun h => hab h.symm), star_zero, mul_zero]

end CubicFirstMoment
end
end

end OAI
