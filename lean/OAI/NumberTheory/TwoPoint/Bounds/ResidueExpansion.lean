import OAI.NumberTheory.TwoPoint.Bounds.Dilation
import OAI.NumberTheory.TwoPoint.Bounds.CharacterTwists
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

namespace OAI

/-!
# Residue classes as finite multiplicative expansions

The character identity in manuscript Lemma `lem:affine-residue` includes
nonunit residue classes. Dividing by the gcd reduces to a unit class, so the
standard character orthogonality relation applies even when the reduced
modulus is one. Each resulting dilation has the finite expansion already
proved in `Dilation`.
-/

open scoped BigOperators ComplexConjugate

namespace TwoPointCorrelations

/-- A character evaluated on the natural numbers, with its usual zeros. -/
noncomputable def naturalCharacter {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ (n : ZMod q)

lemma naturalCharacter_multiplicative {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Multiplicative (naturalCharacter χ) := by
  intro m n _ _ _
  simp [naturalCharacter, map_mul]

lemma naturalCharacter_oneBounded {q : ℕ} (χ : DirichletCharacter ℂ q) :
    OneBounded (naturalCharacter χ) := by
  intro n _
  exact χ.norm_le_one _

@[simp] lemma naturalCharacter_one {q : ℕ} (χ : DirichletCharacter ℂ q) :
    naturalCharacter χ 1 = 1 := by simp [naturalCharacter]

/-- The inverse-value form of conjugation on a unit residue. -/
lemma character_conj_unit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a : ZMod q} (ha : IsUnit a) : conj (χ a) = χ a⁻¹ := by
  rw [show conj (χ a) = χ⁻¹ a from MulChar.star_apply' χ a, MulChar.inv_apply]
  obtain ⟨u, rfl⟩ := ha
  rw [Ring.inverse_unit, ZMod.inv_coe_unit]

lemma residue_character_orthogonality {q c k : ℕ} (hq : 0 < q)
    (hc : c.Coprime q) :
    (if k % q = c % q then (1 : ℂ) else 0) =
      (q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, conj (naturalCharacter χ c) * naturalCharacter χ k := by
  let : NeZero q := ⟨hq.ne'⟩
  have hcunit : IsUnit (c : ZMod q) := (ZMod.isUnit_iff_coprime c q).mpr hc
  have hs := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hcunit (k : ZMod q)
  have htot : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  have heq : ((c : ZMod q) = (k : ZMod q)) ↔ k % q = c % q := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact eq_comm
  simp_rw [naturalCharacter, character_conj_unit _ hcunit]
  simp only [hs, heq]
  split_ifs <;> simp_all

lemma scaled_residue_iff {d q c n : ℕ} (hd : 0 < d) (hn : d ∣ n) :
    n % (d * q) = (d * c) % (d * q) ↔ (n / d) % q = c % q := by
  obtain ⟨k, rfl⟩ := hn
  rw [Nat.mul_div_cancel_left k hd, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left]
  exact Nat.mul_left_cancel_iff hd

lemma dvd_of_scaled_residue {d q c n : ℕ}
    (h : n % (d * q) = (d * c) % (d * q)) : d ∣ n := by
  have hr : d ∣ n % (d * q) := by
    rw [h, Nat.mul_mod_mul_left]
    exact dvd_mul_right d _
  have ht : d ∣ (d * q) * (n / (d * q)) := dvd_mul_of_dvd_left (dvd_mul_right d q) _
  simpa only [Nat.mod_add_div] using dvd_add hr ht

/-- Gcd reduction followed by character orthogonality, valid also for `b = 0`
and for reduced modulus one. No assumption that the original class is a unit
is present. -/
theorem residue_indicator_eq_character_dilations (l b n : ℕ) (hl : 0 < l) :
    (if n % l = b % l then (1 : ℂ) else 0) =
      ((l / b.gcd l).totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ (l / b.gcd l),
          conj (naturalCharacter χ (b / b.gcd l)) *
            dilate (b.gcd l) (naturalCharacter χ) n := by
  let d := b.gcd l
  let q := l / d
  let c := b / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_right b hl
  have hdl : d ∣ l := Nat.gcd_dvd_right b l
  have hdb : d ∣ b := Nat.gcd_dvd_left b l
  have hlq : l = d * q := (Nat.mul_div_cancel' hdl).symm
  have hbc : b = d * c := (Nat.mul_div_cancel' hdb).symm
  have hq : 0 < q := Nat.div_pos (Nat.le_of_dvd hl hdl) hd
  have hc : c.Coprime q := Nat.coprime_div_gcd_div_gcd hd
  change (if n % l = b % l then (1 : ℂ) else 0) =
    (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
      conj (naturalCharacter χ c) * dilate d (naturalCharacter χ) n
  by_cases hn : d ∣ n
  · simp only [dilate, ite_eq_left hn]
    rw [hlq, hbc]
    simp only [scaled_residue_iff hd hn]
    exact residue_character_orthogonality hq hc
  · have hnres : n % l ≠ b % l := by
      intro h
      apply hn
      apply dvd_of_scaled_residue (q := q) (c := c)
      simpa only [← hlq, ← hbc] using h
    simp [hnres, dilate, hn]

/-- Every residue indicator is an explicit finite sum of bounded normalized
multiplicative functions. -/
theorem residue_indicator_eq_components (l b n : ℕ) (hl : 0 < l) (hn : 0 < n) :
    (if n % l = b % l then (1 : ℂ) else 0) =
      ((l / b.gcd l).totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ (l / b.gcd l),
          ∑ E ∈ (b.gcd l).primeFactors.powerset,
            (conj (naturalCharacter χ (b / b.gcd l)) * (-1 : ℂ) ^ E.card) *
              dilationComponent (b.gcd l) (naturalCharacter χ) E n := by
  rw [residue_indicator_eq_character_dilations l b n hl]
  congr 1
  apply Finset.sum_congr rfl
  intro χ _
  rw [dilate_eq_sum_components (b.gcd l) (naturalCharacter χ)
    (Nat.gcd_pos_of_pos_right b hl) (naturalCharacter_multiplicative χ)
    (naturalCharacter_one χ) hn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E _
  ring

lemma Multiplicative.mul {f g : ℕ → ℂ} (hf : Multiplicative f) (hg : Multiplicative g) :
    Multiplicative (fun n => f n * g n) := by
  intro m n hm hn hcop
  dsimp only
  rw [hf m n hm hn hcop, hg m n hm hn hcop]
  ring

lemma OneBounded.mul {f g : ℕ → ℂ} (hf : OneBounded f) (hg : OneBounded g) :
    OneBounded (fun n => f n * g n) := by
  intro n hn
  rw [norm_mul]
  exact (mul_le_mul (hf n hn) (hg n hn) (norm_nonneg _) zero_le_one).trans_eq
    (by norm_num)

/-- The multiplicative pieces of a function restricted to a residue class. -/
noncomputable def residueComponent {q : ℕ} (f : ℕ → ℂ) (d : ℕ)
    (χ : DirichletCharacter ℂ q) (E : Finset ℕ) (n : ℕ) : ℂ :=
  f n * dilationComponent d (naturalCharacter χ) E n

lemma residueComponent_multiplicative {q : ℕ} (f : ℕ → ℂ) (d : ℕ)
    (χ : DirichletCharacter ℂ q) (E : Finset ℕ) (hf : Multiplicative f) :
    Multiplicative (residueComponent f d χ E) :=
  hf.mul (dilationComponent_multiplicative d (naturalCharacter χ) E)

lemma residueComponent_oneBounded {q : ℕ} (f : ℕ → ℂ) (d : ℕ)
    (χ : DirichletCharacter ℂ q) (E : Finset ℕ) (hf : OneBounded f) :
    OneBounded (residueComponent f d χ E) :=
  hf.mul (dilationComponent_oneBounded d (naturalCharacter χ) E
    (naturalCharacter_oneBounded χ))

/-- Restriction to a nonunit progression modifies the character twist only at
primes dividing the fixed gcd. Hence every multiplicative piece preserves the
original uniformly nonpretentious factor. -/
lemma residueComponent_nonpretentious {q : ℕ} (f : ℕ → ℂ) (d : ℕ)
    (χ : DirichletCharacter ℂ q) (E : Finset ℕ) (hq : 0 < q)
    (hf : OneBounded f) (hfnp : UniformlyNonpretentious f) :
    UniformlyNonpretentious (residueComponent f d χ E) := by
  apply (hfnp.twistByCharacter χ hq).finite_prime_change d.primeFactors
    (hf.twistByCharacter χ) (residueComponent_oneBounded f d χ E hf)
  intro p hp hpD
  unfold residueComponent TwoPointCorrelations.twistByCharacter
  congr 1
  simpa only [pow_one, naturalCharacter] using
    dilationComponent_prime_pow d (naturalCharacter χ) E (naturalCharacter_one χ) hp hpD 1

/-- An explicit expansion after multiplication by the original first factor. -/
theorem residue_weight_eq_components (f : ℕ → ℂ) (l b n : ℕ)
    (hl : 0 < l) (hn : 0 < n) :
    (if n % l = b % l then f n else 0) =
      ((l / b.gcd l).totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ (l / b.gcd l),
          ∑ E ∈ (b.gcd l).primeFactors.powerset,
            (conj (naturalCharacter χ (b / b.gcd l)) * (-1 : ℂ) ^ E.card) *
              residueComponent f (b.gcd l) χ E n := by
  calc
    _ = f n * (if n % l = b % l then (1 : ℂ) else 0) := by split_ifs <;> simp
    _ = _ := by
      rw [residue_indicator_eq_components l b n hl hn, mul_left_comm]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E _
      unfold residueComponent
      ring

end TwoPointCorrelations

end OAI
