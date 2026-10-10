import Mathlib

namespace OAI

namespace Ostmann.QuadraticSieve

def jacobiResidue (q : ℕ) (a : ZMod q) : ℤ := jacobiSym (ZMod.cast a) q

@[simp] theorem jacobiResidue_intCast (q : ℕ) (a : ℤ) :
    jacobiResidue q (a : ZMod q) = jacobiSym a q := by
  apply jacobiSym.mod_left'
  exact (ZMod.intCast_eq_intCast_iff' _ _ q).mp (ZMod.intCast_zmod_cast _)

noncomputable def jacobiDirichletCharacterInt (q : ℕ) [NeZero q] : DirichletCharacter ℤ q where
  toFun := jacobiResidue q
  map_one' := by
    simpa only [Int.cast_one, jacobiSym.one_left] using jacobiResidue_intCast q 1
  map_mul' a b := by
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective a
    obtain ⟨b, rfl⟩ := ZMod.intCast_surjective b
    rw [← Int.cast_mul, jacobiResidue_intCast, jacobiResidue_intCast,
      jacobiResidue_intCast, jacobiSym.mul_left]
  map_nonunit' a ha := by
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective a
    rw [jacobiResidue_intCast]
    apply jacobiSym.eq_zero_iff_not_coprime.mpr
    intro h
    apply ha
    rw [ZMod.coe_int_isUnit_iff_isCoprime, isCoprime_comm, Int.isCoprime_iff_gcd_eq_one]
    exact h

@[simp] theorem jacobiDirichletCharacterInt_intCast (q : ℕ) [NeZero q] (a : ℤ) :
    jacobiDirichletCharacterInt q (a : ZMod q) = jacobiSym a q :=
  jacobiResidue_intCast q a

noncomputable def jacobiDirichletCharacter (q : ℕ) [NeZero q] : DirichletCharacter ℂ q :=
  (jacobiDirichletCharacterInt q).ringHomComp (Int.castRingHom ℂ)

@[simp] theorem jacobiDirichletCharacter_intCast (q : ℕ) [NeZero q] (a : ℤ) :
    jacobiDirichletCharacter q (a : ZMod q) = (jacobiSym a q : ℂ) := by
  simp only [jacobiDirichletCharacter, MulChar.ringHomComp_apply,
    jacobiDirichletCharacterInt_intCast]
  rfl

@[simp] theorem jacobiDirichletCharacter_natCast (q a : ℕ) [NeZero q] :
    jacobiDirichletCharacter q (a : ZMod q) = (jacobiSym (a : ℤ) q : ℂ) := by
  simpa only [Int.cast_natCast] using jacobiDirichletCharacter_intCast q (a : ℤ)

theorem jacobiDirichletCharacter_isQuadratic (q : ℕ) [NeZero q] :
    (jacobiDirichletCharacter q).IsQuadratic := by
  intro a
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective a
  rw [jacobiDirichletCharacter_intCast]
  rcases jacobiSym.trichotomy a q with h | h | h <;> simp [h]

@[simp] theorem jacobiDirichletCharacter_inv (q : ℕ) [NeZero q] :
    (jacobiDirichletCharacter q)⁻¹ = jacobiDirichletCharacter q :=
  (jacobiDirichletCharacter_isQuadratic q).inv

theorem jacobiDirichletCharacter_one_isPrimitive :
    (jacobiDirichletCharacter 1).IsPrimitive := by
  rw [DirichletCharacter.level_one (jacobiDirichletCharacter 1)]
  exact DirichletCharacter.isPrimitive_one_level_one

theorem jacobi_nat_modEq {q a b : ℕ} (h : a ≡ b [MOD q]) :
    jacobiSym (a : ℤ) q = jacobiSym (b : ℤ) q := by
  apply jacobiSym.mod_left'
  exact_mod_cast h

theorem exists_jacobi_neg_one_congr_one {q p d : ℕ}
    (hq : Odd q) (hsq : Squarefree q) (hp : p.Prime) (hpq : p ∣ q)
    (hdq : d ∣ q) (hpd : ¬p ∣ d) :
    ∃ a : ℕ, a ≡ 1 [MOD d] ∧ jacobiSym (a : ℤ) q = -1 := by
  let r := q / p
  have hpr : p * r = q := Nat.mul_div_cancel' hpq
  have hsplit := Nat.squarefree_mul_iff.mp (show Squarefree (p * r) by rwa [hpr])
  have hdr : d ∣ r :=
    (hp.coprime_iff_not_dvd.mpr hpd).symm.dvd_of_dvd_mul_left (hpr.symm ▸ hdq)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := quadraticChar_exists_neg_one (F := ZMod p)
    (by simpa only [ZMod.ringChar_zmod_n] using hq.ne_two_of_dvd_nat hpq)
  have hzj : jacobiSym (z.val : ℤ) p = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym]
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hz
  obtain ⟨a, hap, har⟩ := Nat.chineseRemainder hsplit.1 z.val 1
  refine ⟨a, har.of_dvd hdr, ?_⟩
  rw [← hpr, jacobiSym.mul_right' _ hp.ne_zero hsplit.2.2.ne_zero,
    jacobi_nat_modEq hap, jacobi_nat_modEq har, hzj]
  simp

theorem prime_dvd_jacobiDirichletCharacter_conductor {q p : ℕ} [NeZero q]
    (hq : Odd q) (hsq : Squarefree q) (hp : p.Prime) (hpq : p ∣ q) :
    p ∣ (jacobiDirichletCharacter q).conductor := by
  by_contra hpd
  obtain ⟨a, ha, hja⟩ := exists_jacobi_neg_one_congr_one hq hsq hp hpq
    (jacobiDirichletCharacter q).conductor_dvd_level hpd
  have hgcd : Int.gcd (a : ℤ) (q : ℤ) = 1 := by
    by_contra h
    have hz := jacobiSym.eq_zero_iff_not_coprime.mpr h
    rw [hja] at hz
    norm_num at hz
  have hc : IsCoprime (a : ℤ) (q : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
  have ha' : ((a : ℤ) : ZMod (jacobiDirichletCharacter q).conductor) = 1 := by
    simpa only [Int.cast_natCast, Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff a 1 (jacobiDirichletCharacter q).conductor).mpr ha
  have hvalue : (jacobiDirichletCharacter q).primitiveCharacter (a : ℤ) = (-1 : ℂ) := by
    rw [DirichletCharacter.primitiveCharacter_apply_of_isCoprime _ hc,
      jacobiDirichletCharacter_intCast, hja]
    norm_num
  rw [ha', map_one] at hvalue
  norm_num at hvalue

theorem jacobiDirichletCharacter_isPrimitive {q : ℕ} [NeZero q]
    (hq : Odd q) (hsq : Squarefree q) :
    (jacobiDirichletCharacter q).IsPrimitive := by
  change (jacobiDirichletCharacter q).conductor = q
  apply Nat.dvd_antisymm (jacobiDirichletCharacter q).conductor_dvd_level
  have hprod : (∏ p ∈ q.primeFactors, p) ∣ (jacobiDirichletCharacter q).conductor := by
    apply (Nat.prod_primeFactors_dvd_iff (jacobiDirichletCharacter q).conductor_ne_zero).mpr
    intro p hp
    obtain ⟨hpp, hpq⟩ := (Nat.mem_primeFactors_of_ne_zero hsq.ne_zero).mp hp
    exact (Nat.mem_primeFactors_of_ne_zero (jacobiDirichletCharacter q).conductor_ne_zero).mpr
      ⟨hpp, prime_dvd_jacobiDirichletCharacter_conductor hq hsq hpp hpq⟩
  simpa only [Nat.prod_primeFactors_of_squarefree hsq] using hprod

end Ostmann.QuadraticSieve

end OAI
