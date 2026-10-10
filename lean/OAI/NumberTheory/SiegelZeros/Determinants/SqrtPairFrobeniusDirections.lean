import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Characters.BiquadraticBasis

namespace OAI

namespace SiegelZeros

open scoped Pointwise
open scoped NumberField
namespace WeightedTorusJets

open scoped NumberField

lemma sqrtPair_frobenius_directions {L : Type*} [Field L] [NumberField L]
    (a b : L) (d e : ℚ) (ha : a ^ 2 = algebraMap ℚ L d)
    (hb : b ^ 2 = algebraMap ℚ L e) (hd : ¬ IsSquare d) (he : ¬ IsSquare e)
    (hne : IntermediateField.adjoin ℚ {a} ≠ IntermediateField.adjoin ℚ {b}) :
    let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
    let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    ∃ σ τ : B ≃ₐ[ℚ] B,
      σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
      Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
      (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
      (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
      ∀ (p : ℕ) (φ : L ≃ₐ[ℚ] L), φ a = -a →
        (∀ y : 𝓞 L, (p : 𝓞 L) ∣ y ^ p - φ • y) →
          ((∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - σ • x) ∨
            (∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - (σ * τ) • x)) := by
  dsimp
  let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  obtain ⟨σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm⟩ :=
    sqrtPair_four_automorphisms a b d e ha hb hd he hne
  have ha0 : a ≠ 0 := by
    intro h
    have hmap : algebraMap ℚ L d = 0 := by simpa [h] using ha.symm
    have hd0 : d = 0 := (algebraMap ℚ L).injective (hmap.trans (map_zero _).symm)
    exact hd (hd0 ▸ IsSquare.zero)
  have ha'0 : a' ≠ 0 := fun h => ha0 (congrArg (fun x : B => (x : L)) h)
  have ha'neg : a' ≠ -a' := fun h => ha'0 (CharZero.eq_neg_self_iff.mp h)
  refine ⟨σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, ?_⟩
  intro p φ hφ hfrob
  let : IsGalois ℚ B := sqrtPair_isGalois a b d e ha hb hd he hne
  let ψ := φ.restrictNormal B
  have hψa : ψ a' = -a' := by
    apply Subtype.ext
    simpa [ψ, a', AlgEquiv.restrictNormal_apply] using hφ
  have hψcomm (x : B) : B.val (ψ x) = φ (B.val x) :=
    AlgEquiv.restrictNormal_apply B φ x
  have hψfrob : ∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - ψ • x :=
    frobenius_congruence_descends B.val ψ φ hψcomm p hfrob
  rcases hall ψ with hψ | hψ | hψ | hψ
  · rw [hψ, AlgEquiv.one_apply] at hψa
    exact (ha'neg hψa).elim
  · exact Or.inl (hψ ▸ hψfrob)
  · rw [hψ, hτa] at hψa
    exact (ha'neg hψa).elim
  · exact Or.inr (hψ ▸ hψfrob)

section

theorem mem_map_of_forall_mem_primesOver
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] (P : Ideal R) [hP : P.IsMaximal]
    (hunr : Algebra.IsUnramifiedIn S P) {x : S}
    (hx : ∀ (Q : Ideal S) (_ : Q.IsPrime), Q.LiesOver P → x ∈ Q) :
    x ∈ P.map (algebraMap R S) := by
  apply Ideal.mem_of_localization_maximal
  intro Q hQ
  by_cases hle : P.map (algebraMap R S) ≤ Q
  · have hover : Q.LiesOver P := ⟨hP.eq_of_le (Ideal.IsPrime.ne_top' (I := Q.under R))
      (Ideal.map_le_iff_le_comap.mp hle)⟩
    have : Algebra.IsUnramifiedAt R Q := hunr Q inferInstance hover
    let := Localization.AtPrime.algebraOfLiesOver P Q
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      ((Algebra.isUnramifiedAt_iff_map_eq R P Q).mp inferInstance).2]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime Q) Q x).mpr (hx Q inferInstance hover)
  · rw [IsLocalization.AtPrime.map_eq_top_of_not_le _ hle]
    simp

theorem arithFrobAt_eq_of_under_eq
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [CommGroup G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Finite G] [Algebra.IsInvariant R S G]
    (Q Q' : Ideal S) [Q.IsPrime] [Q'.IsPrime]
    [Finite (S ⧸ Q)] [Finite (S ⧸ Q')]
    (h : Q.under R = Q'.under R) :
    arithFrobAt R G Q = arithFrobAt R G Q' :=
  isConj_iff_eq.mp (isConj_arithFrobAt R G Q Q' h)

theorem arithFrobAt_sub_pow_mem_map
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [CommGroup G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Finite G] [Algebra.IsInvariant R S G] [Algebra.EssFiniteType R S]
    [Ring.HasFiniteQuotients S] [FaithfulSMul R S]
    (P : Ideal R) [P.IsMaximal] (hP : P ≠ ⊥)
    (hunr : Algebra.IsUnramifiedIn S P)
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver P] [Finite (S ⧸ Q)] (x : S) :
    arithFrobAt R G Q • x - x ^ Nat.card (R ⧸ P) ∈ P.map (algebraMap R S) := by
  apply mem_map_of_forall_mem_primesOver P hunr
  intro Q' hQ' hover
  have : Q'.LiesOver P := hover
  have : Finite (S ⧸ Q') := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.ne_bot_of_liesOver_of_ne_bot hP Q')
  have hbase : Q.under R = Q'.under R := (Q.over_def P).symm.trans (Q'.over_def P)
  rw [arithFrobAt_eq_of_under_eq Q Q' hbase, Q'.over_def P]
  exact IsArithFrobAt.arithFrobAt R G Q' x

theorem prime_dvd_pow_sub_arithFrobAt
    {S G : Type*} [CommRing S] [CommGroup G] [MulSemiringAction G S]
    [SMulCommClass G ℤ S] [Finite G] [Algebra.IsInvariant ℤ S G]
    [Algebra.EssFiniteType ℤ S] [Ring.HasFiniteQuotients S] [CharZero S]
    (p : ℕ) [Fact p.Prime]
    (hunr : Algebra.IsUnramifiedIn S (Ideal.span {(p : ℤ)}))
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver (Ideal.span {(p : ℤ)})]
    [Finite (S ⧸ Q)] (x : S) :
    (p : S) ∣ x ^ p - arithFrobAt ℤ G Q • x := by
  have hP : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa using (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero : (p : ℤ) ≠ 0)
  have h := arithFrobAt_sub_pow_mem_map (G := G)
    (Ideal.span {(p : ℤ)}) hP hunr Q x
  rw [Int.card_ideal_quot, Ideal.map_span, Set.image_singleton, map_natCast,
    Ideal.mem_span_singleton] at h
  simpa only [neg_sub] using dvd_neg.mpr h

theorem ringOfIntegers_isInvariant
    {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K] :
    Algebra.IsInvariant ℤ (𝓞 K) (K ≃ₐ[ℚ] K) := by
  refine ⟨fun x hx ↦ ?_⟩
  apply (Algebra.isInvariant_of_isGalois ℤ ℚ K (𝓞 K)).isInvariant x
  intro g
  apply NumberField.RingOfIntegers.ext
  change algebraMap (𝓞 K) K (galRestrict ℤ ℚ K (𝓞 K) g x) = algebraMap (𝓞 K) K x
  rw [algebraMap_galRestrict_apply]
  exact congrArg (fun z : 𝓞 K ↦ (z : K)) (hx g)

theorem exists_integer_frobenius_congruence
    {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    (hcomm : ∀ f g : K ≃ₐ[ℚ] K, Commute f g)
    (p : ℕ) [Fact p.Prime]
    (hunr : Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)})) :
    ∃ σ : K ≃ₐ[ℚ] K,
      (∀ (Q : Ideal (𝓞 K)) (_ : Q.IsPrime),
        Q.LiesOver (Ideal.span {(p : ℤ)}) → IsArithFrobAt ℤ σ Q) ∧
      ∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - σ • x := by
  let : CommGroup (K ≃ₐ[ℚ] K) := .mk hcomm
  have : Algebra.IsInvariant ℤ (𝓞 K) (K ≃ₐ[ℚ] K) := ringOfIntegers_isInvariant
  obtain ⟨Q, hQ, hover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 K) (Ideal.span {(p : ℤ)})
  have : Q.LiesOver (Ideal.span {(p : ℤ)}) := hover
  have hp0 : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa using (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero : (p : ℤ) ≠ 0)
  have : Finite ((𝓞 K) ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q)
  refine ⟨arithFrobAt ℤ (K ≃ₐ[ℚ] K) Q, ?_, prime_dvd_pow_sub_arithFrobAt p hunr Q⟩
  intro Q' hQ' hover'
  have : Q'.LiesOver (Ideal.span {(p : ℤ)}) := hover'
  have : Finite ((𝓞 K) ⧸ Q') := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q')
  have hbase : Q.under ℤ = Q'.under ℤ := hover.over.symm.trans hover'.over
  rw [arithFrobAt_eq_of_under_eq Q Q' hbase]
  exact IsArithFrobAt.arithFrobAt ℤ (K ≃ₐ[ℚ] K) Q'

theorem cyclotomic_isUnramifiedIn
    (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] (p : ℕ) [Fact p.Prime] (hpn : ¬ p ∣ n) :
    Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)}) := by
  rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  intro Q hQ hover
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p K Q hpn

theorem exists_cyclotomic_frobenius_congruence
    (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] (p : ℕ) [Fact p.Prime] (hpn : ¬ p ∣ n) :
    ∃ σ : K ≃ₐ[ℚ] K,
      (∀ (Q : Ideal (𝓞 K)) (_ : Q.IsPrime),
        Q.LiesOver (Ideal.span {(p : ℤ)}) → IsArithFrobAt ℤ σ Q) ∧
      ∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - σ • x := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  apply exists_integer_frobenius_congruence (p := p)
  · intro σ τ
    change σ * τ = τ * σ
    apply (IsCyclotomicExtension.Rat.galEquivZMod n K).injective
    simp only [map_mul, mul_comm]
  · exact cyclotomic_isUnramifiedIn n K p hpn

theorem not_isSquare_rat_two : ¬ IsSquare (2 : ℚ) := by
  norm_num

theorem real_character_inv {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) : χ⁻¹ = χ := by
  rw [← MulChar.star_eq_inv]
  apply MulChar.ext'
  intro a
  exact Complex.conj_eq_iff_im.mpr (hreal a)

theorem real_character_isQuadratic {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) : χ.IsQuadratic := by
  rw [MulChar.isQuadratic_iff_sq_eq_one]
  calc
    χ ^ 2 = χ⁻¹ * χ := by rw [pow_two, real_character_inv χ hreal]
    _ = 1 := inv_mul_cancel χ

open NumberField

theorem canonicalCyclotomicLevelNeZero (q : ℕ) [NeZero q] : NeZero (8 * q) :=
  ⟨Nat.mul_ne_zero (by decide) (NeZero.ne q)⟩
attribute [local instance] canonicalCyclotomicLevelNeZero

theorem canonicalCyclotomicExtension (n : ℕ) [NeZero n] :
    IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) := by
  let : NeZero (n : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  convert CyclotomicField.isCyclotomicExtension n ℚ using 1
  exact Subsingleton.elim _ _
attribute [local instance] canonicalCyclotomicExtension

theorem canonicalCyclotomicNumberField (n : ℕ) [NeZero n] :
    NumberField (CyclotomicField n ℚ) :=
  IsCyclotomicExtension.numberField {n} ℚ (CyclotomicField n ℚ)
attribute [local instance] canonicalCyclotomicNumberField

theorem canonicalCyclotomicAbelian (n : ℕ) [NeZero n] :
    IsAbelianGalois ℚ (CyclotomicField n ℚ) :=
  IsCyclotomicExtension.isAbelianGalois {n} ℚ (CyclotomicField n ℚ)

attribute [local instance] canonicalCyclotomicAbelian

end

theorem quadratic_factorsThrough_of_odd_kernel {q d : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q) (hχ : χ.IsQuadratic)
    (hd : d ∣ q) (hodd : Odd (Nat.card (ZMod.unitsMap hd).ker)) :
    χ.FactorsThrough d := by
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
  intro u hu
  rw [MonoidHom.mem_ker, ← Units.val_inj, MulChar.coe_toUnitHom, Units.val_one]
  have hupow : u ^ Nat.card (ZMod.unitsMap hd).ker = 1 := by
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨u, hu⟩ : (ZMod.unitsMap hd).ker)))
  have hvpow : χ u ^ Nat.card (ZMod.unitsMap hd).ker = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hupow, Units.val_one, map_one]
  have hchar := congrArg (fun ψ : DirichletCharacter R q ↦ ψ u) (hχ.pow_odd hodd)
  rw [MulChar.pow_apply_coe] at hchar
  exact hchar.symm.trans hvpow

theorem card_unitsMap_kernel_mul_totient {q d : ℕ} [NeZero q] (hd : d ∣ q) :
    Nat.card (ZMod.unitsMap hd).ker * d.totient = q.totient := by
  have : NeZero d := ⟨fun h ↦ (NeZero.ne q) (Nat.eq_zero_of_zero_dvd (h ▸ hd))⟩
  let f := ZMod.unitsMap hd
  have hind : f.ker.index = Nat.card (ZMod d)ˣ := by
    rw [← MonoidHom.comap_bot, Subgroup.index_comap_of_surjective ⊥
      (ZMod.unitsMap_surjective hd), Subgroup.index_bot]
  have hcard := f.ker.card_mul_index
  have hcd : Nat.card (ZMod d)ˣ = d.totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hcq : Nat.card (ZMod q)ˣ = q.totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  rwa [hind, hcd, hcq] at hcard

theorem card_unitsMap_kernel_prime_mul {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    (hpm : p ∣ m) :
    Nat.card (ZMod.unitsMap (Nat.dvd_mul_left m p)).ker = p := by
  have : NeZero (p * m) := ⟨Nat.mul_ne_zero hp.ne_zero hm⟩
  have hcard := card_unitsMap_kernel_mul_totient (Nat.dvd_mul_left m p)
  rw [Nat.totient_mul_of_prime_of_dvd hp hpm] at hcard
  exact Nat.eq_of_mul_eq_mul_right (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)) hcard

theorem primitive_quadratic_no_odd_prime_square {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q)
    (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) : ¬ p ^ 2 ∣ q := by
  intro hpq
  obtain ⟨k, hk⟩ := hpq
  have hq : q = p * (p * k) := by rw [hk]; ring
  have hdiv : p * k ∣ q := ⟨p, by rw [hq, mul_comm]⟩
  have hm : p * k ≠ 0 := by
    intro h
    exact (NeZero.ne q) (by rw [hq, h, mul_zero])
  have hcard : Nat.card (ZMod.unitsMap hdiv).ker = p := by
    clear hk
    subst q
    exact card_unitsMap_kernel_prime_mul hp hm (Nat.dvd_mul_right p k)
  have hfactor := quadratic_factorsThrough_of_odd_kernel χ hχ hdiv (hcard.symm ▸ hodd)
  have hle : q ≤ p * k := by
    rw [← hprim]
    exact Nat.sInf_le hfactor
  have hlt : p * k < q := by
    rw [hq]
    exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm) hp.one_lt
  exact (not_lt_of_ge hle) hlt

theorem unitsMap_sixteen_mul_kernel_square {m : ℕ} [NeZero (16 * m)]
    (u : (ZMod (16 * m))ˣ)
    (hu : ZMod.unitsMap (show 8 * m ∣ 16 * m from ⟨2, by ring⟩) u = 1) :
    ∃ y : ZMod (16 * m), y ^ 2 = (u : ZMod (16 * m)) := by
  let hd : 8 * m ∣ 16 * m := ⟨2, by ring⟩
  have hval : ((8 * m : ℕ) : ℤ) ∣ (u.val.val - 1 : ℤ) := by
    rw [← Units.val_inj, Units.val_one, ZMod.unitsMap_def, Units.coe_map] at hu
    have hcast : ZMod.castHom hd (ZMod (8 * m)) u.val =
        ((u.val.val : ℤ) : ZMod (8 * m)) := by simp
    rwa [MonoidHom.coe_coe, hcast, ← Int.cast_one, eq_comm,
      ZMod.intCast_eq_intCast_iff_dvd_sub] at hu
  obtain ⟨k, hk⟩ := hval
  have huval : u.val = 1 + (8 * m : ZMod (16 * m)) * (k : ZMod (16 * m)) := by
    have hcast := congrArg (fun z : ℤ ↦ (z : ZMod (16 * m))) hk
    push_cast at hcast
    rw [ZMod.natCast_zmod_val] at hcast
    rw [sub_eq_iff_eq_add] at hcast
    simpa only [add_comm] using hcast
  refine ⟨1 + (4 * m : ZMod (16 * m)) * (k : ZMod (16 * m)), ?_⟩
  rw [huval]
  have hz : (16 * m : ZMod (16 * m)) = 0 := by
    exact_mod_cast (ZMod.natCast_self (16 * m))
  calc
    (1 + (4 * m : ZMod (16 * m)) * k) ^ 2 =
        1 + (8 * m : ZMod (16 * m)) * k + (16 * m : ZMod (16 * m)) * (m * k ^ 2) := by ring
    _ = _ := by rw [hz, zero_mul, add_zero]

theorem quadratic_factorsThrough_eight_mul {m : ℕ} [NeZero (16 * m)]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R (16 * m)) (hχ : χ.IsQuadratic) :
    χ.FactorsThrough (8 * m) := by
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (show 8 * m ∣ 16 * m from ⟨2, by ring⟩)]
  intro u hu
  rw [MonoidHom.mem_ker] at hu
  rw [MonoidHom.mem_ker, ← Units.val_inj, MulChar.coe_toUnitHom, Units.val_one]
  obtain ⟨y, hy⟩ := unitsMap_sixteen_mul_kernel_square u hu
  have hyunit : IsUnit y := (isUnit_pow_iff (by decide : 2 ≠ 0)).mp (hy.symm ▸ u.isUnit)
  rw [← hy, map_pow]
  have hs := congrArg (fun ψ : DirichletCharacter R (16 * m) ↦ ψ hyunit.unit) hχ.sq_eq_one
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe] at hs
  simpa only [hyunit.unit_spec] using hs

theorem primitive_quadratic_not_sixteen_dvd {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q)
    (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) : ¬ 16 ∣ q := by
  rintro ⟨m, rfl⟩
  have hm : 0 < m := Nat.pos_of_ne_zero fun h ↦ (NeZero.ne (16 * m)) (by simp [h])
  have hle : 16 * m ≤ 8 * m := by
    rw [← hprim]
    exact Nat.sInf_le (quadratic_factorsThrough_eight_mul χ hχ)
  omega

theorem quadratic_factorsThrough_odd_two_mul {m : ℕ} [NeZero (2 * m)]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R (2 * m))
    (hχ : χ.IsQuadratic) (hm : Odd m) : χ.FactorsThrough m := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero fun h ↦ (NeZero.ne (2 * m)) (by simp [h])
  have hcard : Nat.card (ZMod.unitsMap (Nat.dvd_mul_left m 2)).ker = 1 := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.totient_pos.mpr hmpos)
    rw [one_mul, card_unitsMap_kernel_mul_totient, Nat.totient_two_mul_of_odd hm]
  apply quadratic_factorsThrough_of_odd_kernel χ hχ (Nat.dvd_mul_left m 2)
  rw [hcard]
  decide

theorem primitive_quadratic_mod_four_ne_two {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q)
    (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) : q % 4 ≠ 2 := by
  intro hqmod
  have hq : q = 2 * (2 * (q / 4) + 1) := by omega
  obtain ⟨m, hm, hq⟩ : ∃ m, Odd m ∧ q = 2 * m :=
    ⟨2 * (q / 4) + 1, ⟨q / 4, rfl⟩, hq⟩
  subst q
  have hle : 2 * m ≤ m := by
    rw [← hprim]
    exact Nat.sInf_le (quadratic_factorsThrough_odd_two_mul χ hχ hm)
  have hmpos : 0 < m := Nat.pos_of_ne_zero fun h ↦ (NeZero.ne (2 * m)) (by simp [h])
  omega

theorem square_divisor_of_primitive_quadratic {q c : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q)
    (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) (hc : c ^ 2 ∣ q) : c = 1 ∨ c = 2 := by
  have hc0 : c ≠ 0 := by
    intro h
    apply NeZero.ne q
    apply Nat.eq_zero_of_zero_dvd
    simpa [h] using hc
  obtain ⟨k, hk⟩ : ∃ k, c = 2 ^ k := ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (p := 2) hc0 (by
    intro p hp hpc
    by_contra hne
    exact primitive_quadratic_no_odd_prime_square χ hχ hprim hp (hp.odd_of_ne_two hne)
      ((pow_dvd_pow_of_dvd hpc 2).trans hc))⟩
  have hk1 : k ≤ 1 := by
    by_contra! hk2
    have h16 : 16 ∣ c ^ 2 := by
      rw [hk, ← pow_mul]
      exact pow_dvd_pow 2 (by omega : 4 ≤ k * 2)
    exact primitive_quadratic_not_sixteen_dvd χ hχ hprim (h16.trans hc)
  interval_cases k <;> simp_all

theorem primitive_quadratic_radicand_eq_or_four_mul {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q)
    (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    {D c d : ℤ} (hD : D.natAbs = q) (hDc : D = c ^ 2 * d) : D = d ∨ D = 4 * d := by
  have hdiv : c.natAbs ^ 2 ∣ q := by
    have h := Int.natAbs_dvd_natAbs.mpr (show c ^ 2 ∣ D from ⟨d, hDc⟩)
    simpa only [Int.natAbs_pow, hD] using h
  rcases square_divisor_of_primitive_quadratic χ hχ hprim hdiv with hc | hc
  · have hsq : c ^ 2 = 1 := by
      have h := congrArg (fun n : ℕ ↦ (n : ℤ) ^ 2) hc
      norm_num [Int.natCast_natAbs] at h
      rcases h with rfl | rfl <;> norm_num
    left
    simpa only [hsq, one_mul] using hDc
  · have hsq : c ^ 2 = 4 := by
      have h := congrArg (fun n : ℕ ↦ (n : ℤ) ^ 2) hc
      norm_num [Int.natCast_natAbs] at h
      exact h
    right
    simpa only [hsq] using hDc

theorem odd_divisor_primitive_quadratic_squarefree {q m : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q)
    (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) (hm : Odd m) (hmq : m ∣ q) :
    Squarefree m := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  rcases hp.eq_two_or_odd' with rfl | hodd
  · exact hm.not_two_dvd_nat ((Nat.dvd_mul_right 2 2).trans hpp)
  · exact primitive_quadratic_no_odd_prime_square χ hχ hprim hp hodd
      ((by simpa only [pow_two] using hpp : p ^ 2 ∣ m).trans hmq)

theorem primitive_quadratic_conductor_shape {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q)
    (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) :
    ∃ u : ℕ, Odd u ∧ Squarefree u ∧ (q = u ∨ q = 4 * u ∨ q = 8 * u) := by
  have h16 : q % 16 ≠ 0 := fun h ↦
    primitive_quadratic_not_sixteen_dvd χ hχ hprim (Nat.dvd_of_mod_eq_zero h)
  have h4 := primitive_quadratic_mod_four_ne_two χ hχ hprim
  by_cases hodd : q % 2 = 1
  · have ho : Odd q := Nat.odd_iff.mpr hodd
    exact ⟨q, ho, odd_divisor_primitive_quadratic_squarefree χ hχ hprim ho dvd_rfl,
      Or.inl rfl⟩
  · by_cases h8 : q % 8 = 0
    · have hq : q = 8 * (q / 8) := by omega
      have ho : Odd (q / 8) := Nat.odd_iff.mpr (by omega)
      have hd : q / 8 ∣ q := ⟨8, by omega⟩
      exact ⟨q / 8, ho, odd_divisor_primitive_quadratic_squarefree χ hχ hprim ho hd,
        Or.inr (Or.inr hq)⟩
    · have hq : q = 4 * (q / 4) := by omega
      have ho : Odd (q / 4) := Nat.odd_iff.mpr (by omega)
      have hd : q / 4 ∣ q := ⟨4, by omega⟩
      exact ⟨q / 4, ho, odd_divisor_primitive_quadratic_squarefree χ hχ hprim ho hd,
        Or.inr (Or.inl hq)⟩

end WeightedTorusJets

open scoped NumberField

end SiegelZeros

end OAI
