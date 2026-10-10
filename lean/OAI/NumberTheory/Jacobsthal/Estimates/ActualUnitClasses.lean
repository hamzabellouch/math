import OAI.NumberTheory.Jacobsthal.Sieve.RealCoprimeResidueCount

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosUnitLifts
attribute [local instance] Classical.decEq

def radical (D : ℕ) : ℕ := ∏ t ∈ D.primeFactors, t

theorem radical_pos (D : ℕ) : 0 < radical D :=
  Finset.prod_pos (fun _ ht => Nat.pos_of_mem_primeFactors ht)

theorem radical_dvd (D : ℕ) : radical D ∣ D := Nat.prod_primeFactors_dvd D

theorem radical_primeFactors (D : ℕ) : (radical D).primeFactors = D.primeFactors :=
  Nat.primeFactors_prod_primeFactors D

theorem totient_radical (D : ℕ) :
    (radical D).totient = ∏ t ∈ D.primeFactors, (t - 1) := by
  rw [Nat.totient_eq_div_primeFactors_mul, radical_primeFactors]
  change radical D / radical D * _ = _
  rw [Nat.div_self (radical_pos D), one_mul]

theorem totient_lift_modulus (D : ℕ) (hD : 0 < D) :
    (D * radical D).totient = D * (radical D).totient := by
  rw [Nat.totient_eq_div_primeFactors_mul]
  rw [Nat.primeFactors_mul hD.ne' (radical_pos D).ne', radical_primeFactors,
    Finset.union_self, totient_radical]
  change D * radical D / radical D * _ = _
  rw [Nat.mul_div_cancel D (radical_pos D)]

theorem totient_lift_modulus' (D : ℕ) (hD : 0 < D) :
    (D * radical D).totient = D.totient * radical D := by
  rw [totient_lift_modulus D hD, totient_radical]
  exact (Nat.totient_mul_prod_primeFactors D).symm

abbrev PrimeIndex (D : ℕ) := {t // t ∈ D.primeFactors}

theorem primeIndex_coprime (D : ℕ) :
    Pairwise (fun t u : PrimeIndex D => Nat.Coprime t.val u.val) := by
  intro t u hne
  exact (Nat.prime_of_mem_primeFactors t.property).coprime_iff_not_dvd.mpr (by
    intro h
    have he := (Nat.prime_of_mem_primeFactors u.property).eq_one_or_self_of_dvd _ h
    rcases he with he | he
    · exact (Nat.prime_of_mem_primeFactors t.property).ne_one he
    · exact hne (Subtype.ext he))

noncomputable def localAllowed (t : ℕ) [NeZero t] (n B a : ℤ) : Finset (ZMod t) :=
  Finset.univ.filter (fun x => (n : ZMod t) + B * x ≠ a)

theorem affine_eq_iff (t : ℕ) (n B a : ℤ) (hB : IsUnit (B : ZMod t))
    (x : ZMod t) :
    (n : ZMod t) + B * x = a ↔ x = (B : ZMod t)⁻¹ * (a - n) := by
  constructor
  · intro h
    calc
      x = (B : ZMod t)⁻¹ * (B * x) := by rw [← mul_assoc, ZMod.inv_mul_of_unit _ hB, one_mul]
      _ = (B : ZMod t)⁻¹ * (a - n) := by congr 1; linear_combination h
  · intro h
    rw [h, ← mul_assoc, ZMod.mul_inv_of_unit _ hB, one_mul]
    ring

theorem localAllowed_card (t : ℕ) [NeZero t] (n B a : ℤ)
    (hB : IsUnit (B : ZMod t)) : (localAllowed t n B a).card = t - 1 := by
  have he : localAllowed t n B a = Finset.univ.erase ((B : ZMod t)⁻¹ * (a - n)) := by
    ext x
    simp [localAllowed, affine_eq_iff t n B a hB]
  rw [he, Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp

noncomputable def crtNat {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i, Finset (ZMod (m i))) : Finset ℕ :=
  (ErdosInverseCRT.crtResidues m hcop E).image ZMod.val

theorem mem_crtNat {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i, Finset (ZMod (m i))) (hpos : 0 < ∏ i, m i) (k : ℕ) :
    k ∈ crtNat m hcop E ↔ k < ∏ i, m i ∧ ∀ i, (k : ZMod (m i)) ∈ E i := by
  let : NeZero (∏ i, m i) := ⟨hpos.ne'⟩
  constructor
  · intro hk
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hk
    refine ⟨ZMod.val_lt r, ?_⟩
    have hh : (r.val : ZMod (∏ i, m i)) ∈ ErdosInverseCRT.crtResidues m hcop E := by
      simpa using hr
    have hx := ErdosInverseCRT.intCast_mem_crtResidues m hcop E (r.val : ℤ)
    simp only [Int.cast_natCast] at hx
    exact hx.mp hh
  · rintro ⟨hk,he⟩
    apply Finset.mem_image.mpr
    refine ⟨(k : ZMod (∏ i,m i)), ?_, ZMod.val_natCast_of_lt hk⟩
    have hx := ErdosInverseCRT.intCast_mem_crtResidues m hcop E (k : ℤ)
    simp only [Int.cast_natCast] at hx
    exact hx.mpr he

theorem crtNat_card {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i, Finset (ZMod (m i))) (hpos : 0 < ∏ i, m i) :
    (crtNat m hcop E).card = ∏ i, (E i).card := by
  let : NeZero (∏ i, m i) := ⟨hpos.ne'⟩
  rw [crtNat, Finset.card_image_of_injective _ (ZMod.val_injective _),
    ErdosInverseCRT.crtResidues_card]

noncomputable def allowedK (D : ℕ) (n B : ℤ) (a : ℕ → ℤ) : Finset ℕ :=
  (Finset.range (radical D)).filter (fun k => ∀ t ∈ D.primeFactors,
    ((n + B * k : ℤ) : ZMod t) ≠ a t)

theorem allowedK_card (D : ℕ) (n B : ℤ) (a : ℕ → ℤ)
    (hB : IsUnit (B : ZMod D)) :
    (allowedK D n B a).card = (radical D).totient := by
  let (t : PrimeIndex D) : NeZero t.val := ⟨(Nat.pos_of_mem_primeFactors t.property).ne'⟩
  let m := fun t : PrimeIndex D => t.val
  let E := fun t : PrimeIndex D => localAllowed t.val n B (a t.val)
  have hm : (∏ t : PrimeIndex D, m t) = radical D := by
    exact Finset.prod_coe_sort D.primeFactors (fun t => t)
  have hpos : 0 < ∏ t : PrimeIndex D, m t := hm ▸ radical_pos D
  have he : allowedK D n B a = crtNat m (primeIndex_coprime D) E := by
    ext k
    rw [mem_crtNat m (primeIndex_coprime D) E hpos]
    simp only [allowedK, Finset.mem_filter, Finset.mem_range, hm]
    simp only [E, localAllowed, Finset.mem_filter, Finset.mem_univ, true_and,
      Int.cast_add, Int.cast_mul, Int.cast_natCast]
    apply and_congr_right
    intro _
    constructor
    · intro h t
      exact h t.val t.property
    · intro h t ht
      exact h ⟨t,ht⟩
  rw [he, crtNat_card m (primeIndex_coprime D) E hpos, totient_radical]
  calc
    (∏ t : PrimeIndex D, (E t).card) = ∏ t : PrimeIndex D, (t.val - 1) := by
      apply Finset.prod_congr rfl
      intro t _
      apply localAllowed_card
      have hd : t.val ∣ D := Nat.dvd_of_mem_primeFactors t.property
      simpa using hB.map (ZMod.castHom hd (ZMod t.val))
    _ = _ := Finset.prod_coe_sort D.primeFactors (fun t => t - 1)

end ErdosUnitLifts

end

section

open scoped BigOperators
namespace ErdosUnitLifts
attribute [local instance] Classical.decEq

def actualN (D : ℕ) (A B : ℤ) (p : ℕ) : ℤ := (A + B * p) / D

noncomputable def actualClasses (D : ℕ) (A B : ℤ) (a : ℕ → ℤ) : Finset ℕ :=
  (Finset.range (D * radical D)).filter (fun p =>
    (D : ℤ) ∣ A + B * p ∧ ∀ t ∈ D.primeFactors,
      (actualN D A B p : ZMod t) ≠ a t)

noncomputable def baseResidue (D : ℕ) (A B : ℤ) : ℕ :=
  (-(A : ZMod D) * (B : ZMod D)⁻¹).val

theorem baseResidue_lt (D : ℕ) (hD : 0 < D) (A B : ℤ) : baseResidue D A B < D := by
  let : NeZero D := ⟨hD.ne'⟩
  exact ZMod.val_lt _

theorem baseResidue_integral (D : ℕ) (hD : 0 < D) (A B : ℤ)
    (hB : IsUnit (B : ZMod D)) : (D : ℤ) ∣ A + B * baseResidue D A B := by
  let : NeZero D := ⟨hD.ne'⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ D).mp
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, baseResidue, ZMod.natCast_zmod_val]
  calc
    (A : ZMod D) + B * (-A * (B : ZMod D)⁻¹) = A - A * (B * (B : ZMod D)⁻¹) := by ring
    _ = 0 := by rw [ZMod.mul_inv_of_unit _ hB]; ring

theorem integral_iff_base_mod (D p0 : ℕ) (hp0 : p0 < D) (A B : ℤ)
    (hB : IsUnit (B : ZMod D)) (h0 : (D : ℤ) ∣ A + B * p0) (p : ℕ) :
    (D : ℤ) ∣ A + B * p ↔ p % D = p0 := by
  have hz0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ D).mpr h0
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at hz0
  have hh : (D : ℤ) ∣ A + B * p ↔ (p : ZMod D) = p0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
    constructor
    · intro hp
      apply hB.mul_left_cancel
      linear_combination hp - hz0
    · intro hp
      simpa only [hp] using hz0
  rw [hh, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hp0]

theorem base_coprime (D p0 : ℕ) (A B : ℤ)
    (hA : IsUnit (A : ZMod D)) (h0 : (D : ℤ) ∣ A + B * p0) :
    Nat.Coprime p0 D := by
  apply (ZMod.isUnit_iff_coprime p0 D).mp
  have hz0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ D).mpr h0
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at hz0
  have he : (B : ZMod D) * p0 = -A := by linear_combination hz0
  apply isUnit_of_mul_isUnit_right (x := (B : ZMod D))
  rw [he]
  exact hA.neg

theorem actualN_lift (D : ℕ) (hD : 0 < D) (A B : ℤ) (p0 k : ℕ) :
    actualN D A B (p0 + D * k) = actualN D A B p0 + B * k := by
  unfold actualN
  have hn : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  have he : A + B * (p0 + D * k : ℕ) = A + B * p0 + (B * k) * D := by push_cast; ring
  rw [he, Int.add_mul_ediv_right _ _ hn]

theorem lift_coprime (D p0 k : ℕ) (hp : Nat.Coprime p0 D) :
    Nat.Coprime (p0 + D * k) (D * radical D) := by
  have hd : Nat.Coprime (p0 + D * k) D :=
    (Nat.coprime_add_mul_left_left p0 D k).mpr hp
  exact Nat.coprime_mul_iff_right.mpr ⟨hd, Nat.Coprime.coprime_dvd_right (radical_dvd D) hd⟩

theorem canonical_lift_iff (D p0 p : ℕ) (hD : 0 < D) (hp0 : p0 < D) :
    p < D * radical D ∧ p % D = p0 ↔
      ∃ k < radical D, p0 + D * k = p := by
  constructor
  · rintro ⟨hp,hm⟩
    refine ⟨p / D, ?_, ?_⟩
    · exact (Nat.div_lt_iff_lt_mul hD).mpr (by simpa [Nat.mul_comm] using hp)
    · simpa only [hm] using Nat.mod_add_div p D
  · rintro ⟨k,hk,rfl⟩
    constructor
    · calc
        p0 + D * k < D + D * k := Nat.add_lt_add_right hp0 _
        _ = D * (k + 1) := by ring
        _ ≤ D * radical D := Nat.mul_le_mul_left D hk
    · simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp0]

theorem actualClasses_eq_lifts (D p0 : ℕ) (hD : 0 < D) (hp0 : p0 < D)
    (A B : ℤ) (a : ℕ → ℤ) (hB : IsUnit (B : ZMod D))
    (h0 : (D : ℤ) ∣ A + B * p0) :
    actualClasses D A B a =
      (allowedK D (actualN D A B p0) B a).image (fun k => p0 + D * k) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hp,hi,ha⟩ := Finset.mem_filter.mp hp
    obtain ⟨k,hk,hkp⟩ := (canonical_lift_iff D p0 p hD hp0).mp
      ⟨Finset.mem_range.mp hp, (integral_iff_base_mod D p0 hp0 A B hB h0 p).mp hi⟩
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, ?_⟩, hkp⟩
    intro t ht
    have hh := ha t ht
    rw [← hkp, actualN_lift D hD] at hh
    exact hh
  · intro hp
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hk,ha⟩ := Finset.mem_filter.mp hk
    have hc := (canonical_lift_iff D p0 (p0 + D * k) hD hp0).mpr
      ⟨k, Finset.mem_range.mp hk, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hc.1, ?_, ?_⟩
    · exact (integral_iff_base_mod D p0 hp0 A B hB h0 _).mpr hc.2
    · intro t ht
      rw [actualN_lift D hD]
      exact ha t ht

theorem actualClasses_card (D : ℕ) (hD : 0 < D) (A B : ℤ) (a : ℕ → ℤ)
    (hB : IsUnit (B : ZMod D)) :
    (actualClasses D A B a).card = (radical D).totient := by
  rw [actualClasses_eq_lifts D (baseResidue D A B) hD (baseResidue_lt D hD A B)
    A B a hB (baseResidue_integral D hD A B hB)]
  rw [Finset.card_image_of_injective]
  · exact allowedK_card D (actualN D A B (baseResidue D A B)) B a hB
  · intro k l h
    exact Nat.eq_of_mul_eq_mul_left hD (Nat.add_left_cancel h)

theorem actualClasses_reduced (D : ℕ) (hD : 0 < D) (A B : ℤ) (a : ℕ → ℤ)
    (hA : IsUnit (A : ZMod D)) (hB : IsUnit (B : ZMod D))
    (p : ℕ) (hp : p ∈ actualClasses D A B a) :
    p < D * radical D ∧ Nat.Coprime p (D * radical D) := by
  have hrange := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
  rw [actualClasses_eq_lifts D (baseResidue D A B) hD (baseResidue_lt D hD A B)
    A B a hB (baseResidue_integral D hD A B hB)] at hp
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hp
  exact ⟨hrange, lift_coprime D _ k
    (base_coprime D _ A B hA (baseResidue_integral D hD A B hB))⟩

theorem actualClasses_fraction (D : ℕ) (hD : 0 < D) (A B : ℤ) (a : ℕ → ℤ)
    (hB : IsUnit (B : ZMod D)) :
    ((actualClasses D A B a).card : ℚ) / (D * radical D).totient = 1 / (D : ℚ) := by
  rw [actualClasses_card D hD A B a hB, totient_lift_modulus D hD, Nat.cast_mul]
  have ht : ((radical D).totient : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (radical_pos D)).ne'
  have hd : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  field_simp

theorem intCast_isUnit_of_natAbs_coprime (D : ℕ) (B : ℤ)
    (hB : Nat.Coprime B.natAbs D) : IsUnit (B : ZMod D) := by
  have hh := (ZMod.isUnit_iff_coprime B.natAbs D).mpr hB
  have ha : IsUnit ((|B| : ℤ) : ZMod D) := by
    simpa only [← Int.natCast_natAbs, Int.cast_natCast] using hh
  rcases le_total 0 B with hp | hn
  · simpa only [abs_of_nonneg hp] using ha
  · have ht : IsUnit (-(B : ZMod D)) := by simpa only [abs_of_nonpos hn, Int.cast_neg] using ha
    simpa only [neg_neg] using ht.neg

theorem actual_unit_lift_packet (D : ℕ) (hD : 0 < D) (A B : ℤ) (a : ℕ → ℤ)
    (hA : Nat.Coprime A.natAbs D) (hB : Nat.Coprime B.natAbs D) :
    (∀ p ∈ actualClasses D A B a, p < D * radical D ∧ Nat.Coprime p (D * radical D)) ∧
    (actualClasses D A B a).card = (radical D).totient ∧
    ((actualClasses D A B a).card : ℚ) / (D * radical D).totient = 1 / (D : ℚ) := by
  have hAu := intCast_isUnit_of_natAbs_coprime D A hA
  have hBu := intCast_isUnit_of_natAbs_coprime D B hB
  exact ⟨fun p hp => actualClasses_reduced D hD A B a hAu hBu p hp,
    actualClasses_card D hD A B a hBu, actualClasses_fraction D hD A B a hBu⟩

theorem actualClasses_one (A B : ℤ) (a : ℕ → ℤ) : actualClasses 1 A B a = {0} := by
  simp [actualClasses, radical]

theorem actual_lift_forbidden_iff (D : ℕ) (hD : 0 < D) (A B : ℤ)
    (hB : IsUnit (B : ZMod D)) (a : ℕ → ℤ) (p0 k t : ℕ)
    (ht : t ∈ D.primeFactors) :
    (actualN D A B (p0 + D * k) : ZMod t) = a t ↔
      (k : ZMod t) = (B : ZMod t)⁻¹ * (a t - actualN D A B p0) := by
  have hb : IsUnit (B : ZMod t) := by
    simpa using hB.map (ZMod.castHom (Nat.dvd_of_mem_primeFactors ht) (ZMod t))
  rw [actualN_lift D hD]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
  exact affine_eq_iff t (actualN D A B p0) B (a t) hb (k : ZMod t)

def reducedClasses (Q : ℕ) : Finset ℕ :=
  (Finset.range Q).filter (fun p => Nat.Coprime p Q)

theorem reducedClasses_card (Q : ℕ) : (reducedClasses Q).card = Q.totient := by
  simp only [reducedClasses, Nat.totient_eq_card_coprime, Nat.coprime_comm]

theorem actual_unit_lift_finite_fraction (D : ℕ) (hD : 0 < D) (A B : ℤ)
    (a : ℕ → ℤ) (hA : Nat.Coprime A.natAbs D) (hB : Nat.Coprime B.natAbs D) :
    actualClasses D A B a ⊆ reducedClasses (D * radical D) ∧
    (actualClasses D A B a).card = ∏ t ∈ D.primeFactors, (t - 1) ∧
    ((actualClasses D A B a).card : ℚ) / (reducedClasses (D * radical D)).card =
      1 / (D : ℚ) := by
  obtain ⟨hr,hc,hf⟩ := actual_unit_lift_packet D hD A B a hA hB
  refine ⟨?_, hc.trans (totient_radical D), ?_⟩
  · intro p hp
    obtain ⟨hpr,hpc⟩ := hr p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpr, hpc⟩
  · simpa only [reducedClasses_card] using hf

end ErdosUnitLifts

end

end Erdos970

end OAI
