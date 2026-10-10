import Mathlib
import OAI.NumberTheory.CubicGram.ResidueCharacters
import OAI.NumberTheory.CubicGram.PrimeFactors

namespace OAI

/-! Unique primary associates and canonical prime factorization. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid
lemma normNat_of_isUnit {u : Eisenstein} (hu : IsUnit u) : normNat u = 1 :=
  Nat.isUnit_iff.mp (hu.map normNatHom)

lemma norm_of_isUnit {u : Eisenstein} (hu : IsUnit u) : norm u = 1 := by
  rw [← normNat_cast, normNat_of_isUnit hu, Nat.cast_one]

lemma primary_iff_residue_one (z : Eisenstein) :
    primary z ↔ Ideal.Quotient.mk (modulus 3) z = 1 := by
  rw [primary, ← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  change Ideal.Quotient.mk (modulus 3) (z-1) = 0 ↔ _
  rw [map_sub, map_one, sub_eq_zero]

lemma primary_mul {a b : Eisenstein} (ha : primary a) (hb : primary b) : primary (a*b) := by
  rw [primary_iff_residue_one, map_mul, (primary_iff_residue_one a).mp ha,
    (primary_iff_residue_one b).mp hb, one_mul]

lemma primary_unit_eq_one {u : Eisenstein} (hu : IsUnit u) (hprimary : primary u) : u = 1 := by
  have hnu : ‖(u : ℂ)‖ = 1 := by
    have hnorm := norm_of_isUnit hu
    rw [norm, Complex.normSq_eq_norm_sq] at hnorm
    nlinarith [_root_.norm_nonneg (u : ℂ)]
  have hsub : ‖(u : ℂ) - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖(u : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hnu, norm_one]; norm_num
  obtain ⟨w, hw⟩ := hprimary
  have hnorm : norm (u-1) = 9 * norm w := by
    rw [hw, norm, Subalgebra.coe_mul, Complex.normSq_mul]
    change Complex.normSq (3 : ℂ) * norm w = 9 * norm w
    norm_num [Complex.normSq_apply]
  have hwlt : (normNat w : ℝ) < 1 := by
    rw [normNat_cast]
    rw [norm, Subalgebra.coe_sub, Subalgebra.coe_one, Complex.normSq_eq_norm_sq] at hnorm
    nlinarith [_root_.norm_nonneg ((u : ℂ)-1)]
  have hwzero : normNat w = 0 := by
    have hnat : normNat w < 1 := by exact_mod_cast hwlt
    omega
  have hw' : w = 0 := by
    by_contra h
    exact normNat_ne_zero h hwzero
  rw [hw', mul_zero, sub_eq_zero] at hw
  exact hw

lemma primary_associated_eq {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hab : Associated a b) : a = b := by
  obtain ⟨u, hu⟩ := hab
  have hm := congrArg (Ideal.Quotient.mk (modulus 3)) hu
  rw [map_mul, (primary_iff_residue_one a).mp ha,
    (primary_iff_residue_one b).mp hb, one_mul] at hm
  have huone := primary_unit_eq_one u.isUnit ((primary_iff_residue_one u).mpr hm)
  simpa only [huone, mul_one] using hu

lemma residue_three_eq_zero : Ideal.Quotient.mk (modulus (3 : Eisenstein)) 3 = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

lemma residue_ofCoords_mod_three (a b : ℤ) :
    Ideal.Quotient.mk (modulus (3 : Eisenstein)) (ofCoords a b) =
      Ideal.Quotient.mk (modulus (3 : Eisenstein)) (ofCoords (a%3) (b%3)) := by
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  refine ⟨ofCoords (a/3) (b/3), ?_⟩
  have ha := Int.emod_add_mul_ediv a 3
  have hb := Int.emod_add_mul_ediv b 3
  have ha' : (a : Eisenstein) = (a%3 : ℤ) + 3*(a/3 : ℤ) := by exact_mod_cast ha.symm
  have hb' : (b : Eisenstein) = (b%3 : ℤ) + 3*(b/3 : ℤ) := by exact_mod_cast hb.symm
  dsimp only [ofCoords]
  rw [ha', hb']
  ring

lemma residue_three_nontrivial : Nontrivial (Residues (3 : Eisenstein)) := by
  let : Finite (Residues (3 : Eisenstein)) := finite_residues (by norm_num)
  apply Finite.one_lt_card_iff_nontrivial.mp
  rw [residues_card (by norm_num : (3 : Eisenstein) ≠ 0)]
  change 1 < ⌊Complex.normSq (3 : ℂ)⌋₊
  norm_num [Complex.normSq_apply]

lemma omegaE_isUnit : IsUnit omegaE := by
  apply isUnit_iff_exists_inv.mpr
  exact ⟨omegaE^2, by simpa only [← pow_succ'] using omegaE_cube⟩

lemma unit_lift_mod_three {z : Eisenstein}
    (hz : IsUnit (Ideal.Quotient.mk (modulus 3) z)) :
    ∃ u : Eisenstein, IsUnit u ∧ primary (z*u) := by
  let := residue_three_nontrivial
  obtain ⟨⟨a,b⟩, rfl⟩ := ofCoords_surjective z
  have ha : 0 ≤ a%3 ∧ a%3 < 3 := ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  have hb : 0 ≤ b%3 ∧ b%3 < 3 := ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  let q := Ideal.Quotient.mk (modulus (3 : Eisenstein))
  have hreduce : q (ofCoords a b) = q (ofCoords (a%3) (b%3)) := residue_ofCoords_mod_three a b
  have hω : (q omegaE)^2 + q omegaE + 1 = 0 := by
    have he : omegaE^2 + omegaE + 1 = 0 := Subtype.ext omega_quadratic
    simpa only [map_add, map_pow, map_one, map_zero] using congrArg q he
  have h3 : (3 : Residues (3 : Eisenstein)) = 0 := by
    simpa only [map_ofNat] using residue_three_eq_zero
  have hunit : IsUnit (q (ofCoords (a%3) (b%3))) := hreduce ▸ hz
  have hbad {v : Residues (3 : Eisenstein)} (hv : IsUnit v) (hsq : v^2 = 0) : False :=
    (hv.pow 2).ne_zero hsq
  have hprimary (u : Eisenstein) (heq : q (ofCoords (a%3) (b%3)) * q u = 1) :
      primary (ofCoords a b * u) := by
    rw [primary_iff_residue_one, map_mul]
    exact (congrArg (· * q u) hreduce).trans heq
  obtain ⟨ha0,ha3⟩ := ha
  obtain ⟨hb0,hb3⟩ := hb
  interval_cases hA : a%3 <;> interval_cases hB : b%3
  · simp [ofCoords] at hunit
  · refine ⟨omegaE^2, omegaE_isUnit.pow 2, hprimary _ ?_⟩
    simpa only [hA, hB, ofCoords, Int.cast_zero, Int.cast_one, zero_add, one_mul,
      map_pow, map_one, ← pow_succ'] using congrArg q omegaE_cube
  · refine ⟨-omegaE^2, (omegaE_isUnit.pow 2).neg, hprimary _ ?_⟩
    simp only [ofCoords, Int.cast_zero, Int.cast_ofNat, zero_add,
      map_mul, map_ofNat, map_neg, map_pow]
    have hc : (q omegaE)^3 = 1 := by simpa only [map_pow, map_one] using congrArg q omegaE_cube
    linear_combination -2*hc - h3
  · refine ⟨1, isUnit_one, hprimary _ ?_⟩
    simp [ofCoords]
  · refine ⟨-omegaE, omegaE_isUnit.neg, hprimary _ ?_⟩
    simp only [ofCoords, Int.cast_one, one_mul, map_add, map_one, map_neg]
    linear_combination -hω
  · apply (hbad hunit ?_).elim
    simp only [ofCoords, Int.cast_one, Int.cast_ofNat, map_add, map_mul, map_one, map_ofNat]
    linear_combination 4*hω - h3
  · refine ⟨-1, isUnit_one.neg, hprimary _ ?_⟩
    simp only [ofCoords, Int.cast_zero, Int.cast_ofNat, zero_mul, add_zero,
      map_ofNat, map_neg, map_one]
    linear_combination -h3
  · apply (hbad hunit ?_).elim
    simp only [ofCoords, Int.cast_one, Int.cast_ofNat, one_mul, map_add, map_ofNat]
    linear_combination hω + h3 * (q omegaE+1)
  · refine ⟨omegaE, omegaE_isUnit, hprimary _ ?_⟩
    simp only [ofCoords, Int.cast_ofNat, map_add, map_mul, map_ofNat]
    linear_combination 2*hω - h3

lemma unit_residue_of_dvd_primary {n d : Eisenstein} (hn : primary n) (hd : d ∣ n) :
    IsUnit (Ideal.Quotient.mk (modulus 3) d) := by
  apply isUnit_of_dvd_one
  rw [← (primary_iff_residue_one n).mp hn]
  exact map_dvd (Ideal.Quotient.mk (modulus 3)) hd

def primaryNormalize (z : Eisenstein) : Eisenstein :=
  if h : IsUnit (Ideal.Quotient.mk (modulus 3) z) then
    z * Classical.choose (unit_lift_mod_three h)
  else z

lemma primaryNormalize_associated (z : Eisenstein) : Associated z (primaryNormalize z) := by
  unfold primaryNormalize
  split_ifs with h
  · exact associated_mul_unit_right _ _ (Classical.choose_spec (unit_lift_mod_three h)).1
  · rfl

lemma primaryNormalize_primary {z : Eisenstein}
    (hz : IsUnit (Ideal.Quotient.mk (modulus 3) z)) : primary (primaryNormalize z) := by
  rw [primaryNormalize, dite_eq_left hz]
  exact (Classical.choose_spec (unit_lift_mod_three hz)).2

lemma primaryNormalize_eq_self {z : Eisenstein} (hz : primary z) : primaryNormalize z = z := by
  exact primary_associated_eq
    (primaryNormalize_primary (unit_residue_of_dvd_primary hz (dvd_refl z))) hz
    (primaryNormalize_associated z).symm

lemma exists_unique_primary_associate {z : Eisenstein}
    (hz : IsUnit (Ideal.Quotient.mk (modulus 3) z)) :
    ∃! w : Eisenstein, primary w ∧ Associated z w := by
  refine ⟨primaryNormalize z, ⟨primaryNormalize_primary hz, primaryNormalize_associated z⟩, ?_⟩
  intro w hw
  exact primary_associated_eq hw.1 (primaryNormalize_primary hz)
    (hw.2.symm.trans (primaryNormalize_associated z))

lemma normNat_primaryNormalize (z : Eisenstein) : normNat (primaryNormalize z) = normNat z :=
  (associated_normNat (primaryNormalize_associated z)).symm

lemma prime_primaryNormalize {z : Eisenstein} (hz : Prime z) : Prime (primaryNormalize z) :=
  (primaryNormalize_associated z).prime_iff.mp hz

lemma primaryNormalize_injOn_primeFactors (n : Eisenstein) :
    Set.InjOn primaryNormalize (primeFactors n : Set Eisenstein) := by
  intro a ha b hb hab
  apply mem_normalizedFactors_eq_of_associated
    (Multiset.mem_toFinset.mp ha) (Multiset.mem_toFinset.mp hb)
  exact (primaryNormalize_associated a).trans (hab ▸ (primaryNormalize_associated b).symm)

def primaryPrimeFactors (n : Eisenstein) : Finset Eisenstein :=
  (primeFactors n).image primaryNormalize

lemma primaryPrimeFactor_spec {n p : Eisenstein} (hn : primary n)
    (hp : p ∈ primaryPrimeFactors n) : primaryPrime p ∧ p ∣ n := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  have hq' : q ∈ normalizedFactors n := Multiset.mem_toFinset.mp hq
  have hd : q ∣ n := dvd_of_mem_normalizedFactors hq'
  exact ⟨⟨primaryNormalize_primary (unit_residue_of_dvd_primary hn hd),
    prime_primaryNormalize (prime_of_normalized_factor q hq')⟩,
    (primaryNormalize_associated q).dvd_iff_dvd_left.mp hd⟩

lemma primary_finset_prod {ι : Type*} (s : Finset ι) (f : ι → Eisenstein)
    (hf : ∀ i ∈ s, primary (f i)) : primary (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [primary]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact primary_mul (hf _ (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma primaryPrimeFactors_prod {n : Eisenstein} (hn : primary n) (hs : Squarefree n) :
    ∏ p ∈ primaryPrimeFactors n, p = n := by
  have heq : (∏ p ∈ primeFactors n, p) = (normalizedFactors n).prod := by
    rw [primeFactors, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr (primeFactors_nodup hs)]
    simp
  apply primary_associated_eq
    (primary_finset_prod _ _ (fun p hp => (primaryPrimeFactor_spec hn hp).1.1)) hn
  rw [primaryPrimeFactors, Finset.prod_image (primaryNormalize_injOn_primeFactors n)]
  exact ((Associated.prod _ _ _ (fun p _ => primaryNormalize_associated p)).symm).trans
    (heq ▸ prod_normalizedFactors hs.ne_zero)

lemma primaryPrimeFactors_card (n : Eisenstein) :
    (primaryPrimeFactors n).card = (primeFactors n).card :=
  Finset.card_image_of_injOn (primaryNormalize_injOn_primeFactors n)

lemma primaryPrimeFactors_norm_prod {n : Eisenstein} (hn : primary n) (hs : Squarefree n) :
    ∏ p ∈ primaryPrimeFactors n, normNat p = normNat n := by
  calc
    _ = normNat (∏ p ∈ primaryPrimeFactors n, p) := (map_prod normNatHom _ _).symm
    _ = normNat n := congrArg normNat (primaryPrimeFactors_prod hn hs)

end CubicFirstMoment
end
end

end OAI
