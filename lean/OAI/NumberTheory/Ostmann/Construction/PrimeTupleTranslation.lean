import Mathlib.Data.Nat.ChineseRemainder
import OAI.NumberTheory.Ostmann.Quadratic.CommonCenterLiftBounds
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticAmplificationIdentity
import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeSetDivisorSum
import OAI.NumberTheory.Ostmann.QuadraticSieve.JacobiCharacter

namespace OAI

/-! # Constructing the common translation for an actual tuple of primes -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def primeTupleSet (P : Finset ℕ) {k : ℕ} (e : Fin k ↪ P) : Finset ℕ :=
  Finset.univ.image (fun i => (e i).val)

theorem primeTupleSet_subset (P : Finset ℕ) {k : ℕ} (e : Fin k ↪ P) :
    primeTupleSet P e ⊆ P := by
  intro p hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  exact (e i).property

theorem primeTupleProduct_eq_set (P : Finset ℕ) {k : ℕ} (e : Fin k ↪ P) :
    primeTupleProduct P e = (primeTupleSet P e).toList.prod := by
  simp only [primeTupleProduct, primeTupleSet, Finset.prod_toList]
  rw [Finset.prod_image]
  intro i _ j _ h
  exact e.injective (Subtype.ext h)

theorem primeTupleProduct_squarefree (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {k : ℕ} (e : Fin k ↪ P) : Squarefree (primeTupleProduct P e) := by
  rw [primeTupleProduct_eq_set]
  exact primeSet_modulus_squarefree _ (fun p hp => hP p (primeTupleSet_subset P e hp))

theorem primeTupleProduct_odd (P : Finset ℕ) (hodd : ∀ p ∈ P, Odd p)
    {k : ℕ} (e : Fin k ↪ P) : Odd (primeTupleProduct P e) := by
  change Odd (∏ i, (e i).val)
  exact Finset.prod_induction _ (fun n => Odd n)
    (fun a b ha hb => ha.mul hb) (by decide) (fun i _ => hodd _ (e i).property)

theorem primeTupleProduct_one_lt (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {k : ℕ} (hk : 0 < k) (e : Fin k ↪ P) : 1 < primeTupleProduct P e := by
  have hlow := primeTupleProduct_lower P 2 (fun p hp => (hP p hp).two_le) e
  exact (Nat.one_lt_pow (by omega : k ≠ 0) (by decide : 1 < 2)).trans_le hlow

theorem exists_primeTuple_translation (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {k : ℕ} (e : Fin k ↪ P) (t : ℕ → ℤ) (L : ℕ) [NeZero L]
    (hcop : L.Coprime (primeTupleProduct P e)) :
    let : NeZero (primeTupleProduct P e) := ⟨(primeTupleProduct_pos P hP e).ne'⟩
    ∃ tM : ZMod (primeTupleProduct P e), ∃ h₀ : ℕ, h₀ < L ∧
      (L : ℤ) ∣ (tM.val : ℤ) + (primeTupleProduct P e : ℤ) * h₀ ∧
      ∀ i, (tM.val : ZMod (e i).val) = (t (e i).val : ZMod (e i).val) := by
  intro _
  let a (i : Fin k) := (t (e i).val : ZMod (e i).val).val
  have hn (i : Fin k) (_hi : i ∈ (Finset.univ : Finset (Fin k))) : (e i).val ≠ 0 :=
    (hP _ (e i).property).ne_zero
  have hpair : Set.Pairwise (Finset.univ : Finset (Fin k))
      (fun i j => (e i).val.Coprime (e j).val) := by
    intro i _ j _ hij
    apply (Nat.coprime_primes (hP _ (e i).property) (hP _ (e j).property)).mpr
    intro he
    exact hij (e.injective (Subtype.ext he))
  let z := Nat.chineseRemainderOfFinset a (fun i => (e i).val) Finset.univ hn hpair
  have hz : z.val < primeTupleProduct P e :=
    Nat.chineseRemainderOfFinset_lt_prod a (fun i => (e i).val) hn hpair
  let tM : ZMod (primeTupleProduct P e) := z.val
  have htM : tM.val = z.val := ZMod.val_natCast_of_lt hz
  let r : ZMod L := -(tM.val : ZMod L) * (primeTupleProduct P e : ZMod L)⁻¹
  have hu : IsUnit (primeTupleProduct P e : ZMod L) :=
    (ZMod.isUnit_iff_coprime _ _).mpr hcop.symm
  refine ⟨tM, r.val, ZMod.val_lt r, ?_, ?_⟩
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ L).mp
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    change (tM.val : ZMod L) + (primeTupleProduct P e : ZMod L) * r = 0
    dsimp [r]
    rw [mul_comm (-(tM.val : ZMod L)), ← mul_assoc, ZMod.mul_inv_of_unit _ hu]
    ring
  · intro i
    let : NeZero (e i).val := ⟨(hP _ (e i).property).ne_zero⟩
    rw [htM]
    have hh := (ZMod.natCast_eq_natCast_iff z.val (a i) (e i).val).mpr
      (z.property i (Finset.mem_univ _))
    change (z.val : ZMod (e i).val) = ((t (e i).val : ZMod (e i).val).val : ZMod (e i).val) at hh
    simpa only [ZMod.natCast_zmod_val] using hh

theorem jacobi_primeTuple_translation (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {k : ℕ} (e : Fin k ↪ P) (t : ℕ → ℤ) (tM n : ℤ)
    (ht : ∀ i, (tM : ZMod (e i).val) = (t (e i).val : ZMod (e i).val)) :
    (jacobiSym (n - tM) (primeTupleProduct P e) : ℝ) =
      ∏ i, (jacobiSym (n - t (e i).val) (e i).val : ℝ) := by
  rw [primeTupleProduct_eq_set]
  simp only [Finset.prod_toList]
  rw [jacobi_product_right _ _ (fun p hp =>
    (hP p (primeTupleSet_subset P e hp)).ne_zero), Int.cast_prod]
  unfold primeTupleSet
  rw [Finset.prod_image (fun i _ j _ h => e.injective (Subtype.ext h))]
  apply Finset.prod_congr rfl
  intro i _
  let : NeZero (e i).val := ⟨(hP _ (e i).property).ne_zero⟩
  have hh : ((n - tM : ℤ) : ZMod (e i).val) = ((n - t (e i).val : ℤ) : ZMod (e i).val) := by
    simp only [Int.cast_sub, ht i]
  have he := congrArg (jacobiCharacter (e i).val) hh
  simpa only [jacobiCharacter_intCast] using he

end Ostmann

end OAI
