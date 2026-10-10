import OAI.NumberTheory.Ostmann.Construction.PrimeTupleTranslation

namespace OAI

/-! # CRT translation tables indexed by the prime product alone -/

namespace Ostmann

open scoped BigOperators Classical

theorem exists_primeSet_translation (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime)
    (t : ℕ → ℤ) (L : ℕ) [NeZero L] (hcop : L.Coprime U.toList.prod) :
    ∃ τ h₀ : ℕ, τ < U.toList.prod ∧ h₀ < L ∧
      (L : ℤ) ∣ (τ : ℤ) + (U.toList.prod : ℤ) * h₀ ∧
      ∀ p ∈ U, (τ : ZMod p) = (t p : ZMod p) := by
  let a (p : ℕ) := (t p : ZMod p).val
  have hn : ∀ p ∈ U, p ≠ 0 := fun p hp => (hU p hp).ne_zero
  have hpair : Set.Pairwise U Nat.Coprime := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hU p hp) (hU q hq)).mpr hpq
  let z := Nat.chineseRemainderOfFinset a id U hn hpair
  have hz : z.val < U.toList.prod := by
    simpa only [Finset.prod_toList, id_eq] using Nat.chineseRemainderOfFinset_lt_prod a id hn hpair
  let r : ZMod L := -(z.val : ZMod L) * (U.toList.prod : ZMod L)⁻¹
  have hu : IsUnit (U.toList.prod : ZMod L) := (ZMod.isUnit_iff_coprime _ _).mpr hcop.symm
  refine ⟨z.val, r.val, hz, ZMod.val_lt r, ?_, ?_⟩
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ L).mp
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    change (z.val : ZMod L) + (U.toList.prod : ZMod L) * r = 0
    dsimp [r]
    rw [mul_comm (-(z.val : ZMod L)), ← mul_assoc, ZMod.mul_inv_of_unit _ hu]
    ring
  · intro p hp
    let : NeZero p := ⟨hn p hp⟩
    have hh := (ZMod.natCast_eq_natCast_iff z.val (a p) p).mpr (z.property p hp)
    simpa only [a, ZMod.natCast_zmod_val] using hh

/-- The chosen translation depends on the squarefree product, so all
permutations of a tuple use the same Fourier phase and coefficient array. -/
theorem exists_primeProduct_translations (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k L : ℕ) [NeZero L] (t : ℕ → ℤ)
    (hcop : ∀ M ∈ primeSubsetProducts P k, L.Coprime M) :
    ∃ τ h₀ : ℕ → ℕ, ∀ M ∈ primeSubsetProducts P k,
      τ M < M ∧ h₀ M < L ∧ (L : ℤ) ∣ (τ M : ℤ) + (M : ℤ) * h₀ M ∧
      ∀ p ∈ M.primeFactors, (τ M : ZMod p) = (t p : ZMod p) := by
  have hex (M : ℕ) : ∃ a b : ℕ, M ∈ primeSubsetProducts P k →
      a < M ∧ b < L ∧ (L : ℤ) ∣ (a : ℤ) + (M : ℤ) * b ∧
      ∀ p ∈ M.primeFactors, (a : ZMod p) = (t p : ZMod p) := by
    by_cases hM : M ∈ primeSubsetProducts P k
    · obtain ⟨U, hU, hprod⟩ := Finset.mem_image.mp hM
      have hUP := (Finset.mem_powersetCard.mp hU).1
      have hp : ∀ p ∈ U, p.Prime := fun p hp => hP p (hUP hp)
      have hprod' : U.toList.prod = M := by simpa only [Finset.prod_toList] using hprod
      obtain ⟨a, b, ha, hb, hd, hc⟩ := exists_primeSet_translation U hp t L
        (by simpa only [hprod'] using hcop M hM)
      refine ⟨a, b, fun _ => ⟨?_, hb, ?_, ?_⟩⟩
      · simpa only [hprod'] using ha
      · simpa only [hprod'] using hd
      · have hf : M.primeFactors = U := by rw [← hprod, Nat.primeFactors_prod hp]
        simpa only [hf] using hc
    · exact ⟨0, 0, fun h => (hM h).elim⟩
  choose τ h₀ hh using hex
  exact ⟨τ, h₀, hh⟩

theorem primeTupleProduct_mem (P : Finset ℕ) {k : ℕ} (e : Fin k ↪ P) :
    primeTupleProduct P e ∈ primeSubsetProducts P k := by
  apply Finset.mem_image.mpr
  refine ⟨primeTupleSet P e, Finset.mem_powersetCard.mpr ⟨primeTupleSet_subset P e, ?_⟩, ?_⟩
  · have hc : (primeTupleSet P e).card = (Finset.univ : Finset (Fin k)).card := by
      apply Finset.card_image_iff.mpr
      intro i _ j _ he
      exact e.injective (Subtype.ext he)
    simpa only [Finset.card_univ, Fintype.card_fin] using hc
  · simpa only [Finset.prod_toList] using (primeTupleProduct_eq_set P e).symm

theorem primeTuple_member_primeFactors (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {k : ℕ} (e : Fin k ↪ P) (i : Fin k) : (e i).val ∈ (primeTupleProduct P e).primeFactors := by
  rw [primeTupleProduct_eq_set, Finset.prod_toList,
    Nat.primeFactors_prod (fun p hp => hP p (primeTupleSet_subset P e hp))]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

end Ostmann

end OAI
