import OAI.NumberTheory.Ostmann.Quadratic.CommonCenterTupleCounts
import OAI.NumberTheory.Ostmann.ZeroDensity.ProgressionLiftCount

namespace OAI

/-! # Uniform lift bounds for ordered distinct prime tuples -/

namespace Ostmann

open scoped BigOperators

def primeTupleProduct (P : Finset ℕ) {r : ℕ} (e : Fin r ↪ P) : ℕ := ∏ i, (e i).1

theorem primeTupleProduct_pos (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {r : ℕ} (e : Fin r ↪ P) : 0 < primeTupleProduct P e :=
  Finset.prod_pos (fun i _ => (hprime _ (e i).2).pos)

private theorem tuple_prime_coprime (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {r : ℕ} (e : Fin r ↪ P) {i j : Fin r} (hij : i ≠ j) :
    ((e i).1).Coprime ((e j).1) := by
  have hne : (e i).1 ≠ (e j).1 := fun h => hij (e.injective (Subtype.ext h))
  apply (hprime _ (e i).2).coprime_iff_not_dvd.mpr
  intro h
  exact hne (((hprime _ (e j).2).eq_one_or_self_of_dvd _ h).resolve_left
    (hprime _ (e i).2).ne_one)

/-- Two lifts of the same distinct prime tuple lie in the same progression
modulo the product of those primes. -/
theorem tuple_lifts_modEq (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (a : ℤ) (t : ℕ → ℤ) {r : ℕ} (e : Fin r ↪ P) (n m : ℤ)
    (hn : ∀ i, ((e i).1 : ℤ) ∣ n - a * t (e i).1)
    (hm : ∀ i, ((e i).1 : ℤ) ∣ m - a * t (e i).1) :
    n ≡ m [ZMOD (primeTupleProduct P e : ℤ)] := by
  apply Int.modEq_iff_dvd.mpr
  have hpair : ((Finset.univ : Finset (Fin r)) : Set (Fin r)).Pairwise
      (fun i j => IsCoprime ((e i).1 : ℤ) ((e j).1 : ℤ)) := by
    intro i _ j _ hij
    exact (tuple_prime_coprime P hprime e hij).cast
  have hd : (∏ i : Fin r, ((e i).1 : ℤ)) ∣ m - n := by
    apply Finset.prod_dvd_of_coprime hpair
    intro i _
    have h := dvd_sub (hm i) (hn i)
    simpa only [sub_sub_sub_cancel_right] using h
  simpa only [primeTupleProduct, Nat.cast_prod] using hd

def integerLiftSet (P : Finset ℕ) (a : ℤ) (t : ℕ → ℤ) {r : ℕ}
    (e : Fin r ↪ P) (H : ℕ) : Finset ℤ :=
  (Finset.Ico (-(H : ℤ)) (H + 1)).filter fun n =>
    ∀ i, ((e i).1 : ℤ) ∣ n - a * t (e i).1

/-- Uniform in the chosen tuple and its residue class. -/
theorem card_integerLiftSet_le (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (a : ℤ) (t : ℕ → ℤ) {r : ℕ} (e : Fin r ↪ P) (H : ℕ) :
    ((integerLiftSet P a t e H).card : ℚ) ≤
      (2 * (H : ℚ) + 1) / (primeTupleProduct P e : ℚ) + 1 := by
  classical
  have hM : 0 < primeTupleProduct P e := primeTupleProduct_pos P hprime e
  by_cases hnon : (integerLiftSet P a t e H).Nonempty
  · obtain ⟨m, hm⟩ := hnon
    have hm' := (Finset.mem_filter.mp hm).2
    have hsub : integerLiftSet P a t e H ⊆
        (Finset.Ico (-(H : ℤ)) (H + 1)).filter
          (fun n => n ≡ m [ZMOD (primeTupleProduct P e : ℤ)]) := by
      intro n hn
      obtain ⟨hI, hn'⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨hI, tuple_lifts_modEq P hprime a t e n m hn' hm'⟩
    have hcard : ((integerLiftSet P a t e H).card : ℚ) ≤
        (((Finset.Ico (-(H : ℤ)) (H + 1)).filter
          (fun n => n ≡ m [ZMOD (primeTupleProduct P e : ℤ)])).card : ℚ) := by
      exact_mod_cast Finset.card_le_card hsub
    refine hcard.trans ?_
    have hp := progression_Ico_card_le (-(H : ℤ)) (H + 1)
      (primeTupleProduct P e) m (by omega) (by exact_mod_cast hM)
    convert hp using 1
    push_cast
    ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hnon, Finset.card_empty, Nat.cast_zero]
    positivity

theorem primeTupleProduct_lower (P : Finset ℕ) (Z : ℕ)
    (hZ : ∀ p ∈ P, Z ≤ p) {r : ℕ} (e : Fin r ↪ P) :
    Z ^ r ≤ primeTupleProduct P e := by
  have h := Finset.prod_le_prod (fun (i : Fin r) (_ : i ∈ Finset.univ) => hZ _ (e i).2)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, primeTupleProduct] using h

/-- The bound used in the lower factorial moment is uniform over the tuple. -/
theorem card_integerLiftSet_le_uniform (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (a : ℤ) (t : ℕ → ℤ) {r : ℕ} (e : Fin r ↪ P) (H Z : ℕ)
    (hZ : 0 < Z) (hmin : ∀ p ∈ P, Z ≤ p) :
    ((integerLiftSet P a t e H).card : ℚ) ≤ (2 * (H : ℚ) + 1) / (Z : ℚ) ^ r + 1 := by
  have hprod : (Z : ℚ) ^ r ≤ (primeTupleProduct P e : ℚ) := by
    exact_mod_cast primeTupleProduct_lower P Z hmin e
  have hpos : (0 : ℚ) < Z := by exact_mod_cast hZ
  have hn : (0 : ℚ) ≤ 2 * (H : ℚ) + 1 := by positivity
  have hd := div_le_div_of_nonneg_left hn (pow_pos hpos r) hprod
  exact (card_integerLiftSet_le P hprime a t e H).trans (by linarith)

end Ostmann

end OAI
