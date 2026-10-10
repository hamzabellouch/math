import OAI.NumberTheory.Ostmann.Construction.PrimeProductMatching
import OAI.NumberTheory.Ostmann.Characters.PivotSquareSplit

namespace OAI

/-! # The supported arithmetic diagonal is a sum over actual prime permutations -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

theorem pivotDiagonal_fintype_eq {A : Type*} (F G : Fintype A)
    (L : A → ℕ) (v : A → ℤ) (c : A → ℂ) :
    @pivotDiagonal A F L v c = @pivotDiagonal A G L v c := by
  cases Subsingleton.elim F G
  rfl

noncomputable def primePermutationCorrelation {H D : Type*} [Fintype H] [Fintype D]
    (P : Finset ℕ) (v : D → ℤ) (c : ((H → P) × D) → ℂ) : ℂ :=
  ∑ e : Equiv.Perm H, ∑ l : H → P, ∑ d : D, ∑ d' : D,
    if v d = v d' then c (l, d) * conj (c (l ∘ e.symm, d')) else 0

theorem primePermutationCorrelation_congr {H D : Type*} [Fintype H] [Fintype D]
    (P : Finset ℕ) (v : D → ℤ) (c c' : ((H → P) × D) → ℂ)
    (h : ∀ (e : Equiv.Perm H) l d d', v d = v d' →
      c (l, d) * conj (c (l ∘ e.symm, d')) = c' (l, d) * conj (c' (l ∘ e.symm, d'))) :
    primePermutationCorrelation P v c = primePermutationCorrelation P v c' := by
  unfold primePermutationCorrelation
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro d' _
  split_ifs with he
  · exact h e l d d' he
  · rfl

theorem prime_pivotDiagonal_matching {A H : Type*} [Fintype A] [Fintype H]
    (p : A → H → ℕ) (hp : ∀ a h, (p a h).Prime) (v : A → ℤ) (c : A → ℂ)
    (hinj : ∀ a, c a ≠ 0 → Function.Injective (p a))
    (hv : ∀ a, c a ≠ 0 → v a ≠ 0)
    (hsmall : ∀ a, c a ≠ 0 → ∀ h, (v a).natAbs < p a h) :
    pivotDiagonal (fun a => ∏ h, p a h) v c =
      ∑ a, ∑ b, ∑ e : Equiv.Perm H,
        if v a = v b ∧ ∀ h, p a h = p b (e h) then c a * conj (c b) else 0 := by
  unfold pivotDiagonal
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : c a = 0
  · simp [ha]
  by_cases hb : c b = 0
  · simp [hb]
  have he := pivot_zero_numerator_iff (∏ h, p a h) (∏ h, p b h)
    (Finset.prod_pos (fun h _ => (hp a h).pos)) (v a) (v b) (hv a ha) (hv b hb)
    (fun q hq hd => by
      obtain ⟨h, rfl⟩ := prime_dvd_prime_product (p a) (hp a) q hq hd
      exact hsmall a ha h)
    (fun q hq hd => by
      obtain ⟨h, rfl⟩ := prime_dvd_prime_product (p b) (hp b) q hq hd
      exact hsmall b hb h)
  simp only [he]
  by_cases hab : v a = v b
  · simp only [hab, and_true, true_and]
    exact prime_product_matching_sum (p a) (p b) (hp a) (hp b) (hinj a ha) (hinj b hb) _
  · simp [hab]

theorem prime_pivotDiagonal_permutations {H D : Type*} [Fintype H] [Fintype D]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (v : D → ℤ)
    (c : ((H → P) × D) → ℂ)
    (hinj : ∀ a, c a ≠ 0 → Function.Injective (fun h => (a.1 h : ℕ)))
    (hv : ∀ a, c a ≠ 0 → v a.2 ≠ 0)
    (hsmall : ∀ a, c a ≠ 0 → ∀ h, (v a.2).natAbs < (a.1 h : ℕ)) :
    pivotDiagonal (fun a => ∏ h, (a.1 h : ℕ)) (fun a => v a.2) c =
      ∑ e : Equiv.Perm H, ∑ l : H → P, ∑ d : D, ∑ d' : D,
        if v d = v d' then c (l, d) * conj (c (l ∘ e.symm, d')) else 0 := by
  rw [prime_pivotDiagonal_matching (fun a h => (a.1 h : ℕ))
    (fun a h => hP _ (a.1 h).property) (fun a => v a.2) c hinj hv hsmall]
  calc
    _ = ∑ e : Equiv.Perm H, ∑ a, ∑ b,
        if v a.2 = v b.2 ∧ ∀ h, (a.1 h : ℕ) = (b.1 (e h) : ℕ)
          then c a * conj (c b) else 0 := by
      calc
        _ = ∑ a, ∑ e : Equiv.Perm H, ∑ b,
            if v a.2 = v b.2 ∧ ∀ h, (a.1 h : ℕ) = (b.1 (e h) : ℕ)
              then c a * conj (c b) else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro d _
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d' _
      rw [Finset.sum_eq_single (l ∘ e.symm)]
      · simp
      · intro r _ hne
        have hn : ¬ ∀ h, (l h : ℕ) = (r (e h) : ℕ) := by
          intro he
          apply hne
          funext h
          apply Subtype.ext
          simpa only [e.apply_symm_apply, Function.comp_apply] using (he (e.symm h)).symm
        simp only [hn, and_false, ite_false]
      · simp

theorem prime_pivotDiagonal_eq_correlation {H D : Type*} [Fintype H] [Fintype D]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (v : D → ℤ)
    (c : ((H → P) × D) → ℂ)
    (hinj : ∀ a, c a ≠ 0 → Function.Injective (fun h => (a.1 h : ℕ)))
    (hv : ∀ a, c a ≠ 0 → v a.2 ≠ 0)
    (hsmall : ∀ a, c a ≠ 0 → ∀ h, (v a.2).natAbs < (a.1 h : ℕ)) :
    pivotDiagonal (fun a => ∏ h, (a.1 h : ℕ)) (fun a => v a.2) c =
      primePermutationCorrelation P v c :=
  prime_pivotDiagonal_permutations P hP v c hinj hv hsmall

end Ostmann

end OAI
