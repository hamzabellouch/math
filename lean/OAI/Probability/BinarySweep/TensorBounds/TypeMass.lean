import Mathlib

namespace OAI

noncomputable section

section

open scoped BigOperators

namespace BinaryCoordinateSweeps.Density

lemma factorial_mode (b c : ℕ) : c.factorial * c^b ≤ b.factorial * c^c := by
  rcases le_total c b with h | h
  · have hi := Nat.factorial_mul_pow_sub_le_factorial h
    calc
      c.factorial * c^b = (c.factorial * c^(b-c)) * c^c := by
        rw [mul_assoc, ← pow_add, Nat.sub_add_cancel h]
      _ ≤ b.factorial * c^c := Nat.mul_le_mul_right _ hi
  · have hi : c.factorial ≤ b.factorial * c^(c-b) := by
      calc
        c.factorial = b.factorial * c.descFactorial (c-b) := by
          simpa only [Nat.sub_sub_self h] using
            (Nat.factorial_mul_descFactorial (Nat.sub_le c b)).symm
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow _ _)
    calc
      c.factorial * c^b ≤ (b.factorial * c^(c-b)) * c^b := Nat.mul_le_mul_right _ hi
      _ = b.factorial * c^c := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel h]

variable {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
lemma multinomial_mode (n : ℕ) (c b : A → ℕ) (hc : ∑ a, c a = n) (hb : ∑ a, b a = n) :
    Nat.multinomial Finset.univ b * ∏ a, (c a)^(b a) ≤
      Nat.multinomial Finset.univ c * ∏ a, (c a)^(c a) := by
  have h := Finset.prod_le_prod (fun a (_ : a ∈ (Finset.univ : Finset A)) => factorial_mode (b a) (c a))
  simp only [Finset.prod_mul_distrib] at h
  have hbs := Nat.multinomial_spec (s := Finset.univ) (f := b)
  have hcs := Nat.multinomial_spec (s := Finset.univ) (f := c)
  rw [hb] at hbs
  rw [hc] at hcs
  refine Nat.le_of_mul_le_mul_left (c := n.factorial) ?_ (Nat.factorial_pos n)
  calc
    n.factorial * (Nat.multinomial Finset.univ b * ∏ a, c a ^ b a) =
        (Nat.multinomial Finset.univ b * Nat.multinomial Finset.univ c) *
          ((∏ a, (c a).factorial) * ∏ a, c a ^ b a) := by rw [← hcs]; ring
    _ ≤ (Nat.multinomial Finset.univ b * Nat.multinomial Finset.univ c) *
          ((∏ a, (b a).factorial) * ∏ a, c a ^ c a) := Nat.mul_le_mul_left _ h
    _ = n.factorial * (Nat.multinomial Finset.univ c * ∏ a, c a ^ c a) := by rw [← hbs]; ring

lemma card_types_le (n : ℕ) :
    (Finset.piAntidiag (Finset.univ : Finset A) n).card ≤ (n+1)^(Fintype.card A) := by
  classical
  let T := ↥(Finset.piAntidiag (Finset.univ : Finset A) n)
  let : Fintype T := FinsetCoe.fintype _
  let f : T → (A → Fin (n+1)) := fun b a => ⟨b.val a, by
    have hb := (Finset.mem_piAntidiag.mp b.property).1
    have hh := Finset.single_le_sum (f := b.val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    exact Nat.lt_succ_of_le (hh.trans_eq hb)⟩
  have hf : Function.Injective f := by
    intro b c h
    apply Subtype.ext
    funext a
    exact congrArg Fin.val (congrFun h a)
  have h := Fintype.card_le_of_injective f hf
  simpa [T, Fintype.card_pi] using h

theorem type_mass_lower_nat (n : ℕ) (c : A → ℕ) (hc : ∑ a, c a = n) :
    n^n ≤ (n+1)^(Fintype.card A) *
      (Nat.multinomial Finset.univ c * ∏ a, c a ^ c a) := by
  calc
    n^n = ∑ b ∈ Finset.piAntidiag Finset.univ n,
        Nat.multinomial Finset.univ b * ∏ a, c a ^ b a := by
      simpa only [Nat.cast_id, hc] using Finset.sum_pow_eq_sum_piAntidiag Finset.univ c n
    _ ≤ ∑ _b ∈ Finset.piAntidiag (Finset.univ : Finset A) n,
        Nat.multinomial Finset.univ c * ∏ a, c a ^ c a := by
      apply Finset.sum_le_sum
      intro b hb
      exact multinomial_mode n c b hc (Finset.mem_piAntidiag.mp hb).1
    _ = (Finset.piAntidiag (Finset.univ : Finset A) n).card *
        (Nat.multinomial Finset.univ c * ∏ a, c a ^ c a) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (card_types_le n)

theorem type_mass_lower (n : ℕ) (hn : 0 < n) (c : A → ℕ) (hc : ∑ a, c a = n) :
    1 ≤ ((n+1 : ℕ) : ℝ)^(Fintype.card A) *
      ((Nat.multinomial Finset.univ c : ℝ) * ∏ a, ((c a : ℝ) / n) ^ c a) := by
  have h : (n : ℝ)^n ≤ ((n+1 : ℕ) : ℝ)^(Fintype.card A) *
      ((Nat.multinomial Finset.univ c : ℝ) * ∏ a, (c a : ℝ)^c a) := by
    exact_mod_cast type_mass_lower_nat n c hc
  have hn' : 0 < (n : ℝ)^n := pow_pos (by exact_mod_cast hn) _
  simp_rw [div_pow]
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hc]
  rw [← mul_div_assoc, ← mul_div_assoc]
  apply (le_div_iff₀ hn').mpr
  simpa only [one_mul, mul_div_assoc] using h

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Density
variable {A I : Type*} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]

def wordCounts (w : I → A) : A →₀ ℕ := ∑ i, Finsupp.single (w i) 1

omit [Fintype A] [DecidableEq I] in
lemma wordCounts_apply (w : I → A) (a : A) :
    wordCounts w a = (Finset.univ.filter (fun i => w i = a)).card := by
  simp only [wordCounts, Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.card_filter]

omit [Fintype A] [DecidableEq I] in
lemma wordCounts_fiber (w : I → A) (a : A) :
    wordCounts w a = Fintype.card {i // w i = a} := by
  rw [Fintype.card_subtype, wordCounts_apply]

omit [Fintype A] [DecidableEq A] [DecidableEq I] in
lemma wordCounts_total (w : I → A) : (wordCounts w).sum (fun _ k => k) = Fintype.card I := by
  rw [wordCounts, ← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  simp

omit [DecidableEq A] [DecidableEq I] in
lemma wordCounts_sum (w : I → A) : ∑ a, wordCounts w a = Fintype.card I := by
  have h := wordCounts_total w
  rw [Finsupp.sum_of_support_subset _ (Finset.subset_univ _) (fun _ k => k) (by simp)] at h
  exact h

omit [DecidableEq I] in
lemma prod_wordCounts {M : Type*} [CommMonoid M] (v : A → M) (w : I → A) :
    ∏ i, v (w i) = ∏ a, v a ^ wordCounts w a := by
  rw [← Fintype.prod_fiberwise' w v]
  apply Finset.prod_congr rfl
  intro a ha
  simp only [Finset.prod_const, Finset.card_univ, wordCounts_fiber]

omit [Fintype A] [DecidableEq A] [DecidableEq I] in
lemma wordCounts_comp (w : I → A) (g : Equiv.Perm I) : wordCounts (w ∘ g) = wordCounts w := by
  unfold wordCounts
  exact Equiv.sum_comp g (fun i => Finsupp.single (w i) 1)

omit [Fintype A] [DecidableEq I] in
lemma exists_perm_eq_of_wordCounts {w v : I → A} (h : wordCounts w = wordCounts v) :
    ∃ g : Equiv.Perm I, ∀ i, v (g i) = w i := by
  have hc (a : A) : Fintype.card {i // w i = a} = Fintype.card {i // v i = a} := by
    rw [← wordCounts_fiber, ← wordCounts_fiber, h]
  let e (a : A) := Fintype.equivOfCardEq (hc a)
  let g := (Equiv.sigmaFiberEquiv w).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv v))
  refine ⟨g, fun i => ?_⟩
  change v ((e (w i) ⟨i,rfl⟩).val) = w i
  exact (e (w i) ⟨i,rfl⟩).property

omit [DecidableEq A] in
lemma word_polynomial (n : ℕ) :
    (∑ a, MvPolynomial.X a : MvPolynomial A ℕ)^n =
      ∑ w : Fin n → A, MvPolynomial.monomial (wordCounts w) 1 := by
  calc
    _ = ∏ _i : Fin n, (∑ a, MvPolynomial.X a : MvPolynomial A ℕ) := by simp
    _ = ∑ w : Fin n → A, ∏ i, (MvPolynomial.X (w i) : MvPolynomial A ℕ) := by
      exact Fintype.prod_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [wordCounts, MvPolynomial.monomial_sum_one]
      rfl

lemma card_words_counts (n : ℕ) (c : A →₀ ℕ) (hc : c.sum (fun _ k => k) = n) :
    Fintype.card {w : Fin n → A // wordCounts w = c} = c.multinomial := by
  have he := congrArg (fun polynomial : MvPolynomial A ℕ => polynomial.coeff c)
    (word_polynomial (A := A) n)
  rw [MvPolynomial.coeff_sum_X_pow_of_fintype, ite_eq_left hc] at he
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Nat.cast_id] at he
  rw [Fintype.card_subtype, Finset.card_filter]
  convert he.symm using 1

lemma card_words_counts_fun (n : ℕ) (c : A → ℕ) (hc : ∑ a, c a = n) :
    Fintype.card {w : Fin n → A // ∀ a, wordCounts w a = c a} =
      Nat.multinomial Finset.univ c := by
  let c' : A →₀ ℕ := Finsupp.equivFunOnFinite.symm c
  have htotal : c'.sum (fun _ k => k) = n := by
    rw [Finsupp.sum_of_support_subset _ (Finset.subset_univ _) _ (by simp)]
    exact hc
  have he : {w : Fin n → A // ∀ a, wordCounts w a = c a} ≃
      {w : Fin n → A // wordCounts w = c'} := Equiv.subtypeEquivRight (fun w => by
    constructor
    · intro h
      apply Finsupp.ext
      exact h
    · intro h a
      exact congrArg (fun b : A →₀ ℕ => b a) h)
  rw [Fintype.card_congr he, card_words_counts n c' htotal,
    Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]
  rfl

end BinaryCoordinateSweeps.Density

end

end OAI
