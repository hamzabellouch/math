import OAI.Combinatorics.MatchingPSD.TensorBounds

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace MatchingSmoothing

lemma pow_mul_factorial_le_mode (t j : ℕ) :
    t ^ j * t.factorial ≤ t ^ t * j.factorial := by
  rcases le_total j t with hj | ht
  · have he : t.factorial = j.factorial * t.descFactorial (t - j) := by
      simpa only [Nat.sub_sub_self hj] using
        (Nat.factorial_mul_descFactorial (Nat.sub_le t j)).symm
    calc
      t ^ j * t.factorial = t ^ j * (j.factorial * t.descFactorial (t - j)) := by rw [he]
      _ ≤ t ^ j * (j.factorial * t ^ (t - j)) := by
        gcongr; exact Nat.descFactorial_le_pow _ _
      _ = t ^ t * j.factorial := by
        rw [mul_comm j.factorial (t ^ (t - j)), ← mul_assoc, ← pow_add, Nat.add_sub_of_le hj]
  · have he : j.factorial = t.factorial * (t + 1).ascFactorial (j - t) := by
      simpa only [Nat.add_sub_of_le ht] using (Nat.factorial_mul_ascFactorial t (j - t)).symm
    have hp : t ^ (j - t) ≤ (t + 1).ascFactorial (j - t) :=
      (Nat.pow_le_pow_left (Nat.le_succ t) _).trans (Nat.pow_succ_le_ascFactorial _ _)
    calc
      t ^ j * t.factorial = t ^ t * (t.factorial * t ^ (j - t)) := by
        rw [mul_comm t.factorial (t ^ (j - t)), ← mul_assoc, ← pow_add, Nat.add_sub_of_le ht]
      _ ≤ t ^ t * (t.factorial * (t + 1).ascFactorial (j - t)) := by gcongr
      _ = t ^ t * j.factorial := by rw [he]

lemma poisson_mass_le_integer_mode (t j : ℕ) :
    (t : ℝ) ^ j / j.factorial ≤ (t : ℝ) ^ t / t.factorial := by
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < j.factorial)
    (by positivity : (0 : ℝ) < t.factorial)).mpr
  exact_mod_cast pow_mul_factorial_le_mode t j

lemma multinomial_term_eq {ι : Type u_1} (s : Finset ι) (k : ι → ℕ) (a : ι → ℝ) :
    (Nat.multinomial s k : ℝ) * ∏ i ∈ s, a i ^ k i =
      ((∑ i ∈ s, k i).factorial : ℝ) * ∏ i ∈ s, (a i ^ k i / (k i).factorial) := by
  rw [Finset.prod_div_distrib]
  have he : (∏ i ∈ s, ((k i).factorial : ℝ)) * Nat.multinomial s k =
      ((∑ i ∈ s, k i).factorial : ℝ) := by exact_mod_cast Nat.multinomial_spec s k
  rw [← he]
  have hn : ∏ i ∈ s, ((k i).factorial : ℝ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (by intro i _; positivity)
  field_simp

lemma multinomial_term_le_mode {ι : Type u_2} (s : Finset ι) (t k : ι → ℕ)
    (hk : ∑ i ∈ s, k i = ∑ i ∈ s, t i) :
    (Nat.multinomial s k : ℝ) * ∏ i ∈ s, (t i : ℝ) ^ k i ≤
      (Nat.multinomial s t : ℝ) * ∏ i ∈ s, (t i : ℝ) ^ t i := by
  rw [multinomial_term_eq, multinomial_term_eq, hk]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.prod_le_prod₀
  · intro i _; positivity
  · intro i _; exact poisson_mass_le_integer_mode _ _

lemma card_piAntidiag_univ_le {ι : Type u_3} [Fintype ι] [DecidableEq ι] (n : ℕ) :
    (Finset.piAntidiag (Finset.univ : Finset ι) n).card ≤
      (n + 1) ^ Fintype.card ι := by
  classical
  let s := Finset.piAntidiag (Finset.univ : Finset ι) n
  have hn (k : s) (i : ι) : k.1 i ≤ n := by
    have he := (Finset.mem_piAntidiag.mp k.2).1
    rw [← he]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  let e : s → (ι → Fin (n + 1)) := fun k i => ⟨k.1 i, Nat.lt_succ_of_le (hn k i)⟩
  have hi : Function.Injective e := by
    intro k l h
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun h i)
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using
    Fintype.card_le_of_injective e hi

lemma multinomial_mode_lower {ι : Type u_4} [Fintype ι] [DecidableEq ι]
    (t : ι → ℕ) (n : ℕ) (ht : ∑ i, t i = n) :
    (n : ℝ) ^ n ≤ (n + 1 : ℝ) ^ Fintype.card ι *
      ((Nat.multinomial Finset.univ t : ℝ) * ∏ i, (t i : ℝ) ^ t i) := by
  have hs : ∑ i, (t i : ℝ) = n := by exact_mod_cast ht
  conv_lhs => rw [← hs, Finset.sum_pow_eq_sum_piAntidiag]
  calc
    _ ≤ ∑ _k ∈ Finset.piAntidiag Finset.univ n,
        (Nat.multinomial Finset.univ t : ℝ) * ∏ i, (t i : ℝ) ^ t i := by
      apply Finset.sum_le_sum
      intro k hk
      apply multinomial_term_le_mode
      exact (Finset.mem_piAntidiag.mp hk).1.trans ht.symm
    _ = ((Finset.piAntidiag (Finset.univ : Finset ι) n).card : ℝ) *
        ((Nat.multinomial Finset.univ t : ℝ) * ∏ i, (t i : ℝ) ^ t i) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_piAntidiag_univ_le (ι := ι) n

section ProductTypes
variable {H : Type u_5} {A : Type u_6} {T : Type u_7} [Fintype H] [DecidableEq H] [Fintype A] [Fintype T]
  [DecidableEq A] [DecidableEq T]

noncomputable def functionFiberEquiv (η : A → T) (k : H → T) :
    {f : H → A // η ∘ f = k} ≃ ((i : H) → {a : A // η a = k i}) where
  toFun f i := ⟨f.1 i, congrFun f.2 i⟩
  invFun g := ⟨fun i => (g i).1, funext (fun i => (g i).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype T] [DecidableEq A] in
lemma card_functionFiber (η : A → T) (k : H → T) :
    Fintype.card {f : H → A // η ∘ f = k} =
      ∏ i, Fintype.card {a : A // η a = k i} := by
  rw [Fintype.card_congr (functionFiberEquiv η k), Fintype.card_pi]

omit [DecidableEq H] in
lemma prod_eq_prod_histogram (f : H → T) (w : T → ℝ) :
    (∏ i, w (f i)) = ∏ t, w t ^ histogram f t := by
  rw [← Fintype.prod_fiberwise f]
  apply Finset.prod_congr rfl
  intro t _
  have he (i : {i // f i = t}) : w (f i.1) = w t := congrArg w i.2
  simp only [he, Finset.prod_const, Finset.card_univ, histogram]

omit [DecidableEq A] in
lemma sum_product_of_types (η : A → T) (q : T → ℝ) (F : (H → T) → ℝ) :
    (∑ f : H → A, F (η ∘ f) * ∏ i, q (η (f i))) =
      ∑ k : H → T, F k * ∏ i, ((Fintype.card {a : A // η a = k i} : ℝ) * q (k i)) := by
  classical
  rw [← Fintype.sum_fiberwise (fun f : H → A => η ∘ f)]
  apply Finset.sum_congr rfl
  intro k _
  have he (f : {f : H → A // η ∘ f = k}) :
      F (η ∘ f.1) * ∏ i, q (η (f.1 i)) = F k * ∏ i, q (k i) := by
    rw [f.2]
    congr 1
    exact Finset.prod_congr rfl (fun i _ => congrArg q (congrFun f.2 i))
  simp_rw [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [card_functionFiber, Nat.cast_prod, Finset.prod_mul_distrib]
  ring

omit [DecidableEq A] in
lemma sum_product_of_type_probabilities (η : A → T) (hη : Function.Surjective η)
    (p : T → ℝ) (F : (H → T) → ℝ) :
    (∑ f : H → A, F (η ∘ f) *
      ∏ i, p (η (f i)) / Fintype.card {a : A // η a = η (f i)}) =
      ∑ k : H → T, F k * ∏ i, p (k i) := by
  rw [sum_product_of_types η
    (fun t => p t / Fintype.card {a : A // η a = t}) F]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have hn : (Fintype.card {a : A // η a = k i} : ℝ) ≠ 0 := by
    obtain ⟨a, ha⟩ := hη (k i)
    exact_mod_cast ne_of_gt ((Fintype.card_pos_iff (α := {a : A // η a = k i})).mpr ⟨⟨a, ha⟩⟩)
  field_simp

omit [DecidableEq A] in
lemma sum_type_probability_eq_multinomial (η : A → T) (hη : Function.Surjective η)
    (k₀ : H → T) (p : T → ℝ) :
    (∑ f : H → A, (if histogram (η ∘ f) = histogram k₀ then (1 : ℝ) else 0) *
      ∏ i, p (η (f i)) / Fintype.card {a : A // η a = η (f i)}) =
      (Nat.multinomial Finset.univ (histogram k₀) : ℝ) *
        ∏ t, p t ^ histogram k₀ t := by
  classical
  rw [sum_product_of_type_probabilities η hη p
    (fun k => if histogram k = histogram k₀ then 1 else 0)]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.sum_subtype_eq_sum_filter]
  simp only [Finset.subtype_univ]
  have he (k : Colorings H T (histogram k₀)) :
      (∏ i, p (k.1 i)) = ∏ t, p t ^ histogram k₀ t := by
    rw [prod_eq_prod_histogram, k.2]
  simp_rw [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_colorings_eq_multinomial]

omit [DecidableEq A] in
lemma integer_mean_type_probability_lower (η : A → T) (hη : Function.Surjective η)
    (k₀ : H → T) (hH : 0 < Fintype.card H) :
    1 ≤ (Fintype.card H + 1 : ℝ) ^ Fintype.card T *
      (∑ f : H → A, (if histogram (η ∘ f) = histogram k₀ then (1 : ℝ) else 0) *
        ∏ i, ((histogram k₀ (η (f i)) : ℝ) / Fintype.card H) /
          Fintype.card {a : A // η a = η (f i)}) := by
  classical
  rw [sum_type_probability_eq_multinomial η hη k₀
    (fun t => (histogram k₀ t : ℝ) / Fintype.card H)]
  have hl := multinomial_mode_lower (histogram k₀) (Fintype.card H) (sum_histogram k₀)
  simp_rw [div_pow]
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, sum_histogram]
  have hp : (0 : ℝ) < (Fintype.card H : ℝ) ^ Fintype.card H := by positivity
  apply (mul_le_mul_iff_left₀ hp).mp
  field_simp
  nlinarith

end ProductTypes

end MatchingSmoothing

end OAI
