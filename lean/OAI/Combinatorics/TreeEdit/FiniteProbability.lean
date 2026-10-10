import OAI.Combinatorics.TreeEdit.Model

namespace OAI

namespace TreeEdit.FiniteProbability
open scoped BigOperators
open Classical

noncomputable def mean {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  (Fintype.card A : ℝ)⁻¹ * ∑ a, f a

lemma mean_nonneg {A : Type*} [Fintype A] {f : A → ℝ} (hf : ∀ a, 0 ≤ f a) :
    0 ≤ mean f := mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg (fun a _ => hf a))

lemma mean_le {A : Type*} [Fintype A] {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    mean f ≤ mean g := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => h a)) (by positivity)

lemma mean_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) : mean (fun _ : A => c) = c := by
  simp only [mean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

lemma mean_add {A : Type*} [Fintype A] (f g : A → ℝ) :
    mean (fun a => f a + g a) = mean f + mean g := by simp [mean, Finset.sum_add_distrib, mul_add]

lemma mean_mul_const {A : Type*} [Fintype A] (f : A → ℝ) (c : ℝ) :
    mean (fun a => f a * c) = mean f * c := by simp [mean, Finset.sum_mul, mul_assoc]

lemma mean_sum {A I : Type*} [Fintype A] (s : Finset I) (f : I → A → ℝ) :
    mean (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, mean (f i) := by
  simp only [mean, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma mean_prod {I : Type*} [Fintype I] {A : I → Type*} [∀ i, Fintype (A i)]
    (f : ∀ i, A i → ℝ) :
    mean (fun a : ∀ i, A i => ∏ i, f i (a i)) = ∏ i, mean (f i) := by
  classical
  simp only [mean, Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib, Finset.prod_mul_distrib]
  congr 1
  exact (Fintype.prod_sum f).symm

noncomputable def probability {A : Type*} [Fintype A] (E : A → Prop) : ℝ :=
  mean (fun a => if E a then 1 else 0)

lemma probability_nonneg {A : Type*} [Fintype A] (E : A → Prop) : 0 ≤ probability E := by
  classical
  exact mean_nonneg (fun _ => by split_ifs <;> norm_num)

lemma probability_le_one {A : Type*} [Fintype A] [Nonempty A] (E : A → Prop) :
    probability E ≤ 1 := by
  classical
  exact (mean_le (fun a => show (if E a then (1 : ℝ) else 0) ≤ 1 by split_ifs <;> norm_num)).trans_eq (mean_const 1)

lemma probability_not {A : Type*} [Fintype A] [Nonempty A] (E : A → Prop) :
    probability (fun a => ¬ E a) = 1 - probability E := by
  classical
  have hh : probability E + probability (fun a => ¬ E a) = 1 := by
    rw [probability, probability, ← mean_add]
    calc
      _ = mean (fun _ : A => (1 : ℝ)) := by
        apply congrArg mean
        funext a
        by_cases h : E a <;> simp [h]
      _ = 1 := mean_const 1
  linarith

lemma probability_mono {A : Type*} [Fintype A] {E F : A → Prop} (h : ∀ a, E a → F a) :
    probability E ≤ probability F := by
  classical
  apply mean_le
  intro a
  by_cases he : E a <;> by_cases hf : F a <;> simp_all

lemma probability_union_bound {A I : Type*} [Fintype A] (s : Finset I) (E : I → A → Prop) :
    probability (fun a => ∃ i ∈ s, E i a) ≤ ∑ i ∈ s, probability (E i) := by
  classical
  simp only [probability]
  rw [← mean_sum]
  apply mean_le
  intro a
  split_ifs with h
  · obtain ⟨i, hi, he⟩ := h
    calc
      (1 : ℝ) = (if E i a then (1 : ℝ) else 0) := by simp [he]
      _ ≤ ∑ j ∈ s, (if E j a then (1 : ℝ) else 0) :=
        Finset.single_le_sum (f := fun j => if E j a then (1 : ℝ) else 0) (fun j _ => by split_ifs <;> norm_num) hi
  · exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)

lemma probability_exists {A : Type*} [Fintype A] {E : A → Prop} (h : 0 < probability E) : ∃ a, E a := by
  classical
  by_contra hn
  have hz : probability E = 0 := by simp [probability, mean, not_exists.mp hn]
  linarith

lemma mean_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (f : B → ℝ) :
    mean (fun a => f (e a)) = mean f := by
  simp only [mean, Fintype.card_congr e]
  congr 1
  exact e.sum_comp f

lemma mean_pair {A B : Type*} [Fintype A] [Fintype B] (f : A × B → ℝ) :
    mean f = mean (fun a => mean (fun b => f (a, b))) := by
  simp only [mean, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma probability_eq {A : Type*} [Fintype A] (a : A) :
    probability (· = a) = (Fintype.card A : ℝ)⁻¹ := by
  simp [probability, mean]

lemma probability_eq_of_uniform {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (f : A → B) (hf : ∀ b c, probability (fun a => f a = b) = probability (fun a => f a = c))
    (b : B) : probability (fun a => f a = b) = (Fintype.card B : ℝ)⁻¹ := by
  have hB : Nonempty B := ⟨f (Classical.arbitrary A)⟩
  have hs : (∑ c : B, probability (fun a => f a = c)) = 1 := by
    simp only [probability]
    rw [← mean_sum]
    simpa using mean_const (A := A) (1 : ℝ)
  have he : (∑ c : B, probability (fun a => f a = c)) =
      (Fintype.card B : ℝ) * probability (fun a => f a = b) := by
    conv_lhs => arg 2; ext c; rw [hf c b]
    simp
  rw [he] at hs
  apply mul_left_cancel₀ (show (Fintype.card B : ℝ) ≠ 0 by exact_mod_cast Fintype.card_ne_zero)
  rw [hs, mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)]

lemma perm_eval_probability {A : Type*} [Fintype A] (a b : A) :
    probability (fun σ : Equiv.Perm A => σ a = b) = (Fintype.card A : ℝ)⁻¹ := by
  apply probability_eq_of_uniform
  intro b c
  let τ := Equiv.swap b c
  let e : Equiv.Perm A ≃ Equiv.Perm A := Equiv.mulLeft τ
  have he (σ : Equiv.Perm A) : e σ a = c ↔ σ a = b := by
    change τ (σ a) = c ↔ σ a = b
    rw [← Equiv.swap_apply_left b c]
    exact τ.injective.eq_iff
  have hh := mean_equiv e (fun σ : Equiv.Perm A => if σ a = c then (1 : ℝ) else 0)
  simpa only [he, probability] using hh

lemma permutation_avoidance {A I : Type*} [Fintype A] [Fintype I]
    (f : I → A) (a : A) :
    probability (fun σ : Equiv.Perm A => ∃ i, σ (f i) = a) ≤
      (Fintype.card I : ℝ) / Fintype.card A := by
  calc
    _ ≤ ∑ i : I, probability (fun σ : Equiv.Perm A => σ (f i) = a) := by
      simpa using probability_union_bound Finset.univ (fun (i : I) (σ : Equiv.Perm A) => σ (f i) = a)
    _ = _ := by simp [perm_eval_probability, div_eq_mul_inv]

lemma markov {A : Type*} [Fintype A] {E : A → Prop} {f : A → ℝ} {c : ℝ}
    (hc : 0 < c) (hf : ∀ a, 0 ≤ f a) (hE : ∀ a, E a → c ≤ f a) :
    probability E ≤ mean f / c := by
  apply (le_div_iff₀ hc).mpr
  rw [probability, ← mean_mul_const]
  apply mean_le
  intro a
  by_cases h : E a
  · simpa [h] using hE a h
  · simpa [h] using hf a

lemma independent_lower_tail {I : Type*} [Fintype I] {A : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] (E : ∀ i, A i → Prop)
    (hE : ∀ i, (4 : ℝ) / 5 ≤ probability (E i)) :
    probability (fun a : ∀ i, A i =>
      4 * (Finset.univ.filter (fun i => E i (a i))).card < Fintype.card I) ≤
        (4 / 5 : ℝ) ^ Fintype.card I := by
  let f : ∀ i, A i → ℝ := fun i a => if E i a then 1 else 4
  have hf (i : I) : mean (f i) ≤ 8 / 5 := by
    have hh : mean (f i) + 3 * probability (E i) = 4 := by
      rw [probability]
      have hm := mean_mul_const (fun a => if E i a then (1 : ℝ) else 0) 3
      rw [mul_comm 3, ← hm, ← mean_add]
      calc
        _ = mean (fun _ : A i => (4 : ℝ)) := by
          apply congrArg mean
          funext a
          dsimp [f]
          by_cases h : E i a <;> norm_num [h]
        _ = _ := mean_const 4
    linarith [hE i]
  have hprod (a : ∀ i, A i) :
      ∏ i, f i (a i) = (4 : ℝ) ^ (Finset.univ.filter (fun i => ¬ E i (a i))).card := by
    simp only [f, Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  have hd (a : ∀ i, A i) (ha : 4 * (Finset.univ.filter (fun i => E i (a i))).card < Fintype.card I) :
      (2 : ℝ) ^ Fintype.card I ≤ ∏ i, f i (a i) := by
    have hh := Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun i => E i (a i))
    simp only [Finset.card_univ] at hh
    rw [hprod, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hh := markov (f := fun a : ∀ i, A i => ∏ i, f i (a i)) (by positivity : 0 < (2 : ℝ) ^ Fintype.card I)
    (fun a => Finset.prod_nonneg (fun i _ => by dsimp [f]; split_ifs <;> norm_num)) hd
  calc
    _ ≤ mean (fun a : ∀ i, A i => ∏ i, f i (a i)) / (2 : ℝ) ^ Fintype.card I := hh
    _ = (∏ i, mean (f i)) / (2 : ℝ) ^ Fintype.card I := by rw [mean_prod]
    _ ≤ (8 / 5 : ℝ) ^ Fintype.card I / (2 : ℝ) ^ Fintype.card I := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc
        _ ≤ ∏ i : I, (8 / 5 : ℝ) := Finset.prod_le_prod₀ (fun i _ => mean_nonneg (fun a => by dsimp [f]; split_ifs <;> norm_num)) (fun i _ => hf i)
        _ = _ := by simp only [Finset.prod_const, Finset.card_univ]
    _ = _ := by rw [← div_pow]; norm_num

lemma mean_fiberwise {A B : Type*} [Fintype A] [Fintype B] (f : A → B) (g : B → ℝ) :
    mean (fun a => g (f a)) = ∑ b : B, probability (fun a => f a = b) * g b := by
  have he (a : A) : g (f a) = ∑ b : B, (if f a = b then (1 : ℝ) else 0) * g b := by simp
  simp_rw [probability, ← mean_mul_const]
  rw [← mean_sum]
  apply congrArg mean
  funext a
  exact he a

lemma probability_comp_uniform {A B : Type*} [Fintype A] [Fintype B] (f : A → B)
    (hf : ∀ b, probability (fun a => f a = b) = (Fintype.card B : ℝ)⁻¹) (E : B → Prop) :
    probability (fun a => E (f a)) = probability E := by
  rw [probability, mean_fiberwise f (fun b => if E b then (1 : ℝ) else 0)]
  simp_rw [hf]
  simp only [probability, mean, Finset.mul_sum]

lemma probability_subsingleton {A : Type*} [Fintype A] (E : A → Prop)
    (hE : ∀ a b, E a → E b → a = b) : probability E ≤ (Fintype.card A : ℝ)⁻¹ := by
  by_cases h : ∃ a, E a
  · obtain ⟨a, ha⟩ := h
    exact (probability_mono (fun b hb => hE b a hb ha)).trans_eq (probability_eq a)
  · have hz : probability E = 0 := by simp [probability, mean, not_exists.mp h]
    rw [hz]
    positivity

lemma hom_uniform {A B : Type*} [AddGroup A] [AddGroup B] [Fintype A] [Fintype B]
    (f : A →+ B) (hf : Function.Surjective f) (b : B) :
    probability (fun a => f a = b) = (Fintype.card B : ℝ)⁻¹ := by
  apply probability_eq_of_uniform
  intro b c
  obtain ⟨x, hx⟩ := hf (c - b)
  let e : A ≃ A := Equiv.addLeft x
  have he (a : A) : f (e a) = c ↔ f a = b := by
    change f (x + a) = c ↔ f a = b
    rw [map_add, hx]
    constructor <;> intro h
    · exact add_left_cancel (h.trans (sub_add_cancel c b).symm)
    · rw [h, sub_add_cancel]
  have hh := mean_equiv e (fun a => if f a = c then (1 : ℝ) else 0)
  simpa only [he, probability] using hh

lemma probability_pair {A B : Type*} [Fintype A] [Fintype B] (E : A × B → Prop) :
    probability E = mean (fun a => probability (fun b => E (a, b))) := mean_pair _

lemma independent_lower_tail_subset {I : Type*} [Fintype I] {A : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] (E : ∀ i, A i → Prop)
    (s : Finset I) {n : ℕ} (hn : n ≤ s.card)
    (hE : ∀ i ∈ s, (4 : ℝ) / 5 ≤ probability (E i)) :
    probability (fun a : ∀ i, A i =>
      4 * (Finset.univ.filter (fun i => E i (a i))).card < n) ≤ (4 / 5 : ℝ) ^ n := by
  let f : ∀ i, A i → ℝ := fun i a => if i ∈ s then (if E i a then 1 else 4) else 1
  have hf (i : I) : mean (f i) ≤ if i ∈ s then 8 / 5 else 1 := by
    by_cases hi : i ∈ s
    · simp only [hi, ↓reduceIte]
      have hh : mean (f i) + 3 * probability (E i) = 4 := by
        rw [probability]
        rw [mul_comm 3, ← mean_mul_const, ← mean_add]
        calc
          _ = mean (fun _ : A i => (4 : ℝ)) := by
            apply congrArg mean
            funext a
            dsimp [f]
            by_cases h : E i a <;> norm_num [h, hi]
          _ = _ := mean_const 4
      linarith [hE i hi]
    · simp only [f, hi, ↓reduceIte, mean_const, le_refl]
  have hprod (a : ∀ i, A i) :
      ∏ i, f i (a i) = (4 : ℝ) ^ (s.filter (fun i => ¬ E i (a i))).card := by
    simp only [f, Finset.prod_ite, Finset.prod_const_one, mul_one, one_mul,
      Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const]
  have hd (a : ∀ i, A i) (ha : 4 * (Finset.univ.filter (fun i => E i (a i))).card < n) :
      (2 : ℝ) ^ s.card ≤ ∏ i, f i (a i) := by
    have hh := Finset.card_filter_add_card_filter_not (s := s) (p := fun i => E i (a i))
    have hsub : (s.filter (fun i => E i (a i))).card ≤
        (Finset.univ.filter (fun i => E i (a i))).card := Finset.card_le_card (by intro j hj; simpa using (Finset.mem_filter.mp hj).2)
    rw [hprod, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hh := markov (f := fun a : ∀ i, A i => ∏ i, f i (a i)) (by positivity : 0 < (2 : ℝ) ^ s.card)
    (fun a => Finset.prod_nonneg (fun i _ => by dsimp [f]; split_ifs <;> norm_num)) hd
  calc
    _ ≤ mean (fun a : ∀ i, A i => ∏ i, f i (a i)) / (2 : ℝ) ^ s.card := hh
    _ = (∏ i, mean (f i)) / (2 : ℝ) ^ s.card := by rw [mean_prod]
    _ ≤ (8 / 5 : ℝ) ^ s.card / (2 : ℝ) ^ s.card := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc
        _ ≤ ∏ i : I, (if i ∈ s then (8 / 5 : ℝ) else 1) := Finset.prod_le_prod₀ (fun i _ => mean_nonneg (fun a => by dsimp [f]; split_ifs <;> norm_num)) (fun i _ => hf i)
        _ = _ := by simp [div_pow]
    _ = (4 / 5 : ℝ) ^ s.card := by rw [← div_pow]; norm_num
    _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn

lemma pair_success_lower {A Z : Type*} [Fintype A] [Fintype Z]
    (E : Z → Prop) (F : Z → A → Prop) {p : ℝ}
    (h : ∀ z, E z → p ≤ probability (F z)) :
    p * probability E ≤ probability (fun a : Z × A => F a.1 a.2) := by
  rw [probability_pair, mul_comm p, probability, ← mean_mul_const]
  apply mean_le
  intro z
  by_cases hz : E z
  · simpa [hz] using h z hz
  · simpa [hz] using probability_nonneg (F z)

lemma pair_failure_bound {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (E : A → Prop) (F : A → B → Prop) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ a, ¬ E a → probability (F a) ≤ δ) :
    probability (fun x : A × B => F x.1 x.2) ≤ probability E + δ := by
  rw [probability_pair]
  calc
    _ ≤ mean (fun a => (if E a then (1 : ℝ) else 0) + δ) := mean_le (by
      intro a
      by_cases ha : E a
      · simp only [ha, ↓reduceIte]
        exact (probability_le_one (F a)).trans (by linarith)
      · simpa [ha] using h a ha)
    _ = _ := by rw [mean_add, mean_const]; rfl

end TreeEdit.FiniteProbability

end OAI
