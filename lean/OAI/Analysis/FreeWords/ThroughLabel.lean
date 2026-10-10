import Mathlib

namespace OAI

noncomputable section

namespace KKThroughLabel

open scoped BigOperators

noncomputable section

def beta (C : ℕ → ℝ) (d r : ℕ) (W : Sym (Fin d) r) : ℝ :=
  (if (W : Multiset (Fin d)).Nodup then 7 * Real.sqrt ((r - 1).factorial : ℝ)
   else C r) * (d : ℝ) ^ (-((r - 1 : ℕ) : ℝ) / 2)

def throughSum (C : ℕ → ℝ) (d r : ℕ) (a : Fin d) : ℝ :=
  ∑ W ∈ (Finset.univ : Finset (Sym (Fin d) r)).filter (fun W => a ∈ W),
    beta C d r W ^ 2

section Counting

variable {α : Type*} [Fintype α] [DecidableEq α]

def wordsThrough (r : ℕ) (a : α) : Finset (Sym α r) :=
  Finset.univ.filter (fun W => a ∈ W)

def distinctThrough (r : ℕ) (a : α) : Finset (Sym α r) :=
  (wordsThrough r a).filter (fun W => (W : Multiset α).Nodup)

def repeatedThrough (r : ℕ) (a : α) : Finset (Sym α r) :=
  (wordsThrough r a).filter (fun W => ¬(W : Multiset α).Nodup)

@[simp] theorem mem_wordsThrough {r : ℕ} {a : α} {W : Sym α r} :
    W ∈ wordsThrough r a ↔ a ∈ W := by simp [wordsThrough]

@[simp] theorem mem_distinctThrough {r : ℕ} {a : α} {W : Sym α r} :
    W ∈ distinctThrough r a ↔ a ∈ W ∧ (W : Multiset α).Nodup := by
  simp [distinctThrough]

@[simp] theorem mem_repeatedThrough {r : ℕ} {a : α} {W : Sym α r} :
    W ∈ repeatedThrough r a ↔ a ∈ W ∧ ¬(W : Multiset α).Nodup := by
  simp [repeatedThrough]

theorem card_sym_le_pow (r : ℕ) : Fintype.card (Sym α r) ≤ Fintype.card α ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hsurj : Function.Surjective
        (fun p : α × Sym α r => Sym.cons p.1 p.2) := by
      intro W
      obtain ⟨a, ha⟩ := W.exists_mem
      exact ⟨(a, W.erase a ha), Sym.cons_erase ha⟩
    calc
      Fintype.card (Sym α (r + 1)) ≤ Fintype.card (α × Sym α r) :=
        Fintype.card_le_of_surjective _ hsurj
      _ = Fintype.card α * Fintype.card (Sym α r) := Fintype.card_prod _ _
      _ ≤ Fintype.card α * Fintype.card α ^ r := Nat.mul_le_mul_left _ ih
      _ = Fintype.card α ^ (r + 1) := by rw [pow_succ, mul_comm]

theorem card_distinctThrough_le_choose (r : ℕ) (a : α) :
    (distinctThrough (r + 1) a).card ≤ (Fintype.card α).choose r := by
  let f : Sym α (r + 1) → Finset α := fun W => (W : Multiset α).erase a |>.toFinset
  have hcard (W : Sym α (r + 1)) (hW : W ∈ distinctThrough (r + 1) a) :
      (f W).card = r := by
    obtain ⟨ha, hn⟩ := mem_distinctThrough.mp hW
    change a ∈ (W : Multiset α) at ha
    change ((W : Multiset α).erase a).toFinset.card = r
    rw [Multiset.toFinset_card_of_nodup (hn.erase a), Multiset.card_erase_of_mem ha,
      Sym.card_coe, Nat.pred_succ]
  have hinj : Set.InjOn f (distinctThrough (r + 1) a : Set (Sym α (r + 1))) := by
    intro W hW V hV h
    obtain ⟨haW, hnW⟩ := mem_distinctThrough.mp hW
    obtain ⟨haV, hnV⟩ := mem_distinctThrough.mp hV
    change a ∈ (W : Multiset α) at haW
    change a ∈ (V : Multiset α) at haV
    have he : (W : Multiset α).erase a = (V : Multiset α).erase a :=
      (hnW.erase a).toFinset_inj (hnV.erase a) h
    apply Sym.ext
    simpa only [Multiset.cons_erase haW, Multiset.cons_erase haV] using
      congrArg (Multiset.cons a) he
  calc
    (distinctThrough (r + 1) a).card ≤ (Finset.univ.powersetCard r : Finset (Finset α)).card := by
      apply Finset.card_le_card_of_injOn f _ hinj
      intro W hW
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard W hW⟩
    _ = (Fintype.card α).choose r := by simp

omit [Fintype α] [DecidableEq α] in
theorem exists_double_cons {r : ℕ} (W : Sym α (r + 2))
    (hW : ¬ (W : Multiset α).Nodup) :
    ∃ (b : α) (V : Sym α r), W = Sym.cons b (Sym.cons b V) := by
  rw [Multiset.nodup_iff_ne_cons_cons] at hW
  push Not at hW
  obtain ⟨b, V, hV⟩ := hW
  have hcard : V.card = r := by
    have := congrArg Multiset.card hV
    simp only [Multiset.card_cons, Sym.card_coe] at this
    omega
  exact ⟨b, ⟨V, hcard⟩, Sym.ext hV⟩

theorem repeatedThrough_subset (r : ℕ) (a : α) :
    repeatedThrough (r + 3) a ⊆
      (Finset.univ : Finset (Sym α (r + 1))).image (fun V => Sym.cons a (Sym.cons a V)) ∪
      (Finset.univ : Finset α).biUnion (fun b =>
        (Finset.univ : Finset (Sym α r)).image (fun V => Sym.cons a (Sym.cons b (Sym.cons b V)))) := by
  intro W hW
  obtain ⟨ha, hn⟩ := mem_repeatedThrough.mp hW
  obtain ⟨V, rfl⟩ := Sym.exists_cons_of_mem ha
  by_cases hav : a ∈ V
  · obtain ⟨Z, rfl⟩ := Sym.exists_cons_of_mem hav
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨Z, Finset.mem_univ _, rfl⟩)
  · change a ∉ (V : Multiset α) at hav
    have hV : ¬ (V : Multiset α).Nodup := by
      simpa only [Sym.coe_cons, Multiset.nodup_cons, hav, not_false_eq_true, true_and] using hn
    obtain ⟨b, Z, rfl⟩ := exists_double_cons V hV
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨b, Finset.mem_univ _, Finset.mem_image.mpr ⟨Z, Finset.mem_univ _, rfl⟩⟩)

theorem card_repeatedThrough_le (r : ℕ) (a : α) :
    (repeatedThrough (r + 3) a).card ≤ 2 * Fintype.card α ^ (r + 1) := by
  calc
    (repeatedThrough (r + 3) a).card ≤
        ((Finset.univ : Finset (Sym α (r + 1))).image
          (fun V => Sym.cons a (Sym.cons a V)) ∪
         (Finset.univ : Finset α).biUnion (fun b =>
          (Finset.univ : Finset (Sym α r)).image
           (fun V => Sym.cons a (Sym.cons b (Sym.cons b V))))).card :=
      Finset.card_le_card (repeatedThrough_subset r a)
    _ ≤ Fintype.card (Sym α (r + 1)) +
        Fintype.card α * Fintype.card (Sym α r) := by
      refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
      · simpa using Finset.card_image_le
          (s := (Finset.univ : Finset (Sym α (r + 1))))
          (f := fun V => Sym.cons a (Sym.cons a V))
      · refine (Finset.card_biUnion_le).trans ?_
        calc
          _ ≤ ∑ _b : α, Fintype.card (Sym α r) := by
            apply Finset.sum_le_sum
            intro b hb
            simpa using Finset.card_image_le
              (s := (Finset.univ : Finset (Sym α r)))
              (f := fun V => Sym.cons a (Sym.cons b (Sym.cons b V)))
          _ = _ := by simp
    _ ≤ Fintype.card α ^ (r + 1) + Fintype.card α * Fintype.card α ^ r :=
      Nat.add_le_add (card_sym_le_pow _) (Nat.mul_le_mul_left _ (card_sym_le_pow _))
    _ = 2 * Fintype.card α ^ (r + 1) := by rw [pow_succ]; ring

@[simp] theorem repeatedThrough_one (a : α) : repeatedThrough 1 a = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro W hW
  obtain ⟨ha, hn⟩ := mem_repeatedThrough.mp hW
  obtain ⟨V, rfl⟩ := Sym.exists_cons_of_mem ha
  have hV : V = Sym.nil := Subsingleton.elim _ _
  subst V
  exact hn (by simp [Sym.coe_cons])

@[simp] theorem repeatedThrough_two (a : α) :
    repeatedThrough 2 a = {Sym.cons a (Sym.cons a Sym.nil)} := by
  ext W
  constructor
  · intro hW
    obtain ⟨ha, hn⟩ := mem_repeatedThrough.mp hW
    obtain ⟨b, V, rfl⟩ := exists_double_cons W hn
    have hV : V = Sym.nil := Subsingleton.elim _ _
    subst V
    have hab : a = b := by simpa using ha
    subst b
    simp
  · intro hW
    obtain rfl := Finset.mem_singleton.mp hW
    simp [Sym.coe_cons]

theorem card_repeatedThrough_le_all (r : ℕ) (a : α) :
    (repeatedThrough (r + 2) a).card ≤ 2 * Fintype.card α ^ r := by
  cases r with
  | zero => simp
  | succ r => exact card_repeatedThrough_le r a

end Counting

theorem neg_half_rpow_sq (d n : ℕ) :
    ((d : ℝ) ^ (-(n : ℝ) / 2)) ^ 2 = 1 / (d : ℝ) ^ n := by
  calc
    ((d : ℝ) ^ (-(n : ℝ) / 2)) ^ 2 =
        (d : ℝ) ^ ((-(n : ℝ) / 2) * (2 : ℝ)) := by
      rw [Real.rpow_mul (Nat.cast_nonneg d), Real.rpow_two]
    _ = (d : ℝ) ^ (-(n : ℝ)) := by congr 1; ring
    _ = 1 / (d : ℝ) ^ n := by
      rw [Real.rpow_neg (Nat.cast_nonneg d), Real.rpow_natCast, one_div]

theorem beta_sq (C : ℕ → ℝ) (d n : ℕ) (W : Sym (Fin d) (n + 1)) :
    beta C d (n + 1) W ^ 2 =
      if (W : Multiset (Fin d)).Nodup then
        49 * (n.factorial : ℝ) / (d : ℝ) ^ n
      else C (n + 1) ^ 2 / (d : ℝ) ^ n := by
  simp only [beta, Nat.add_sub_cancel, mul_pow, neg_half_rpow_sq]
  split_ifs with hW
  · rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    ring
  · ring

theorem throughSum_eq (C : ℕ → ℝ) (d n : ℕ) (a : Fin d) :
    throughSum C d (n + 1) a =
      ((distinctThrough (n + 1) a).card : ℝ) *
        (49 * (n.factorial : ℝ) / (d : ℝ) ^ n) +
      ((repeatedThrough (n + 1) a).card : ℝ) *
        (C (n + 1) ^ 2 / (d : ℝ) ^ n) := by
  change (∑ W ∈ wordsThrough (n + 1) a, beta C d (n + 1) W ^ 2) = _
  rw [← Finset.sum_filter_add_sum_filter_not (wordsThrough (n + 1) a)
    (fun W => (W : Multiset (Fin d)).Nodup) (fun W => beta C d (n + 1) W ^ 2)]
  have h₁ : (∑ W ∈ distinctThrough (n + 1) a, beta C d (n + 1) W ^ 2) =
      ((distinctThrough (n + 1) a).card : ℝ) *
        (49 * (n.factorial : ℝ) / (d : ℝ) ^ n) := by
    calc
      _ = ∑ _W ∈ distinctThrough (n + 1) a,
          (49 * (n.factorial : ℝ) / (d : ℝ) ^ n) := by
        apply Finset.sum_congr rfl
        intro W hW
        rw [beta_sq, ite_eq_left (mem_distinctThrough.mp hW).2]
      _ = _ := by simp
  have h₂ : (∑ W ∈ repeatedThrough (n + 1) a, beta C d (n + 1) W ^ 2) =
      ((repeatedThrough (n + 1) a).card : ℝ) *
        (C (n + 1) ^ 2 / (d : ℝ) ^ n) := by
    calc
      _ = ∑ _W ∈ repeatedThrough (n + 1) a, C (n + 1) ^ 2 / (d : ℝ) ^ n := by
        apply Finset.sum_congr rfl
        intro W hW
        rw [beta_sq, ite_eq_right (mem_repeatedThrough.mp hW).2]
      _ = _ := by simp
  exact congrArg₂ (· + ·) h₁ h₂

theorem distinct_contribution_le (d n : ℕ) (hd : 0 < d) (a : Fin d) :
    ((distinctThrough (n + 1) a).card : ℝ) *
      (49 * (n.factorial : ℝ) / (d : ℝ) ^ n) ≤ 49 := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hf : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr n.factorial_pos
  have hcard : ((distinctThrough (n + 1) a).card : ℝ) ≤ (d.choose n : ℝ) := by
    exact_mod_cast (show (distinctThrough (n + 1) a).card ≤ d.choose n by
      simpa only [Fintype.card_fin] using card_distinctThrough_le_choose n a)
  calc
    _ ≤ (d.choose n : ℝ) * (49 * (n.factorial : ℝ) / (d : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ ((d : ℝ) ^ n / (n.factorial : ℝ)) *
        (49 * (n.factorial : ℝ) / (d : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div n d) (by positivity)
    _ = 49 := by field_simp

theorem repeated_contribution_le (C : ℕ → ℝ) (d n : ℕ) (hd : 0 < d) (a : Fin d) :
    ((repeatedThrough (n + 2) a).card : ℝ) *
      (C (n + 2) ^ 2 / (d : ℝ) ^ (n + 1)) ≤ 2 * C (n + 2) ^ 2 / d := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hcard : ((repeatedThrough (n + 2) a).card : ℝ) ≤ 2 * (d : ℝ) ^ n := by
    exact_mod_cast (show (repeatedThrough (n + 2) a).card ≤ 2 * d ^ n by
      simpa only [Fintype.card_fin] using card_repeatedThrough_le_all n a)
  calc
    _ ≤ (2 * (d : ℝ) ^ n) * (C (n + 2) ^ 2 / (d : ℝ) ^ (n + 1)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 2 * C (n + 2) ^ 2 / d := by rw [pow_succ]; field_simp; ring

theorem throughSum_le (C : ℕ → ℝ) (d r : ℕ) (hd : 0 < d)
    (hr : 1 ≤ r) (a : Fin d) : throughSum C d r a ≤ 49 + 2 * C r ^ 2 / d := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [Nat.add_comm 1 r]
  cases r with
  | zero =>
    change throughSum C d 1 a ≤ 49 + 2 * C 1 ^ 2 / d
    rw [throughSum_eq C d 0 a]
    change ((distinctThrough 1 a).card : ℝ) *
        (49 * (Nat.factorial 0 : ℝ) / (d : ℝ) ^ 0) +
        ((repeatedThrough 1 a).card : ℝ) * (C 1 ^ 2 / (d : ℝ) ^ 0) ≤ _
    rw [repeatedThrough_one, Finset.card_empty, Nat.cast_zero, zero_mul, add_zero]
    exact (distinct_contribution_le d 0 hd a).trans (le_add_of_nonneg_right (by positivity))
  | succ r =>
    rw [throughSum_eq]
    exact add_le_add (distinct_contribution_le d (r + 1) hd a)
      (repeated_contribution_le C d r hd a)

theorem through_label (C : ℕ → ℝ) (D : ℕ → ℕ) (N : ℕ) (_ : 1 ≤ N) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧
      (∀ r : ℕ, 1 ≤ r → r ≤ N → D r ≤ d₀) ∧
      ∀ d : ℕ, d₀ ≤ d → ∀ r : ℕ, 1 ≤ r → r ≤ N →
        ∀ a : Fin d, throughSum C d r a ≤ 64 := by
  let b : ℕ → ℕ := fun r => max (D r) ⌈2 * C r ^ 2 / 15⌉₊
  let d₀ : ℕ := max 1 ((Finset.Icc 1 N).sup b)
  have hb (r : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N) : b r ≤ d₀ :=
    (Finset.le_sup (f := b) (Finset.mem_Icc.mpr ⟨hr, hrN⟩)).trans (le_max_right _ _)
  refine ⟨d₀, le_max_left _ _, ?_, ?_⟩
  · intro r hr hrN
    exact (le_max_left _ _).trans (hb r hr hrN)
  · intro d hd r hr hrN a
    have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hd)
    have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hdpos
    have hceil : ⌈2 * C r ^ 2 / 15⌉₊ ≤ d :=
      (le_max_right _ _).trans ((hb r hr hrN).trans hd)
    have hsize : 2 * C r ^ 2 / 15 ≤ (d : ℝ) := Nat.ceil_le.mp hceil
    have herr : 2 * C r ^ 2 / d ≤ 15 := by
      apply (div_le_iff₀ hdR).mpr
      linarith
    exact (throughSum_le C d r hdpos hr a).trans (by linarith)

end

end KKThroughLabel
end

end OAI
