import OAI.Combinatorics.MatchingPSD.RepresentationDimension

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace MatchingSmoothing

variable {α : Type u_1} {β : Type u_2} [Fintype α] [DecidableEq β]

noncomputable def histogram (f : α → β) (b : β) : ℕ :=
  Fintype.card {a // f a = b}

lemma sum_histogram [Fintype β] (f : α → β) : ∑ b, histogram f b = Fintype.card α := by
  classical
  simp only [histogram]
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv f)

abbrev Colorings (α : Type u_3) (β : Type u_4) [Fintype α] [DecidableEq β] (s : β → ℕ) :=
  {f : α → β // histogram f = s}

noncomputable instance coloringsFintype [Fintype β] (s : β → ℕ) :
    Fintype (Colorings α β s) := Fintype.ofFinite _

noncomputable def fiberEquivOfHistogram {f g : α → β} (h : histogram f = histogram g)
    (b : β) : {a // f a = b} ≃ {a // g a = b} :=
  Fintype.equivOfCardEq (congrFun h b)

noncomputable def permOfHistogram {f g : α → β} (h : histogram f = histogram g) :
    Equiv.Perm α :=
  (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight (fiberEquivOfHistogram h)).trans (Equiv.sigmaFiberEquiv g))

lemma permOfHistogram_spec {f g : α → β} (h : histogram f = histogram g)
    (a : α) : g (permOfHistogram h a) = f a := by
  exact (fiberEquivOfHistogram h (f a) ⟨a, rfl⟩).property

lemma histogram_comp_perm (f : α → β) (σ : Equiv.Perm α) :
    histogram (f ∘ σ) = histogram f := by
  funext b
  apply Fintype.card_congr
  exact { toFun := fun x => ⟨σ x, x.property⟩
          invFun := fun y => ⟨σ.symm y, by simpa using y.property⟩
          left_inv := by intro x; ext; simp
          right_inv := by intro x; ext; simp }

noncomputable def fiberPermEquiv (f g : α → β) :
    {σ : Equiv.Perm α // f ∘ σ = g} ≃
      (∀ b, {a // g a = b} ≃ {a // f a = b}) where
  toFun σ b :=
    { toFun := fun x => ⟨σ.1 x, (congrFun σ.2 x).trans x.property⟩
      invFun := fun y => ⟨σ.1.symm y, by
        exact (congrFun σ.2 (σ.1.symm y)).symm.trans (by simpa using y.property)⟩
      left_inv := by intro x; ext; simp
      right_inv := by intro x; ext; simp }
  invFun e := ⟨Equiv.ofFiberEquiv e, by
    funext a; exact Equiv.ofFiberEquiv_map e a⟩
  left_inv σ := by apply Subtype.ext; ext a; rfl
  right_inv e := by
    funext b
    apply Equiv.ext
    rintro ⟨a, ha⟩
    subst b
    rfl

lemma card_colorings_mul_factorials [Fintype β] (f : α → β) :
    Fintype.card (Colorings α β (histogram f)) *
      (∏ b, (histogram f b).factorial) = (Fintype.card α).factorial := by
  classical
  let F : Equiv.Perm α → Colorings α β (histogram f) :=
    fun σ => ⟨f ∘ σ, histogram_comp_perm f σ⟩
  have hf (g : Colorings α β (histogram f)) :
      Fintype.card {σ // F σ = g} = ∏ b, (histogram f b).factorial := by
    let e₁ : {σ // F σ = g} ≃ {σ : Equiv.Perm α // f ∘ σ = g.1} :=
      Equiv.subtypeEquivRight (fun σ => Subtype.ext_iff)
    rw [Fintype.card_congr e₁, Fintype.card_congr (fiberPermEquiv f g.1),
      Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro b _
    rw [Fintype.card_equiv (fiberEquivOfHistogram g.2 b)]
    exact congrArg Nat.factorial (congrFun g.2 b)
  have he := Fintype.card_congr (Equiv.sigmaFiberEquiv F)
  rw [Fintype.card_sigma, Fintype.card_perm] at he
  simpa only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul] using he

lemma card_colorings_eq_multinomial [Fintype β] (f : α → β) :
    Fintype.card (Colorings α β (histogram f)) =
      Nat.multinomial Finset.univ (histogram f) := by
  have h := card_colorings_mul_factorials f
  rw [Nat.multinomial, sum_histogram f, ← h, Nat.mul_div_cancel]
  exact Finset.prod_pos (by intro b _; exact Nat.factorial_pos _)

lemma card_perm_color_fiber [DecidableEq α] [Fintype β] (f : α → β) (g : Colorings α β (histogram f)) :
    Fintype.card {σ : Equiv.Perm α // f ∘ σ = g.1} =
      ∏ b, (histogram f b).factorial := by
  classical
  rw [Fintype.card_congr (fiberPermEquiv f g.1), Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro b _
  rw [Fintype.card_equiv (fiberEquivOfHistogram g.2 b)]
  exact congrArg Nat.factorial (congrFun g.2 b)

lemma sum_perm_comp [DecidableEq α] [Fintype β] (f : α → β) (φ : (α → β) → ℝ) :
    ∑ σ : Equiv.Perm α, φ (f ∘ σ) =
      (∏ b, ((histogram f b).factorial : ℝ)) *
        ∑ g : Colorings α β (histogram f), φ g.1 := by
  classical
  let F : Equiv.Perm α → Colorings α β (histogram f) :=
    fun σ => ⟨f ∘ σ, histogram_comp_perm f σ⟩
  rw [← Fintype.sum_fiberwise F (fun σ => φ (f ∘ σ)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  have he : ∀ σ : {σ // F σ = g}, φ (f ∘ σ.1) = φ g.1 := by
    intro σ
    exact congrArg φ (congrArg Subtype.val σ.2)
  simp_rw [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  let e : {σ // F σ = g} ≃ {σ : Equiv.Perm α // f ∘ σ = g.1} :=
    Equiv.subtypeEquivRight (fun σ => Subtype.ext_iff)
  rw [Fintype.card_congr e, card_perm_color_fiber]
  simp

lemma mean_perm_comp [DecidableEq α] [Fintype β] (f : α → β) (φ : (α → β) → ℝ) :
    (Fintype.card (Colorings α β (histogram f)) : ℝ) *
      (∑ σ : Equiv.Perm α, φ (f ∘ σ)) =
    (Fintype.card (Equiv.Perm α) : ℝ) *
      ∑ g : Colorings α β (histogram f), φ g.1 := by
  rw [sum_perm_comp, ← mul_assoc]
  congr 1
  have h := card_colorings_mul_factorials f
  rw [Fintype.card_perm]
  exact_mod_cast h

variable {H : Type u_5} [Fintype H] [DecidableEq H]

def pairConstant (f : H × Bool → β) : Prop := ∀ i, f (i, false) = f (i, true)

instance pairConstantDecidable (f : H × Bool → β) : Decidable (pairConstant f) :=
  inferInstanceAs (Decidable (∀ i, f (i, false) = f (i, true)))

def duplicateColoring (k : H → β) : H × Bool → β := fun v => k v.1

noncomputable def pairConstantEquiv : {f : H × Bool → β // pairConstant f} ≃ (H → β) where
  toFun f i := f.1 (i, false)
  invFun k := ⟨duplicateColoring k, by intro i; rfl⟩
  left_inv f := by
    apply Subtype.ext
    funext ⟨i, b⟩
    cases b
    · rfl
    · exact f.2 i
  right_inv k := rfl

def spliceColoring (k l : H → β) : H × Bool → β :=
  fun v => if v.2 then l v.1 else k v.1

omit [DecidableEq H] in
lemma histogram_spliceColoring (k l : H → β) :
    histogram (spliceColoring k l) = histogram k + histogram l := by
  funext b
  change Fintype.card {v : H × Bool // spliceColoring k l v = b} = _
  let e : {v : H × Bool // spliceColoring k l v = b} ≃
      ({i // k i = b} ⊕ {i // l i = b}) :=
    { toFun := fun v => if h : v.1.2 = true then
        Sum.inr ⟨v.1.1, by simpa [spliceColoring, h] using v.2⟩ else
        Sum.inl ⟨v.1.1, by simpa [spliceColoring, h] using v.2⟩
      invFun := Sum.elim (fun i => ⟨(i.1, false), i.2⟩) (fun i => ⟨(i.1, true), i.2⟩)
      left_inv := by
        rintro ⟨⟨i, b⟩, h⟩
        cases b <;> rfl
      right_inv := by intro v; cases v <;> rfl }
  rw [Fintype.card_congr e, Fintype.card_sum]
  rfl

omit [DecidableEq H] in
lemma histogram_duplicateColoring (k : H → β) :
    histogram (duplicateColoring k) = fun b => 2 * histogram k b := by
  have he : duplicateColoring k = spliceColoring k k := by
    funext ⟨i, b⟩; cases b <;> rfl
  rw [he, histogram_spliceColoring]
  funext b
  simp [two_mul]

omit [DecidableEq H] in
lemma card_colorings_double_ge_square [Fintype β] (s : β → ℕ) :
    Fintype.card (Colorings H β s) ^ 2 ≤
      Fintype.card (Colorings (H × Bool) β (fun b => 2 * s b)) := by
  classical
  let e : Colorings H β s × Colorings H β s →
      Colorings (H × Bool) β (fun b => 2 * s b) := fun kl =>
    ⟨spliceColoring kl.1.1 kl.2.1, by
      rw [histogram_spliceColoring, kl.1.2, kl.2.2]
      funext b; simp [two_mul]⟩
  have hi : Function.Injective e := by
    intro kl mn h
    apply Prod.ext
    · apply Subtype.ext
      funext i
      exact congrFun (congrArg Subtype.val h) (i, false)
    · apply Subtype.ext
      funext i
      exact congrFun (congrArg Subtype.val h) (i, true)
  simpa only [Fintype.card_prod, pow_two] using Fintype.card_le_of_injective e hi

noncomputable def constantColoringsEquiv (s : β → ℕ) :
    {g : Colorings (H × Bool) β (fun b => 2 * s b) // pairConstant g.1} ≃
      Colorings H β s where
  toFun g := ⟨fun i => g.1.1 (i, false), by
    have he : duplicateColoring (fun i => g.1.1 (i, false)) = g.1.1 := by
      funext ⟨i, b⟩
      cases b
      · rfl
      · exact g.2 i
    have hh := congrArg histogram he
    rw [histogram_duplicateColoring, g.1.2] at hh
    funext b
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (congrFun hh b)⟩
  invFun k := ⟨⟨duplicateColoring k.1, by rw [histogram_duplicateColoring, k.2]⟩,
    by intro i; rfl⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    funext ⟨i, b⟩
    cases b
    · rfl
    · exact g.2 i
  right_inv k := by apply Subtype.ext; rfl

lemma sum_indicator_card {X : Type u_6} [Fintype X] (p : X → Prop) [DecidablePred p] :
    (∑ x, if p x then (1 : ℝ) else 0) = (Fintype.card {x // p x} : ℝ) := by
  simp only [Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> norm_num

lemma sum_pairConstant (F : (H × Bool → β) → ℝ) [Fintype β] :
    (∑ f, if pairConstant f then F f else 0) = ∑ k : H → β, F (duplicateColoring k) := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_subtype_eq_sum_filter]
  simp only [Finset.subtype_univ]
  exact Fintype.sum_equiv pairConstantEquiv _ _ (by
    intro f
    congr 1
    exact (congrArg Subtype.val (pairConstantEquiv.symm_apply_apply f)).symm)

lemma pairConstant_perm_sum_bound [Fintype β] (k : H → β) :
    (Fintype.card (Colorings H β (histogram k)) : ℝ) *
      (∑ σ : Equiv.Perm (H × Bool),
        if pairConstant (duplicateColoring k ∘ σ) then (1 : ℝ) else 0) ≤
        Fintype.card (Equiv.Perm (H × Bool)) := by
  classical
  let A := Fintype.card (Colorings H β (histogram k))
  let B := Fintype.card (Colorings (H × Bool) β (fun b => 2 * histogram k b))
  let S := ∑ σ : Equiv.Perm (H × Bool),
    if pairConstant (duplicateColoring k ∘ σ) then (1 : ℝ) else 0
  have hA : (0 : ℝ) < A := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨⟨k, rfl⟩⟩ : 0 < A)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  have hB : (A : ℝ) ^ 2 ≤ B := by exact_mod_cast card_colorings_double_ge_square (histogram k)
  have he := mean_perm_comp (duplicateColoring k)
    (fun g => if pairConstant g then (1 : ℝ) else 0)
  rw [histogram_duplicateColoring] at he
  conv_rhs at he =>
    arg 2
    rw [sum_indicator_card, Fintype.card_congr (constantColoringsEquiv (histogram k))]
  change (B : ℝ) * S = _ at he
  change (A : ℝ) * S ≤ _
  nlinarith [mul_le_mul_of_nonneg_right hB hS]

lemma sum_le_card_mul_of_fiber_bound {X : Type u_7} {J : Type u_8} [Fintype X] [Fintype J]
    [DecidableEq J] (g : X → J) (a : X → ℝ) (P : ℝ) (hP : 0 ≤ P)
    (ha : ∀ x, (Fintype.card {y // g y = g x} : ℝ) * a x ≤ P) :
    ∑ x, a x ≤ (Fintype.card J : ℝ) * P := by
  rw [← Fintype.sum_fiberwise g a]
  calc
    _ ≤ ∑ _j : J, P := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hn : Nonempty {y // g y = j}
      · have hc : (0 : ℝ) < Fintype.card {y // g y = j} := by
          exact_mod_cast Fintype.card_pos_iff.mpr hn
        apply (mul_le_mul_iff_right₀ hc).mp
        rw [Finset.mul_sum]
        calc
          _ ≤ ∑ _y : {y // g y = j}, P := by
            apply Finset.sum_le_sum
            intro y _
            simpa only [y.2] using ha y.1
          _ = _ := by simp
      · have : IsEmpty {y // g y = j} := ⟨fun y => hn ⟨y⟩⟩
        simpa using hP
    _ = _ := by simp

noncomputable def boundedHistogram (f : H → β) : β → Fin (Fintype.card H + 1) :=
  fun b => ⟨histogram f b, Nat.lt_succ_of_le
    (Fintype.card_le_of_injective (fun a : {a // f a = b} => a.1) Subtype.val_injective)⟩

omit [DecidableEq H] in
lemma boundedHistogram_eq_iff (f g : H → β) :
    boundedHistogram f = boundedHistogram g ↔ histogram f = histogram g := by
  constructor
  · intro h; funext b; exact congrArg Fin.val (congrFun h b)
  · intro h; funext b; apply Fin.ext; exact congrFun h b

lemma common_pairColorings_moment [Fintype β] :
    (∑ σ : Equiv.Perm (H × Bool),
      (Fintype.card {f : H × Bool → β // pairConstant f ∧ pairConstant (f ∘ σ)} : ℝ)) ≤
    (Fintype.card (Equiv.Perm (H × Bool)) : ℝ) *
      (Fintype.card H + 1 : ℝ) ^ Fintype.card β := by
  classical
  conv_lhs =>
    arg 2
    ext σ
    rw [← sum_indicator_card]
  rw [Finset.sum_comm]
  have he (f : H × Bool → β) :
      ∑ σ : Equiv.Perm (H × Bool),
        (if pairConstant f ∧ pairConstant (f ∘ σ) then (1 : ℝ) else 0) =
      if pairConstant f then ∑ σ : Equiv.Perm (H × Bool),
        (if pairConstant (f ∘ σ) then (1 : ℝ) else 0) else 0 := by
    split_ifs with hf <;> simp [hf]
  simp_rw [he]
  rw [sum_pairConstant]
  have hb := sum_le_card_mul_of_fiber_bound (boundedHistogram (H := H) (β := β))
    (fun k => ∑ σ : Equiv.Perm (H × Bool),
      if pairConstant (duplicateColoring k ∘ σ) then (1 : ℝ) else 0)
    (Fintype.card (Equiv.Perm (H × Bool)) : ℝ) (by positivity) (by
      intro k
      let e : {l : H → β // boundedHistogram l = boundedHistogram k} ≃
          Colorings H β (histogram k) :=
        Equiv.subtypeEquivRight (fun l => boundedHistogram_eq_iff l k)
      rw [Fintype.card_congr e]
      exact pairConstant_perm_sum_bound k)
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_add,
    Nat.cast_one, mul_comm] using hb

end MatchingSmoothing

end OAI
