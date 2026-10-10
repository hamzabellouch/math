import OAI.Combinatorics.ParityLifts.BaseLabels

namespace OAI

namespace ParityWL

open scoped BigOperators

section BalancedBags

open scoped Classical

variable {t : ℕ} {W : Type} [Fintype W] {F : SimpleGraph W}
variable {a : F →g template t} {b : TemplateVertex t → Bit}

noncomputable def regionSet {n : ℕ} (region : W → Option (Fin n))
    (i : Option (Fin n)) : Finset W := Finset.univ.filter (fun x => region x = i)

lemma sum_regions {n : ℕ} (region : W → Option (Fin n)) (f : W → Bit) :
    ∑ x, f x = (∑ x ∈ regionSet region none, f x) +
      ∑ i, ∑ x ∈ regionSet region (some i), f x := by
  rw [← Finset.sum_fiberwise Finset.univ region f, Fintype.sum_option]
  rfl

/-- The star about a sink bag, with its vertex partition obtained from a tree
decomposition. -/
structure BalancedStar (w : WeightedWitness (template t) F a b) where
  regions : ℕ
  region : W → Option (Fin regions)
  bag : Finset W
  bag_eq : bag = regionSet region none
  size : bag.card ≤ t
  separator : Fin regions → Finset W
  separator_sub : ∀ i, separator i ⊆ bag
  separator_small : ∀ i, (separator i).card < t
  boundary : ∀ i, ∀ x ∈ regionSet region (some i), ∀ y,
    F.Adj x y → y ∉ regionSet region (some i) → y ∈ separator i
  zero_mass : ∀ i (j : Fin t),
    (∀ x ∈ separator i, a x ≠ .inl j) →
      w.mass (regionSet region (some i)) (.inl j) = 0

omit [Fintype W] in
lemma main_card_le (B : Finset W) (hp : ∀ i : Fin t, ∃ x ∈ B, a x = .inl i) :
    t ≤ B.card := by
  choose x hx ht using hp
  have hinj : Function.Injective x := by
    intro i j he
    have hh : Sum.inl i = (Sum.inl j : TemplateVertex t) :=
      (ht i).symm.trans ((congrArg a he).trans (ht j))
    exact Sum.inl.inj hh
  have hsub : Finset.univ.image x ⊆ B := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, _, rfl⟩
    exact hx i
  have hc := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hc

omit [Fintype W] in
lemma missing_main (B : Finset W) (hB : B.card < t) :
    ∃ i : Fin t, ∀ x ∈ B, a x ≠ .inl i := by
  by_contra h
  push Not at h
  have h' := main_card_le (a := a) B h
  omega

lemma BalancedStar.partition_mass (w : WeightedWitness (template t) F a b)
    (s : BalancedStar w) (u : TemplateVertex t) :
    w.mass Finset.univ u = w.mass s.bag u +
      ∑ i, w.mass (regionSet s.region (some i)) u := by
  rw [s.bag_eq]
  exact sum_regions s.region (fun x => @ite Bit (a x = u)
    (Classical.propDecidable _) (w.vertex x) 0)

lemma BalancedStar.main_present (w : WeightedWitness (template t) F a (starParity t))
    (s : BalancedStar w) (ht : 0 < t) (i : Fin t) :
    ∃ x ∈ s.bag, a x = .inl i := by
  by_contra h
  push Not at h
  have hb := w.mass_eq_zero s.bag (.inl i) h
  have hz : ∀ j, w.mass (regionSet s.region (some j)) (.inl i) = 0 := by
    intro j
    exact s.zero_mass j i (fun x hx => h x (s.separator_sub j hx))
  have hm := s.partition_mass w (.inl i)
  rw [w.main_mass ht i, hb] at hm
  simp only [hz, Finset.sum_const_zero, add_zero] at hm
  exact one_ne_zero hm

lemma BalancedStar.representatives (w : WeightedWitness (template t) F a (starParity t))
    (s : BalancedStar w) (ht : 0 < t) :
    ∃ x : Fin t → W, (∀ i, a (x i) = .inl i) ∧
      s.bag = Finset.univ.image x := by
  choose x hx ha using s.main_present w ht
  have hinj : Function.Injective x := by
    intro i j he
    have hh : Sum.inl i = (Sum.inl j : TemplateVertex t) :=
      (ha i).symm.trans ((congrArg a he).trans (ha j))
    exact Sum.inl.inj hh
  refine ⟨x, ha, ?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact hx i
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    exact s.size

end BalancedBags

section MismatchPredicates

open scoped Classical

variable {t : ℕ} (C : ChoiceSystem t) {W : Type} {F : SimpleGraph W}
variable (φ : F →g baseGraph C)

noncomputable def leftTest (p : MainPair t) (α : C.Label p) (x : W) : Bit :=
  if leftLabelAt C p (φ x) = some α then 0 else 1

noncomputable def rightTest (p : MainPair t) (α : C.Label p) (x : W) : Bit :=
  if rightLabelAt C p (φ x) = some α then 1 else 0

noncomputable def helperTest (h : Helper t) (α : C.Label h.1.1) (x : W) : Bit :=
  if helperLabelAt C h (φ x) = some α then 0 else 1

lemma test_main_compatible (p : MainPair t) (α : C.Label p) {x y : W}
    (hxy : F.Adj x y) (hx : baseType (φ x) = .inl p.1.1)
    (hy : baseType (φ y) = .inl p.1.2) :
    leftTest C φ p α x + rightTest C φ p α y = 1 := by
  have he := base_main_labels C p (φ.map_adj hxy) hx hy
  unfold leftTest rightTest
  rw [he]
  split_ifs <;> simp

lemma test_helper_left_compatible (h : Helper t) (α : C.Label h.1.1) {x y : W}
    (hxy : F.Adj x y) (hx : baseType (φ x) = .inl h.1.1.1.1)
    (hy : baseType (φ y) = .inr h) :
    leftTest C φ h.1.1 α x = helperTest C φ h α y := by
  have he := base_helper_left_labels C h (φ.map_adj hxy.symm) hy hx
  unfold leftTest helperTest
  rw [he]

lemma test_helper_right_compatible (h : Helper t) (α : C.Label h.1.1) {x y : W}
    (hxy : F.Adj x y) (hx : baseType (φ x) = .inl h.1.1.1.2)
    (hy : baseType (φ y) = .inr h) :
    rightTest C φ h.1.1 α x = 1 + helperTest C φ h α y := by
  have he := base_helper_right_labels C h (φ.map_adj hxy.symm) hy hx
  unfold rightTest helperTest
  rw [he]
  split_ifs <;> simp [CharTwo.add_self_eq_zero]

lemma bit_complement_left {x y : Bit} (h : x + y = 1) : x = 1 + y := by
  have he := congrArg (· + y) h
  simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero] using he

lemma bit_complement_right {x y : Bit} (h : x + y = 1) : y = 1 + x :=
  bit_complement_left (by rwa [add_comm])

end MismatchPredicates

end ParityWL

end OAI
