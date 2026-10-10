import OAI.Combinatorics.ParityLifts.BalancedBags

namespace OAI

namespace ParityWL

open scoped BigOperators

section ChoiceFromBalancedStar

open scoped Classical

variable {t : ℕ} (C : ChoiceSystem t) {W : Type} [Fintype W]
variable {F : SimpleGraph W} (φ : F →g baseGraph C)
variable (w : WeightedWitness (template t) F ((baseProjection C).comp φ) (starParity t))

lemma mismatch_side_zero (p : MainPair t) (α : C.Label p) (Y S : Finset W)
    (hb : ∀ x ∈ Y, ∀ y, F.Adj x y → y ∉ Y → y ∈ S)
    (hn : ∀ x ∈ S, ∀ h : Helper t, baseType (φ x) ≠ .inr h)
    (hp : ∀ x ∈ S, baseType (φ x) = .inl p.1.1 → leftTest C φ p α x = 0)
    (hq : ∀ x ∈ S, baseType (φ x) = .inl p.1.2 → rightTest C φ p α x = 0)
    (ℓ : Fin t) (hℓ : ∀ x ∈ S, baseType (φ x) ≠ .inl ℓ)
    (hm : w.mass Y (.inl ℓ) = 0) :
    w.testMass Y (.inl p.1.1) (leftTest C φ p α) +
      w.testMass Y (.inl p.1.2) (rightTest C φ p α) = 0 := by
  by_cases hi : ℓ = p.1.1
  · subst ℓ
    have ht := w.testMass_transfer
      (u := .inl p.1.2) (v := .inl p.1.1) (Ne.symm (ne_of_lt p.2))
      Y S (rightTest C φ p α) (fun x => 1 + leftTest C φ p α x) hb hℓ hq (by
        intro x y he hx hy
        exact bit_complement_right (test_main_compatible C φ p α he.symm hy hx))
    rw [ht, w.testMass_complement, hm]
  · by_cases hj : ℓ = p.1.2
    · subst ℓ
      have ht := w.testMass_transfer
        (u := .inl p.1.1) (v := .inl p.1.2) (ne_of_lt p.2)
        Y S (leftTest C φ p α) (fun x => 1 + rightTest C φ p α x) hb hℓ hp (by
          intro x y he hx hy
          exact bit_complement_left (test_main_compatible C φ p α he hx hy))
      rw [ht, add_comm, w.testMass_complement, hm]
    · let h : Helper t := ⟨(p, ℓ), hi, hj⟩
      have hh : ∀ x ∈ S, ((baseProjection C).comp φ) x ≠ .inr h :=
        fun x hx => hn x hx h
      have ht₀ := w.testMass_transfer
        (u := .inl p.1.1) (v := .inr h) (Or.inl rfl)
        Y S (leftTest C φ p α) (helperTest C φ h α) hb hh hp (by
          intro x y he hx hy
          exact test_helper_left_compatible C φ h α he hx hy)
      have ht₁ := w.testMass_transfer
        (u := .inl p.1.2) (v := .inr h) (Or.inr (Or.inl rfl))
        Y S (rightTest C φ p α) (fun x => 1 + helperTest C φ h α x) hb hh hq (by
          intro x y he hx hy
          exact test_helper_right_compatible C φ h α he hx hy)
      have hmass := w.mass_separator
        (u := .inr h) (v := .inl ℓ) (Or.inr (Or.inr rfl)) Y S hb hh hℓ
      rw [ht₀, ht₁, w.testMass_complement, hmass, hm]

lemma BalancedStar.partition_testMass
    (s : BalancedStar w) (u : TemplateVertex t) (p : W → Bit) :
    w.testMass Finset.univ u p = w.testMass s.bag u p +
      ∑ i, w.testMass (regionSet s.region (some i)) u p := by
  rw [s.bag_eq]
  exact sum_regions s.region (fun x => @ite Bit (((baseProjection C).comp φ) x = u)
    (Classical.propDecidable _) (w.vertex x * p x) 0)

/-- The helper boundary argument from a finite partition around a balanced bag. -/
theorem choice_of_balancedStar (s : BalancedStar w) (ht : 0 < t) : C.Successful := by
  obtain ⟨xs, htype, hbag⟩ := s.representatives w ht
  have hd' : ∀ i : Fin t, ∃ d : C.Domain i, φ (xs i) = .inl ⟨i, d⟩ := by
    intro i
    exact (baseType_inl_iff C (φ (xs i)) i).mp (htype i)
  choose d hd using hd'
  refine ⟨d, ?_⟩
  intro p
  by_contra hneq
  let α := C.leftLabel p (d p.1.1)
  have hp : ∀ x ∈ s.bag, baseType (φ x) = .inl p.1.1 →
      leftTest C φ p α x = 0 := by
    intro x hx hx'
    rw [hbag] at hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    have hi : i = p.1.1 := Sum.inl.inj ((htype i).symm.trans hx')
    subst i
    simp [leftTest, hd, α]
  have hq : ∀ x ∈ s.bag, baseType (φ x) = .inl p.1.2 →
      rightTest C φ p α x = 0 := by
    intro x hx hx'
    rw [hbag] at hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    have hi : i = p.1.2 := Sum.inl.inj ((htype i).symm.trans hx')
    subst i
    simp [rightTest, hd, α, Ne.symm hneq]
  have hn : ∀ x ∈ s.bag, ∀ h : Helper t, baseType (φ x) ≠ .inr h := by
    intro x hx h he
    rw [hbag] at hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    have hh := (htype i).symm.trans he
    cases hh
  have ho : ∀ j, w.testMass (regionSet s.region (some j)) (.inl p.1.1)
      (leftTest C φ p α) + w.testMass (regionSet s.region (some j)) (.inl p.1.2)
      (rightTest C φ p α) = 0 := by
    intro j
    obtain ⟨ℓ, hℓ⟩ := missing_main (a := (baseProjection C).comp φ)
      (s.separator j) (s.separator_small j)
    exact mismatch_side_zero C φ w p α _ _ (s.boundary j)
      (fun x hx => hn x (s.separator_sub j hx))
      (fun x hx => hp x (s.separator_sub j hx))
      (fun x hx => hq x (s.separator_sub j hx)) ℓ hℓ (s.zero_mass j ℓ hℓ)
  have hglobal := w.global_mismatch (u := .inl p.1.1) (v := .inl p.1.2)
    (ne_of_lt p.2) (leftTest C φ p α) (rightTest C φ p α)
    (fun _ _ he hx hy => test_main_compatible C φ p α he hx hy)
  rw [w.main_mass ht p.1.1, s.partition_testMass C φ w, s.partition_testMass C φ w,
    w.testMass_zero s.bag (.inl p.1.1) _ hp,
    w.testMass_zero s.bag (.inl p.1.2) _ hq, zero_add, zero_add,
    ← Finset.sum_add_distrib] at hglobal
  simp only [ho, Finset.sum_const_zero] at hglobal
  exact zero_ne_one hglobal

end ChoiceFromBalancedStar

end ParityWL

end OAI
