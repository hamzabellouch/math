import OAI.NumberTheory.Ostmann.Quadratic.KernelPairSelection

namespace OAI

/-! # Retaining entire populated kernel fibers -/

namespace Ostmann

open scoped BigOperators Classical

/-- Fibers smaller than the cutoff remove at most the number of kernels times
that cutoff. The estimate concerns actual endpoint populations. -/
theorem small_kernel_fibers_card (S : Finset ℤ) (f : ℤ → ℤ) (Q : ℕ) :
    (S.filter fun x => (S.filter fun y => f y = f x).card < Q).card ≤
      (S.image f).card * Q := by
  let R := S.filter fun x => (S.filter fun y => f y = f x).card < Q
  have hsub : R ⊆ S := Finset.filter_subset _ _
  have hf (u : ℤ) (hu : u ∈ R.image f) :
      (R.filter fun x => f x = u).card ≤ Q := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    exact (Finset.card_le_card (Finset.filter_subset_filter _ hsub)).trans
      (Nat.le_of_lt (Finset.mem_filter.mp hx).2)
  calc
    R.card = ∑ u ∈ R.image f, (R.filter fun x => f x = u).card :=
      Finset.card_eq_sum_card_image f R
    _ ≤ ∑ _u ∈ R.image f, Q := Finset.sum_le_sum hf
    _ = (R.image f).card * Q := by simp
    _ ≤ (S.image f).card * Q := Nat.mul_le_mul_right Q
      (Finset.card_le_card (Finset.image_subset_image hsub))

/-- The retained set is a union of entire original fibers. -/
def populatedKernelPoints (S : Finset ℤ) (f : ℤ → ℤ) (A : ℤ → Prop)
    [DecidablePred A] (Q : ℕ) : Finset ℤ :=
  S.filter fun x => A (f x) ∧ Q ≤ (S.filter fun y => f y = f x).card

theorem populatedKernelPoints_subset (S : Finset ℤ) (f : ℤ → ℤ) (A : ℤ → Prop)
    [DecidablePred A] (Q : ℕ) : populatedKernelPoints S f A Q ⊆ S :=
  Finset.filter_subset _ _

theorem populatedKernelPoints_loss (S : Finset ℤ) (f : ℤ → ℤ) (A : ℤ → Prop)
    [DecidablePred A] (Q : ℕ) :
    S.card ≤ (populatedKernelPoints S f A Q).card +
      (S.filter fun x => ¬ A (f x)).card + (S.image f).card * Q := by
  let B := S.filter fun x => ¬ A (f x)
  let D := S.filter fun x => (S.filter fun y => f y = f x).card < Q
  have hcover : S ⊆ populatedKernelPoints S f A Q ∪ B ∪ D := by
    intro x hx
    by_cases ha : A (f x)
    · by_cases hq : Q ≤ (S.filter fun y => f y = f x).card
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hx, ha, hq⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, Nat.lt_of_not_ge hq⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, ha⟩))
  have hcard := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hcard' := Finset.card_union_le (populatedKernelPoints S f A Q) B
  have hd := small_kernel_fibers_card S f Q
  dsimp only [B, D] at hcard hcard'
  omega

theorem populatedKernelPoints_fiber (S : Finset ℤ) (f : ℤ → ℤ) (A : ℤ → Prop)
    [DecidablePred A] (Q : ℕ) {u : ℤ} (hu : u ∈ (populatedKernelPoints S f A Q).image f) :
    A u ∧ Q ≤ (S.filter fun y => f y = u).card ∧
      ((populatedKernelPoints S f A Q).filter fun y => f y = u) =
        (S.filter fun y => f y = u) := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨hxS, ha, hq⟩ := Finset.mem_filter.mp hx
  refine ⟨ha, hq, ?_⟩
  ext y
  simp only [populatedKernelPoints, Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨hy, heq⟩
    exact ⟨⟨hy, by simpa only [heq] using ha, by simpa only [heq] using hq⟩, heq⟩

/-- A strict population surplus supplies an actual nonexceptional endpoint pair. -/
theorem exists_nonexceptional_endpoint_pair (S T : Finset ℤ) (f g : ℤ → ℤ)
    (E : ℤ → Prop) [DecidablePred E] (M : ℝ)
    (hbad : (((S.product T).filter fun z => E (f z.1 * g z.2)).card : ℝ) ≤ M)
    (hlarge : M < (S.card : ℝ) * T.card) :
    ∃ x ∈ S, ∃ y ∈ T, ¬ E (f x * g y) := by
  by_contra! hn
  have heq : (S.product T).filter (fun z => E (f z.1 * g z.2)) = S.product T := by
    apply Finset.filter_true_of_mem
    intro z hz
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hz
    exact hn z.1 hx z.2 hy
  rw [heq, Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul] at hbad
  exact (not_lt_of_ge hbad) hlarge

/-- A bound on the exceptional endpoint pairs, smaller than the retained
product, gives two complete populated fibers outside the exceptional family. -/
theorem exists_populated_kernel_pair (S T : Finset ℤ) (f g : ℤ → ℤ)
    (A B : ℤ → Prop) [DecidablePred A] [DecidablePred B] (Q : ℕ)
    (E : ℤ → Prop) [DecidablePred E] (M : ℝ)
    (hbad : (((S.product T).filter fun z => E (f z.1 * g z.2)).card : ℝ) ≤ M)
    (hlarge : M < ((populatedKernelPoints S f A Q).card : ℝ) *
      (populatedKernelPoints T g B Q).card) :
    ∃ u ∈ S.image f, ∃ v ∈ T.image g, A u ∧ B v ∧ ¬ E (u * v) ∧
      Q ≤ (S.filter fun x => f x = u).card ∧ Q ≤ (T.filter fun y => g y = v).card := by
  let U := populatedKernelPoints S f A Q
  let V := populatedKernelPoints T g B Q
  have hex : ∃ z ∈ U.product V, ¬ E (f z.1 * g z.2) := by
    by_contra! hn
    have hsub : U.product V ⊆ (S.product T).filter fun z => E (f z.1 * g z.2) := by
      intro z hz
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨populatedKernelPoints_subset S f A Q hx, populatedKernelPoints_subset T g B Q hy⟩,
        hn z hz⟩
    have hc : (U.card : ℝ) * V.card ≤
        (((S.product T).filter fun z => E (f z.1 * g z.2)).card : ℝ) := by
      have hcN : U.card * V.card ≤
          ((S.product T).filter fun z => E (f z.1 * g z.2)).card := by
        simpa only [Finset.product_eq_sprod, Finset.card_product] using Finset.card_le_card hsub
      exact_mod_cast hcN
    exact (not_lt_of_ge (hc.trans hbad)) hlarge
  obtain ⟨⟨x, y⟩, hxy, hout⟩ := hex
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
  have hfx := populatedKernelPoints_fiber S f A Q (Finset.mem_image_of_mem f hx)
  have hgy := populatedKernelPoints_fiber T g B Q (Finset.mem_image_of_mem g hy)
  exact ⟨f x, Finset.mem_image_of_mem f (populatedKernelPoints_subset S f A Q hx),
    g y, Finset.mem_image_of_mem g (populatedKernelPoints_subset T g B Q hy),
    hfx.1, hgy.1, hout, hfx.2.1, hgy.2.1⟩

end Ostmann

end OAI
