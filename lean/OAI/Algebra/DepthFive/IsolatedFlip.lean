import Mathlib

namespace OAI

/-!
Canonical removal of isolated positions in an independent set.

The value `true` denotes the D type from the manuscript.  The set `S`
contains the positions allowed to flip (interior V layers), and `R a b`
means that `b` is a neighbor of `a`.  Independence is the only property
of the path graph needed for the fiber calculation.
-/

noncomputable section

open scoped BigOperators

namespace Problem335.IsolatedFlip

variable {α : Type*} [Fintype α] [DecidableEq α]

def eligible (S : Finset α) (R : α → α → Prop) (w : α → Bool) : Finset α := by
  classical
  exact S.filter (fun a => ∀ b, R a b → w b = true)

def flip (S : Finset α) (R : α → α → Prop) (w : α → Bool) (a : α) : Bool := by
  classical
  exact if a ∈ eligible S R w then true else w a

def unset (w : α → Bool) (T : Finset α) (a : α) : Bool :=
  if a ∈ T then false else w a

def removed (S : Finset α) (R : α → α → Prop) (w : α → Bool) : Finset α := by
  classical
  exact (eligible S R w).filter (fun a => w a = false)

@[simp] theorem mem_eligible {α : Type u_1} [Fintype α] [DecidableEq α]
    {S : Finset α} {R : α → α → Prop}
    {w : α → Bool} {a : α} :
    a ∈ eligible S R w ↔ a ∈ S ∧ ∀ b, R a b → w b = true := by
  classical
  simp [eligible]

theorem eligible_subset (S : Finset α) (R : α → α → Prop) (w : α → Bool) :
    eligible S R w ⊆ S := by
  intro a ha
  exact (mem_eligible.mp ha).1

theorem flip_eq_of_not_mem {S : Finset α} {R : α → α → Prop}
    {w : α → Bool} {a : α} (ha : a ∉ S) : flip S R w a = w a := by
  classical
  have h : a ∉ eligible S R w := fun h => ha (eligible_subset S R w h)
  simp [flip, h]

theorem eligible_congr {S : Finset α} {R : α → α → Prop}
    (hS : ∀ a ∈ S, ∀ b, R a b → b ∉ S)
    {w z : α → Bool} (h : ∀ a, a ∉ S → w a = z a) :
    eligible S R w = eligible S R z := by
  ext a
  simp only [mem_eligible]
  constructor
  · rintro ⟨ha, hw⟩
    refine ⟨ha, ?_⟩
    intro b hab
    rw [← h b (hS a ha b hab)]
    exact hw b hab
  · rintro ⟨ha, hz⟩
    refine ⟨ha, ?_⟩
    intro b hab
    rw [h b (hS a ha b hab)]
    exact hz b hab

theorem eligible_flip {S : Finset α} {R : α → α → Prop}
    (hS : ∀ a ∈ S, ∀ b, R a b → b ∉ S) (w : α → Bool) :
    eligible S R (flip S R w) = eligible S R w := by
  apply eligible_congr hS
  intro a ha
  exact flip_eq_of_not_mem ha

theorem flip_idempotent {S : Finset α} {R : α → α → Prop}
    (hS : ∀ a ∈ S, ∀ b, R a b → b ∉ S) (w : α → Bool) :
    flip S R (flip S R w) = flip S R w := by
  classical
  funext a
  simp only [flip, eligible_flip hS]
  split_ifs <;> rfl

theorem eligible_unset {S : Finset α} {R : α → α → Prop}
    (hS : ∀ a ∈ S, ∀ b, R a b → b ∉ S)
    (w : α → Bool) {T : Finset α} (hT : T ⊆ S) :
    eligible S R (unset w T) = eligible S R w := by
  apply eligible_congr hS
  intro a ha
  have hn : a ∉ T := fun ht => ha (hT ht)
  simp [unset, hn]

theorem flip_unset {S : Finset α} {R : α → α → Prop}
    (hS : ∀ a ∈ S, ∀ b, R a b → b ∉ S)
    {w : α → Bool} (hw : flip S R w = w)
    {T : Finset α} (hT : T ⊆ eligible S R w) :
    flip S R (unset w T) = w := by
  classical
  have he := eligible_unset hS w (hT.trans (eligible_subset S R w))
  funext a
  have hw' := congrFun hw a
  simp only [flip, he] at hw' ⊢
  by_cases ha : a ∈ eligible S R w
  · simpa [ha] using hw'
  · have hn : a ∉ T := fun ht => ha (hT ht)
    simp [ha, unset, hn]

theorem removed_subset {α : Type u_1} [Fintype α] [DecidableEq α]
    (S : Finset α) (R : α → α → Prop) (w : α → Bool) :
    removed S R w ⊆ eligible S R w := by
  classical
  exact Finset.filter_subset _ _

theorem unset_flip_removed (S : Finset α) (R : α → α → Prop)
    (w : α → Bool) : unset (flip S R w) (removed S R w) = w := by
  classical
  funext a
  by_cases ha : a ∈ eligible S R w
  · cases hw : w a <;> simp [unset, removed, flip, ha, hw]
  · simp [unset, removed, flip, ha]

theorem removed_unset {S : Finset α} {R : α → α → Prop}
    (hS : ∀ a ∈ S, ∀ b, R a b → b ∉ S)
    {w : α → Bool} (hw : flip S R w = w)
    {T : Finset α} (hT : T ⊆ eligible S R w) :
    removed S R (unset w T) = T := by
  classical
  have he := eligible_unset hS w (hT.trans (eligible_subset S R w))
  ext a
  simp only [removed, Finset.mem_filter, he]
  constructor
  · rintro ⟨ha, hz⟩
    by_contra hn
    have hw' := congrFun hw a
    simp [flip, ha] at hw'
    simp [unset, hn, hw'] at hz
  · intro ha
    exact ⟨hT ha, by simp [unset, ha]⟩

/-! Each fiber of the canonicalization is exactly a powerset. -/

def fiberEquiv {S : Finset α} {R : α → α → Prop}
    (hS : ∀ a ∈ S, ∀ b, R a b → b ∉ S)
    (w : α → Bool) (hw : flip S R w = w) :
    {z : α → Bool // flip S R z = w} ≃
      {T : Finset α // T ⊆ eligible S R w} where
  toFun z := ⟨removed S R z, by
    have he : eligible S R z = eligible S R w := by
      exact (eligible_flip hS z).symm.trans (congrArg (eligible S R) z.property)
    rw [← he]
    exact removed_subset S R z⟩
  invFun T := ⟨unset w T, flip_unset hS hw T.property⟩
  left_inv z := by
    apply Subtype.ext
    change unset w (removed S R z) = z
    exact (congrArg (fun q => unset q (removed S R z)) z.property.symm).trans
      (unset_flip_removed S R z)
  right_inv T := by
    apply Subtype.ext
    exact removed_unset hS hw T.property

theorem fiber_card {S : Finset α} {R : α → α → Prop}
    (hS : ∀ a ∈ S, ∀ b, R a b → b ∉ S)
    (w : α → Bool) (hw : flip S R w = w) :
    Fintype.card {z : α → Bool // flip S R z = w} =
      2 ^ (eligible S R w).card := by
  classical
  rw [Fintype.card_congr (fiberEquiv hS w hw)]
  simpa only [Finset.mem_powerset] using
    (Fintype.card_coe (eligible S R w).powerset).trans (Finset.card_powerset _)

theorem fiber_sum_pow {S : Finset α} {R : α → α → Prop}
    (hS : ∀ a ∈ S, ∀ b, R a b → b ∉ S)
    (w : α → Bool) (hw : flip S R w = w)
    {K : Type*} [CommSemiring K] (c : K) :
    (∑ z : {z : α → Bool // flip S R z = w},
      c ^ (removed S R z).card) = (1 + c) ^ (eligible S R w).card := by
  classical
  calc
    _ = ∑ T : {T : Finset α // T ⊆ eligible S R w}, c ^ T.val.card :=
      Fintype.sum_equiv (fiberEquiv hS w hw) _ _ (fun _ => rfl)
    _ = ∑ T ∈ (eligible S R w).powerset, c ^ T.card :=
      (Finset.sum_subtype (p := fun T : Finset α => T ⊆ eligible S R w)
        (eligible S R w).powerset (fun _ => Finset.mem_powerset)
        (fun T => c ^ T.card)).symm
    _ = _ := by
      simpa [Finset.prod_const, add_comm] using
        (Finset.prod_add_one (f := fun _ : α => c) (eligible S R w)).symm

theorem fiber_weight_sum {S : Finset α} {R : α → α → Prop}
    (hS : ∀ a ∈ S, ∀ b, R a b → b ∉ S)
    (w : α → Bool) (hw : flip S R w = w)
    {K : Type*} [CommSemiring K] (c : K) (W : (α → Bool) → K)
    (hW : ∀ z, flip S R z = w → W z = W w * c ^ (removed S R z).card) :
    (∑ z : {z : α → Bool // flip S R z = w}, W z) =
      W w * (1 + c) ^ (eligible S R w).card := by
  classical
  calc
    _ = ∑ z : {z : α → Bool // flip S R z = w},
        W w * c ^ (removed S R z).card :=
      Finset.sum_congr rfl (fun z _ => hW z z.property)
    _ = W w * ∑ z : {z : α → Bool // flip S R z = w},
        c ^ (removed S R z).card := (Finset.mul_sum _ _ _).symm
    _ = _ := by rw [fiber_sum_pow hS w hw]

theorem total_weight_sum {S : Finset α} {R : α → α → Prop}
    (hS : ∀ a ∈ S, ∀ b, R a b → b ∉ S)
    {K : Type*} [CommSemiring K] (c : K) (W : (α → Bool) → K)
    (hW : ∀ z, W z = W (flip S R z) * c ^ (removed S R z).card) :
    (∑ z, W z) = ∑ w ∈ Finset.univ.filter (fun w => flip S R w = w),
      W w * (1 + c) ^ (eligible S R w).card := by
  classical
  rw [Finset.sum_filter]
  calc
    _ = ∑ w, ∑ z : {z : α → Bool // flip S R z = w}, W z :=
      (Fintype.sum_fiberwise (flip S R) W).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : flip S R w = w
      · rw [ite_eq_left hw]
        apply fiber_weight_sum hS w hw c W
        intro z hz
        simpa only [hz] using hW z
      · rw [ite_eq_right hw]
        have hempty : IsEmpty {z : α → Bool // flip S R z = w} := by
          refine ⟨fun z => hw ?_⟩
          exact (congrArg (flip S R) z.property.symm).trans
            ((flip_idempotent hS z).trans z.property)
        let := hempty
        simp

theorem correction_removal {S : Finset α} {R : α → α → Prop}
    (hS : ∀ a ∈ S, ∀ b, R a b → b ∉ S)
    (c : ℝ) (hc : 0 ≤ c) (W : (α → Bool) → ℝ)
    (hWnonneg : ∀ z, 0 ≤ W z)
    (hW : ∀ z, W z = W (flip S R z) * c ^ (removed S R z).card) :
    (∑ z, W z) ≤ (1 + c) ^ S.card *
      ∑ w ∈ Finset.univ.filter (fun w => flip S R w = w), W w := by
  classical
  rw [total_weight_sum hS c W hW, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w _
  rw [mul_comm ((1 + c) ^ S.card)]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by linarith : 1 ≤ 1 + c)
      (Finset.card_le_card (eligible_subset S R w))) (hWnonneg w)

end Problem335.IsolatedFlip

end

end OAI
