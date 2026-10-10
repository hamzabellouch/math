import OAI.Dynamics.ConditionalShuffle.Fibers

namespace OAI

noncomputable section
namespace Revealed.Split
open scoped Classical
variable {ι α β : Type*} [decidableEq_α : DecidableEq α] [DecidableEq β]

lemma trans_free_swap (L : Sum ι α ≃ β) (a b : α) :
    L.trans (Equiv.swap (L (.inr a)) (L (.inr b))) =
      (Equiv.sumCongr (Equiv.refl ι) (Equiv.swap a b)).trans L := by
  ext x
  cases x with
  | inl i => simp [Equiv.swap_apply_def, L.injective.eq_iff]
  | inr x =>
      by_cases hxa : x = a
      · subst x
        simp
      · by_cases hxb : x = b
        · subst x
          simp
        · simp [Equiv.swap_apply_def, L.injective.eq_iff, hxa, hxb]

end Revealed.Split

namespace Thorp.Conditional
open scoped Classical
open Revealed.Split
variable {ι α : Type} [fintype_ι : Fintype ι] [fintype_α : Fintype α] [decidableEq_α : DecidableEq α]

lemma step_same_at_iff (d : ℕ) (c c' : Coins (d + 1)) (x : Position (d + 1)) :
    step (d + 1) c x = step (d + 1) c' x ↔ c (Fin.tail x) = c' (Fin.tail x) := by
  obtain ⟨⟨b,s⟩, rfl⟩ := (splitPosition d).symm.surjective x
  change rotate (d + 1) (Fin.cons (b ^^ c s) s) =
      rotate (d + 1) (Fin.cons (b ^^ c' s) s) ↔ c s = c' s
  rw [(rotate (d + 1)).injective.eq_iff]
  constructor
  · intro h
    have hh := congrFun h 0
    simp only [Fin.cons_zero] at hh
    cases b <;> simpa using hh
  · intro h
    rw [h]

lemma outside_step_injective (d : ℕ) (L : Sum ι α ≃ Position (d + 1))
    (h : ∀ s : Position d, ∃ i : ι, Fin.tail (L (.inl i)) = s) :
    Function.Injective (fun c : Coins (d + 1) => outside (L.trans (step (d + 1) c))) := by
  let retained_fintype_ι := fintype_ι
  let retained_fintype_α := fintype_α
  let retained_decidableEq_α := decidableEq_α
  intro c c' hc
  funext s
  obtain ⟨i, hi⟩ := h s
  have hh := congrFun (congrArg Subtype.val hc) i
  change step (d + 1) c (L (.inl i)) = step (d + 1) c' (L (.inl i)) at hh
  have he := (step_same_at_iff d c c' _).mp hh
  rwa [hi] at he

lemma pair_free_labels (d : ℕ) (L : Sum ι α ≃ Position (d + 1)) (s : Position d)
    (h : ∀ i : ι, Fin.tail (L (.inl i)) ≠ s) :
    ∃ a b : α, a ≠ b ∧ L (.inr a) = Fin.cons false s ∧ L (.inr b) = Fin.cons true s := by
  let retained_fintype_ι := fintype_ι
  let retained_fintype_α := fintype_α
  let retained_decidableEq_α := decidableEq_α
  have ex (bit : Bool) : ∃ a : α, L (.inr a) = Fin.cons bit s := by
    obtain ⟨x,hx⟩ := L.surjective (Fin.cons bit s)
    cases x with
    | inl i =>
        have hh := congrArg Fin.tail hx
        simp only [Fin.tail_cons] at hh
        exact False.elim (h i hh)
    | inr a => exact ⟨a,hx⟩
  obtain ⟨a,ha⟩ := ex false
  obtain ⟨b,hb⟩ := ex true
  refine ⟨a,b,?_,ha,hb⟩
  intro hh
  subst b
  have hc := congrFun (ha.symm.trans hb) 0
  simp at hc

lemma free_pair_toggle (d : ℕ) (L : Sum ι α ≃ Position (d + 1)) (s : Position d)
    (a b : α) (ha : L (.inr a) = Fin.cons false s) (hb : L (.inr b) = Fin.cons true s)
    (c : Coins (d + 1)) :
    L.trans (step (d + 1) (toggleCoin s c)) =
      (Equiv.sumCongr (Equiv.refl ι) (Equiv.swap a b)).trans (L.trans (step (d + 1) c)) := by
  let retained_fintype_ι := fintype_ι
  let retained_fintype_α := fintype_α
  rw [Parity.step_toggle]
  have hs := trans_free_swap L a b
  rw [ha,hb] at hs
  rw [← Equiv.trans_assoc, ← hs]
  rfl

lemma physical_step_signDichotomy [Nontrivial α] (d : ℕ) (L : Sum ι α ≃ Position (d + 1))
    (o : Outside ι α (Position (d + 1))) :
    Trim.signDichotomy (Revealed.Disintegration.conditional
      (fairMass (fun c : Coins (d + 1) =>
        (outside (L.trans (step (d + 1) c)), assignment (L.trans (step (d + 1) c))))) o) := by
  by_cases h : ∀ s : Position d, ∃ i : ι, Fin.tail (L (.inl i)) = s
  · exact Trim.signDichotomy_conditional_injective _ _ (outside_step_injective d L h) o
  · push Not at h
    obtain ⟨s,hs⟩ := h
    obtain ⟨a,b,hab,ha,hb⟩ := pair_free_labels d L s hs
    apply Trim.signDichotomy_conditional_symmetry _ _ (toggleCoin s) (Equiv.swap a b)
    · intro c
      rw [free_pair_toggle d L s a b ha hb c, outside_pre]
    · intro c
      rw [free_pair_toggle d L s a b ha hb c, assignment_pre]
    · rw [Specht.complexSign_eq, Equiv.Perm.sign_swap hab]
      simp

end Thorp.Conditional

end

end OAI
