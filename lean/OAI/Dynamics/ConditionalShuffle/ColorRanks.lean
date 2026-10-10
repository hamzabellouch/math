import OAI.Dynamics.ConditionalShuffle.SortedImages

namespace OAI

noncomputable section
open scoped Classical
namespace Revealed.Color
open Thorp
variable {A C : Type} [fintype_A : Fintype A] [fintype_C : Fintype C]

def layoutColor (d : ℕ) (L : Sum A C ≃ Position (d+1)) : Coloring d :=
  fun x => (L.symm x).isLeft

@[simp] lemma layoutColor_A (d : ℕ) (L : Sum A C ≃ Position (d+1)) (a : A) :
    layoutColor d L (L (.inl a)) = true := by
  let retained_fintype_A := fintype_A
  let retained_fintype_C := fintype_C
  simp [layoutColor]
@[simp] lemma layoutColor_C (d : ℕ) (L : Sum A C ≃ Position (d+1)) (b : C) :
    layoutColor d L (L (.inr b)) = false := by
  let retained_fintype_A := fintype_A
  let retained_fintype_C := fintype_C
  simp [layoutColor]

def leftEnds (d : ℕ) (L : Sum A C ≃ Position (d+1)) (g : State (d+1)) : A → Lex (Position (d+1)) :=
  fun a => toLex (g (L (.inl a)))
def rightEnds (d : ℕ) (L : Sum A C ≃ Position (d+1)) (g : State (d+1)) : C → Lex (Position (d+1)) :=
  fun b => toLex (g (L (.inr b)))

lemma leftEnds_injective (d : ℕ) (L : Sum A C ≃ Position (d+1)) (g : State (d+1)) :
    Function.Injective (leftEnds d L g) := by
  let retained_fintype_A := fintype_A
  let retained_fintype_C := fintype_C
  intro a b hh
  exact Sum.inl_injective (L.injective (g.injective hh))
lemma rightEnds_injective (d : ℕ) (L : Sum A C ≃ Position (d+1)) (g : State (d+1)) :
    Function.Injective (rightEnds d L g) := by
  let retained_fintype_A := fintype_A
  let retained_fintype_C := fintype_C
  intro a b hh
  exact Sum.inr_injective (L.injective (g.injective hh))

def leftRank (d : ℕ) (L : Sum A C ≃ Position (d+1)) (g : State (d+1)) : A ≃ Fin (Fintype.card A) :=
  imageRank (leftEnds d L g) (leftEnds_injective d L g)
def rightRank (d : ℕ) (L : Sum A C ≃ Position (d+1)) (g : State (d+1)) : C ≃ Fin (Fintype.card C) :=
  imageRank (rightEnds d L g) (rightEnds_injective d L g)

def internalA (d : ℕ) (L : Sum A C ≃ Position (d+1)) (g : State (d+1)) : Equiv.Perm A :=
  (leftRank d L g).trans (leftRank d L 1).symm
def internalC (d : ℕ) (L : Sum A C ≃ Position (d+1)) (g : State (d+1)) : Equiv.Perm C :=
  (rightRank d L g).trans (rightRank d L 1).symm

lemma internalA_depends (d : ℕ) (L : Sum A C ≃ Position (d+1)) (g g' : State (d+1))
    (hh : ∀ a, g (L (.inl a)) = g' (L (.inl a))) : internalA d L g = internalA d L g' := by
  have he : leftEnds d L g = leftEnds d L g' := funext hh
  simp only [internalA, leftRank, he]
lemma internalC_depends (d : ℕ) (L : Sum A C ≃ Position (d+1)) (g g' : State (d+1))
    (hh : ∀ b, g (L (.inr b)) = g' (L (.inr b))) : internalC d L g = internalC d L g' := by
  have he : rightEnds d L g = rightEnds d L g' := funext hh
  simp only [internalC, rightRank, he]

def sortedTransport (d : ℕ) (L : Sum A C ≃ Position (d+1)) (g : State (d+1)) : State (d+1) :=
  L.symm.trans ((Equiv.sumCongr (internalA d L g).symm (internalC d L g).symm).trans (L.trans g))

lemma transport_A (d : ℕ) (L : Sum A C ≃ Position (d+1)) (g : State (d+1)) (a : A) :
    sortedTransport d L g (L (.inl a)) =
      ofLex (sortedImage (leftEnds d L g) (leftEnds_injective d L g) (leftRank d L 1 a)) := by
  simp only [sortedTransport, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.sumCongr_apply,
    Sum.map_inl, internalA, Equiv.symm_trans, Equiv.symm_symm]
  rfl
lemma transport_C (d : ℕ) (L : Sum A C ≃ Position (d+1)) (g : State (d+1)) (b : C) :
    sortedTransport d L g (L (.inr b)) =
      ofLex (sortedImage (rightEnds d L g) (rightEnds_injective d L g) (rightRank d L 1 b)) := by
  simp only [sortedTransport, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.sumCongr_apply,
    Sum.map_inr, internalC, Equiv.symm_trans, Equiv.symm_symm]
  rfl

theorem physical_color_factor (d : ℕ) (L : Sum A C ≃ Position (d+1)) (g : State (d+1)) :
    g = sortedTransport d L g *
      (L.symm.trans ((Equiv.sumCongr (internalA d L g) (internalC d L g)).trans L)) := by
  apply Equiv.ext; intro x
  obtain ⟨s,rfl⟩ := L.surjective x
  cases s <;> simp [sortedTransport]

lemma color_range_A (d : ℕ) (L : Sum A C ≃ Position (d+1)) (g : State (d+1)) :
    Set.range (fun a => g (L (.inl a))) = {x | layoutColor d L (g.symm x) = true} := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩; simp only [Set.mem_ofPred_eq, Equiv.symm_apply_apply, layoutColor_A]
  · intro hx
    obtain ⟨s,rfl⟩ := (L.trans g).surjective x
    cases s with
    | inl a => exact ⟨a,rfl⟩
    | inr b => simp only [Set.mem_ofPred_eq, Equiv.trans_apply, Equiv.symm_apply_apply, layoutColor_C, Bool.false_eq_true] at hx

lemma color_range_C (d : ℕ) (L : Sum A C ≃ Position (d+1)) (g : State (d+1)) :
    Set.range (fun b => g (L (.inr b))) = {x | layoutColor d L (g.symm x) = false} := by
  ext x
  constructor
  · rintro ⟨b,rfl⟩; simp only [Set.mem_ofPred_eq, Equiv.symm_apply_apply, layoutColor_C]
  · intro hx
    obtain ⟨s,rfl⟩ := (L.trans g).surjective x
    cases s with
    | inr b => exact ⟨b,rfl⟩
    | inl a => simp only [Set.mem_ofPred_eq, Equiv.trans_apply, Equiv.symm_apply_apply, layoutColor_A, Bool.true_eq_false] at hx

lemma transport_depends_only_color (d : ℕ) (L : Sum A C ≃ Position (d+1)) (g g' : State (d+1))
    (hh : ∀ x, layoutColor d L (g.symm x) = layoutColor d L (g'.symm x)) :
    sortedTransport d L g = sortedTransport d L g' := by
  have ha : Set.range (leftEnds d L g) = Set.range (leftEnds d L g') := by
    change Set.range (toLex ∘ (fun a => g (L (.inl a)) )) = Set.range (toLex ∘ (fun a => g' (L (.inl a))))
    simp only [Set.range_comp, color_range_A, hh]
  have hc : Set.range (rightEnds d L g) = Set.range (rightEnds d L g') := by
    change Set.range (toLex ∘ (fun b => g (L (.inr b)) )) = Set.range (toLex ∘ (fun b => g' (L (.inr b))))
    simp only [Set.range_comp, color_range_C, hh]
  have hra := sortedImage_eq_of_range _ _ (leftEnds_injective d L g) (leftEnds_injective d L g') ha
  have hrc := sortedImage_eq_of_range _ _ (rightEnds_injective d L g) (rightEnds_injective d L g') hc
  apply Equiv.ext; intro x
  obtain ⟨s,rfl⟩ := L.surjective x
  cases s with
  | inl a => rw [transport_A, transport_A, hra]
  | inr b => rw [transport_C, transport_C, hrc]

lemma transport_occupancy (d : ℕ) (L : Sum A C ≃ Position (d+1)) (t : ℕ) (c c' : History (d+1) t)
    (hh : occupancy d (layoutColor d L) t c = occupancy d (layoutColor d L) t c') :
    sortedTransport d L (run (d+1) t c) = sortedTransport d L (run (d+1) t c') := by
  apply transport_depends_only_color
  have he := congrFun hh (Fin.last t)
  change occupied d (layoutColor d L) t c = occupied d (layoutColor d L) t c' at he
  rw [occupied_run, occupied_run] at he
  exact congrFun he

end Revealed.Color

end

end OAI
