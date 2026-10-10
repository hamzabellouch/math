import Mathlib

namespace OAI

/-!
# Finite permutation representations of balls in free groups
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree.GraphProducer

variable (A : Type*) [Finite A] [DecidableEq A]

def WordBall (N : ℕ) := {g : FreeGroup A // FreeGroup.norm g ≤ N}

instance (N : ℕ) : Finite (WordBall A N) := by
  have h := List.finite_length_le (A × Bool) N
  let : Fintype {l : List (A × Bool) // l.length ≤ N} := h.fintype
  let f : WordBall A N → {l : List (A × Bool) // l.length ≤ N} :=
    fun g => ⟨g.val.toWord, g.property⟩
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (FreeGroup.toWord_injective (congrArg Subtype.val hxy))
  exact Finite.of_injective f hf

instance (N : ℕ) : Fintype (WordBall A N) := Fintype.ofFinite _

def ballOne (N : ℕ) : WordBall A N := ⟨1, by simp⟩

omit [Finite A] in
@[simp] theorem ballOne_val (N : ℕ) : (ballOne A N).val = 1 := rfl

theorem exists_ball_perm (N : ℕ) (a : A) :
    ∃ σ : Equiv.Perm (WordBall A N), ∀ g : WordBall A N,
      ∀ _h : FreeGroup.norm (FreeGroup.of a * g.val) ≤ N,
        (σ g).val = FreeGroup.of a * g.val := by
  let P := {g : WordBall A N // FreeGroup.norm (FreeGroup.of a * g.val) ≤ N}
  let f : P → WordBall A N := fun g => g.val
  let t : P → WordBall A N := fun g => ⟨FreeGroup.of a * g.val.val, g.property⟩
  have hf : Function.Injective f := Subtype.val_injective
  have ht : Function.Injective t := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact mul_left_cancel (congrArg Subtype.val hxy)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f t hf ht
  refine ⟨σ, fun g h => ?_⟩
  exact congrArg Subtype.val (hσ ⟨g, h⟩)

noncomputable def ballPerm (N : ℕ) (a : A) : Equiv.Perm (WordBall A N) :=
  (exists_ball_perm A N a).choose

theorem ballPerm_apply (N : ℕ) (a : A) (g : WordBall A N)
    (h : FreeGroup.norm (FreeGroup.of a * g.val) ≤ N) :
    (ballPerm A N a g).val = FreeGroup.of a * g.val :=
  (exists_ball_perm A N a).choose_spec g h

theorem ballPerm_inv_apply (N : ℕ) (a : A) (g : WordBall A N)
    (h : FreeGroup.norm ((FreeGroup.of a)⁻¹ * g.val) ≤ N) :
    ((ballPerm A N a)⁻¹ g).val = (FreeGroup.of a)⁻¹ * g.val := by
  let y : WordBall A N := ⟨(FreeGroup.of a)⁻¹ * g.val, h⟩
  have hy : FreeGroup.norm (FreeGroup.of a * y.val) ≤ N := by
    simpa [y] using g.property
  have heq : ballPerm A N a y = g := by
    apply Subtype.ext
    simpa [y] using ballPerm_apply A N a y hy
  have hh : (ballPerm A N a)⁻¹ g = y := (ballPerm A N a).symm_apply_eq.mpr heq.symm
  exact congrArg Subtype.val hh

noncomputable def ballRep (N : ℕ) : FreeGroup A →* Equiv.Perm (WordBall A N) :=
  FreeGroup.lift (ballPerm A N)

omit [Finite A] [DecidableEq A] in
lemma mk_cons_letter (a : A) (b : Bool) (l : List (A × Bool)) :
    FreeGroup.mk ((a,b) :: l) =
      (if b then FreeGroup.of a else (FreeGroup.of a)⁻¹) * FreeGroup.mk l := by
  cases b <;> rfl

theorem ballRep_word (N : ℕ) (l : List (A × Bool)) (hl : l.length ≤ N) :
    (ballRep A N (FreeGroup.mk l) (ballOne A N)).val = FreeGroup.mk l := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    obtain ⟨a, b⟩ := c
    have hlt : l.length ≤ N := by simpa using (Nat.le_of_succ_le hl)
    have hv := ih hlt
    have hm : FreeGroup.norm (FreeGroup.mk ((a,b)::l)) ≤ N :=
      FreeGroup.norm_mk_le.trans hl
    rw [mk_cons_letter] at hm ⊢
    rw [map_mul]
    change ((ballRep A N (if b then FreeGroup.of a else (FreeGroup.of a)⁻¹))
      (ballRep A N (FreeGroup.mk l) (ballOne A N))).val = _
    change (ballRep A N (FreeGroup.mk l) (ballOne A N)).val = FreeGroup.mk l at hv
    change (FreeGroup.lift (ballPerm A N) (FreeGroup.mk l) (ballOne A N)).val = FreeGroup.mk l at hv
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, map_inv, ballRep,
        FreeGroup.lift_apply_of]
      rw [ballPerm_inv_apply]
      · rw [hv]
      · rw [hv]
        exact hm
    · simp only [↓reduceIte, ballRep, FreeGroup.lift_apply_of]
      rw [ballPerm_apply]
      · rw [hv]
      · rw [hv]
        exact hm

theorem ballRep_apply_one (N : ℕ) (g : FreeGroup A) (hg : FreeGroup.norm g ≤ N) :
    (ballRep A N g (ballOne A N)).val = g := by
  simpa only [FreeGroup.mk_toWord] using ballRep_word A N g.toWord hg

theorem ballRep_injective_on (N : ℕ) :
    Set.InjOn (ballRep A N) {g | FreeGroup.norm g ≤ N} := by
  intro g hg h hh heq
  have := congrArg (fun σ : Equiv.Perm (WordBall A N) => (σ (ballOne A N)).val) heq
  simpa [ballRep_apply_one A N g hg, ballRep_apply_one A N h hh] using this

theorem ballRep_ne_one (N : ℕ) (l : List (A × Bool))
    (hl : FreeGroup.IsReduced l) (hne : l ≠ []) (hlen : l.length ≤ N) :
    ballRep A N (FreeGroup.mk l) ≠ 1 := by
  intro heq
  have h := ballRep_injective_on A N (FreeGroup.norm_mk_le.trans hlen)
    (by simp : FreeGroup.norm (1 : FreeGroup A) ≤ N) (by simpa using heq)
  apply hne
  have ht := congrArg FreeGroup.toWord h
  simpa [FreeGroup.toWord_mk, hl.reduce_eq] using ht

theorem prefixes_injective (N : ℕ) (l : List (A × Bool))
    (hl : FreeGroup.IsReduced l) (hlen : l.length ≤ N)
    (x : Equiv.Perm (WordBall A N)) :
    Function.Injective (fun i : Fin (l.length + 1) =>
      x * ballRep A N (FreeGroup.mk (l.take i.val))) := by
  intro i j hij
  have ht (t : ℕ) : FreeGroup.norm (FreeGroup.mk (l.take t)) ≤ N :=
    FreeGroup.norm_mk_le.trans (by
      rw [List.length_take]
      exact (min_le_right _ _).trans hlen)
  have heq := ballRep_injective_on A N (ht i.val) (ht j.val) (mul_left_cancel hij)
  have hi : FreeGroup.IsReduced (l.take i.val) := hl.take _
  have hj : FreeGroup.IsReduced (l.take j.val) := hl.take _
  have he := congrArg (fun g : FreeGroup A => g.toWord.length) heq
  simp only [FreeGroup.toWord_mk, hi.reduce_eq, hj.reduce_eq, List.length_take] at he
  apply Fin.ext
  simpa [Nat.min_eq_left (Nat.le_of_lt_succ i.isLt),
    Nat.min_eq_left (Nat.le_of_lt_succ j.isLt)] using he

end DiscreteFree.GraphProducer

end

end OAI
