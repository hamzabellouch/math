import Mathlib

namespace OAI

/-! Four-path pairing identities for the mixed-operator moment argument. -/

namespace Problem335
namespace Pairings

open scoped BigOperators

/-- Equality of differences of coordinate vectors has only the two pairing patterns. -/
theorem coordinate_difference_eq_iff {α : Type*} (p q r s : α) :
    (Finsupp.single p (1 : ℤ) - Finsupp.single q 1 =
      Finsupp.single r 1 - Finsupp.single s 1) ↔
    (p = q ∧ r = s) ∨ (p = r ∧ q = s) := by
  classical
  constructor
  · intro h
    by_cases hpq : p = q
    · left
      refine ⟨hpq, ?_⟩
      by_contra hrs
      have hr := congrArg (fun f : α →₀ ℤ => f r) h
      simp [hpq, hrs] at hr
    · right
      have hpr : p = r := by
        by_contra hpr
        have hp := congrArg (fun f : α →₀ ℤ => f p) h
        simp only [Finsupp.sub_apply, Finsupp.single_apply] at hp
        split_ifs at hp <;> simp_all
      refine ⟨hpr, ?_⟩
      by_contra hqs
      have hq := congrArg (fun f : α →₀ ℤ => f q) h
      simp only [Finsupp.sub_apply, Finsupp.single_apply] at hq
      split_ifs at hq <;> simp_all
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

/-- The two cases become disjoint when the all-equal case is assigned to normal pairing. -/
theorem coordinate_difference_eq_iff_exclusive {α : Type*} (p q r s : α) :
    (Finsupp.single p (1 : ℤ) - Finsupp.single q 1 =
      Finsupp.single r 1 - Finsupp.single s 1) ↔
    (p = q ∧ r = s) ∨ (p = r ∧ q = s ∧ p ≠ q) := by
  rw [coordinate_difference_eq_iff]
  constructor
  · rintro (h | ⟨hpr, hqs⟩)
    · exact Or.inl h
    · by_cases hpq : p = q
      · exact Or.inl ⟨hpq, by simpa [← hpr, ← hqs] using hpq⟩
      · exact Or.inr ⟨hpr, hqs, hpq⟩
  · rintro (h | ⟨hpr, hqs, _⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hpr, hqs⟩

/-- Pairing patterns at a layer, with the inequality omitted in the diagonal case. -/
inductive Kind where
  | normal
  | diagonal
  deriving DecidableEq

protected abbrev Kind.enumList : List Kind := [.normal, .diagonal]

protected theorem Kind.enumList_getElem?_ctorIdx_eq (kind : Kind) :
    Kind.enumList[kind.ctorIdx]? = some kind := by
  cases kind <;> rfl

protected theorem Kind.enumList_nodup : Kind.enumList.Nodup := by decide

instance : Fintype Kind where
  elems := ⟨Kind.enumList, Multiset.coe_nodup.mpr Kind.enumList_nodup⟩
  complete kind := List.mem_iff_getElem?.mpr
    ⟨kind.ctorIdx, Kind.enumList_getElem?_ctorIdx_eq kind⟩

/-- Boolean words use false for the normal pairing and true for the diagonal pairing. -/
def boolKindEquiv : Bool ≃ Kind where
  toFun b := if b then .diagonal else .normal
  invFun
    | .normal => false
    | .diagonal => true
  left_inv b := by cases b <;> rfl
  right_inv k := by cases k <;> rfl

@[simp] theorem boolKindEquiv_false : boolKindEquiv false = Kind.normal := rfl
@[simp] theorem boolKindEquiv_true : boolKindEquiv true = Kind.diagonal := rfl

/-- The four labels contributed by the four paths at a single vertex. -/
@[ext]
structure Labels (α : Type*) where
  p : α
  q : α
  r : α
  s : α
  deriving Fintype

def Respects {α : Type*} : Kind → Labels α → Prop
  | .normal, x => x.p = x.q ∧ x.r = x.s
  | .diagonal, x => x.p = x.r ∧ x.q = x.s

instance {α : Type*} [DecidableEq α] (τ : Kind) (x : Labels α) :
    Decidable (Respects τ x) := by
  cases τ <;> unfold Respects <;> infer_instance

/-- The exact (disjoint) pairing classes before relaxing the diagonal inequality. -/
def ExactRespects {α : Type*} : Kind → Labels α → Prop
  | .normal, x => x.p = x.q ∧ x.r = x.s
  | .diagonal, x => x.p = x.r ∧ x.q = x.s ∧ x.p ≠ x.q

theorem ExactRespects.respects {α : Type*} {τ : Kind} {x : Labels α}
    (h : ExactRespects τ x) : Respects τ x := by
  cases τ
  · exact h
  · exact ⟨h.1, h.2.1⟩

/-- No compatible coordinate quadruple belongs to both exact pairing classes. -/
theorem exactRespects_unique {α : Type*} {τ σ : Kind} {x : Labels α}
    (hτ : ExactRespects τ x) (hσ : ExactRespects σ x) : τ = σ := by
  cases τ <;> cases σ <;> simp_all [ExactRespects]

/-- Every compatible coordinate quadruple has a unique exact pairing type. -/
theorem coordinate_difference_eq_iff_existsUnique {α : Type*} (x : Labels α) :
    (Finsupp.single x.p (1 : ℤ) - Finsupp.single x.q 1 =
      Finsupp.single x.r 1 - Finsupp.single x.s 1) ↔
    ∃! τ : Kind, ExactRespects τ x := by
  rw [coordinate_difference_eq_iff_exclusive]
  constructor
  · rintro (h | h)
    · exact ⟨.normal, h, fun _ hk => exactRespects_unique hk h⟩
    · exact ⟨.diagonal, h, fun _ hk => exactRespects_unique hk h⟩
  · rintro ⟨τ, h, _⟩
    cases τ
    · exact Or.inl h
    · exact Or.inr h

/-- Labels allowed by both adjacent layers. -/
abbrev Vertex (α : Type*) (τ σ : Kind) :=
  {x : Labels α // Respects τ x ∧ Respects σ x}

def normalVertexEquiv (α : Type*) : Vertex α .normal .normal ≃ α × α where
  toFun x := (x.1.p, x.1.r)
  invFun x := ⟨⟨x.1, x.1, x.2, x.2⟩, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩⟩
  left_inv x := by
    have hp := x.2
    apply Subtype.ext
    apply Labels.ext <;> simp_all [Respects]
  right_inv x := by cases x; rfl

def diagonalVertexEquiv (α : Type*) : Vertex α .diagonal .diagonal ≃ α × α where
  toFun x := (x.1.p, x.1.q)
  invFun x := ⟨⟨x.1, x.2, x.1, x.2⟩, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩⟩
  left_inv x := by
    have hp := x.2
    apply Subtype.ext
    apply Labels.ext <;> simp_all [Respects]
  right_inv x := by cases x; rfl

def mixedVertexEquiv (α : Type*) : Vertex α .normal .diagonal ≃ α where
  toFun x := x.1.p
  invFun x := ⟨⟨x, x, x, x⟩, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩⟩
  left_inv x := by
    have hp := x.2
    apply Subtype.ext
    apply Labels.ext <;> simp_all [Respects]
  right_inv x := rfl

def swapVertexEquiv (α : Type*) (τ σ : Kind) : Vertex α τ σ ≃ Vertex α σ τ where
  toFun x := ⟨x.1, x.2.symm⟩
  invFun x := ⟨x.1, x.2.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Equal pairings give two independent labels; different pairings give one. -/
theorem card_vertex (α : Type*) [Fintype α] [DecidableEq α] (τ σ : Kind) :
    Fintype.card (Vertex α τ σ) =
      Fintype.card α ^ (if τ = σ then 2 else 1) := by
  cases τ <;> cases σ
  · simpa [pow_two] using Fintype.card_congr (normalVertexEquiv α)
  · simpa using Fintype.card_congr (mixedVertexEquiv α)
  · simpa using Fintype.card_congr
      ((swapVertexEquiv α .diagonal .normal).trans (mixedVertexEquiv α))
  · simpa [pow_two] using Fintype.card_congr (diagonalVertexEquiv α)

/-- Number of interfaces at which a word changes its letter. -/
def adjacentSwitches {β : Type*} [DecidableEq β] {L : ℕ}
    (τ : Fin (L + 1) → β) : ℕ :=
  (Finset.univ.filter (fun i : Fin L => τ i.castSucc ≠ τ i.succ)).card

/-- Relabeling letters injectively preserves the number of switches. -/
theorem adjacentSwitches_comp_injective {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    {L : ℕ} (τ : Fin (L + 1) → β) (f : β → γ) (hf : Function.Injective f) :
    adjacentSwitches (fun i => f (τ i)) = adjacentSwitches τ := by
  unfold adjacentSwitches
  congr 1
  apply Finset.filter_congr
  intro i _
  exact not_congr hf.eq_iff

/-- Each unchanged interface has two free labels, and each changed interface has one. -/
theorem free_label_exponent {β : Type*} [DecidableEq β] {L : ℕ}
    (τ : Fin (L + 1) → β) :
    (∑ i : Fin L, if τ i.castSucc = τ i.succ then 2 else 1) =
      2 * L - adjacentSwitches τ := by
  have h : (∑ i : Fin L, if τ i.castSucc = τ i.succ then 2 else 1) +
      adjacentSwitches τ = 2 * L := by
    rw [adjacentSwitches, Finset.card_eq_sum_ones, Finset.sum_filter,
      ← Finset.sum_add_distrib]
    calc
      _ = ∑ _i : Fin L, 2 := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp_all
      _ = 2 * L := by simp [Nat.mul_comm]
  omega

/-- The relaxed four-path assignments factor as a product over internal vertices. -/
abbrev Assignments (α : Type*) {L : ℕ} (τ : Fin (L + 1) → Kind) :=
  (i : Fin L) → Vertex α (τ i.castSucc) (τ i.succ)

/-- Exact unweighted count of relaxed assignments for a fixed pairing word. -/
theorem card_assignments (α : Type*) [Fintype α] [DecidableEq α]
    {L : ℕ} (τ : Fin (L + 1) → Kind) :
    Fintype.card (Assignments α τ) =
      Fintype.card α ^ (2 * L - adjacentSwitches τ) := by
  unfold Assignments
  rw [Fintype.card_pi]
  simp_rw [card_vertex]
  rw [Finset.prod_pow_eq_pow_sum, free_label_exponent]

end Pairings
end Problem335

end OAI
