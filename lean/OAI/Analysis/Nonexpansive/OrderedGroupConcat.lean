import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic.Common

namespace OAI

/-!
# Concatenation of ordered finite groups

Each parent contributes a finite group. The global index is the sum of the
sizes of earlier groups plus the local index. This arithmetic construction
gives both the monotone parent map and the order embedding induced by retaining
an increasing subsequence within each group.
-/

namespace ReflexiveFixedPoints.OrderedGroupConcat

open scoped BigOperators

variable {n : ℕ}

/-- The number of entries after concatenating all groups. -/
def total (c : Fin n → ℕ) : ℕ := ∑ p, c p

/-- The number of entries in groups preceding `p`. -/
def offset (c : Fin n → ℕ) (p : Fin n) : ℕ :=
  ∑ q ∈ Finset.univ.filter (fun q => q < p), c q

@[simp] theorem offset_zero (c : Fin (n + 1) → ℕ) : offset c 0 = 0 := by
  simp [offset]

/-- Appending one parent group advances the prefix counter by its size. -/
theorem offset_succ (c : Fin (n + 1) → ℕ) (p : Fin n) :
    offset c p.succ = offset c p.castSucc + c p.castSucc := by
  have hs : Finset.univ.filter (fun q : Fin (n + 1) => q < p.succ) =
      insert p.castSucc (Finset.univ.filter (fun q : Fin (n + 1) => q < p.castSucc)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    change q.val < p.val + 1 ↔ q = p.castSucc ∨ q.val < p.val
    constructor
    · intro h
      by_cases hq : q = p.castSucc
      · exact Or.inl hq
      · right
        have hne : q.val ≠ p.val := fun he => hq (Fin.ext he)
        omega
    · rintro (rfl | h)
      · exact Nat.lt_succ_self _
      · omega
  unfold offset
  rw [hs, Finset.sum_insert (by simp)]
  exact Nat.add_comm _ _

/-- A group and an index in that group. -/
abbrev Index (c : Fin n → ℕ) := Σ p : Fin n, Fin (c p)

theorem offset_add_le_total (c : Fin n → ℕ) (p : Fin n) :
    offset c p + c p ≤ total c := by
  have hs : insert p (Finset.univ.filter (fun q : Fin n => q < p)) ⊆
      (Finset.univ : Finset (Fin n)) := Finset.subset_univ _
  have h := Finset.sum_le_sum_of_subset (f := c) hs
  simpa [offset, total, Finset.sum_insert, Nat.add_comm] using h

theorem offset_add_le_offset (c : Fin n → ℕ) {p q : Fin n} (hpq : p < q) :
    offset c p + c p ≤ offset c q := by
  have hs : insert p (Finset.univ.filter (fun r : Fin n => r < p)) ⊆
      Finset.univ.filter (fun r : Fin n => r < q) := by
    intro r hr
    rcases Finset.mem_insert.mp hr with h | h
    · subst r
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpq⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, lt_trans (Finset.mem_filter.mp h).2 hpq⟩
  have h := Finset.sum_le_sum_of_subset (f := c) hs
  simpa [offset, Finset.sum_insert, Nat.add_comm] using h

theorem offset_mono (c : Fin n → ℕ) : Monotone (offset c) := by
  intro p q hpq
  rcases lt_or_eq_of_le hpq with h | h
  · have := offset_add_le_offset c h
    omega
  · subst q
    exact le_rfl

/-- The actual concatenation ordinal, with its bound proved from the sum. -/
def encode (c : Fin n → ℕ) (s : Index c) : Fin (total c) :=
  ⟨offset c s.1 + s.2.val, by
    have := offset_add_le_total c s.1
    have := s.2.isLt
    omega⟩

@[simp] theorem encode_val (c : Fin n → ℕ) (p : Fin n) (i : Fin (c p)) :
    (encode c ⟨p, i⟩).val = offset c p + i.val := rfl

theorem encode_lt_of_parent_lt (c : Fin n → ℕ) {p q : Fin n}
    (hpq : p < q) (i : Fin (c p)) (j : Fin (c q)) :
    encode c ⟨p, i⟩ < encode c ⟨q, j⟩ := by
  change offset c p + i.val < offset c q + j.val
  have := offset_add_le_offset c hpq
  have := i.isLt
  omega

theorem encode_injective (c : Fin n → ℕ) : Function.Injective (encode c) := by
  rintro ⟨p, i⟩ ⟨q, j⟩ h
  rcases lt_trichotomy p q with hpq | hpq | hpq
  · exact False.elim ((ne_of_lt (encode_lt_of_parent_lt c hpq i j)) h)
  · subst q
    have hv := congrArg Fin.val h
    simp only [encode_val] at hv
    have hij : i = j := Fin.ext (by omega)
    subst j
    rfl
  · exact False.elim ((ne_of_lt (encode_lt_of_parent_lt c hpq j i)) h.symm)

/-- The concatenation is exhaustive: injectivity and the exact finite
cardinality prove that every global ordinal has a group and a local index. -/
noncomputable def equiv (c : Fin n → ℕ) : Index c ≃ Fin (total c) :=
  Equiv.ofBijective (encode c)
    ((Fintype.bijective_iff_injective_and_card (encode c)).2
      ⟨encode_injective c, by
        simp [total, Fintype.card_fin]
        exact (Fintype.card_fin (∑ p : Fin n, c p)).symm⟩)

@[simp] theorem equiv_apply (c : Fin n → ℕ) (s : Index c) :
    equiv c s = encode c s := rfl

@[simp] theorem equiv_val (c : Fin n → ℕ) (p : Fin n) (i : Fin (c p)) :
    (equiv c ⟨p, i⟩).val = offset c p + i.val := rfl

/-- Each individual group is an increasing interval in the concatenation. -/
def group (c : Fin n → ℕ) (p : Fin n) : Fin (c p) ↪o Fin (total c) :=
  OrderEmbedding.ofStrictMono (fun i => encode c ⟨p, i⟩) (by
    intro i j hij
    change offset c p + i.val < offset c p + j.val
    exact Nat.add_lt_add_left hij _)

@[simp] theorem group_apply (c : Fin n → ℕ) (p : Fin n) (i : Fin (c p)) :
    group c p i = encode c ⟨p, i⟩ := rfl

@[simp] theorem group_val (c : Fin n → ℕ) (p : Fin n) (i : Fin (c p)) :
    (group c p i).val = offset c p + i.val := rfl

/-- The parent of a global index. -/
noncomputable def parent (c : Fin n → ℕ) (i : Fin (total c)) : Fin n :=
  ((equiv c).symm i).1

@[simp] theorem parent_group (c : Fin n → ℕ) (p : Fin n) (i : Fin (c p)) :
    parent c (group c p i) = p := by
  change ((equiv c).symm (equiv c ⟨p, i⟩)).1 = p
  rw [Equiv.symm_apply_apply]

theorem parent_monotone (c : Fin n → ℕ) : Monotone (parent c) := by
  intro a b hab
  obtain ⟨⟨p, i⟩, rfl⟩ := (equiv c).surjective a
  obtain ⟨⟨q, j⟩, rfl⟩ := (equiv c).surjective b
  change parent c (group c p i) ≤ parent c (group c q j)
  rw [parent_group, parent_group]
  by_contra h
  have hqp : q < p := lt_of_not_ge h
  have hlt := encode_lt_of_parent_lt c hqp j i
  exact (not_lt_of_ge hab) hlt

theorem parent_surjective (c : Fin n → ℕ) (hc : ∀ p, 0 < c p) :
    Function.Surjective (parent c) := by
  intro p
  exact ⟨group c p ⟨0, hc p⟩, parent_group c p _⟩

/-- Reindex a sum over the actual parent fiber by the local group indices. -/
theorem sum_parent_fiber (c : Fin n → ℕ) (p : Fin n)
    {A : Type*} [AddCommMonoid A] (f : Fin (total c) → A) :
    (∑ i ∈ Finset.univ.filter (fun i => parent c i = p), f i) =
      ∑ j : Fin (c p), f (group c p j) := by
  classical
  symm
  apply Finset.sum_bij (fun j _ => group c p j)
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, parent_group c p j⟩
  · intro j hj k hk h
    exact (group c p).injective h
  · intro i hi
    obtain ⟨⟨q, j⟩, rfl⟩ := (equiv c).surjective i
    have hq : q = p := by
      have h := (Finset.mem_filter.mp hi).2
      change parent c (group c q j) = p at h
      simpa only [parent_group] using h
    subst q
    exact ⟨j, Finset.mem_univ _, rfl⟩
  · intro j hj
    rfl

theorem total_pos (c : Fin n → ℕ) (hn : 0 < n) (hc : ∀ p, 0 < c p) :
    0 < total c := by
  let p : Fin n := ⟨0, hn⟩
  have := offset_add_le_total c p
  have := hc p
  omega

variable {c d : Fin n → ℕ}

/-- Retaining the prescribed ordered subsequence inside each parent group. -/
noncomputable def retainFun (r : ∀ p, Fin (c p) ↪o Fin (d p))
    (i : Fin (total c)) : Fin (total d) :=
  let s := (equiv c).symm i
  encode d ⟨s.1, r s.1 s.2⟩

@[simp] theorem retainFun_group (r : ∀ p, Fin (c p) ↪o Fin (d p))
    (p : Fin n) (i : Fin (c p)) :
    retainFun r (group c p i) = group d p (r p i) := by
  change (fun s : Index c => encode d ⟨s.1, r s.1 s.2⟩)
    ((equiv c).symm (equiv c ⟨p, i⟩)) = encode d ⟨p, r p i⟩
  rw [Equiv.symm_apply_apply]

theorem retainFun_strictMono (r : ∀ p, Fin (c p) ↪o Fin (d p)) :
    StrictMono (retainFun r) := by
  intro a b hab
  obtain ⟨⟨p, i⟩, rfl⟩ := (equiv c).surjective a
  obtain ⟨⟨q, j⟩, rfl⟩ := (equiv c).surjective b
  change retainFun r (group c p i) < retainFun r (group c q j)
  rw [retainFun_group, retainFun_group]
  rcases lt_trichotomy p q with hpq | hpq | hpq
  · exact encode_lt_of_parent_lt d hpq (r p i) (r q j)
  · subst q
    have hij : i < j := by
      change offset c p + i.val < offset c p + j.val at hab
      change i.val < j.val
      omega
    exact (group d p).strictMono ((r p).strictMono hij)
  · exact False.elim ((not_lt_of_ge hab.le)
      (encode_lt_of_parent_lt c hpq j i))

/-- The global increasing retained subsequence. -/
noncomputable def retain (r : ∀ p, Fin (c p) ↪o Fin (d p)) :
    Fin (total c) ↪o Fin (total d) :=
  OrderEmbedding.ofStrictMono (retainFun r) (retainFun_strictMono r)

@[simp] theorem retain_group (r : ∀ p, Fin (c p) ↪o Fin (d p))
    (p : Fin n) (i : Fin (c p)) :
    retain r (group c p i) = group d p (r p i) := retainFun_group r p i

@[simp] theorem parent_retain (r : ∀ p, Fin (c p) ↪o Fin (d p))
    (i : Fin (total c)) : parent d (retain r i) = parent c i := by
  obtain ⟨⟨p, j⟩, rfl⟩ := (equiv c).surjective i
  change parent d (retain r (group c p j)) = parent c (group c p j)
  rw [retain_group, parent_group, parent_group]

@[simp] theorem retain_group_val (r : ∀ p, Fin (c p) ↪o Fin (d p))
    (p : Fin n) (i : Fin (c p)) :
    (retain r (group c p i)).val = offset d p + (r p i).val := by
  rw [retain_group, group_val]

end ReflexiveFixedPoints.OrderedGroupConcat

end OAI
