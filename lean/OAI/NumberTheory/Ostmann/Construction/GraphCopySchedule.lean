import OAI.NumberTheory.Ostmann.Characters.AnchorGraphEvolution

namespace OAI

/-! # The graph on the literal copied and retained slot labels

The ambient label type includes both alternatives at a transfer. The actual
partition restricts the copied alternative to H and the retained alternative to
Y. Thus copying and retaining never identify two surviving slots. -/

namespace Ostmann

universe u

/-- A copied label remembers its sign; a retained label remembers its old slot. -/
def CopyScheduleVertex (I : Type u) : ℕ → Type u
  | 0 => I
  | n + 1 => (Bool × CopyScheduleVertex I n) ⊕ CopyScheduleVertex I n

noncomputable def copyScheduleOutside {I : Type*} : (n : ℕ) → I → CopyScheduleVertex I n
  | 0, i => i
  | n + 1, i => Sum.inr (copyScheduleOutside n i)

noncomputable def copySchedulePositive {I : Type*} : (n : ℕ) → I → CopyScheduleVertex I n
  | 0, i => i
  | n + 1, i => Sum.inl (true, copySchedulePositive n i)

noncomputable def copySchedulePath {I : Type*} :
    (n : ℕ) → (Fin n → Bool) → I → CopyScheduleVertex I n
  | 0, _, i => i
  | n + 1, t, i => Sum.inl (t (Fin.last n), copySchedulePath n (fun j => t j.castSucc) i)

/-- A fresh anchor is retained until its reserved step, copied exactly once,
and then retained at every later step. -/
noncomputable def copyScheduleAnchor {I : Type*} :
    (n : ℕ) → ℕ → Bool → I → CopyScheduleVertex I n
  | 0, _, _, i => i
  | n + 1, j, b, i =>
      if j = n then Sum.inl (b, copyScheduleOutside n i)
      else Sum.inr (copyScheduleAnchor n j b i)

theorem copyScheduleAnchor_new {I : Type*} (n : ℕ) (b : Bool) (i : I) :
    copyScheduleAnchor (n + 1) n b i = Sum.inl (b, copyScheduleOutside n i) := by
  change (if n = n then (Sum.inl (b, copyScheduleOutside n i) :
    (Bool × CopyScheduleVertex I n) ⊕ CopyScheduleVertex I n)
    else Sum.inr (copyScheduleAnchor n n b i)) = _
  exact ite_eq_left rfl

theorem copyScheduleAnchor_old {I : Type*} (n j : ℕ) (b : Bool) (i : I) (hj : j ≠ n) :
    copyScheduleAnchor (n + 1) j b i = Sum.inr (copyScheduleAnchor n j b i) := by
  change (if j = n then (Sum.inl (b, copyScheduleOutside n i) :
    (Bool × CopyScheduleVertex I n) ⊕ CopyScheduleVertex I n)
    else Sum.inr (copyScheduleAnchor n j b i)) = _
  exact ite_eq_right hj

/-- Collapse only the erased pivot. Both surviving alternatives have their
original predecessor, as in the manuscript's H/Y partition. -/
def copySchedulePredecessor {I : Type*} {n : ℕ} (p : CopyScheduleVertex I n) :
    Option (CopyScheduleVertex I n ⊕ CopyScheduleVertex I n) → CopyScheduleVertex I n
  | none => p
  | some (.inl i) => i
  | some (.inr i) => i

noncomputable def copyScheduleGraph {I : Type*} (g : I → I → ℤ) (pivot : ℕ → I) :
    (n : ℕ) → CopyScheduleVertex I n → CopyScheduleVertex I n → ℤ
  | 0 => g
  | n + 1 => transferredGraph (fun i j =>
      copyScheduleGraph g pivot n
        (copySchedulePredecessor (copySchedulePositive n (pivot n)) i)
        (copySchedulePredecessor (copySchedulePositive n (pivot n)) j))

@[simp] theorem copySchedulePath_snoc {I : Type*} {n : ℕ}
    (t : Fin n → Bool) (b : Bool) (i : I) :
    copySchedulePath (n + 1) (Fin.snoc t b) i =
      Sum.inl (b, copySchedulePath n t i) := by
  simp only [copySchedulePath, Fin.snoc_last, Fin.snoc_castSucc]
  rfl

@[simp] theorem copyScheduleGraph_outside_copy {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ)
    (a i : CopyScheduleVertex I n) (b : Bool) :
    copyScheduleGraph g pivot (n + 1) (.inr a) (.inl (b, i)) =
      transferCopySign b * copyScheduleGraph g pivot n a i := rfl

@[simp] theorem copyScheduleGraph_copy_outside {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ)
    (i a : CopyScheduleVertex I n) (b : Bool) :
    copyScheduleGraph g pivot (n + 1) (.inl (b, i)) (.inr a) =
      transferCopySign b * copyScheduleGraph g pivot n i a := rfl

@[simp] theorem copyScheduleGraph_copy_copy {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ)
    (i j : CopyScheduleVertex I n) (b c : Bool) :
    copyScheduleGraph g pivot (n + 1) (.inl (b, i)) (.inl (c, j)) =
      if b = c then transferCopySign b * copyScheduleGraph g pivot n i j
      else transferCopySign b * copyScheduleGraph g pivot n i
        (copySchedulePositive n (pivot n)) := rfl

theorem copyScheduleGraph_diagonal {I : Type*} (g : I → I → ℤ) (pivot : ℕ → I)
    (hg : ∀ i, g i i = 0) (n : ℕ) : ∀ i, copyScheduleGraph g pivot n i i = 0 := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    apply transferredGraph_diagonal
    intro i
    exact ih _

/-- Incoming edges from an unused reserved anchor simply accumulate the signs
of the copied word. The pivot sequence does not enter this identity. -/
theorem copyScheduleGraph_fresh_to_path {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ) (a i : I) (t : Fin n → Bool) :
    copyScheduleGraph g pivot n (copyScheduleOutside n a) (copySchedulePath n t i) =
      finalCopyParity t * g a i := by
  induction n with
  | zero => simp [copyScheduleGraph, copyScheduleOutside, copySchedulePath, finalCopyParity, copyPathParity]
  | succ n ih =>
    change transferCopySign (t (Fin.last n)) *
      copyScheduleGraph g pivot n (copyScheduleOutside n a)
        (copySchedulePath n (fun j => t j.castSucc) i) = _
    rw [ih]
    have ht : Fin.snoc (fun j => t j.castSucc) (t (Fin.last n)) = t := by
      ext j
      refine Fin.lastCases ?_ (fun k => ?_) j <;> simp
    rw [← ht, finalCopyParity_snoc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_assoc]

theorem copyScheduleGraph_fresh_to_positive {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ) (a i : I) :
    copyScheduleGraph g pivot n (copyScheduleOutside n a) (copySchedulePositive n i) = g a i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change transferCopySign true *
      copyScheduleGraph g pivot n (copyScheduleOutside n a) (copySchedulePositive n i) = _
    simpa [transferCopySign] using ih

/-- A regular original word has the same signed edge to every future active
pivot. The hypothesis refers only to the initial graph's off-diagonal edges. -/
theorem copyScheduleGraph_path_to_positive {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ) (i a : I)
    (hp : ∀ k < n, g i (pivot k) = 1) (ha : g i a = 1) (t : Fin n → Bool) :
    copyScheduleGraph g pivot n (copySchedulePath n t i) (copySchedulePositive n a) =
      finalCopyParity t := by
  induction n generalizing a with
  | zero => simpa [copyScheduleGraph, copySchedulePath, copySchedulePositive, finalCopyParity, copyPathParity] using ha
  | succ n ih =>
    change (if t (Fin.last n) = true then
      transferCopySign (t (Fin.last n)) * copyScheduleGraph g pivot n
        (copySchedulePath n (fun j => t j.castSucc) i) (copySchedulePositive n a)
      else transferCopySign (t (Fin.last n)) * copyScheduleGraph g pivot n
        (copySchedulePath n (fun j => t j.castSucc) i) (copySchedulePositive n (pivot n))) = _
    have hprev : ∀ k < n, g i (pivot k) = 1 := fun k hk => hp k (by omega)
    rw [ih a hprev ha, ih (pivot n) hprev (hp n (by omega))]
    split_ifs <;>
      have ht : Fin.snoc (fun j => t j.castSucc) (t (Fin.last n)) = t := by
        ext j
        refine Fin.lastCases ?_ (fun k => ?_) j <;> simp
    all_goals rw [← ht, finalCopyParity_snoc]; simp

/-- The same regular row holds against every anchor not yet used. -/
theorem copyScheduleGraph_path_to_fresh {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ) (i a : I)
    (ha : g i a = 1) (t : Fin n → Bool) :
    copyScheduleGraph g pivot n (copySchedulePath n t i) (copyScheduleOutside n a) =
      finalCopyParity t := by
  induction n with
  | zero => simpa [copyScheduleGraph, copySchedulePath, copyScheduleOutside, finalCopyParity, copyPathParity] using ha
  | succ n ih =>
    change transferCopySign (t (Fin.last n)) * copyScheduleGraph g pivot n
      (copySchedulePath n (fun j => t j.castSucc) i) (copyScheduleOutside n a) = _
    rw [ih]
    have ht : Fin.snoc (fun j => t j.castSucc) (t (Fin.last n)) = t := by
      ext j
      refine Fin.lastCases ?_ (fun k => ?_) j <;> simp
    rw [← ht, finalCopyParity_snoc]
    simp

end Ostmann

end OAI
