import OAI.Probability.FreeIsing.Model

namespace OAI

noncomputable section

namespace Problem367

abbrev ReducedTail {d : ℕ} (c : Fin d) (n : ℕ) :=
  {w : List (Fin d) // w.length = n ∧ List.IsChain (fun a b => a ≠ b) (c :: w)}

abbrev TreeShell (d n : ℕ) := {v : TreeVertex d // v.1.length = n}

instance reducedTailFinite {d : ℕ} (c : Fin d) (n : ℕ) : Finite (ReducedTail c n) :=
  Finite.of_injective (β := List.Vector (Fin d) n)
    (fun w : ReducedTail c n => (⟨w.1, w.2.1⟩ : List.Vector (Fin d) n))
    (fun _ _ h => Subtype.ext (congrArg (fun w : List.Vector (Fin d) n => w.1) h))

instance reducedTailFintype {d : ℕ} (c : Fin d) (n : ℕ) : Fintype (ReducedTail c n) :=
  Fintype.ofFinite _

instance treeShellFinite (d n : ℕ) : Finite (TreeShell d n) :=
  Finite.of_injective (β := List.Vector (Fin d) n)
    (fun w : TreeShell d n => (⟨w.1.1, w.2⟩ : List.Vector (Fin d) n))
    (fun _ _ h => Subtype.ext (Subtype.ext
      (congrArg (fun w : List.Vector (Fin d) n => w.1) h)))

instance treeShellFintype (d n : ℕ) : Fintype (TreeShell d n) :=
  Fintype.ofFinite _

def reducedTailSuccEquiv {d : ℕ} (c : Fin d) (n : ℕ) :
    ReducedTail c (n + 1) ≃ Σ a : {a : Fin d // c ≠ a}, ReducedTail a.1 n where
  toFun w := by
    rcases w with ⟨w, hlen, hchain⟩
    cases w with
    | nil => simp at hlen
    | cons a w =>
      exact ⟨⟨a, (List.isChain_cons_cons.mp hchain).1⟩,
        ⟨w, by simpa using hlen, (List.isChain_cons_cons.mp hchain).2⟩⟩
  invFun w := ⟨w.1.1 :: w.2.1,
    by simp [w.2.2.1], List.isChain_cons_cons.mpr ⟨w.1.2, w.2.2.2⟩⟩
  left_inv w := by
    rcases w with ⟨w, hlen, hchain⟩
    cases w with
    | nil => simp at hlen
    | cons a w => rfl
  right_inv w := by
    rcases w with ⟨⟨a, ha⟩, ⟨w, hlen, hchain⟩⟩
    rfl

def treeShellSuccEquiv (d n : ℕ) :
    TreeShell d (n + 1) ≃ Σ c : Fin d, ReducedTail c n where
  toFun w := by
    rcases w with ⟨⟨w, hchain⟩, hlen⟩
    cases w with
    | nil => simp at hlen
    | cons a w => exact ⟨a, ⟨w, by simpa using hlen, hchain⟩⟩
  invFun w := ⟨⟨w.1 :: w.2.1, w.2.2.2⟩, by simp [w.2.2.1]⟩
  left_inv w := by
    rcases w with ⟨⟨w, hchain⟩, hlen⟩
    cases w with
    | nil => simp at hlen
    | cons a w => rfl
  right_inv w := by
    rcases w with ⟨a, ⟨w, hlen, hchain⟩⟩
    rfl

def reducedTailZeroEquiv {d : ℕ} (c : Fin d) : ReducedTail c 0 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], by simp⟩
  left_inv w := by
    apply Subtype.ext
    exact (List.length_eq_zero_iff.mp w.2.1).symm
  right_inv _ := rfl

def treeShellZeroEquiv (d : ℕ) : TreeShell d 0 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨⟨[], by simp⟩, rfl⟩
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    exact (List.length_eq_zero_iff.mp w.2).symm
  right_inv _ := rfl

@[simp] theorem card_reducedTail {d : ℕ} (c : Fin d) (n : ℕ) :
    Fintype.card (ReducedTail c n) = (d - 1) ^ n := by
  induction n generalizing c with
  | zero =>
    simpa using Fintype.card_congr (reducedTailZeroEquiv c)
  | succ n ih =>
    rw [Fintype.card_congr (reducedTailSuccEquiv c n), Fintype.card_sigma]
    simp only [ih]
    have hc : Fintype.card {a : Fin d // c ≠ a} = d - 1 := by
      simp
    simp [hc, pow_succ, Nat.mul_comm]

@[simp] theorem card_treeShell_zero (d : ℕ) : Fintype.card (TreeShell d 0) = 1 := by
  simpa using Fintype.card_congr (treeShellZeroEquiv d)

@[simp] theorem card_treeShell_succ (d n : ℕ) :
    Fintype.card (TreeShell d (n + 1)) = d * (d - 1) ^ n := by
  rw [Fintype.card_congr (treeShellSuccEquiv d n), Fintype.card_sigma]
  simp

abbrev TreeBall (d n : ℕ) := {v : TreeVertex d // v.1.length ≤ n}

def treeBallEquivSigma (d n : ℕ) :
    TreeBall d n ≃ Σ k : Fin (n + 1), TreeShell d k.1 where
  toFun w := ⟨⟨w.1.1.length, Nat.lt_succ_of_le w.2⟩, ⟨w.1, rfl⟩⟩
  invFun w := ⟨w.2.1, by
    rw [w.2.2]
    exact Nat.le_of_lt_succ w.1.2⟩
  left_inv _ := rfl
  right_inv w := by
    rcases w with ⟨⟨k, hk⟩, ⟨v, hv⟩⟩
    cases hv
    rfl

instance treeBallFinite (d n : ℕ) : Finite (TreeBall d n) :=
  Finite.of_equiv (Σ k : Fin (n + 1), TreeShell d k.1) (treeBallEquivSigma d n).symm

instance treeBallFintype (d n : ℕ) : Fintype (TreeBall d n) := Fintype.ofFinite _

theorem finite_treeShell (d n : ℕ) : {v : TreeVertex d | v.1.length = n}.Finite :=
  @Set.toFinite _ _ (treeShellFinite d n)

theorem finite_treeBall (d n : ℕ) : {v : TreeVertex d | v.1.length ≤ n}.Finite :=
  @Set.toFinite _ _ (treeBallFinite d n)

@[simp] theorem card_treeBall (d n : ℕ) :
    Fintype.card (TreeBall d n) = 1 + d * ∑ k ∈ Finset.range n, (d - 1) ^ k := by
  rw [Fintype.card_congr (treeBallEquivSigma d n), Fintype.card_sigma]
  rw [Fin.sum_univ_eq_sum_range (fun k => Fintype.card (TreeShell d k)),
    Finset.sum_range_succ']
  simp [Finset.mul_sum, Nat.add_comm]

def treeShellFinset (d n : ℕ) : Finset (TreeVertex d) :=
  Finset.univ.map ⟨fun v : TreeShell d n => v.1, Subtype.val_injective⟩

def treeBallFinset (d n : ℕ) : Finset (TreeVertex d) :=
  Finset.univ.map ⟨fun v : TreeBall d n => v.1, Subtype.val_injective⟩

@[simp] theorem mem_treeShellFinset (d n : ℕ) (v : TreeVertex d) :
    v ∈ treeShellFinset d n ↔ v.1.length = n := by
  simp [treeShellFinset]

@[simp] theorem mem_treeBallFinset (d n : ℕ) (v : TreeVertex d) :
    v ∈ treeBallFinset d n ↔ v.1.length ≤ n := by
  simp [treeBallFinset]

@[simp] theorem card_treeShellFinset_zero (d : ℕ) : (treeShellFinset d 0).card = 1 := by
  simp [treeShellFinset]

@[simp] theorem card_treeShellFinset_succ (d n : ℕ) :
    (treeShellFinset d (n + 1)).card = d * (d - 1) ^ n := by
  simp [treeShellFinset]

@[simp] theorem card_treeBallFinset (d n : ℕ) :
    (treeBallFinset d n).card = 1 + d * ∑ k ∈ Finset.range n, (d - 1) ^ k := by
  simp [treeBallFinset]

theorem monotone_treeBallFinset (d : ℕ) : Monotone (treeBallFinset d) := by
  intro n m hnm v hv
  exact (mem_treeBallFinset d m v).mpr (((mem_treeBallFinset d n v).mp hv).trans hnm)

@[simp] theorem iUnion_treeBallFinset (d : ℕ) :
    (⋃ n : ℕ, (treeBallFinset d n : Set (TreeVertex d))) = Set.univ := by
  ext v
  simp only [Set.mem_iUnion, Finset.mem_coe, mem_treeBallFinset, Set.mem_univ, iff_true]
  exact ⟨v.1.length, le_rfl⟩

theorem exists_subset_treeBallFinset {d : ℕ} (s : Finset (TreeVertex d)) :
    ∃ n, s ⊆ treeBallFinset d n := by
  classical
  refine ⟨s.sup (fun v => v.1.length), ?_⟩
  intro v hv
  exact (mem_treeBallFinset d _ v).mpr (Finset.le_sup (f := fun w => w.1.length) hv)

theorem sum_treeShell_succ {M : Type*} [AddCommMonoid M]
    (d n : ℕ) (f : List (Fin d) → M) :
    (∑ v : TreeShell d (n + 1), f v.1.1) =
      ∑ c : Fin d, ∑ w : ReducedTail c n, f (c :: w.1) := by
  calc
    (∑ v : TreeShell d (n + 1), f v.1.1) =
        ∑ s : Σ c : Fin d, ReducedTail c n, f (s.1 :: s.2.1) :=
      ((treeShellSuccEquiv d n).symm.sum_comp (fun v => f v.1.1)).symm
    _ = _ := Fintype.sum_sigma _

theorem sum_reducedTail_succ {M : Type*} [AddCommMonoid M]
    {d : ℕ} (c : Fin d) (n : ℕ) (f : List (Fin d) → M) :
    (∑ w : ReducedTail c (n + 1), f w.1) =
      ∑ a : {a : Fin d // c ≠ a}, ∑ w : ReducedTail a.1 n, f (a.1 :: w.1) := by
  calc
    (∑ w : ReducedTail c (n + 1), f w.1) =
        ∑ s : Σ a : {a : Fin d // c ≠ a}, ReducedTail a.1 n, f (s.1.1 :: s.2.1) :=
      ((reducedTailSuccEquiv c n).symm.sum_comp (fun w => f w.1)).symm
    _ = _ := Fintype.sum_sigma _

@[simp] theorem sum_treeShell_zero {M : Type*} [AddCommMonoid M]
    (d : ℕ) (f : List (Fin d) → M) : (∑ v : TreeShell d 0, f v.1.1) = f [] := by
  calc
    (∑ v : TreeShell d 0, f v.1.1) = ∑ _ : Unit, f [] :=
      ((treeShellZeroEquiv d).symm.sum_comp (fun v => f v.1.1)).symm
    _ = _ := by simp

@[simp] theorem sum_reducedTail_zero {M : Type*} [AddCommMonoid M]
    {d : ℕ} (c : Fin d) (f : List (Fin d) → M) :
    (∑ w : ReducedTail c 0, f w.1) = f [] := by
  calc
    (∑ w : ReducedTail c 0, f w.1) = ∑ _ : Unit, f [] :=
      ((reducedTailZeroEquiv c).symm.sum_comp (fun w => f w.1)).symm
    _ = _ := by simp

end Problem367

end

end OAI
