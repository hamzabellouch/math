import OAI.Probability.DilutedSpin.Core

namespace OAI

section
section
open scoped BigOperators

namespace DilutedSpinGlass.PrescribedTree

/-- The unique labeled position in a unary tree. -/
def singleLeaf : (n : ℕ) → Leaf (single n)
  | 0 => ()
  | n+1 => ⟨0, singleLeaf n⟩

/-- The old paths keep their separate labels when a genuine fresh branch is added. -/
def oldLeaf : {n : ℕ} → (S : PrescribedTree n) → (v : Internal S) →
    Leaf S → Leaf (grow S v)
  | 0, .leaf, v, _ => nomatch v
  | n+1, .node k C, v, a => by
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none => exact ⟨a.1.succ, a.2⟩
    | some v =>
      obtain ⟨i,v⟩ := v
      refine ⟨a.1, ?_⟩
      by_cases h : a.1 = i
      · have b : Leaf (C i) := h ▸ a.2
        simpa only [grow, h, Function.update_self] using oldLeaf (C i) v b
      · simpa only [grow, Function.update_of_ne h] using a.2

/-- The single distinguished newly added replica position. -/
def newLeaf : {n : ℕ} → (S : PrescribedTree n) → (v : Internal S) → Leaf (grow S v)
  | 0, .leaf, v => nomatch v
  | n+1, .node k C, v => by
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none => exact ⟨0, singleLeaf n⟩
    | some v =>
      obtain ⟨i,v⟩ := v
      refine ⟨i, ?_⟩
      simpa only [grow, Function.update_self] using newLeaf (C i) v

/-- Split depth compares positions, never the sampled spin values. Equal
positions have split depth n; distinct positions split strictly before n. -/
def splitDepth : {n : ℕ} → (S : PrescribedTree n) → Leaf S → Leaf S → ℕ
  | 0, .leaf, _, _ => 0
  | _+1, .node _ C, a, b => if h : a.1 = b.1 then
      1 + splitDepth (C a.1) a.2 (h.symm ▸ b.2) else 0

@[simp] theorem splitDepth_self {n : ℕ} (S : PrescribedTree n) (a : Leaf S) :
    splitDepth S a a = n := by
  induction S with
  | leaf => rfl
  | @node n k C ih => simp [splitDepth, ih, Nat.add_comm]

theorem splitDepth_le {n : ℕ} (S : PrescribedTree n) (a b : Leaf S) :
    splitDepth S a b ≤ n := by
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    rcases a with ⟨i,a⟩
    rcases b with ⟨j,b⟩
    change (if h : i = j then 1 + splitDepth (C i) a (h.symm ▸ b) else 0) ≤ n+1
    split_ifs with h
    · have := ih i a (h.symm ▸ b)
      omega
    · exact Nat.zero_le _

theorem splitDepth_eq_height {n : ℕ} (S : PrescribedTree n) (a b : Leaf S) :
    splitDepth S a b = n ↔ a = b := by
  induction S with
  | leaf => cases a; cases b; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | @node n k C ih =>
    rcases a with ⟨i,a⟩
    rcases b with ⟨j,b⟩
    constructor
    · intro h
      change (if hij : i = j then 1 + splitDepth (C i) a (hij.symm ▸ b) else 0) = n+1 at h
      by_cases hij : i = j
      · subst j
        rw [dite_eq_left rfl] at h
        change 1 + splitDepth (C i) a b = n+1 at h
        have hsub : a = b := (ih i a b).mp (by omega)
        subst b
        rfl
      · rw [dite_eq_right hij] at h
        omega
    · intro hab
      rw [hab]
      exact splitDepth_self _ _

variable {Ω : Type}

theorem pathAt_singleLeaf (n : ℕ) (x : Sample Ω (single n)) :
    pathAt (single n) (singleLeaf n) x = singlePath n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((x 0).1, pathAt (single n) (singleLeaf n) (x 0).2) =
      ((x 0).1, singlePath n (x 0).2)
    rw [ih]

theorem pathAt_node {n : ℕ} (k : ℕ+) (C : Fin k → PrescribedTree n)
    (i : Fin k) (a : Leaf (C i)) (x : Sample Ω (.node k C)) :
    pathAt (.node k C) ⟨i,a⟩ x = ((x i).1, pathAt (C i) a (x i).2) := rfl

theorem pathAt_cast {n : ℕ} (A B : PrescribedTree n) (h : B = A)
    (a : Leaf A) (x : Ω × Sample Ω B) :
    (x.1, pathAt B (cast (congrArg Leaf h.symm) a) x.2) =
      ((cast (congrArg (fun R => Ω × Sample Ω R) h) x).1,
        pathAt A a (cast (congrArg (fun R => Ω × Sample Ω R) h) x).2) := by
  subst B
  rfl

theorem pathAt_oldLeaf {n : ℕ} (S : PrescribedTree n) (v : Internal S)
    (a : Leaf S) (x : Sample Ω (grow S v)) :
    pathAt (grow S v) (oldLeaf S v a) x = pathAt S a (oldSample S v x) := by
  induction S with
  | leaf => exact v.elim
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none => rfl
    | some z =>
      obtain ⟨i,v⟩ := z
      obtain ⟨j,a⟩ := a
      change _ = ((oldSample (.node k C) (some ⟨i,v⟩) x j).1,
        pathAt (C j) a (oldSample (.node k C) (some ⟨i,v⟩) x j).2)
      let C' := Function.update C i (grow (C i) v)
      by_cases h : j = i
      · subst j
        let y : Ω × Sample Ω (grow (C i) v) :=
          cast (congrArg (fun R => Ω × Sample Ω R) (Function.update_self i (grow (C i) v) C)) (x i)
        have hc := pathAt_cast (grow (C i) v) (C' i)
          (Function.update_self ..) (oldLeaf (C i) v a) (x i)
        have hh := congrArg (fun z => (y.1,z)) (ih i v a y.2)
        erw [oldLeaf.eq_1, oldSample.eq_1]
        dsimp only [id]
        simp only
        exact hc.trans hh
      · have hc := pathAt_cast (C j) (C' j) (Function.update_of_ne h ..) a (x j)
        erw [oldLeaf.eq_1, oldSample.eq_1]
        dsimp only [id]
        simp only [dite_eq_right h]
        exact hc

theorem pathAt_newLeaf {n : ℕ} (S : PrescribedTree n) (v : Internal S)
    (x : Sample Ω (grow S v)) :
    pathAt (grow S v) (newLeaf S v) x = newPath S v x := by
  induction S with
  | leaf => exact v.elim
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none => exact congrArg (fun y => ((x 0).1,y)) (pathAt_singleLeaf n (x 0).2)
    | some z =>
      obtain ⟨i,v⟩ := z
      let C' := Function.update C i (grow (C i) v)
      let y : Ω × Sample Ω (grow (C i) v) :=
        cast (congrArg (fun R => Ω × Sample Ω R) (Function.update_self i (grow (C i) v) C)) (x i)
      have hc := pathAt_cast (grow (C i) v) (C' i)
        (Function.update_self ..) (newLeaf (C i) v) (x i)
      have hh := congrArg (fun z => (y.1,z)) (ih i v y.2)
      erw [newLeaf.eq_1, newPath.eq_1]
      dsimp only [id]
      exact hc.trans hh

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The deepest reference prefix and its forbidden reference-containing
children. This describes the whole compatible choice set, including both old
unused leaves and fresh divergences in reference-free subtrees. -/
inductive Divergence : {n : ℕ} → PrescribedTree n → Type
  | here {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
      (excluded : Finset (Fin k)) : Divergence (.node k C)
  | descend {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
      (i : Fin k) (next : Divergence (C i)) : Divergence (.node k C)

namespace Divergence

def oldAllowed : {n : ℕ} → {S : PrescribedTree n} → Divergence S → Leaf S → Prop
  | _+1, .node _ _, .here J, a => a.1 ∉ J
  | _+1, .node _ _, .descend i D, a => ∃ h : a.1 = i, oldAllowed D (h ▸ a.2)

def freshAllowed : {n : ℕ} → {S : PrescribedTree n} → Divergence S → Internal S → Prop
  | _+1, .node k C, .here J, v =>
      match (v : Option ((i : Fin k) × Internal (C i))) with
      | none => True
      | some ⟨i,_⟩ => i ∉ J
  | _+1, .node k C, .descend i D, v =>
      match (v : Option ((j : Fin k) × Internal (C j))) with
      | none => False
      | some ⟨j,v⟩ => ∃ h : j = i, freshAllowed D (h ▸ v)

noncomputable def coefficient : {n : ℕ} → {S : PrescribedTree n} →
    Divergence S → (Fin (n+1) → ℝ) → ℝ
  | _+1, .node _ _, .here J, m => m 0 - (J.card : ℝ)*m 1
  | _+1, .node _ _, .descend _ D, m => coefficient D (fun j => m j.succ)

end Divergence

/-- Full cancellation inside a reference-free subtree, indexed by actual
leaf positions and actual internal vertices. -/
theorem all_choices_total {n : ℕ} (S : PrescribedTree n) (m : Fin (n+1) → ℝ)
    (hend : m (Fin.last n) = 1) :
    (∑ _a : Leaf S, (1 : ℝ)) + (∑ v : Internal S, gamma S m v) = m 0 := by
  have hcard : Fintype.card (Leaf S) = leaves S := by
    clear hend m
    induction S with
    | leaf => exact Fintype.card_unit
    | @node height arity children inductionHypotheses =>
      change Fintype.card ((index : Fin arity) × Leaf (children index)) = _
      simp [Fintype.card_sigma, leaves, inductionHypotheses]
  rw [sum_gamma]
  simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_one, hend]
  ring

/-- The signed normalizing sum of ALL eligible old-or-fresh choices with a
specified deepest reference prefix is independent of all unused old branches.
Unlike reference_total, this is stated on the actual global choice indices. -/
theorem divergence_choice_total {n : ℕ} {S : PrescribedTree n}
    (D : Divergence S) (m : Fin (n+1) → ℝ) (hend : m (Fin.last n) = 1) :
    (∑ a : Leaf S, if D.oldAllowed a then (1 : ℝ) else 0) +
      (∑ v : Internal S, if D.freshAllowed v then gamma S m v else 0) = D.coefficient m := by
  induction D with
  | @here n k C J =>
    change (∑ a : (i : Fin k) × Leaf (C i), _) +
      (∑ v : Option ((i : Fin k) × Internal (C i)), _) = _
    rw [Fintype.sum_sigma, Fintype.sum_option, Fintype.sum_sigma]
    have ho_def (i : Fin k) (a : Leaf (C i)) :
        (Divergence.here J : Divergence (.node k C)).oldAllowed (⟨i,a⟩ : Leaf (.node k C)) ↔ i ∉ J := by
      erw [Divergence.oldAllowed.eq_1]
    simp_rw [ho_def]
    simp! only [Divergence.freshAllowed, Divergence.coefficient, gamma, ite_true]
    change (∑ i, ∑ _a : Leaf (C i), if i ∉ J then (1:ℝ) else 0) +
      (m 0 - (k:ℝ)*m 1 + ∑ i, ∑ v : Internal (C i),
        if i ∉ J then gamma (C i) (fun j => m j.succ) v else 0) =
      m 0 - (J.card:ℝ)*m 1
    have hm' : (fun j : Fin (n+1) => m j.succ) (Fin.last n) = 1 := hend
    have ht (i : Fin k) :
        (∑ a : Leaf (C i), if i ∉ J then (1:ℝ) else 0) +
          (∑ v : Internal (C i), if i ∉ J then gamma (C i) (fun j => m j.succ) v else 0) =
          if i ∉ J then m 1 else 0 := by
      by_cases hi : i ∉ J
      · simp only [hi]
        exact all_choices_total (C i) _ hm'
      · simp only [hi, ite_false, Finset.sum_const_zero, zero_add]
    calc
      _ = m 0 - (k:ℝ)*m 1 + ∑ i, (
          (∑ a : Leaf (C i), if i ∉ J then (1:ℝ) else 0) +
          (∑ v : Internal (C i), if i ∉ J then gamma (C i) (fun j => m j.succ) v else 0)) := by
        rw [Finset.sum_add_distrib]; ring
      _ = m 0 - (k:ℝ)*m 1 + ∑ i : Fin k, if i ∉ J then m 1 else 0 := by simp_rw [ht]
      _ = _ := by
        rw [← Finset.sum_filter]
        have hset : Finset.univ.filter (fun i : Fin k => i ∉ J) = Finset.univ \ J := by ext i; simp
        rw [hset, Finset.sum_const, nsmul_eq_mul, Finset.card_sdiff, Finset.inter_univ,
          Nat.cast_sub (Finset.card_le_card (Finset.subset_univ J))]
        simp only [Finset.card_univ, Fintype.card_fin]
        ring
  | @descend n k C i D ih =>
    change (∑ a : (j : Fin k) × Leaf (C j), _) +
      (∑ v : Option ((j : Fin k) × Internal (C j)), _) = _
    rw [Fintype.sum_sigma, Fintype.sum_option, Fintype.sum_sigma]
    have ho_def (j : Fin k) (a : Leaf (C j)) :
        (Divergence.descend i D).oldAllowed (⟨j,a⟩ : Leaf (.node k C)) ↔
          ∃ h : j = i, D.oldAllowed (h ▸ a) := by
      erw [Divergence.oldAllowed.eq_2]
    simp_rw [ho_def]
    simp! only [Divergence.freshAllowed, Divergence.coefficient, gamma, ite_false]
    change (∑ j, ∑ a : Leaf (C j), if ∃ h : j = i, D.oldAllowed (h ▸ a) then (1:ℝ) else 0) +
      (0 + ∑ j, ∑ v : Internal (C j), if ∃ h : j = i, D.freshAllowed (h ▸ v) then
        gamma (C j) (fun q => m q.succ) v else 0) = D.coefficient (fun q => m q.succ)
    rw [zero_add]
    have ho (j : Fin k) :
        (∑ a : Leaf (C j), if ∃ h : j = i, D.oldAllowed (h ▸ a) then (1:ℝ) else 0) =
          if j = i then (∑ a : Leaf (C i), if D.oldAllowed a then (1:ℝ) else 0) else 0 := by
      by_cases h : j = i
      · subst j; simp
      · simp [h]
    have hf (j : Fin k) :
        (∑ v : Internal (C j), if ∃ h : j = i, D.freshAllowed (h ▸ v) then
          gamma (C j) (fun q => m q.succ) v else 0) =
          if j = i then (∑ v : Internal (C i), if D.freshAllowed v then
            gamma (C i) (fun q => m q.succ) v else 0) else 0 := by
      by_cases h : j = i
      · subst j; simp
      · simp [h]
    simp_rw [ho, hf]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact ih _ hend

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Positional split depth of a genuinely fresh branch from an old reference. -/
def freshSplitDepth : {n : ℕ} → (S : PrescribedTree n) → Internal S → Leaf S → ℕ
  | 0, .leaf, v, _ => nomatch v
  | _+1, .node k C, v, a =>
    match (v : Option ((i : Fin k) × Internal (C i))) with
    | none => 0
    | some ⟨i,v⟩ => if h : a.1 = i then 1 + freshSplitDepth (C i) v (h ▸ a.2) else 0

theorem splitDepth_cast {n : ℕ} (A B : PrescribedTree n) (h : B = A) (a b : Leaf A) :
    splitDepth B (cast (congrArg Leaf h.symm) a) (cast (congrArg Leaf h.symm) b) =
      splitDepth A a b := by
  subst B
  rfl

/-- Fresh splitting refers to the enlarged tree's actual labeled positions. -/
theorem splitDepth_new_old {n : ℕ} (S : PrescribedTree n) (v : Internal S) (a : Leaf S) :
    splitDepth (grow S v) (newLeaf S v) (oldLeaf S v a) = freshSplitDepth S v a := by
  induction S with
  | leaf => exact v.elim
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      change (if h : (0 : Fin (k+1)) = a.1.succ then _ else 0) = 0
      rw [dite_eq_right (Ne.symm (Fin.succ_ne_zero a.1))]
    | some v =>
      obtain ⟨i,v⟩ := v
      obtain ⟨j,a⟩ := a
      by_cases h : j = i
      · subst j
        let C' := Function.update C i (grow (C i) v)
        have heq : C' i = grow (C i) v := Function.update_self ..
        have hc := splitDepth_cast (grow (C i) v) (C' i) heq
          (newLeaf (C i) v) (oldLeaf (C i) v a)
        erw [newLeaf.eq_1, oldLeaf.eq_1]
        dsimp only [id]
        simp only [dite_eq_left]
        change (if h : i = i then 1 + splitDepth (C' i)
          (cast (congrArg Leaf heq.symm) (newLeaf (C i) v))
          (cast (congrArg Leaf heq.symm) (oldLeaf (C i) v a)) else 0) =
          (if h : i = i then 1 + freshSplitDepth (C i) v a else 0)
        simp only
        rw [hc, ih]
      · erw [newLeaf.eq_1, oldLeaf.eq_1]
        dsimp only [id]
        simp only [dite_eq_right h]
        change (if h' : i = j then _ else 0) = (if h' : j = i then _ else 0)
        rw [dite_eq_right (Ne.symm h), dite_eq_right h]

noncomputable def childRefs {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    (R : Finset (Leaf (.node k C))) (i : Fin k) : Finset (Leaf (C i)) :=
  Finset.univ.filter (fun a => (⟨i,a⟩ : Leaf (.node k C)) ∈ R)

@[simp] theorem mem_childRefs {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    (R : Finset (Leaf (.node k C))) (i : Fin k) (a : Leaf (C i)) :
    a ∈ childRefs R i ↔ (⟨i,a⟩ : Leaf (.node k C)) ∈ R := by
  simp [childRefs]

/-- A proposed fresh split at depth d along a reference path. Every child
containing any reference through the chosen prefix is forbidden. -/
noncomputable def referenceDivergence : {n : ℕ} → (S : PrescribedTree n) →
    (a : Leaf S) → (d : ℕ) → d < n → Finset (Leaf S) → Divergence S
  | 0, .leaf, _, d, hd, _ => (Nat.not_lt_zero d hd).elim
  | _+1, .node _ _, _, 0, _, R => .here (R.image (fun a => a.1))
  | n+1, .node _ C, a, d+1, hd, R => .descend a.1
      (referenceDivergence (C a.1) a.2 d (by omega) (childRefs R a.1))

/-- Shared-prefix equations determine the same allowed old-or-fresh set as
references; this positional definition does not examine any spin values. -/
def matchesOldProfile {n : ℕ} (S : PrescribedTree n) (R : Finset (Leaf S))
    (a : Leaf S) (d : ℕ) (b : Leaf S) : Prop :=
  ∀ r ∈ R, splitDepth S b r = min d (splitDepth S a r)

def matchesFreshProfile {n : ℕ} (S : PrescribedTree n) (R : Finset (Leaf S))
    (a : Leaf S) (d : ℕ) (v : Internal S) : Prop :=
  ∀ r ∈ R, freshSplitDepth S v r = min d (splitDepth S a r)

/-- A reference itself is never an eligible old leaf. -/
theorem matchesOldProfile_not_mem {n : ℕ} (S : PrescribedTree n) (R : Finset (Leaf S))
    (a b : Leaf S) {d : ℕ} (hd : d < n) (h : matchesOldProfile S R a d b) : b ∉ R := by
  intro hb
  have h' := h b hb
  rw [splitDepth_self] at h'
  have := min_le_left d (splitDepth S a b)
  omega

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem splitDepth_same_child {n : ℕ} {k : ℕ+} (C : Fin k → PrescribedTree n)
    (i : Fin k) (a b : Leaf (C i)) :
    splitDepth (.node k C) ⟨i,a⟩ ⟨i,b⟩ = 1 + splitDepth (C i) a b := by
  change (if h : i = i then 1 + splitDepth (C i) a (h.symm ▸ b) else 0) = _
  simp

theorem splitDepth_diff_child {n : ℕ} {k : ℕ+} (C : Fin k → PrescribedTree n)
    (i j : Fin k) (hij : i ≠ j) (a : Leaf (C i)) (b : Leaf (C j)) :
    splitDepth (.node k C) ⟨i,a⟩ ⟨j,b⟩ = 0 := by
  change (if h : i = j then 1 + splitDepth (C i) a (h.symm ▸ b) else 0) = 0
  rw [dite_eq_right hij]

theorem splitDepth_node_zero {n : ℕ} {k : ℕ+} (C : Fin k → PrescribedTree n)
    (a b : Leaf (.node k C)) :
    splitDepth (.node k C) a b = 0 ↔ a.1 ≠ b.1 := by
  obtain ⟨i,a⟩ := a
  obtain ⟨j,b⟩ := b
  by_cases h : i = j
  · subst j
    rw [splitDepth_same_child]
    simp
  · rw [splitDepth_diff_child C i j h]
    simp [h]

/-- Ancestry constraints with ALL existing references, not merely a local
subtree, are exactly the global eligible-old-leaf selector. -/
theorem referenceDivergence_oldAllowed {n : ℕ} (S : PrescribedTree n)
    (a : Leaf S) (d : ℕ) (hd : d < n) (R : Finset (Leaf S)) (ha : a ∈ R) (b : Leaf S) :
    (referenceDivergence S a d hd R).oldAllowed b ↔ matchesOldProfile S R a d b := by
  induction S generalizing d with
  | leaf => omega
  | @node n k C ih =>
    cases d with
    | zero =>
      change b.1 ∉ R.image (fun a => a.1) ↔
        ∀ r ∈ R, splitDepth (.node k C) b r = 0
      constructor
      · intro h r hr
        apply (splitDepth_node_zero C b r).mpr
        intro heq
        exact h (Finset.mem_image.mpr ⟨r,hr,heq.symm⟩)
      · intro h hb
        obtain ⟨r,hr,heq⟩ := Finset.mem_image.mp hb
        exact ((splitDepth_node_zero C b r).mp (h r hr)) heq.symm
    | succ d =>
      obtain ⟨i,a⟩ := a
      obtain ⟨j,b⟩ := b
      have hd' : d < n := by omega
      by_cases hji : j = i
      · subst j
        have hchild : a ∈ childRefs R i := (mem_childRefs R i a).mpr ha
        have hreduce : (referenceDivergence (.node k C) ⟨i,a⟩ (d+1) hd R).oldAllowed ⟨i,b⟩ ↔
            (referenceDivergence (C i) a d hd' (childRefs R i)).oldAllowed b := by
          change (∃ h : i = i,
            (referenceDivergence (C i) a d hd' (childRefs R i)).oldAllowed (h ▸ b)) ↔ _
          simp
        rw [hreduce, ih i a d hd' (childRefs R i) hchild b]
        constructor
        · intro h r hr
          obtain ⟨j,r⟩ := r
          by_cases hji : j = i
          · subst j
            have hh := h r ((mem_childRefs R i r).mpr hr)
            rw [splitDepth_same_child, splitDepth_same_child]
            omega
          · rw [splitDepth_diff_child C i j (Ne.symm hji),
              splitDepth_diff_child C i j (Ne.symm hji)]
            exact (Nat.min_zero _).symm
        · intro h r hr
          have hh := h ⟨i,r⟩ ((mem_childRefs R i r).mp hr)
          rw [splitDepth_same_child, splitDepth_same_child] at hh
          omega
      · have hnone : ¬(referenceDivergence (.node k C) ⟨i,a⟩ (d+1) hd R).oldAllowed ⟨j,b⟩ := by
          change ¬∃ h : j = i, _
          exact fun ⟨h,_⟩ => hji h
        rw [iff_false_left hnone]
        intro h
        have hh := h ⟨i,a⟩ ha
        rw [splitDepth_diff_child C j i hji] at hh
        have hhself : splitDepth (.node k C) (⟨i,a⟩ : Leaf (.node k C)) ⟨i,a⟩ = n+1 :=
          splitDepth_self _ _
        rw [hhself] at hh
        omega

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem freshSplitDepth_same_child {n : ℕ} {k : ℕ+} (C : Fin k → PrescribedTree n)
    (i : Fin k) (v : Internal (C i)) (a : Leaf (C i)) :
    freshSplitDepth (.node k C) (some ⟨i,v⟩) ⟨i,a⟩ = 1 + freshSplitDepth (C i) v a := by
  change (if h : i = i then 1 + freshSplitDepth (C i) v (h ▸ a) else 0) = _
  simp

theorem freshSplitDepth_diff_child {n : ℕ} {k : ℕ+} (C : Fin k → PrescribedTree n)
    (i j : Fin k) (hij : j ≠ i) (v : Internal (C i)) (a : Leaf (C j)) :
    freshSplitDepth (.node k C) (some ⟨i,v⟩) ⟨j,a⟩ = 0 := by
  change (if h : j = i then 1 + freshSplitDepth (C i) v (h ▸ a) else 0) = 0
  rw [dite_eq_right hij]

theorem freshSplitDepth_node_zero {n : ℕ} {k : ℕ+} (C : Fin k → PrescribedTree n)
    (i : Fin k) (v : Internal (C i)) (a : Leaf (.node k C)) :
    freshSplitDepth (.node k C) (some ⟨i,v⟩) a = 0 ↔ a.1 ≠ i := by
  obtain ⟨j,a⟩ := a
  by_cases h : j = i
  · subst j
    rw [freshSplitDepth_same_child]
    simp
  · rw [freshSplitDepth_diff_child C i j h]
    simp [h]

/-- Fresh divergences satisfy exactly the same all-reference positional profile
as the old-choice selector; the profile is also the actual new leaf's profile
in the enlarged tree, by splitDepth_new_old. -/
theorem referenceDivergence_freshAllowed {n : ℕ} (S : PrescribedTree n)
    (a : Leaf S) (d : ℕ) (hd : d < n) (R : Finset (Leaf S)) (ha : a ∈ R) (v : Internal S) :
    (referenceDivergence S a d hd R).freshAllowed v ↔ matchesFreshProfile S R a d v := by
  induction S generalizing d with
  | leaf => omega
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases d with
    | zero =>
      cases v with
      | none =>
        change True ↔ ∀ r ∈ R, (0 : ℕ) = 0
        simp
      | some v =>
        obtain ⟨i,v⟩ := v
        change i ∉ R.image (fun a => a.1) ↔
          ∀ r ∈ R, freshSplitDepth (.node k C) (some ⟨i,v⟩) r = 0
        constructor
        · intro h r hr
          apply (freshSplitDepth_node_zero C i v r).mpr
          intro heq
          exact h (Finset.mem_image.mpr ⟨r,hr,heq⟩)
        · intro h hb
          obtain ⟨r,hr,heq⟩ := Finset.mem_image.mp hb
          exact ((freshSplitDepth_node_zero C i v r).mp (h r hr)) heq
    | succ d =>
      obtain ⟨i,a⟩ := a
      have hd' : d < n := by omega
      cases v with
      | none =>
        change False ↔ _
        rw [false_iff]
        intro h
        have hh := h ⟨i,a⟩ ha
        change 0 = min (d+1) (splitDepth (.node k C) (⟨i,a⟩ : Leaf (.node k C)) ⟨i,a⟩) at hh
        have hhself : splitDepth (.node k C) (⟨i,a⟩ : Leaf (.node k C)) ⟨i,a⟩ = n+1 :=
          splitDepth_self _ _
        rw [hhself] at hh
        omega
      | some v =>
        obtain ⟨j,v⟩ := v
        by_cases hji : j = i
        · subst j
          have hchild : a ∈ childRefs R i := (mem_childRefs R i a).mpr ha
          have hreduce : (referenceDivergence (.node k C) ⟨i,a⟩ (d+1) hd R).freshAllowed (some ⟨i,v⟩) ↔
              (referenceDivergence (C i) a d hd' (childRefs R i)).freshAllowed v := by
            change (∃ h : i = i,
              (referenceDivergence (C i) a d hd' (childRefs R i)).freshAllowed (h ▸ v)) ↔ _
            simp
          rw [hreduce, ih i a d hd' (childRefs R i) hchild v]
          constructor
          · intro h r hr
            obtain ⟨j,r⟩ := r
            by_cases hji : j = i
            · subst j
              have hh := h r ((mem_childRefs R i r).mpr hr)
              rw [freshSplitDepth_same_child, splitDepth_same_child]
              omega
            · rw [freshSplitDepth_diff_child C i j hji,
                splitDepth_diff_child C i j (Ne.symm hji)]
              exact (Nat.min_zero _).symm
          · intro h r hr
            have hh := h ⟨i,r⟩ ((mem_childRefs R i r).mp hr)
            rw [freshSplitDepth_same_child, splitDepth_same_child] at hh
            omega
        · have hnone : ¬(referenceDivergence (.node k C) ⟨i,a⟩ (d+1) hd R).freshAllowed (some ⟨j,v⟩) := by
            change ¬∃ h : j = i, _
            exact fun ⟨h,_⟩ => hji h
          rw [iff_false_left hnone]
          intro h
          have hh := h ⟨i,a⟩ ha
          rw [freshSplitDepth_diff_child C j i (Ne.symm hji)] at hh
          have hhself : splitDepth (.node k C) (⟨i,a⟩ : Leaf (.node k C)) ⟨i,a⟩ = n+1 :=
            splitDepth_self _ _
          rw [hhself] at hh
          omega

/-- The reference-path normalizing identity over globally admissible old or
fresh labels. No conditioning on sampled spin values occurs in the selector. -/
theorem reference_profile_total {n : ℕ} (S : PrescribedTree n)
    (a : Leaf S) (d : ℕ) (hd : d < n) (R : Finset (Leaf S)) (ha : a ∈ R)
    (m : Fin (n+1) → ℝ) (hend : m (Fin.last n) = 1) :
    (∑ b : Leaf S, if matchesOldProfile S R a d b then (1 : ℝ) else 0) +
      (∑ v : Internal S, if matchesFreshProfile S R a d v then gamma S m v else 0) =
      (referenceDivergence S a d hd R).coefficient m := by
  simp_rw [← referenceDivergence_oldAllowed S a d hd R ha,
    ← referenceDivergence_freshAllowed S a d hd R ha]
  exact divergence_choice_total _ m hend

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Freshness is positional and survives deterministic or atomic spin laws. -/
theorem freshSplitDepth_lt {n : ℕ} (S : PrescribedTree n) (v : Internal S) (a : Leaf S) :
    freshSplitDepth S v a < n := by
  induction S with
  | leaf => exact v.elim
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none => exact Nat.zero_lt_succ n
    | some v =>
      obtain ⟨i,v⟩ := v
      obtain ⟨j,a⟩ := a
      by_cases hji : j = i
      · subst j
        rw [freshSplitDepth_same_child]
        have := ih i v a
        omega
      · rw [freshSplitDepth_diff_child C i j hji]
        omega

/-- Old leaves retain their pairwise positional ancestry under actual grow. -/
theorem splitDepth_old_old {n : ℕ} (S : PrescribedTree n) (v : Internal S) (a b : Leaf S) :
    splitDepth (grow S v) (oldLeaf S v a) (oldLeaf S v b) = splitDepth S a b := by
  induction S with
  | leaf => exact v.elim
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    obtain ⟨j,a⟩ := a
    obtain ⟨l,b⟩ := b
    cases v with
    | none =>
      let D : Fin ((k+1 : ℕ+) : ℕ) → PrescribedTree n := Fin.cases (single n) C
      change splitDepth (.node (k+1) D) ⟨j.succ,a⟩ ⟨l.succ,b⟩ =
        splitDepth (.node k C) ⟨j,a⟩ ⟨l,b⟩
      by_cases h : j = l
      · subst l
        exact (@splitDepth_same_child n (k+1) D j.succ a b).trans
          (splitDepth_same_child C j a b).symm
      · exact (@splitDepth_diff_child n (k+1) D j.succ l.succ
          (fun he => h (Fin.succ_inj.mp he)) a b).trans
          (splitDepth_diff_child C j l h a b).symm
    | some v =>
      obtain ⟨i,v⟩ := v
      let C' := Function.update C i (grow (C i) v)
      by_cases hjl : j = l
      · subst l
        rw [splitDepth_same_child]
        by_cases hji : j = i
        · subst j
          have heq : C' i = grow (C i) v := Function.update_self ..
          have hc := splitDepth_cast (grow (C i) v) (C' i) heq
            (oldLeaf (C i) v a) (oldLeaf (C i) v b)
          erw [oldLeaf.eq_1, oldLeaf.eq_1]
          dsimp only [id]
          simp only [dite_eq_left]
          change (if h : i = i then 1 + splitDepth (C' i)
            (cast (congrArg Leaf heq.symm) (oldLeaf (C i) v a))
            (cast (congrArg Leaf heq.symm) (oldLeaf (C i) v b)) else 0) = _
          simp only [dite_eq_left, hc, ih]
        · have heq : C' j = C j := Function.update_of_ne hji ..
          have hc := splitDepth_cast (C j) (C' j) heq a b
          erw [oldLeaf.eq_1, oldLeaf.eq_1]
          dsimp only [id]
          simp only [dite_eq_right hji]
          change (if h : j = j then 1 + splitDepth (C' j)
            (cast (congrArg Leaf heq.symm) a)
            (cast (congrArg Leaf heq.symm) b) else 0) = _
          simp only [dite_eq_left, hc]
      · rw [splitDepth_diff_child C j l hjl]
        apply (splitDepth_node_zero C' _ _).mpr
        change j ≠ l
        exact hjl

theorem oldLeaf_injective {n : ℕ} (S : PrescribedTree n) (v : Internal S) :
    Function.Injective (oldLeaf S v) := by
  intro a b hab
  apply (splitDepth_eq_height S a b).mp
  rw [← splitDepth_old_old S v a b, hab, splitDepth_self]

theorem newLeaf_ne_oldLeaf {n : ℕ} (S : PrescribedTree n) (v : Internal S) (a : Leaf S) :
    newLeaf S v ≠ oldLeaf S v a := by
  intro h
  have he := splitDepth_new_old S v a
  rw [h, splitDepth_self] at he
  have := freshSplitDepth_lt S v a
  omega

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- A finite number of represented equivalence classes depends only on the
kernel relation, not on their ambient set of representatives. -/
theorem card_image_of_same_kernel {ι α β : Type*} [DecidableEq ι]
    [DecidableEq α] [DecidableEq β] (R : Finset ι) (f : ι → α) (g : ι → β)
    (h : ∀ i ∈ R, ∀ j ∈ R, f i = f j ↔ g i = g j) :
    (R.image f).card = (R.image g).card := by
  induction R using Finset.induction_on with
  | empty => simp
  | @insert a R ha ih =>
    have hR : ∀ i ∈ R, ∀ j ∈ R, f i = f j ↔ g i = g j := by
      intro i hi j hj
      exact h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    have he : f a ∈ R.image f ↔ g a ∈ R.image g := by
      constructor
      · intro hh
        obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp hh
        exact Finset.mem_image.mpr ⟨i,hi,(h i (Finset.mem_insert_of_mem hi) a
          (Finset.mem_insert_self ..)).mp heq⟩
      · intro hg
        obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp hg
        exact Finset.mem_image.mpr ⟨i,hi,(h i (Finset.mem_insert_of_mem hi) a
          (Finset.mem_insert_self ..)).mpr heq⟩
    rw [Finset.image_insert, Finset.image_insert]
    by_cases hf : f a ∈ R.image f
    · rw [Finset.card_insert_of_mem hf, Finset.card_insert_of_mem (he.mp hf), ih hR]
    · rw [Finset.card_insert_of_notMem hf,
        Finset.card_insert_of_notMem (fun hg => hf (he.mpr hg)), ih hR]

/-- Reference labels in a particular child, preserving their identities. -/
abbrev ChildLabels {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    {ι : Type} (r : ι → Leaf (.node k C)) (i : Fin k) := {l : ι // (r l).1 = i}

def childLabelLeaf {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    {ι : Type} (r : ι → Leaf (.node k C)) (i : Fin k) (l : ChildLabels r i) : Leaf (C i) :=
  l.property ▸ (r l.val).2

theorem sigma_cast_snd {α : Type*} {β : α → Type*} (x : Sigma β) (i : α)
    (h : x.1 = i) : (⟨i,h ▸ x.2⟩ : Sigma β) = x := by
  obtain ⟨j,x⟩ := x
  dsimp at h
  subst i
  rfl

/-- Returning a restricted reference label to its original tree. -/
theorem childLabelLeaf_embed {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    {ι : Type} (r : ι → Leaf (.node k C)) (i : Fin k) (l : ChildLabels r i) :
    (⟨i,childLabelLeaf r i l⟩ : Leaf (.node k C)) = r l.val := by
  exact sigma_cast_snd (r l.val) i l.property

/-- The child reference set really is the image of the child-restricted labels. -/
theorem childRefs_image {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    {ι : Type} [Fintype ι] (r : ι → Leaf (.node k C)) (i : Fin k) :
    childRefs (Finset.univ.image r) i =
      Finset.univ.image (childLabelLeaf r i) := by
  classical
  ext b
  constructor
  · intro hb
    obtain ⟨l,_,hl⟩ := (Finset.mem_image (f := r)).mp ((mem_childRefs _ i b).mp hb)
    have hi : (r l).1 = i := congrArg Sigma.fst hl
    apply Finset.mem_image.mpr
    refine ⟨⟨l,hi⟩,Finset.mem_univ _, ?_⟩
    have he := (childLabelLeaf_embed r i ⟨l,hi⟩).trans hl
    exact eq_of_heq ((Sigma.mk.inj_iff.mp he).2)
  · intro hb
    obtain ⟨l,_,hl⟩ := Finset.mem_image.mp hb
    apply (mem_childRefs _ i b).mpr
    exact (Finset.mem_image (f := r)).mpr ⟨l.val,Finset.mem_univ _, by
      rw [← childLabelLeaf_embed r i l, hl]⟩


/-- One-step signed reference normalization is determined by the entire
labeled splitting matrix, not by the unused old leaves of its realization. -/
theorem reference_coefficient_invariant {n : ℕ} (S T : PrescribedTree n)
    {ι : Type} [Fintype ι] (r : ι → Leaf S) (s : ι → Leaf T) (a : ι)
    (hsplit : ∀ i j, splitDepth S (r i) (r j) = splitDepth T (s i) (s j))
    (d : ℕ) (hd : d < n) (m : Fin (n+1) → ℝ) :
    (referenceDivergence S (r a) d hd (Finset.univ.image r)).coefficient m =
      (referenceDivergence T (s a) d hd (Finset.univ.image s)).coefficient m := by
  classical
  induction n generalizing ι d with
  | zero => omega
  | succ n ih =>
    cases S with | node k C =>
    cases T with | node k' C' =>
    have hf (i j : ι) : (r i).1 = (r j).1 ↔ (s i).1 = (s j).1 := by
      have he := hsplit i j
      have hr := splitDepth_node_zero C (r i) (r j)
      have hs := splitDepth_node_zero C' (s i) (s j)
      rw [he] at hr
      tauto
    cases d with
    | zero =>
      change m 0 - (((Finset.univ.image r).image (fun b => b.1)).card : ℝ)*m 1 =
        m 0 - (((Finset.univ.image s).image (fun b => b.1)).card : ℝ)*m 1
      rw [Finset.image_image, Finset.image_image]
      have he := card_image_of_same_kernel Finset.univ (fun i => (r i).1)
        (fun i => (s i).1) (fun i _ j _ => hf i j)
      dsimp only [Function.comp_def]
      erw [he]
    | succ d =>
      let I := ChildLabels r (r a).1
      let rr : I → Leaf (C (r a).1) := childLabelLeaf r (r a).1
      let ss : I → Leaf (C' (s a).1) := fun l =>
        childLabelLeaf s (s a).1 ⟨l.val,(hf l.val a).mp l.property⟩
      let aa : I := ⟨a,rfl⟩
      have hr (i : I) : (⟨(r a).1,rr i⟩ : Leaf (.node k C)) = r i.val :=
        childLabelLeaf_embed r _ i
      have hs (i : I) : (⟨(s a).1,ss i⟩ : Leaf (.node k' C')) = s i.val :=
        childLabelLeaf_embed s _ _
      have hsplit' (i j : I) : splitDepth (C (r a).1) (rr i) (rr j) =
          splitDepth (C' (s a).1) (ss i) (ss j) := by
        have he := hsplit i.val j.val
        rw [← hr i, ← hr j, ← hs i, ← hs j,
          splitDepth_same_child, splitDepth_same_child] at he
        omega
      have hR := childRefs_image r (r a).1
      have hS : childRefs (Finset.univ.image s) (s a).1 = Finset.univ.image ss := by
        ext b
        constructor
        · intro hb
          obtain ⟨l,_,hl⟩ := (Finset.mem_image (f := s)).mp ((mem_childRefs _ _ b).mp hb)
          have hls : (s l).1 = (s a).1 := by
            have hh := congrArg (fun x : Leaf (.node k' C') => x.1) hl
            exact hh
          let l' : I := ⟨l,(hf l a).mpr hls⟩
          refine Finset.mem_image.mpr ⟨l',Finset.mem_univ _, ?_⟩
          have hh := (hs l').trans hl
          exact eq_of_heq ((Sigma.mk.inj_iff.mp hh).2)
        · intro hb
          obtain ⟨l,_,hl⟩ := Finset.mem_image.mp hb
          apply (mem_childRefs _ _ b).mpr
          exact (Finset.mem_image (f := s)).mpr ⟨l.val,Finset.mem_univ _, by rw [← hs l, hl]⟩
      have hd' : d < n := by omega
      change (referenceDivergence (C (r a).1) (r a).2 d hd'
        (childRefs (Finset.univ.image r) (r a).1)).coefficient (fun j => m j.succ) =
        (referenceDivergence (C' (s a).1) (s a).2 d hd'
        (childRefs (Finset.univ.image s) (s a).1)).coefficient (fun j => m j.succ)
      rw [hR,hS]
      exact ih _ _ rr ss aa hsplit' d hd' _

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem splitDepth_symm {n : ℕ} (S : PrescribedTree n) (a b : Leaf S) :
    splitDepth S a b = splitDepth S b a := by
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    obtain ⟨i,a⟩ := a
    obtain ⟨j,b⟩ := b
    by_cases h : i = j
    · subst j
      rw [splitDepth_same_child, splitDepth_same_child, ih]
    · rw [splitDepth_diff_child C i j h, splitDepth_diff_child C j i (Ne.symm h)]

/-- Positional ancestry is an ultrametric similarity, independently of spins. -/
theorem splitDepth_ultrametric {n : ℕ} (S : PrescribedTree n) (a b c : Leaf S) :
    min (splitDepth S a b) (splitDepth S b c) ≤ splitDepth S a c := by
  induction S with
  | leaf => exact le_refl _
  | @node n k C ih =>
    obtain ⟨i,a⟩ := a
    obtain ⟨j,b⟩ := b
    obtain ⟨l,c⟩ := c
    by_cases hij : i = j
    · subst j
      by_cases hil : i = l
      · subst l
        rw [splitDepth_same_child, splitDepth_same_child, splitDepth_same_child]
        have h := ih i a b c
        omega
      · rw [splitDepth_diff_child C i l hil, Nat.min_zero]
        exact Nat.zero_le _
    · rw [splitDepth_diff_child C i j hij, Nat.zero_min]
      exact Nat.zero_le _

 
theorem deepest_reference_profile {n : ℕ} (S : PrescribedTree n) (b a r : Leaf S)
    (hmax : splitDepth S b r ≤ splitDepth S b a) :
    splitDepth S b r = min (splitDepth S b a) (splitDepth S a r) := by
  have h1 := splitDepth_ultrametric S b a r
  have h2 := splitDepth_ultrametric S a b r
  rw [splitDepth_symm S a b, min_eq_right hmax] at h2
  exact le_antisymm (le_min hmax h2) h1

theorem splitDepth_lt_of_ne {n : ℕ} (S : PrescribedTree n) (a b : Leaf S) (hab : a ≠ b) :
    splitDepth S a b < n := by
  have hle := splitDepth_le S a b
  have hne : splitDepth S a b ≠ n := fun h => hab ((splitDepth_eq_height S a b).mp h)
  omega

/-- A deepest reference exists among any finite nonempty set of labels. -/
theorem exists_deepest_reference {n : ℕ} (S : PrescribedTree n)
    {ι : Type} [Fintype ι] [Nonempty ι] (r : ι → Leaf S) (b : Leaf S) :
    ∃ a, ∀ i, splitDepth S b (r i) ≤ splitDepth S b (r a) := by
  obtain ⟨a,_,ha⟩ := Finset.exists_max_image Finset.univ (fun i => splitDepth S b (r i))
    Finset.univ_nonempty
  exact ⟨a,fun i => ha i (Finset.mem_univ i)⟩

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Full ancestry selector for using an old unused path as the next color. -/
def labeledOldMatch {n : ℕ} (S T : PrescribedTree n) {ι : Type}
    (r : ι → Leaf S) (s : ι → Leaf T) (b : Leaf T) (x : Leaf S) : Prop :=
  ∀ i, splitDepth S x (r i) = splitDepth T b (s i)

/-- Full ancestry selector for a genuinely fresh path as the next color. -/
def labeledFreshMatch {n : ℕ} (S T : PrescribedTree n) {ι : Type}
    (r : ι → Leaf S) (s : ι → Leaf T) (b : Leaf T) (v : Internal S) : Prop :=
  ∀ i, freshSplitDepth S v (r i) = splitDepth T b (s i)

theorem labeledOldMatch_profile {n : ℕ} (S T : PrescribedTree n)
    {ι : Type} [Fintype ι] (r : ι → Leaf S) (s : ι → Leaf T) (b : Leaf T) (a : ι)
    (hsplit : ∀ i j, splitDepth S (r i) (r j) = splitDepth T (s i) (s j))
    (hmax : ∀ i, splitDepth T b (s i) ≤ splitDepth T b (s a)) (x : Leaf S) :
    labeledOldMatch S T r s b x ↔
      matchesOldProfile S (Finset.univ.image r) (r a) (splitDepth T b (s a)) x := by
  constructor
  · intro h y hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
    rw [h i, hsplit, deepest_reference_profile T b (s a) (s i) (hmax i)]
  · intro h i
    have hh := h (r i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    rw [hsplit] at hh
    rw [hh, deepest_reference_profile T b (s a) (s i) (hmax i)]

theorem labeledFreshMatch_profile {n : ℕ} (S T : PrescribedTree n)
    {ι : Type} [Fintype ι] (r : ι → Leaf S) (s : ι → Leaf T) (b : Leaf T) (a : ι)
    (hsplit : ∀ i j, splitDepth S (r i) (r j) = splitDepth T (s i) (s j))
    (hmax : ∀ i, splitDepth T b (s i) ≤ splitDepth T b (s a)) (v : Internal S) :
    labeledFreshMatch S T r s b v ↔
      matchesFreshProfile S (Finset.univ.image r) (r a) (splitDepth T b (s a)) v := by
  constructor
  · intro h y hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
    rw [h i, hsplit, deepest_reference_profile T b (s a) (s i) (hmax i)]
  · intro h i
    have hh := h (r i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    rw [hsplit] at hh
    rw [hh, deepest_reference_profile T b (s a) (s i) (hmax i)]

/-- Every eligible old or fresh choice is counted once. Its signed total
depends only on the prescribed reference splitting matrix. -/
theorem labeled_choice_total {n : ℕ} (S T : PrescribedTree n)
    {ι : Type} [Fintype ι] (r : ι → Leaf S) (s : ι → Leaf T) (b : Leaf T) (a : ι)
    (hsplit : ∀ i j, splitDepth S (r i) (r j) = splitDepth T (s i) (s j))
    (hne : b ≠ s a) (hmax : ∀ i, splitDepth T b (s i) ≤ splitDepth T b (s a))
    (m : Fin (n+1) → ℝ) (hend : m (Fin.last n) = 1) :
    (∑ x : Leaf S, if labeledOldMatch S T r s b x then (1:ℝ) else 0) +
      (∑ v : Internal S, if labeledFreshMatch S T r s b v then gamma S m v else 0) =
      (referenceDivergence T (s a) (splitDepth T b (s a))
        (splitDepth_lt_of_ne T b (s a) hne) (Finset.univ.image s)).coefficient m := by
  simp_rw [labeledOldMatch_profile S T r s b a hsplit hmax,
    labeledFreshMatch_profile S T r s b a hsplit hmax]
  rw [reference_profile_total S (r a) (splitDepth T b (s a))
    (splitDepth_lt_of_ne T b (s a) hne) (Finset.univ.image r)
    (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩) m hend]
  exact reference_coefficient_invariant S T r s a hsplit _ _ m

/-- Eligible old leaves are unused, since the target color is new. -/
theorem labeledOldMatch_unused {n : ℕ} (S T : PrescribedTree n) {ι : Type}
    (r : ι → Leaf S) (s : ι → Leaf T) (b : Leaf T) (x : Leaf S)
    (hne : ∀ i, b ≠ s i) (h : labeledOldMatch S T r s b x) : ∀ i, x ≠ r i := by
  intro i hi
  have hh := h i
  rw [hi,splitDepth_self] at hh
  exact hne i ((splitDepth_eq_height T b (s i)).mp hh.symm)

/-- On adding an eligible old color, ALL reference ancestries are retained. -/
theorem labeledOldMatch_cons {n p : ℕ} (S T : PrescribedTree n)
    (r : Fin p → Leaf S) (s : Fin p → Leaf T) (b : Leaf T) (x : Leaf S)
    (hsplit : ∀ i j, splitDepth S (r i) (r j) = splitDepth T (s i) (s j))
    (h : labeledOldMatch S T r s b x) : ∀ i j : Fin (p+1),
      splitDepth S ((Fin.cons x r : Fin (p+1) → Leaf S) i) ((Fin.cons x r : Fin (p+1) → Leaf S) j) =
        splitDepth T ((Fin.cons b s : Fin (p+1) → Leaf T) i) ((Fin.cons b s : Fin (p+1) → Leaf T) j) := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Fin.cons_zero, splitDepth_self]
  · exact h j
  · simpa only [Fin.cons_zero, Fin.cons_succ, splitDepth_symm S (r i) x,
      splitDepth_symm T (s i) b] using h i
  · exact hsplit i j

/-- On adding an eligible fresh color, ALL reference ancestries are retained. -/
theorem labeledFreshMatch_cons {n p : ℕ} (S T : PrescribedTree n)
    (r : Fin p → Leaf S) (s : Fin p → Leaf T) (b : Leaf T) (v : Internal S)
    (hsplit : ∀ i j, splitDepth S (r i) (r j) = splitDepth T (s i) (s j))
    (h : labeledFreshMatch S T r s b v) : ∀ i j : Fin (p+1),
      splitDepth (grow S v) ((Fin.cons (newLeaf S v) (oldLeaf S v ∘ r) : Fin (p+1) → Leaf (grow S v)) i)
        ((Fin.cons (newLeaf S v) (oldLeaf S v ∘ r) : Fin (p+1) → Leaf (grow S v)) j) =
        splitDepth T ((Fin.cons b s : Fin (p+1) → Leaf T) i) ((Fin.cons b s : Fin (p+1) → Leaf T) j) := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Fin.cons_zero, splitDepth_self]
  · simp only [Fin.cons_zero, Fin.cons_succ, Function.comp_apply,splitDepth_new_old]
    exact h j
  · simp only [Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
    rw [splitDepth_symm,splitDepth_new_old,splitDepth_symm T (s i) b]
    exact h i
  · simp only [Fin.cons_succ,Function.comp_apply,splitDepth_old_old]
    exact hsplit i j

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The one-step coefficient cannot vanish for a genuine reference divergence
and strictly increasing cavity exponents. -/
theorem reference_coefficient_neg {n : ℕ} (S : PrescribedTree n)
    (a : Leaf S) (d : ℕ) (hd : d < n) (R : Finset (Leaf S)) (ha : a ∈ R)
    (m : Fin (n+1) → ℝ) (hm : StrictMono m) (hnonneg : ∀ j, 0 ≤ m j) :
    (referenceDivergence S a d hd R).coefficient m < 0 := by
  classical
  induction S generalizing d with
  | leaf => omega
  | @node n k C ih =>
    cases d with
    | zero =>
      change m 0 - ((R.image (fun b => b.1)).card : ℝ)*m 1 < 0
      have hcard : 1 ≤ (R.image (fun b => b.1)).card :=
        Finset.card_pos.mpr ⟨a.1,Finset.mem_image.mpr ⟨a,ha,rfl⟩⟩
      have hm01 : m 0 < m 1 := hm (by norm_num)
      have hc : (1:ℝ) ≤ ((R.image (fun b => b.1)).card : ℝ) := by exact_mod_cast hcard
      have hp := hnonneg 1
      nlinarith
    | succ d =>
      change (referenceDivergence (C a.1) a.2 d (by omega)
        (childRefs R a.1)).coefficient (fun j => m j.succ) < 0
      apply ih a.1 a.2 d (by omega) (childRefs R a.1)
      · apply (mem_childRefs R a.1 a.2).mpr
        change a ∈ R
        exact ha
      · intro i j hij
        exact hm (Fin.succ_lt_succ_iff.mpr hij)
      · exact fun j => hnonneg j.succ

/-- A finite color prescription. The deepest-reference witness is only
positional data; exists_deepest_reference supplies it for every new leaf. -/
inductive ReferencePlan {n : ℕ} (T : PrescribedTree n) :
    {p : ℕ} → (Fin (p+1) → Leaf T) → Type
  | nil {p : ℕ} {s : Fin (p+1) → Leaf T} : ReferencePlan T s
  | cons {p : ℕ} {s : Fin (p+1) → Leaf T} (b : Leaf T) (a : Fin (p+1))
      (fresh : ∀ i, b ≠ s i)
      (deepest : ∀ i, splitDepth T b (s i) ≤ splitDepth T b (s a))
      (next : ReferencePlan T (Fin.cons b s)) : ReferencePlan T s

/-- The deterministic product of one-step reference factors. -/
noncomputable def referencePlanNormalizer {n : ℕ} (T : PrescribedTree n)
    (m : Fin (n+1) → ℝ) : {p : ℕ} → {s : Fin (p+1) → Leaf T} → ReferencePlan T s → ℝ
  | _, _, .nil => 1
  | _, s, .cons b a hne _ next =>
      (referenceDivergence T (s a) (splitDepth T b (s a))
        (splitDepth_lt_of_ne T b (s a) (hne a)) (Finset.univ.image s)).coefficient m *
          referencePlanNormalizer T m next

/-- The signed sum over the actual sequential old-or-fresh choices. Every
fresh choice changes the entire current tree with grow, and transports all
previous references. No constant normalization is built into this recursion. -/
noncomputable def referenceHistoryTotal {n : ℕ} (T : PrescribedTree n)
    (m : Fin (n+1) → ℝ) : {p : ℕ} → {s : Fin (p+1) → Leaf T} → ReferencePlan T s →
      (S : PrescribedTree n) → (Fin (p+1) → Leaf S) → ℝ
  | _, _, .nil, _, _ => 1
  | _, s, .cons b _ _ _ next, S, r =>
      (∑ x : Leaf S, if labeledOldMatch S T r s b x then
        referenceHistoryTotal T m next S (Fin.cons x r) else 0) +
      (∑ v : Internal S, if labeledFreshMatch S T r s b v then
        gamma S m v * referenceHistoryTotal T m next (grow S v)
          (Fin.cons (newLeaf S v) (oldLeaf S v ∘ r)) else 0)

/-- Reference-path totals for any finite number of colors and any old tree.
The histories have globally consistent splitting matrices at every step. -/
theorem reference_history_total {n p : ℕ} (T : PrescribedTree n)
    (m : Fin (n+1) → ℝ) (hend : m (Fin.last n) = 1)
    {s : Fin (p+1) → Leaf T} (P : ReferencePlan T s) (S : PrescribedTree n)
    (r : Fin (p+1) → Leaf S)
    (hsplit : ∀ i j, splitDepth S (r i) (r j) = splitDepth T (s i) (s j)) :
    referenceHistoryTotal T m P S r = referencePlanNormalizer T m P := by
  induction P generalizing S with
  | nil => rfl
  | @cons p s b a hne hmax next ih =>
    dsimp only [referenceHistoryTotal,referencePlanNormalizer]
    have ho (x : Leaf S) :
        (if labeledOldMatch S T r s b x then referenceHistoryTotal T m next S (Fin.cons x r)
          else 0) = (if labeledOldMatch S T r s b x then (1:ℝ) else 0) *
            referencePlanNormalizer T m next := by
      split_ifs with hx
      · rw [ih S (Fin.cons x r) (labeledOldMatch_cons S T r s b x hsplit hx),one_mul]
      · simp
    have hf (v : Internal S) :
        (if labeledFreshMatch S T r s b v then gamma S m v *
          referenceHistoryTotal T m next (grow S v)
            (Fin.cons (newLeaf S v) (oldLeaf S v ∘ r)) else 0) =
          (if labeledFreshMatch S T r s b v then gamma S m v else 0) *
            referencePlanNormalizer T m next := by
      split_ifs with hv
      · rw [ih (grow S v) (Fin.cons (newLeaf S v) (oldLeaf S v ∘ r))
          (labeledFreshMatch_cons S T r s b v hsplit hv)]
      · simp
    simp_rw [ho,hf]
    rw [← Finset.sum_mul,← Finset.sum_mul,← add_mul,
      labeled_choice_total S T r s b a hsplit (hne a) hmax m hend]

/-- In particular division by the reference normalization is legitimate. -/
theorem referencePlanNormalizer_ne_zero {n p : ℕ} (T : PrescribedTree n)
    (m : Fin (n+1) → ℝ) (hm : StrictMono m) (hnonneg : ∀ j, 0 ≤ m j)
    {s : Fin (p+1) → Leaf T} (P : ReferencePlan T s) :
    referencePlanNormalizer T m P ≠ 0 := by
  induction P with
  | nil => exact one_ne_zero
  | @cons p s b a hne hmax next ih =>
    dsimp only [referencePlanNormalizer]
    apply mul_ne_zero _ ih
    exact ne_of_lt (reference_coefficient_neg T (s a) _ _ _
      (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩) m hm hnonneg)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
