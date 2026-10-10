import OAI.Probability.SwitchChain.FixedBlockVariance

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.FixedBlockMarginal
open FixedBlock

def average {X : Type*} [Fintype X] (f : X → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card X : ℝ)

theorem average_congr {X : Type*} [Fintype X] {f g : X → ℝ}
    (h : ∀ x, f x = g x) : average f = average g := by
  simp only [average]
  congr 1
  exact Finset.sum_congr rfl (fun x _ => h x)

theorem average_const {X : Type*} [Fintype X] [Nonempty X] (c : ℝ) :
    average (fun _ : X => c) = c := by
  have hc : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [average, hc]

theorem average_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (f : Y → ℝ) : average (fun x => f (e x)) = average f := by
  simp only [average, e.sum_comp, Fintype.card_congr e]

theorem average_comm {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y → ℝ) :
    average (fun x => average (fun y => f x y)) =
      average (fun y => average (fun x => f x y)) := by
  simp only [average, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

theorem average_prod {X Y : Type*} [Fintype X] [Fintype Y] (f : X × Y → ℝ) :
    average f = average (fun x => average (fun y => f (x, y))) := by
  simp only [average, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

variable {α : Type*} [sectionFintypeα : Fintype α] [sectionDecidableEqα : DecidableEq α]

theorem permutation_average_eq {p : Fin 3 → ℕ}
    (f : Partition (α := α) p → ℝ) (c d : Partition (α := α) p) :
    average (fun σ : Equiv.Perm α => f (relabel σ c)) =
      average (fun σ : Equiv.Perm α => f (relabel σ d)) := by
  obtain ⟨τ, rfl⟩ := exists_relabel c d
  symm
  calc
    average (fun σ : Equiv.Perm α => f (relabel σ (relabel τ c))) =
        average (fun σ : Equiv.Perm α => f (relabel (σ * τ) c)) := by
      apply average_congr
      intro σ
      rw [relabel_mul]
    _ = _ := by
      simpa using average_equiv (Equiv.mulRight τ) (fun σ : Equiv.Perm α => f (relabel σ c))

theorem average_eq_permutation_average {p : Fin 3 → ℕ}
    (f : Partition (α := α) p → ℝ) (c : Partition (α := α) p) :
    average f = average (fun σ : Equiv.Perm α => f (relabel σ c)) := by
  let : Nonempty (Partition (α := α) p) := ⟨c⟩
  calc
    average f = average (fun _ : Equiv.Perm α => average f) := (average_const _).symm
    _ = average (fun σ : Equiv.Perm α =>
        average (fun d : Partition (α := α) p => f (relabel σ d))) := by
      apply average_congr
      intro σ
      exact (average_equiv (FixedBlockVariance.relabelPerm p σ) f).symm
    _ = average (fun d : Partition (α := α) p =>
        average (fun σ : Equiv.Perm α => f (relabel σ d))) := average_comm _
    _ = average (fun _ : Partition (α := α) p =>
        average (fun σ : Equiv.Perm α => f (relabel σ c))) := by
      apply average_congr
      intro d
      exact permutation_average_eq f d c
    _ = _ := average_const _

theorem exists_perm_map (s t : Finset α) (h : s.card = t.card) :
    ∃ σ : Equiv.Perm α, s.map σ.toEmbedding = t := by
  let e : {a : α // a ∈ s} ≃ {a : α // a ∈ t} :=
    Fintype.equivOfCardEq (by simpa using h)
  refine ⟨e.extendSubtype, ?_⟩
  ext a
  constructor
  · intro ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
    exact e.extendSubtype_mem b hb
  · intro ha
    let b := e.extendSubtype.symm a
    have hb : b ∈ s := by
      by_contra hn
      have hh := e.extendSubtype_not_mem b hn
      exact hh (by simpa [b] using ha)
    exact Finset.mem_map.mpr ⟨b, hb, e.extendSubtype.apply_symm_apply a⟩

theorem average_row_eq {p p' : Fin 3 → ℕ} (i : Fin 3) (h : p i = p' i)
    (c : Partition (α := α) p) (d : Partition (α := α) p') (g : Finset α → ℝ) :
    average (fun x : Partition (α := α) p => g (row x.val i)) =
      average (fun x : Partition (α := α) p' => g (row x.val i)) := by
  have hcard : (row c.val i).card = (row d.val i).card :=
    (c.property i).trans (h.trans (d.property i).symm)
  obtain ⟨τ, hτ⟩ := exists_perm_map (row c.val i) (row d.val i) hcard
  have hrow : row (relabel τ c).val i = row d.val i := by
    change row (fun a => c.val (τ.symm a)) i = row d.val i
    rw [row_relabel, hτ]
  rw [average_eq_permutation_average _ (relabel τ c),
    average_eq_permutation_average _ d]
  apply average_congr
  intro σ
  change g (row (fun a => (relabel τ c).val (σ.symm a)) i) =
    g (row (fun a => d.val (σ.symm a)) i)
  rw [row_relabel, row_relabel, hrow]

variable {β : Type*} [Fintype β] [DecidableEq β]

theorem row_function_average_eq
    {p q p' q' : Fin 3 → ℕ} (i : Fin 3) (hp : p i = p' i) (hq : q i = q' i)
    (c : Partition (α := α) p) (c' : Partition (α := α) p')
    (d : Partition (α := β) q) (d' : Partition (α := β) q')
    (g : Finset α → Finset β → ℝ) :
    FixedBlockVariance.average p q (fun x => g (row x.1.val i) (row x.2.val i)) =
      FixedBlockVariance.average p' q' (fun x => g (row x.1.val i) (row x.2.val i)) := by
  change average (fun x : Partition (α := α) p × Partition (α := β) q =>
      g (row x.1.val i) (row x.2.val i)) =
    average (fun x : Partition (α := α) p' × Partition (α := β) q' =>
      g (row x.1.val i) (row x.2.val i))
  rw [average_prod, average_prod]
  calc
    _ = average (fun x : Partition (α := α) p =>
        average (fun y : Partition (α := β) q' => g (row x.val i) (row y.val i))) := by
      apply average_congr
      intro x
      exact average_row_eq i hq d d' (g (row x.val i))
    _ = _ := average_row_eq i hp c c'
      (fun s => average (fun y : Partition (α := β) q' => g s (row y.val i)))

abbrev Subsets (k : ℕ) := {s : Finset α // s.card = k}

def subsetPerm (k : ℕ) (σ : Equiv.Perm α) : Equiv.Perm (Subsets (α := α) k) where
  toFun s := ⟨s.val.map σ.toEmbedding, by simpa using s.property⟩
  invFun s := ⟨s.val.map σ.symm.toEmbedding, by simpa using s.property⟩
  left_inv s := by
    apply Subtype.ext
    ext a
    simp
  right_inv s := by
    apply Subtype.ext
    ext a
    simp

include sectionFintypeα sectionDecidableEqα in
theorem subsetPerm_mul (k : ℕ) (σ τ : Equiv.Perm α) (s : Subsets (α := α) k) :
    subsetPerm k (σ * τ) s = subsetPerm k σ (subsetPerm k τ s) := by
  have retainedsectionFintypeα := sectionFintypeα
  have retainedsectionDecidableEqα := sectionDecidableEqα
  apply Subtype.ext
  ext a
  simp [subsetPerm]
  rfl

theorem subset_permutation_average_eq (k : ℕ) (g : Subsets (α := α) k → ℝ)
    (s t : Subsets (α := α) k) :
    average (fun σ : Equiv.Perm α => g (subsetPerm k σ s)) =
      average (fun σ : Equiv.Perm α => g (subsetPerm k σ t)) := by
  obtain ⟨τ, hτ⟩ := exists_perm_map s.val t.val (s.property.trans t.property.symm)
  have ht : subsetPerm k τ s = t := Subtype.ext hτ
  rw [← ht]
  symm
  calc
    _ = average (fun σ : Equiv.Perm α => g (subsetPerm k (σ * τ) s)) := by
      apply average_congr
      intro σ
      rw [subsetPerm_mul]
    _ = _ := by
      simpa using average_equiv (Equiv.mulRight τ)
        (fun σ : Equiv.Perm α => g (subsetPerm k σ s))

theorem subset_average_eq_permutation_average (k : ℕ)
    (g : Subsets (α := α) k → ℝ) (s : Subsets (α := α) k) :
    average g = average (fun σ : Equiv.Perm α => g (subsetPerm k σ s)) := by
  let : Nonempty (Subsets (α := α) k) := ⟨s⟩
  calc
    average g = average (fun _ : Equiv.Perm α => average g) := (average_const _).symm
    _ = average (fun σ : Equiv.Perm α =>
        average (fun t : Subsets (α := α) k => g (subsetPerm k σ t))) := by
      apply average_congr
      intro σ
      exact (average_equiv (subsetPerm k σ) g).symm
    _ = average (fun t : Subsets (α := α) k =>
        average (fun σ : Equiv.Perm α => g (subsetPerm k σ t))) := average_comm _
    _ = average (fun _ : Subsets (α := α) k =>
        average (fun σ : Equiv.Perm α => g (subsetPerm k σ s))) := by
      apply average_congr
      intro t
      exact subset_permutation_average_eq k g t s
    _ = _ := average_const _

theorem average_row_eq_subset_average {p : Fin 3 → ℕ} (i : Fin 3)
    (c : Partition (α := α) p) (g : Finset α → ℝ) :
    average (fun x : Partition (α := α) p => g (row x.val i)) =
      average (fun s : Subsets (α := α) (p i) => g s.val) := by
  rw [average_eq_permutation_average _ c,
    subset_average_eq_permutation_average _ _ ⟨row c.val i, c.property i⟩]
  apply average_congr
  intro σ
  change g (row (fun a => c.val (σ.symm a)) i) = g ((row c.val i).map σ.toEmbedding)
  rw [row_relabel]

theorem row_function_average_eq_subset_average {p q : Fin 3 → ℕ} (i : Fin 3)
    (c : Partition (α := α) p) (d : Partition (α := β) q)
    (g : Finset α → Finset β → ℝ) :
    FixedBlockVariance.average p q (fun x => g (row x.1.val i) (row x.2.val i)) =
      average (fun x : Subsets (α := α) (p i) × Subsets (α := β) (q i) =>
        g x.1.val x.2.val) := by
  change average (fun x : Partition (α := α) p × Partition (α := β) q =>
      g (row x.1.val i) (row x.2.val i)) = _
  rw [average_prod, average_prod]
  calc
    _ = average (fun x : Partition (α := α) p =>
        average (fun y : Subsets (α := β) (q i) => g (row x.val i) y.val)) := by
      apply average_congr
      intro x
      exact average_row_eq_subset_average i d (g (row x.val i))
    _ = _ := average_row_eq_subset_average i c
      (fun s => average (fun y : Subsets (α := β) (q i) => g s y.val))

end Problem315.FixedBlockMarginal

end

end OAI
