import OAI.Probability.SwitchChain.FixedBlockPartitions
import OAI.Probability.SwitchChain.PermutationGenerator

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.FixedBlockVariance
open FixedBlock

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable (p q : Fin 3 → ℕ)

abbrev State := Partition (α := α) p × Partition (α := β) q

def relabelPerm (σ : Equiv.Perm α) : Equiv.Perm (Partition (α := α) p) where
  toFun := relabel σ
  invFun := relabel σ.symm
  left_inv c := by
    apply Subtype.ext
    funext a
    simp [relabel]
  right_inv c := by
    apply Subtype.ext
    funext a
    simp [relabel]

def move : (α × α) ⊕ (β × β) → Equiv.Perm (State (α := α) (β := β) p q)
  | Sum.inl ab => Equiv.prodCongr (relabelPerm p (Equiv.swap ab.1 ab.2)) (Equiv.refl _)
  | Sum.inr ab => Equiv.prodCongr (Equiv.refl _) (relabelPerm q (Equiv.swap ab.1 ab.2))

def key (i : Fin 3) (x : State (α := α) (β := β) p q) : Finset α × Finset β :=
  (row x.1.val i, row x.2.val i)

theorem key_move_eq (i : Fin 3) (s : (α × α) ⊕ (β × β))
    (x y : State (α := α) (β := β) p q) (h : key p q i x = key p q i y) :
    key p q i (move p q s x) = key p q i (move p q s y) := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  change row x.1.val i = row y.1.val i at h1
  change row x.2.val i = row y.2.val i at h2
  cases s with
  | inl ab =>
      change (row (fun a => x.1.val ((Equiv.swap ab.1 ab.2).symm a)) i, row x.2.val i) =
        (row (fun a => y.1.val ((Equiv.swap ab.1 ab.2).symm a)) i, row y.2.val i)
      rw [row_relabel, row_relabel, h1, h2]
  | inr ab =>
      change (row x.1.val i, row (fun b => x.2.val ((Equiv.swap ab.1 ab.2).symm b)) i) =
        (row y.1.val i, row (fun b => y.2.val ((Equiv.swap ab.1 ab.2).symm b)) i)
      rw [row_relabel, row_relabel, h1, h2]

theorem constant_of_move_invariant
    (f : State (α := α) (β := β) p q → ℝ)
    (hf : ∀ s x, f (move p q s x) = f x)
    (x y : State (α := α) (β := β) p q) : f x = f y := by
  have hleft (d : Partition (α := β) q) (c e : Partition (α := α) p) :
      f (c, d) = f (e, d) := by
    apply eq_of_swap_invariant (fun c => f (c, d)) _ c e
    intro a b c
    exact hf (Sum.inl (a, b)) (c, d)
  have hright (c : Partition (α := α) p) (d e : Partition (α := β) q) :
      f (c, d) = f (c, e) := by
    apply eq_of_swap_invariant (fun d => f (c, d)) _ d e
    intro a b d
    exact hf (Sum.inr (a, b)) (c, d)
  exact (hleft x.2 x.1 y.1).trans (hright y.1 x.2 y.2)

def rowSpace (i : Fin 3) : Submodule ℝ (EuclideanSpace ℝ (State (α := α) (β := β) p q)) where
  carrier := {f | (∑ x, f x = 0) ∧ ∀ x y, key p q i x = key p q i y → f x = f y}
  zero_mem' := by simp
  add_mem' := by
    rintro f g ⟨hfc, hfk⟩ ⟨hgc, hgk⟩
    constructor
    · simp only [PiLp.add_apply, Finset.sum_add_distrib, hfc, hgc, zero_add]
    · intro x y h
      simp only [PiLp.add_apply, hfk x y h, hgk x y h]
  smul_mem' := by
    rintro c f ⟨hfc, hfk⟩
    constructor
    · simp only [PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, hfc, mul_zero]
    · intro x y h
      simp only [PiLp.smul_apply, hfk x y h]

theorem rowSpace_invariant (i : Fin 3)
    (f : EuclideanSpace ℝ (State (α := α) (β := β) p q))
    (hf : f ∈ rowSpace p q i) :
    PermutationGenerator.operator (move p q) f ∈ rowSpace p q i := by
  constructor
  · exact PermutationGenerator.sum_apply (move p q) f
  · intro x y h
    change (∑ s, (f x - f (move p q s x))) = ∑ s, (f y - f (move p q s y))
    apply Finset.sum_congr rfl
    intro s hs
    rw [hf.2 x y h, hf.2 _ _ (key_move_eq p q i s x y h)]

theorem local_energy_bound
    (f : Fin 3 → EuclideanSpace ℝ (State (α := α) (β := β) p q))
    (hf : ∀ i, f i ∈ rowSpace p q i)
    (s : (α × α) ⊕ (β × β)) (x : State (α := α) (β := β) p q) :
    (∑ i, (f i x - f i (move p q s x))) ^ 2 ≤
      2 * ∑ i, (f i x - f i (move p q s x)) ^ 2 := by
  cases s with
  | inl ab =>
      obtain ⟨i, hia, hib⟩ := exists_unused_color (x.1.val ab.1) (x.1.val ab.2)
      apply three_sum_sq_le_twice _ i
      have hk : key p q i (move p q (Sum.inl ab) x) = key p q i x := by
        change (row (fun a => x.1.val ((Equiv.swap ab.1 ab.2).symm a)) i, row x.2.val i) =
          (row x.1.val i, row x.2.val i)
        rw [row_swap_unchanged _ _ _ _ (Ne.symm hia) (Ne.symm hib)]
      rw [(hf i).2 _ _ hk, sub_self]
  | inr ab =>
      obtain ⟨i, hia, hib⟩ := exists_unused_color (x.2.val ab.1) (x.2.val ab.2)
      apply three_sum_sq_le_twice _ i
      have hk : key p q i (move p q (Sum.inr ab) x) = key p q i x := by
        change (row x.1.val i, row (fun b => x.2.val ((Equiv.swap ab.1 ab.2).symm b)) i) =
          (row x.1.val i, row x.2.val i)
        rw [row_swap_unchanged _ _ _ _ (Ne.symm hia) (Ne.symm hib)]
      rw [(hf i).2 _ _ hk, sub_self]

theorem centered_row_norm_bound [Nonempty (State (α := α) (β := β) p q)]
    (f : Fin 3 → EuclideanSpace ℝ (State (α := α) (β := β) p q))
    (hf : ∀ i, f i ∈ rowSpace p q i) :
    ‖∑ i, f i‖ ^ 2 ≤ 2 * ∑ i, ‖f i‖ ^ 2 := by
  exact PermutationGenerator.norm_sum_sq_le_of_invariant_moves (move p q)
    (constant_of_move_invariant p q) (rowSpace p q)
    (fun i f hf => hf.1) (rowSpace_invariant p q) 2
    (local_energy_bound p q) f hf

def average (f : State (α := α) (β := β) p q → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card (State (α := α) (β := β) p q) : ℝ)

def variance (f : State (α := α) (β := β) p q → ℝ) : ℝ :=
  (∑ x, (f x - average p q f) ^ 2) /
    (Fintype.card (State (α := α) (β := β) p q) : ℝ)

theorem sum_sub_average [Nonempty (State (α := α) (β := β) p q)]
    (f : State (α := α) (β := β) p q → ℝ) :
    ∑ x, (f x - average p q f) = 0 := by
  have hc : (Fintype.card (State (α := α) (β := β) p q) : ℝ) ≠ 0 :=
    by exact_mod_cast Fintype.card_ne_zero
  simp only [average, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

theorem average_sum (f : Fin 3 → State (α := α) (β := β) p q → ℝ) :
    average p q (fun x => ∑ i, f i x) = ∑ i, average p q (f i) := by
  unfold average
  rw [Finset.sum_comm, Finset.sum_div]

theorem row_variance_bound [Nonempty (State (α := α) (β := β) p q)]
    (f : Fin 3 → State (α := α) (β := β) p q → ℝ)
    (hf : ∀ i x y, key p q i x = key p q i y → f i x = f i y) :
    variance p q (fun x => ∑ i, f i x) ≤ 2 * ∑ i, variance p q (f i) := by
  let g : Fin 3 → EuclideanSpace ℝ (State (α := α) (β := β) p q) :=
    fun i => WithLp.toLp 2 (fun x => f i x - average p q (f i))
  have hg (i : Fin 3) : g i ∈ rowSpace p q i := by
    constructor
    · exact sum_sub_average p q (f i)
    · intro x y h
      change f i x - average p q (f i) = f i y - average p q (f i)
      rw [hf i x y h]
  have h := centered_row_norm_bound p q g hg
  have htotal : ‖∑ i, g i‖ ^ 2 =
      ∑ x, ((∑ i, f i x) - average p q (fun y => ∑ i, f i y)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro x hx
    have he : (∑ i, g i) x = ∑ i, (f i x - average p q (f i)) := by simp [g]
    rw [he, Finset.sum_sub_distrib, average_sum]
  have heach (i : Fin 3) : ‖g i‖ ^ 2 = ∑ x, (f i x - average p q (f i)) ^ 2 := by
    exact EuclideanSpace.real_norm_sq_eq (g i)
  rw [htotal] at h
  simp_rw [heach] at h
  unfold variance
  rw [← Finset.sum_div, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right h (Nat.cast_nonneg _)

theorem variance_sum_row_functions [Nonempty (State (α := α) (β := β) p q)]
    (g : Fin 3 → Finset α → Finset β → ℝ) :
    variance p q (fun x => ∑ i, g i (row x.1.val i) (row x.2.val i)) ≤
      2 * ∑ i, variance p q (fun x => g i (row x.1.val i) (row x.2.val i)) := by
  apply row_variance_bound p q
  intro i x y h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  change row x.1.val i = row y.1.val i at h1
  change row x.2.val i = row y.2.val i at h2
  rw [h1, h2]

end Problem315.FixedBlockVariance

end

end OAI
