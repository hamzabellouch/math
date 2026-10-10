import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.FixedBlock

variable {α : Type*} [Fintype α] [sectionDecidableEqα : DecidableEq α]

def row (c : α → Fin 3) (i : Fin 3) : Finset α :=
  Finset.univ.filter (fun a => c a = i)

include sectionDecidableEqα in
@[simp] lemma mem_row (c : α → Fin 3) (i : Fin 3) (a : α) :
    a ∈ row c i ↔ c a = i := by
  have retainedsectionDecidableEqα := sectionDecidableEqα
  simp [row]

lemma row_relabel (σ : Equiv.Perm α) (c : α → Fin 3) (i : Fin 3) :
    row (fun a => c (σ.symm a)) i = (row c i).map σ.toEmbedding := by
  ext a
  simp []

abbrev Partition (sizes : Fin 3 → ℕ) :=
  {c : α → Fin 3 // ∀ i, (row c i).card = sizes i}

def relabel {sizes : Fin 3 → ℕ} (σ : Equiv.Perm α) (c : Partition (α := α) sizes) :
    Partition (α := α) sizes :=
  ⟨fun a => c.val (σ.symm a), by
    intro i
    rw [row_relabel, Finset.card_map]
    exact c.property i⟩

@[simp] lemma relabel_val {sizes : Fin 3 → ℕ} (σ : Equiv.Perm α)
    (c : Partition (α := α) sizes) (a : α) :
    (relabel σ c).val a = c.val (σ.symm a) := rfl

@[simp] lemma relabel_one {sizes : Fin 3 → ℕ} (c : Partition (α := α) sizes) :
    relabel 1 c = c := by apply Subtype.ext; rfl

lemma relabel_mul {sizes : Fin 3 → ℕ} (σ τ : Equiv.Perm α)
    (c : Partition (α := α) sizes) :
    relabel (σ * τ) c = relabel σ (relabel τ c) := by
  apply Subtype.ext
  rfl

lemma row_swap_unchanged (c : α → Fin 3) (a b : α) (i : Fin 3)
    (hai : c a ≠ i) (hbi : c b ≠ i) :
    row (fun x => c ((Equiv.swap a b).symm x)) i = row c i := by
  ext x
  simp only [mem_row, Equiv.symm_swap]
  by_cases hxa : x = a
  · subst x
    simp [hai, hbi]
  · by_cases hxb : x = b
    · subst x
      simp [hai, hbi]
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

lemma exists_unused_color (a b : Fin 3) : ∃ i : Fin 3, i ≠ a ∧ i ≠ b := by
  fin_cases a <;> fin_cases b <;> decide

lemma three_sum_sq_le_twice (f : Fin 3 → ℝ) (i : Fin 3) (hi : f i = 0) :
    (∑ j, f j) ^ 2 ≤ 2 * ∑ j, (f j) ^ 2 := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  fin_cases i
  · change f 0 = 0 at hi
    rw [hi]
    nlinarith [sq_nonneg (f 1 - f 2)]
  · change f 1 = 0 at hi
    rw [hi]
    nlinarith [sq_nonneg (f 0 - f 2)]
  · change f 2 = 0 at hi
    rw [hi]
    nlinarith [sq_nonneg (f 0 - f 1)]

lemma row_transposition_energy (c : α → Fin 3) (a b : α)
    (g : Fin 3 → Finset α → ℝ) :
    (∑ i, (g i (row c i) -
      g i (row (fun x => c ((Equiv.swap a b).symm x)) i))) ^ 2 ≤
    2 * ∑ i, (g i (row c i) -
      g i (row (fun x => c ((Equiv.swap a b).symm x)) i)) ^ 2 := by
  obtain ⟨i, hia, hib⟩ := exists_unused_color (c a) (c b)
  apply three_sum_sq_le_twice _ i
  rw [row_swap_unchanged c a b i (Ne.symm hia) (Ne.symm hib)]
  ring

lemma exists_relabel {sizes : Fin 3 → ℕ}
    (c d : Partition (α := α) sizes) :
    ∃ σ : Equiv.Perm α, relabel σ c = d := by
  classical
  have hcard (i : Fin 3) :
      Fintype.card {a : α // c.val a = i} = Fintype.card {a : α // d.val a = i} := by
    simpa [Fintype.card_subtype, row] using (c.property i).trans (d.property i).symm
  let e (i : Fin 3) : {a : α // c.val a = i} ≃ {a : α // d.val a = i} :=
    Fintype.equivOfCardEq (hcard i)
  let σ : Equiv.Perm α := Equiv.ofFiberEquiv e
  refine ⟨σ, Subtype.ext ?_⟩
  funext a
  have h := Equiv.ofFiberEquiv_map e (σ.symm a)
  change d.val (σ (σ.symm a)) = c.val (σ.symm a) at h
  change c.val (σ.symm a) = d.val a
  simpa only [Equiv.apply_symm_apply] using h.symm

lemma eq_of_swap_invariant {sizes : Fin 3 → ℕ}
    (f : Partition (α := α) sizes → ℝ)
    (hf : ∀ a b c, f (relabel (Equiv.swap a b) c) = f c)
    (c d : Partition (α := α) sizes) : f c = f d := by
  obtain ⟨σ, hσ⟩ := exists_relabel c d
  have hperm (σ : Equiv.Perm α) : ∀ c, f (relabel σ c) = f c := by
    induction σ using Equiv.Perm.swap_induction_on with
    | one => intro c; simp
    | swap_mul σ a b hab ih =>
      intro c
      rw [relabel_mul, hf, ih]
  rw [← hσ, hperm]

end Problem315.FixedBlock

end

end OAI
