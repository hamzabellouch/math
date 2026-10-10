import Mathlib

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison

abbrev Pairing (J : Type*) := {σ : Equiv.Perm J // Function.Involutive σ ∧ ∀ j, σ j ≠ j}

namespace Pairing

variable {J : Type*}

instance : CoeFun (Pairing J) (fun _ => J → J) := ⟨fun σ => σ.val⟩

@[simp] theorem apply_apply (σ : Pairing J) (j : J) : σ (σ j) = j := σ.property.1 j

theorem apply_ne (σ : Pairing J) (j : J) : σ j ≠ j := σ.property.2 j

theorem injective (σ : Pairing J) : Function.Injective σ := σ.val.injective

@[ext] theorem ext (σ τ : Pairing J) (h : ∀ j, σ j = τ j) : σ = τ := by
  apply Subtype.ext
  exact Equiv.ext h

instance [Fintype J] : Fintype (Pairing J) := Fintype.ofFinite _

instance : DecidableEq (Pairing J) := Classical.decEq _

variable [LinearOrder J]

def repr (σ : Pairing J) (j : J) : J := min j (σ j)

@[simp] theorem repr_apply (σ : Pairing J) (j : J) : repr σ (σ j) = repr σ j := by
  simp only [repr, apply_apply, min_comm]

theorem repr_eq_iff (σ : Pairing J) (i j : J) :
    repr σ i = repr σ j ↔ j = i ∨ j = σ i := by
  constructor
  · intro h
    unfold repr at h
    rcases le_total i (σ i) with hi | hi <;>
      rcases le_total j (σ j) with hj | hj
    · rw [min_eq_left hi, min_eq_left hj] at h
      exact Or.inl h.symm
    · rw [min_eq_left hi, min_eq_right hj] at h
      exact Or.inr (by simpa only [apply_apply] using congrArg σ h.symm)
    · rw [min_eq_right hi, min_eq_left hj] at h
      exact Or.inr h.symm
    · rw [min_eq_right hi, min_eq_right hj] at h
      exact Or.inl (σ.injective h).symm
  · rintro (rfl | rfl)
    · rfl
    · exact (repr_apply σ i).symm

def labels (σ : Pairing J) (p : J) (n : ℕ) (j : J) : J × ℕ :=
  (repr σ j, if repr σ j = repr σ p then n else 0)

@[simp] theorem labels_eq_iff (σ : Pairing J) (p : J) (n : ℕ) (i j : J) :
    labels σ p n i = labels σ p n j ↔ j = i ∨ j = σ i := by
  constructor
  · intro h
    exact (repr_eq_iff σ i j).mp (congrArg Prod.fst h)
  · intro h
    have hh := (repr_eq_iff σ i j).mpr h
    simp only [labels, hh]

variable [Fintype J]

def contraction {E : Type*} (σ : Pairing J) (B : E → E → ℂ) (v : J → E) : ℂ :=
  ∏ j ∈ Finset.univ.filter (fun j => j < σ j), B (v j) (v (σ j))

omit [Fintype J] in
theorem pair_tests_iff {L : Type*} (σ : Pairing J) (f : J → L) :
    (∀ j, j < σ j → f j = f (σ j)) ↔ ∀ j, f j = f (σ j) := by
  constructor
  · intro h j
    rcases lt_or_gt_of_ne (σ.apply_ne j).symm with hj | hj
    · exact h j hj
    · have hh := h (σ j) (by simpa only [apply_apply] using hj)
      simpa only [apply_apply] using hh.symm
  · intro h j _
    exact h j

theorem contraction_isolation {E : Type*} (τ σ : Pairing J) (p : J) (n : ℕ)
    (v : J × ℕ → E) (B : E → E → ℂ)
    (hv : ∀ a b, B (v a) (v b) = if a = b then 1 else 0) :
    contraction σ B (fun j => v (labels τ p n j)) = if σ = τ then 1 else 0 := by
  classical
  unfold contraction
  simp_rw [hv]
  rw [Finset.prod_ite_zero]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.prod_const_one]
  have he : (∀ j, j < σ j → labels τ p n j = labels τ p n (σ j)) ↔ σ = τ := by
    rw [pair_tests_iff]
    constructor
    · intro h
      apply ext
      intro j
      rcases (labels_eq_iff τ p n j (σ j)).mp (h j) with hh | hh
      · exact (σ.apply_ne j hh).elim
      · exact hh
    · rintro rfl
      intro j
      exact (labels_eq_iff σ p n j (σ j)).mpr (Or.inr rfl)
  simp only [he]

end Pairing

end Kadison
end

end OAI
