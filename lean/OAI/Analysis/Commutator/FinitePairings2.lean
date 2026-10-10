import Mathlib
import OAI.Analysis.Commutator.Pairings

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

namespace Kadison.Pairing

variable {J : Type*} [LinearOrder J]

def finiteLabels (σ : Pairing J) (p : J) {N : ℕ} (n : Fin (N+1)) (j : J) :
    J × Fin (N+1) :=
  (repr σ j, if repr σ j = repr σ p then n else 0)

@[simp] lemma finiteLabels_eq_iff (σ : Pairing J) (p : J) {N : ℕ}
    (n : Fin (N+1)) (i j : J) :
    finiteLabels σ p n i = finiteLabels σ p n j ↔ j = i ∨ j = σ i := by
  constructor
  · intro h
    exact (repr_eq_iff σ i j).mp (congrArg Prod.fst h)
  · intro h
    have hh := (repr_eq_iff σ i j).mpr h
    simp only [finiteLabels, hh]

variable [Fintype J]

lemma finite_contraction_isolation {E : Type*} (τ σ : Pairing J) (p : J) {N : ℕ}
    (n : Fin (N+1)) (v : J × Fin (N+1) → E) (B : E → E → ℂ)
    (hv : ∀ a b, B (v a) (v b) = if a = b then 1 else 0) :
    contraction σ B (fun j => v (finiteLabels τ p n j)) = if σ = τ then 1 else 0 := by
  classical
  unfold contraction
  simp_rw [hv]
  rw [Finset.prod_ite_zero]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.prod_const_one]
  have he : (∀ j, j < σ j → finiteLabels τ p n j = finiteLabels τ p n (σ j)) ↔ σ = τ := by
    rw [pair_tests_iff]
    constructor
    · intro h
      apply ext
      intro j
      rcases (finiteLabels_eq_iff τ p n j (σ j)).mp (h j) with hh | hh
      · exact (σ.apply_ne j hh).elim
      · exact hh
    · rintro rfl j
      exact (finiteLabels_eq_iff σ p n j (σ j)).mpr (Or.inr rfl)
  simp only [he]

end Kadison.Pairing
end

end OAI
