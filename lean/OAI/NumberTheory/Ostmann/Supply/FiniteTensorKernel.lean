import Mathlib.Data.Fin.Tuple.Basic
import OAI.NumberTheory.Ostmann.Characters.TensorKernelEnergy

namespace OAI

/-! # Finite products of the local residue matrices -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

universe u v

theorem kernel_energy_reindex {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (M : α → β → ℂ) (A : ℝ)
    (hM : ∀ f : β → ℂ, (∑ x, ‖∑ y, M x y * f y‖ ^ 2) ≤ A ^ 2 * ∑ y, ‖f y‖ ^ 2)
    (e : γ ≃ α) (d : δ ≃ β) (f : δ → ℂ) :
    (∑ x, ‖∑ y, M (e x) (d y) * f y‖ ^ 2) ≤ A ^ 2 * ∑ y, ‖f y‖ ^ 2 := by
  have hi (x : γ) : (∑ y, M (e x) (d y) * f y) =
      ∑ y, M (e x) y * f (d.symm y) := by
    exact Fintype.sum_equiv d _ _ (by intro y; simp)
  simp_rw [hi]
  rw [e.sum_comp (fun x => ‖∑ y, M x y * f (d.symm y)‖ ^ 2)]
  convert hM (fun y => f (d.symm y)) using 1
  rw [d.symm.sum_comp (fun y => ‖f y‖ ^ 2)]

noncomputable def finiteTensorKernel {ι : Type*} [Fintype ι]
    {α : ι → Type u} {β : ι → Type v} (M : ∀ i, α i → β i → ℂ)
    (x : ∀ i, α i) (y : ∀ i, β i) : ℂ := ∏ i, M i (x i) (y i)

/-- Iterating the two-factor bound never introduces the sizes of the residue fields. -/
theorem finiteTensorKernel_energy_le {n : ℕ}
    (α : Fin n → Type u) (β : Fin n → Type v)
    [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    (M : ∀ i, α i → β i → ℂ) (A : Fin n → ℝ)
    (hM : ∀ i (f : β i → ℂ), (∑ x, ‖∑ y, M i x y * f y‖ ^ 2) ≤ A i ^ 2 * ∑ y, ‖f y‖ ^ 2)
    (f : (∀ i, β i) → ℂ) :
    (∑ x, ‖∑ y, finiteTensorKernel M x y * f y‖ ^ 2) ≤
      (∏ i, A i) ^ 2 * ∑ y, ‖f y‖ ^ 2 := by
  induction n with
  | zero => simp [finiteTensorKernel]
  | succ n ih =>
    have ht := tensorKernel_energy_le (M 0)
      (finiteTensorKernel (fun i : Fin n => M i.succ)) (A 0) (∏ i : Fin n, A i.succ)
      (hM 0) (ih (fun i => α i.succ) (fun i => β i.succ)
        (fun i => M i.succ) (fun i => A i.succ) (fun i => hM i.succ))
    have hr := kernel_energy_reindex _ _ ht (Fin.consEquiv α).symm
      (Fin.consEquiv β).symm f
    simpa only [finiteTensorKernel, Fin.prod_univ_succ, tensorKernel,
      Fin.consEquiv_symm_apply, Fin.tail] using hr

/-- Tensor coordinates evaluate as the product of the local kernel pairings. -/
theorem finiteTensorKernel_pairing {ι : Type*} [Fintype ι]
    {α : ι → Type u} {β : ι → Type v}
    [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    (M : ∀ i, α i → β i → ℂ) (a : ∀ i, α i → ℂ) (b : ∀ i, β i → ℂ) :
    (∑ x, conj (∏ i, a i (x i)) * ∑ y, finiteTensorKernel M x y * ∏ i, b i (y i)) =
      ∏ i, ∑ x, conj (a i x) * ∑ y, M i x y * b i y := by
  have hi (x : ∀ i, α i) :
      (∑ y, finiteTensorKernel M x y * ∏ i, b i (y i)) =
        ∏ i, ∑ y, M i (x i) y * b i y := by
    simp only [finiteTensorKernel, ← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i y => M i (x i) y * b i y)).symm
  simp only [hi, map_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => conj (a i x) * ∑ y, M i x y * b i y)).symm

end Ostmann

end OAI
