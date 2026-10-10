import Mathlib
import OAI.Analysis.Commutator.CycleInvariants2

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.SchurWeyl

variable {𝕜 I J : Type*} [CommRing 𝕜] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

theorem rawCycleTrace_zero_of_fixed_centered (σ : Equiv.Perm J)
    (A : J → Matrix I I 𝕜) (j : J) (hj : σ j = j)
    (htrace : Matrix.trace (A j) = 0) : rawCycleTrace σ A = 0 := by
  classical
  have hne (r : {r : J // r ≠ j}) : σ r.1 ≠ j := by
    intro he
    exact r.2 (σ.injective (he.trans hj.symm))
  let C (b : {r : J // r ≠ j} → I) : 𝕜 :=
    ∏ r : {r : J // r ≠ j}, A r.1 (b ⟨σ r.1, hne r⟩) (b r)
  have hprod (b : {r : J // r ≠ j} → I) (i : I) :
      (∏ r, A r ((Equiv.funSplitAt j I).symm (i, b) (σ r))
        ((Equiv.funSplitAt j I).symm (i, b) r)) = A j i i * C b := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ j]
    simp only [hj, Equiv.funSplitAt_symm_apply]
    congr 1
    apply Finset.prod_congr rfl
    intro r _
    simp [hne r, r.2]
  rw [rawCycleTrace_eq_sum]
  calc
    _ = ∑ bi : I × ({r : J // r ≠ j} → I),
        ∏ r, A r ((Equiv.funSplitAt j I).symm bi (σ r))
          ((Equiv.funSplitAt j I).symm bi r) := by
      exact Fintype.sum_equiv (Equiv.funSplitAt j I) _ _
        (fun _ => by simp only [Equiv.symm_apply_apply])
    _ = ∑ b : {r : J // r ≠ j} → I, ∑ i : I, A j i i * C b := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_congr rfl (fun i _ => hprod b i)
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      rw [← Finset.sum_mul]
      change Matrix.trace (A j) * C b = 0
      rw [htrace, zero_mul]

theorem cycleTrace_zero_of_fixed_centered (σ : Equiv.Perm J)
    (A : J → Matrix I I ℂ) (j : J) (hj : σ j = j)
    (htrace : Matrix.trace (A j) = 0) : cycleTrace σ A = 0 := by
  rw [cycleTrace, rawCycleTrace_zero_of_fixed_centered σ A j hj htrace, mul_zero]

theorem centered_expansion_pairings (a : J) (d : Equiv.Perm J → ℂ)
    (hd : ∀ σ, 2 * cycleCount σ < Fintype.card J + 1 → d σ = 0)
    (A : J → Matrix I I ℂ) (hA : ∀ j, j ≠ a → Matrix.trace (A j) = 0) :
    (∑ σ, d σ * cycleTrace σ A) =
      ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm J =>
        σ a = a ∧ (∀ j, σ (σ j) = j) ∧ ∀ j, σ j = j → j = a),
      d σ * cycleTrace σ A := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro σ _ hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn
  by_cases he : 2 * cycleCount σ < Fintype.card J + 1
  · rw [hd σ he, zero_mul]
  by_cases hf : ∀ j, σ j = j → j = a
  · obtain ⟨ha, hi⟩ := endpoint_cycle_classification σ a hf (Nat.le_of_not_gt he)
    exact (hn ⟨ha, hi, hf⟩).elim
  · obtain ⟨j, hj, hja⟩ := by simpa only [not_forall, Classical.not_imp] using hf
    rw [cycleTrace_zero_of_fixed_centered σ A j hj (hA j hja), mul_zero]

end Kadison.SchurWeyl
end

end OAI
