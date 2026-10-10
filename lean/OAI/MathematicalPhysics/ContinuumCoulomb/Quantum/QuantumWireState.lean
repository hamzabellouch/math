import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPaddedGate

namespace OAI

/-! Exact state and measurement transport under wire permutations. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaWirePermutation_apply {n : ℕ}
    (e : SourceSpinBasis n ≃ SourceSpinBasis n)
    (u : EuclideanSpace ℂ (SourceSpinBasis n)) (s : SourceSpinBasis n) :
    qmaApplyMatrix (qmaWirePermutation e) u s = u (e.symm s) := by
  change (∑ t, (if s = e t then (1:ℂ) else 0)*u t) = _
  rw [Finset.sum_eq_single (e.symm s)]
  · simp
  · intro t _ ht
    have hs : s ≠ e t := fun h => ht ((e.eq_symm_apply.mpr h.symm))
    simp [hs]
  · simp

theorem qmaWirePermutation_norm {n : ℕ}
    (e : SourceSpinBasis n ≃ SourceSpinBasis n)
    (u : EuclideanSpace ℂ (SourceSpinBasis n)) :
    ‖qmaApplyMatrix (qmaWirePermutation e) u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,qmaWirePermutation_apply]
  exact e.symm.sum_comp (fun s => ‖u s‖^2)

theorem qmaWirePermutation_mask {n : ℕ} (σ : Equiv.Perm (Fin n))
    (i : Fin n) (b : Fin 2) (u : EuclideanSpace ℂ (SourceSpinBasis n)) :
    qmaMask (fun s => s (σ.symm i) = b)
      (qmaApplyMatrix (qmaWirePermutation (qmaWireBasis σ)) u) =
    qmaApplyMatrix (qmaWirePermutation (qmaWireBasis σ)) (qmaMask (fun s => s i = b) u) := by
  ext s
  simp only [qmaMask_apply,qmaWirePermutation_apply,qmaWireBasis_symm]
  rfl

theorem qmaWirePermutation_probability {n : ℕ} (σ : Equiv.Perm (Fin n))
    (i : Fin n) (b : Fin 2) (u : EuclideanSpace ℂ (SourceSpinBasis n)) :
    ‖qmaMask (fun s => s (σ.symm i) = b)
      (qmaApplyMatrix (qmaWirePermutation (qmaWireBasis σ)) u)‖^2 =
    ‖qmaMask (fun s => s i = b) u‖^2 := by
  rw [qmaWirePermutation_mask,qmaWirePermutation_norm]

end ContinuumCoulomb

end

end OAI
