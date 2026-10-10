import OAI.GroupTheory.PolycyclicRecognition.Lattices.KernelCompletionHeight
import OAI.GroupTheory.PolycyclicRecognition.Lattices.IntegralLatticePowerIndex

namespace OAI

/-! # A compact vector cover for a finite-power integer lattice -/

noncomputable section
namespace PolycyclicRecognition

theorem integralRealHeight_power (n m : ℕ) (z : IntegralLatticeGroup n) :
    integralRealHeight (latticePowerHom n m z) = (m : ℝ) • integralRealHeight z := by
  change integralRealHeight (z ^ m) = _
  rw [map_pow]
  exact (Nat.cast_smul_eq_nsmul ℝ m (integralRealHeight z)).symm

theorem scaledIntegral_compact_cover (n : ℕ) {m : ℕ} (hm : 0 < m) :
    ∃ K : Set (AbelianRealSpace n), IsCompact K ∧
      ∀ v : AbelianRealSpace n, ∃ (z : IntegralLatticeGroup n) (k : AbelianRealSpace n),
        k ∈ K ∧ integralRealHeight (latticePowerHom n m z) + k = v := by
  obtain ⟨K, hK, hc⟩ := (abelianRealLattice_uniform n).2
  refine ⟨(fun x : AbelianRealSpace n => (m : ℝ) • x) '' K,
    hK.image (((m : ℝ) • LinearMap.id :
      AbelianRealSpace n →ₗ[ℝ] AbelianRealSpace n).toContinuousLinearMap.continuous), ?_⟩
  intro v
  obtain ⟨a, u, hu, he⟩ := hc ((m : ℝ)⁻¹ • v)
  obtain ⟨z, hz⟩ := (abelianRealLatticeEquiv n).surjective a
  have hza : integralRealHeight z = (a : AbelianRealSpace n) := congrArg Subtype.val hz
  refine ⟨z, (m : ℝ) • u, ⟨u, hu, rfl⟩, ?_⟩
  rw [integralRealHeight_power, hza, ← smul_add]
  change (m : ℝ) • ((a : AbelianRealSpace n) + u) = v
  change (a : AbelianRealSpace n) + u = (m : ℝ)⁻¹ • v at he
  rw [he, smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast Nat.ne_of_gt hm

end PolycyclicRecognition

end

end OAI
