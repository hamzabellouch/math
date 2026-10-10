import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ScalarScaleBudgets

namespace OAI

/-! The physical scale lies in the domain required by the numerical field
program after a fixed, input-independent exponent threshold. -/

noncomputable section
namespace ContinuumCoulomb

theorem exists_manufactured_scale_threshold {a : ℝ} (ha : 0 < a) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ k : ℕ, q ≤ k → ∀ N : ℝ, 2 ≤ N → 1 ≤ a*(N^k)^30 := by
  obtain ⟨q,hq,hbound⟩ := exists_polynomial_constant_bounds ha 1
  refine ⟨q,by omega,fun k hk N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hinv : 1/(N^k)^30 ≤ a := by
    calc
      _ ≤ (N^q)⁻¹ := by
        rw [one_div]
        apply inv_anti₀ (by positivity)
        rw [← pow_mul]
        exact pow_le_pow_right₀ hN1 (by omega)
      _ ≤ _ := (hbound N hN).1
  exact (div_le_iff₀ (by positivity : 0 < (N^k)^30)).mp hinv

end ContinuumCoulomb

end

end OAI
