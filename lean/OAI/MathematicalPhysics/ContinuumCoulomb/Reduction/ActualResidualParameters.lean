import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedResidualParameters
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCounterterms

namespace OAI

/-! The counterterm size in the residual theorem is computed from the
actual orbital Coulomb sums; no independent coefficient bound is assumed. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem actual_counterterm_scale_bound {freq N a : ℝ} (hf : 0 < freq)
    (hN : 0 < N) (ha : 0 < a) (r k : ℕ) {m : ℕ}
    (u : Fin m → PlanarPosition) (hm : (m:ℝ) ≤ N^r) (i : Fin m) :
    0 ≤ localizedCounterterm freq u i/(a*(N^k)^30) ∧
      localizedCounterterm freq u i/(a*(N^k)^30) ≤
        localizedCountertermBound freq*N^r/(a*(N^k)^30) := by
  refine ⟨div_nonneg (localizedCounterterm_nonnegative freq u i) (by positivity),?_⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (localizedCounterterm_bound hf u i).trans (by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hm (localizedCountertermBound_nonnegative freq))

theorem exists_actual_manufactured_residual_parameters {freq rho a : ℝ}
    (hf : 0 < freq) (hrho : 0 ≤ rho) (ha : 0 < a) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ r s k : ℕ, k₀+7*r+72*s ≤ k → ∀ N : ℝ, 2 ≤ N →
      ∀ H S D : ℝ, (N^k)^50 ≤ H → H ≤ 2*(N^k)^50 →
        (N^k)^5 ≤ S → S ≤ 2*(N^k)^5 → 25*(k:ℝ)*Real.log N ≤ D →
      ∀ (m : ℕ) (u : Fin m → PlanarPosition), (m:ℝ) ≤ N^r → (∀ j, ‖u j‖ ≤ N^s) →
        let η := localizedCountertermBound freq*N^r/(a*(N^k)^30)
        (∀ i, 0 ≤ localizedCounterterm freq u i/(a*(N^k)^30) ∧
          localizedCounterterm freq u i/(a*(N^k)^30) ≤ η) ∧
        0 ≤ η ∧ η ≤ 1 ∧ 4*(m:ℝ)^2*(∑ j,
          manufacturedOrbitalSquaredError rho H S freq η D ((N^k)^5) u j) ≤
          ((N^k)^19)⁻¹^2 := by
  obtain ⟨k₀,hk₀,hbound⟩ := exists_manufactured_residual_parameter_offset hf hrho ha
    (localizedCountertermBound_nonnegative freq)
  refine ⟨k₀,hk₀,?_⟩
  intro r s k hk N hN H S D hHlo hHhi hSlo hShi hD m u hm hu
  have hN0 : 0 < N := by linarith
  dsimp only
  have hη : 0 ≤ localizedCountertermBound freq*N^r/(a*(N^k)^30) :=
    div_nonneg (mul_nonneg (localizedCountertermBound_nonnegative freq) (by positivity)) (by positivity)
  have hb := hbound r s k hk N hN H S D _ hHlo hHhi hSlo hShi hD hη le_rfl m u hm hu
  exact ⟨actual_counterterm_scale_bound hf hN0 ha r k u hm,hη,hb⟩

end ContinuumCoulomb

end

end OAI
