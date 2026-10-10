import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingGateMotion
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarScaling
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarPulse

namespace OAI

/-! Every scaled translation gate is a linear combination of two fixed
compact smooth kernels. The scaling cancels between potential and gradient. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows PlanarHamiltonian VelocityDetector
open scoped ContDiff BigOperators

def gateKernel (j : Fin 2) : Plane → Plane :=
  translationGate (gateCutoff 1) 0 (PlanarHamiltonian.basis j)

theorem gateKernel_smooth (j : Fin 2) : ContDiff ℝ ∞ (gateKernel j) :=
  translationGate_smooth (gateCutoff_smooth 1) _ _

theorem gateKernel_compact (j : Fin 2) : HasCompactSupport (gateKernel j) :=
  translationGate_compactSupport (gateCutoff_compactSupport (by norm_num : (0 : ℝ) < 1)) _ _

theorem gateKernel_jet_bound (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ j : Fin 2, ∀ i ≤ m, ∀ x, ‖iteratedFDeriv ℝ i (gateKernel j) x‖ ≤ C := by
  obtain ⟨C₀, h₀, hb₀⟩ := (gateKernel_compact 0).exists_bound_iteratedFDeriv (gateKernel_smooth 0) m
  obtain ⟨C₁, h₁, hb₁⟩ := (gateKernel_compact 1).exists_bound_iteratedFDeriv (gateKernel_smooth 1) m
  refine ⟨max C₀ C₁, h₀.trans (le_max_left _ _), ?_⟩
  intro j i hi x
  fin_cases j
  · exact (hb₀ i hi x).trans (le_max_left _ _)
  · exact (hb₁ i hi x).trans (le_max_right _ _)

theorem field_affine_scale {H : Plane → ℝ} (hH : ContDiff ℝ ∞ H)
    (r : ℝ) (c x : Plane) :
    field (fun y => H (scalarAffineScale r c y)) x = r • field H (scalarAffineScale r c x) := by
  unfold field
  rw [spatialD_affine_scale hH, spatialD_affine_scale hH]
  module

theorem translationGate_unit_kernel (v x : Plane) :
    translationGate (gateCutoff 1) 0 v x = ∑ j : Fin 2, v j • gateKernel j x := by
  have hs (j : Fin 2) : ContDiff ℝ ∞
      (fun y => gateCutoff 1 y * translationPotential (PlanarHamiltonian.basis j) y) :=
    (gateCutoff_smooth 1).mul (translationPotential_smooth _)
  have he : (fun y => gateCutoff 1 y * translationPotential v y) =
      fun y => ∑ j : Fin 2, v j * (gateCutoff 1 y *
        translationPotential (PlanarHamiltonian.basis j) y) := by
    funext y
    simp only [Fin.sum_univ_two, translationPotential, basis_apply, Fin.reduceEq,
      ite_true, ite_false, one_mul, zero_mul, sub_zero, zero_sub]
    ring
  simp only [translationGate, sub_zero]
  rw [he, field_sum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [field_const_mul (hs j)]
    simp only [gateKernel, translationGate, sub_zero]
  · exact fun j _ => contDiff_const.mul (hs j)

theorem translationGate_scaled_kernel {R : ℝ} (hR : R ≠ 0) (c v x : Plane) :
    translationGate (gateCutoff R) c v x =
      ∑ j : Fin 2, v j • gateKernel j (scalarAffineScale R⁻¹ c x) := by
  let H := fun y => gateCutoff 1 y * translationPotential v y
  have hH : ContDiff ℝ ∞ H := (gateCutoff_smooth 1).mul (translationPotential_smooth v)
  have he : (fun y => gateCutoff R (y - c) * translationPotential v (y - c)) =
      fun y => R * H (scalarAffineScale R⁻¹ c y) := by
    funext y
    have hg : gateCutoff R (y - c) = gateCutoff 1 (scalarAffineScale R⁻¹ c y) := by
      unfold gateCutoff scalarAffineScale
      congr 1
      funext j
      simp [div_eq_mul_inv, mul_comm]
    rw [hg]
    dsimp [H, scalarAffineScale, translationPotential]
    field_simp [hR]
  have hs : ContDiff ℝ ∞ (fun y => H (scalarAffineScale R⁻¹ c y)) :=
    hH.comp (scalarAffineScale_smooth _ _)
  rw [translationGate, he, field_const_mul hs, field_affine_scale hH]
  rw [smul_smul, mul_inv_cancel₀ hR, one_smul]
  simpa only [translationGate, sub_zero, H] using
    translationGate_unit_kernel v (scalarAffineScale R⁻¹ c x)

end ForcedComputation.ExpandingDetector

end

end OAI
