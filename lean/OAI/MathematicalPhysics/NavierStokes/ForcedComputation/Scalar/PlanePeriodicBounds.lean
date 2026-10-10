import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.TorusGeometry
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Regularity

namespace OAI

/-! Uniform bounds and a torus-distance modulus for smooth periodic data. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Set
open scoped ContDiff NNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
theorem planePeriodic_bound {g : Plane → F} (hg : Continuous g) (hp : PlanePeriodic g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖g x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : Plane) (fun _ => 1))).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  let y : Plane := fun j => x j - (⌊x j⌋ : ℤ)
  have hy : y ∈ Icc (0 : Plane) (fun _ => 1) := by
    constructor
    · intro j
      change 0 ≤ Int.fract (x j)
      exact Int.fract_nonneg _
    · intro j
      change Int.fract (x j) ≤ 1
      exact (Int.fract_lt_one _).le
  have he : y + (fun j => ((⌊x j⌋ : ℤ) : ℝ)) = x := by
    ext j
    simp [y]
  have hv := hp y (fun j => ⌊x j⌋)
  rw [he] at hv
  rw [hv]
  exact (hC y hy).trans (le_max_left _ _)

theorem planePeriodic_fderiv {g : Plane → F} (hg : Differentiable ℝ g)
    (hp : PlanePeriodic g) : PlanePeriodic (fderiv ℝ g) := by
  intro x n
  exact fderiv_translation hg (fun y => hp y n) x

theorem planePeriodic_lipschitz {g : Plane → F} (hg : ContDiff ℝ 1 g)
    (hp : PlanePeriodic g) : ∃ K : ℝ≥0, LipschitzWith K g := by
  obtain ⟨C, hC, hbound⟩ := planePeriodic_bound (hg.continuous_fderiv (by simp))
    (planePeriodic_fderiv (hg.differentiable (by simp)) hp)
  refine ⟨⟨C, hC⟩, lipschitzWith_of_nnnorm_fderiv_le (hg.differentiable (by simp)) ?_⟩
  intro x
  exact_mod_cast hbound x

omit [NormedSpace ℝ F] in
theorem planePeriodic_norm_sub_le_torus {g : Plane → F} {K : ℝ≥0}
    (hK : LipschitzWith K g) (hp : PlanePeriodic g) (x y : Plane) :
    ‖g x - g y‖ ≤ K * VelocityDetector.torusNorm (x - y) := by
  let z := y + VelocityDetector.centeredRepresentative (x - y)
  have he : z + (fun j => ((⌊(x - y) j + 1 / 2⌋ : ℤ) : ℝ)) = x := by
    ext j
    simp only [z, VelocityDetector.centeredRepresentative, Pi.add_apply, Pi.sub_apply]
    ring
  have hz : g z = g x := by
    have h := hp z (fun j => ⌊(x - y) j + 1 / 2⌋)
    rw [he] at h
    exact h.symm
  have hn : ‖z - y‖ ≤ VelocityDetector.torusNorm (x - y) := by
    have he' : z - y = VelocityDetector.centeredRepresentative (x - y) := by
      dsimp [z]
      abel
    rw [he']
    exact planeCoordinates_norm_le
      (planeCoordinates.symm (VelocityDetector.centeredRepresentative (x - y)))
  rw [← hz]
  exact (hK.norm_sub_le z y).trans (mul_le_mul_of_nonneg_left hn K.coe_nonneg)

end ForcedComputation

end

end OAI
