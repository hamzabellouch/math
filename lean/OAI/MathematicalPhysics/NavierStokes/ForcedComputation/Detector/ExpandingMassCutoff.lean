import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingGateProfile
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarComparison

namespace OAI

/-! A smooth concentration cutoff with one fixed finite integer bound on
its Laplacian. The bound is proved from compact support. It can be baked
into a finite force program and does not depend on a machine or viscosity. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows PlanarHamiltonian VelocityDetector Set
open scoped ContDiff Topology

def massCutoff : Plane → ℝ := gateCutoff (1 / 3)

theorem massCutoff_smooth : ContDiff ℝ ∞ massCutoff := gateCutoff_smooth _

theorem massCutoff_compactSupport : HasCompactSupport massCutoff :=
  gateCutoff_compactSupport (by norm_num)

theorem massCutoff_range (x : Plane) : massCutoff x ∈ Icc (0 : ℝ) 1 := gateCutoff_range _ x

theorem massCutoff_support : tsupport massCutoff ⊆ {x | ∀ j, |x j| ≤ 1} := by
  simpa only [massCutoff, show (3 : ℝ) * (1 / 3) = 1 by norm_num] using
    (gateCutoff_tsupport (by norm_num : (0 : ℝ) < 1 / 3))

theorem massCutoff_one_near {x : Plane} (hx : ∀ j, |x j| < 2 / 3) :
    massCutoff =ᶠ[𝓝 x] fun _ => 1 := by
  apply gateCutoff_one_near (by norm_num : (0 : ℝ) < 1 / 3)
  intro j
  convert hx j using 1
  norm_num

theorem scalarLaplacian_compactSupport {f : Plane → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (scalarLaplacian f) := by
  have h₀ := (hf.fderiv_apply ℝ (basis 0)).fderiv_apply ℝ (basis 0)
  have h₁ := (hf.fderiv_apply ℝ (basis 1)).fderiv_apply ℝ (basis 1)
  have he : scalarLaplacian f = (fun x => spatialD 0 (spatialD 0 f) x +
      spatialD 1 (spatialD 1 f) x) := by
    funext x
    simp only [scalarLaplacian, Fin.sum_univ_two]
  rw [he]
  exact h₀.add h₁

theorem scalarLaplacian_smooth {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (scalarLaplacian f) := by
  unfold scalarLaplacian
  exact ContDiff.sum (fun j _ => spatialD_smooth j (spatialD_smooth j hf))

theorem massCutoff_laplacian_bound :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ x, |scalarLaplacian massCutoff x| ≤ C := by
  obtain ⟨B, hB⟩ := (scalarLaplacian_smooth massCutoff_smooth).continuous.bounded_above_of_compact_support (scalarLaplacian_compactSupport massCutoff_compactSupport)
  let C : ℕ := ⌈max 1 B⌉₊
  have hC : max 1 B ≤ (C : ℝ) := Nat.le_ceil _
  have h₁ : (1 : ℝ) ≤ C := (le_max_left _ _).trans hC
  refine ⟨C, by exact_mod_cast h₁, ?_⟩
  intro x
  exact (show |scalarLaplacian massCutoff x| ≤ B by
    simpa only [Real.norm_eq_abs] using hB x).trans ((le_max_right _ _).trans hC)

end ForcedComputation.ExpandingDetector

end

end OAI
