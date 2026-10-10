import OAI.GroupTheory.PolycyclicRecognition.Algebra.RightTranslationInvariant
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ChartedVectorFieldBracket

namespace OAI

/-! # Smoothness of the actual adjoint action

Conjugation fixes the identity, so its parameter-dependent derivative has
constant source and target tangent spaces. The general derivative theorem
therefore gives smoothness in the ordinary operator norm.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Function
open scoped Manifold ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

def adjointLinearMap (g : G) : E →L[ℝ] E :=
  conjugationDifferentialHom (E := E) g

theorem contMDiff_conjugationDifferentialHom :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E →L[ℝ] E)) ∞
      (adjointLinearMap (E := E) (G := G)) := by
  let c : G → G → G := fun g h => g * h * g⁻¹
  have hc : ContMDiff ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E)) ∞ (uncurry c) :=
    (contMDiff_fst.mul contMDiff_snd).mul contMDiff_fst.inv
  intro g₀
  have h := (hc (g₀, 1)).mfderiv c (fun _ : G => (1 : G))
    (m := ∞) contMDiffAt_const (by simp)
  have heq : inTangentCoordinates (𝓘(ℝ, E)) (𝓘(ℝ, E))
      (fun _ : G => (1 : G)) (fun g => c g 1)
      (fun g => mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (c g) 1) g₀ =
      (adjointLinearMap (E := E) (G := G)) := by
    funext g
    rw [inTangentCoordinates_eq_mfderiv_comp_abuse]
    · have hrange : range (𝓘(ℝ, E)) = (univ : Set E) := by ext z; simp
      rw [hrange, mfderivWithin_univ]
      change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) (c g₀ 1))
          (c g 1) : E →L[ℝ] E).comp
          ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (c g) 1 : E →L[ℝ] E).comp
            (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) (1 : G)).symm
              (extChartAt (𝓘(ℝ, E)) (1 : G) 1) : E →L[ℝ] E)) = adjointLinearMap (E := E) g
      rw [show c g₀ 1 = 1 by simp [c], show c g 1 = 1 by simp [c],
        mfderiv_extChartAt_self, mfderiv_chart_symm_base]
      exact ContinuousLinearMap.ext fun _ => rfl
    · exact mem_chart_source _ _
    · simpa only [c, mul_one, mul_inv_cancel] using mem_chart_source E (1 : G)
  rw [heq] at h
  exact h

end PolycyclicRecognition

end

end OAI
