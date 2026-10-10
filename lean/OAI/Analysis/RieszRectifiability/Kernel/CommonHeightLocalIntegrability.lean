import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.IntrinsicHeightData
import OAI.Analysis.RieszRectifiability.Kernel.LocalHeightData

namespace OAI

/-!
# Intrinsic local integrability of common heights

Square integrability on bounded projection regions implies integrability on every
plane ball, since the coordinate-plane measure has finite mass there. Pulling
these ball restrictions back along an affine isometric parametrization gives
local integrability of the intrinsic height function on Euclidean space.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal Topology

theorem locallyIntegrable_of_integrableOn_origin_balls {d : ℕ}
    (f : Ambient d → ℝ)
    (hf : ∀ R : ℝ, 0 < R → IntegrableOn f (ball 0 R)) : LocallyIntegrable f := by
  intro x
  refine ⟨ball 0 (‖x‖ + 1), isOpen_ball.mem_nhds ?_, hf _ (by positivity)⟩
  simp only [mem_ball, dist_zero_right]
  linarith

theorem common_height_intrinsic_locallyIntegrable {n d : ℕ}
    (e : (Fin n → ℝ) → Ambient d) (π : Ambient d → Fin n → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π)
    (hleft : LeftInverse π e) (a : Ambient d) (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (hplane : e = affinePlaneSection a L) (f : Ambient d → ℝ)
    (hf : ∀ H, MemLp f 2
      ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) :
    LocallyIntegrable (fun x : Ambient n => f (a + L x)) := by
  have he0 : e 0 = a := by rw [hplane]; simp [affinePlaneSection]
  have hνg : GlobalUpperGrowth n ((2 * (Q : ℝ)) ^ n) (coordinatePlaneMeasure e) := by
    simpa only [Fintype.card_fin] using! coordinatePlaneMeasure_upper_growth e π
      he.continuous.measurable Q hπ hleft
  apply locallyIntegrable_of_integrableOn_origin_balls
  intro R hR
  obtain ⟨H, hH⟩ := (eventually_ball_subset_boundedProjectionRegion e π K Q hπ hleft R).exists
  have hmem : MemLp f 2 ((coordinatePlaneMeasure e).restrict (ball (e 0) R)) :=
    MemLp.mono_measure (Measure.restrict_mono hH le_rfl) (hf H)
  let : IsFiniteMeasure ((coordinatePlaneMeasure e).restrict (ball (e 0) R)) :=
    finiteMeasure_restrict_ball_of_globalGrowth n ((2 * (Q : ℝ)) ^ n)
      (coordinatePlaneMeasure e) hνg (e 0) R hR
  have hi : IntegrableOn f (ball (e 0) R) (coordinatePlaneMeasure e) :=
    hmem.integrable (by norm_num)
  rw [he0, hplane] at hi
  exact height_local_integrable_affine_pullback a L f R hi

end

end RieszRectifiability

end OAI
