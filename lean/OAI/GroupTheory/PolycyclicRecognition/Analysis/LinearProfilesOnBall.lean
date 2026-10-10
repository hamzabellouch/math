import OAI.GroupTheory.PolycyclicRecognition.Analysis.AffineScaleStabilization

namespace OAI

/-! # Finite linear profiles tested on one fixed ball -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem linearMap_eq_of_eqOn_closedBall {R : ℝ} (hR : 0 < R)
    (f g : V →ₗ[ℝ] W) (h : EqOn f g (Metric.closedBall 0 R)) : f = g := by
  ext x
  let c := R / (‖x‖ + 1)
  have hc : 0 < c := div_pos hR (by positivity)
  have hx : c • x ∈ Metric.closedBall 0 R := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    calc
      c * ‖x‖ ≤ c * (‖x‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) hc.le
      _ = R := div_mul_cancel₀ _ (by positivity)
  have hh := h hx
  rw [map_smul, map_smul] at hh
  exact smul_right_injective W hc.ne' hh

/-- An ambient linear label observed through a surjective height map. -/
def linearBallProfile (q : V →L[ℝ] W) (A : W →L[ℝ] W) (R : ℝ) :
    C(Metric.closedBall (0 : V) R, W) :=
  ⟨fun z => A (q z), A.continuous.comp (q.continuous.comp continuous_subtype_val)⟩

theorem linearBallProfile_injective (q : V →L[ℝ] W) (hq : Function.Surjective q)
    {R : ℝ} (hR : 0 < R) : Function.Injective (fun A => linearBallProfile q A R) := by
  intro A B h
  have he : A.toLinearMap.comp q.toLinearMap = B.toLinearMap.comp q.toLinearMap :=
    linearMap_eq_of_eqOn_closedBall hR _ _ (fun z hz =>
      congrArg (fun f : C(Metric.closedBall (0 : V) R, W) => f ⟨z, hz⟩) h)
  ext w
  obtain ⟨v, rfl⟩ := hq w
  exact DFunLike.congr_fun he v

/-- A linear contraction restricts continuously to the same ball. -/
def closedBallLinearSelf (ψ : V →L[ℝ] V) (hψ : ∀ x, ‖ψ x‖ ≤ ‖x‖) (R : ℝ) :
    C(Metric.closedBall (0 : V) R, Metric.closedBall (0 : V) R) := by
  let f : Metric.closedBall (0 : V) R → Metric.closedBall (0 : V) R :=
    fun z => ⟨ψ z, by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hψ z).trans (by simpa only [Metric.mem_closedBall, dist_zero_right] using z.property)⟩
  exact ⟨f, (ψ.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem linearBallProfile_rescale (q : V →L[ℝ] W) (A : W →L[ℝ] W)
    (ψ : V →L[ℝ] V) (hψ : ∀ x, ‖ψ x‖ ≤ ‖x‖) (R t : ℝ)
    (he : ∀ x, t • q (ψ x) = q x) (z : Metric.closedBall (0 : V) R) :
    t • linearBallProfile q A R (closedBallLinearSelf ψ hψ R z) =
      linearBallProfile q A R z := by
  change t • A (q (ψ z)) = A (q z)
  rw [← map_smul, he]

end PolycyclicRecognition

end

end OAI
