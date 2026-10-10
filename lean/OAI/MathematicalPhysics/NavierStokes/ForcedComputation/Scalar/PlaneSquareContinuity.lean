import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneMassContinuity

namespace OAI

/-! An integrable square envelope upgrades pointwise time continuity to
continuity of the squared L2 distance. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows MeasureTheory Set Filter
open scoped Topology

theorem square_distance_continuousOn {F : ℝ → Plane → ℝ} {S : Set ℝ}
    {b : Plane → ℝ}
    (hspace : ∀ t ∈ S, Continuous (F t))
    (htime : ∀ x, ContinuousOn (fun t => F t x) S)
    (hb : Integrable (fun x => b x ^ 2))
    (hbound : ∀ t ∈ S, ∀ x, |F t x| ≤ b x)
    {s : ℝ} (hs : s ∈ S) :
    ContinuousOn (fun t => ∫ x, (F t x - F s x) ^ 2) S := by
  apply continuousOn_of_dominated
    (fun t ht => ((hspace t ht).sub (hspace s hs)).pow 2 |>.aestronglyMeasurable)
    (bound := fun x => 4 * b x ^ 2)
  · intro t ht
    filter_upwards [] with x
    have hb0 : 0 ≤ b x := (abs_nonneg _).trans (hbound s hs x)
    have hd : |F t x - F s x| ≤ 2 * b x :=
      (abs_sub _ _).trans (by linarith [hbound t ht x, hbound s hs x])
    have hsq := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * b x)).mpr hd
    change ‖(F t x - F s x) ^ 2‖ ≤ 4 * b x ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (F t x - F s x)]
  · exact hb.const_mul 4
  · exact Filter.Eventually.of_forall (fun x => ((htime x).sub continuousOn_const).pow 2)

def SquareDistanceContinuousOn (F : ℝ → Plane → ℝ) (S : Set ℝ) : Prop :=
  ∀ s ∈ S, Tendsto (fun t => ∫ x, (F t x - F s x) ^ 2) (𝓝[S] s) (𝓝 0)

theorem squareDistanceContinuousOn_of_envelope {F : ℝ → Plane → ℝ} {S : Set ℝ}
    {b : Plane → ℝ}
    (hspace : ∀ t ∈ S, Continuous (F t))
    (htime : ∀ x, ContinuousOn (fun t => F t x) S)
    (hb : Integrable (fun x => b x ^ 2))
    (hbound : ∀ t ∈ S, ∀ x, |F t x| ≤ b x) :
    SquareDistanceContinuousOn F S := by
  intro s hs
  have hh := square_distance_continuousOn hspace htime hb hbound hs s hs
  simpa [ContinuousWithinAt] using hh

end ForcedComputation.VelocityDetector

end

end OAI
