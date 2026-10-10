import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodizationSupportDAlong

namespace OAI

noncomputable section
namespace VelocityDetection.Periodization
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open JointCalculus SpatialCalculus

theorem support_spatialD {n : ℕ} {K : Set (Coord n)} (hK : IsClosed K)
    {f : ScalarField n} (hf : ContDiff ℝ ∞ (uncurry f))
    (hs : ∀ t X, f t X ≠ 0 → X ∈ K) (i : Fin n) :
    ∀ t X, spatialD i f t X ≠ 0 → X ∈ K := by
  simp_rw [spatialD_eq hf]
  exact support_dAlong hK hs (0,Pi.single i 1)

theorem support_laplacian {n : ℕ} {K : Set (Coord n)} (hK : IsClosed K)
    {f : ScalarField n} (hf : ContDiff ℝ ∞ (uncurry f))
    (hs : ∀ t X, f t X ≠ 0 → X ∈ K) :
    ∀ t X, laplacian f t X ≠ 0 → X ∈ K := by
  intro t X h
  obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact support_spatialD hK (TailSpace.Jets.contDiff_uncurry_spatialD hf i)
    (support_spatialD hK hf hs i) i t X hi

end VelocityDetection.Periodization
end

end OAI
