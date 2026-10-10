import OAI.Geometry.EinsteinFour.JacobiSineReference
import OAI.Geometry.EinsteinFour.JacobiCompressionLimit

namespace OAI

/-! Radial determinant comparison from the Jacobi ODE. -/

namespace PositiveEinsteinFour.Jacobi

open Filter

noncomputable section

def radialCurvature (R : ℝ → NormalMatrix) (t s : ℝ) : NormalMatrix := R (s * t) - 1

theorem sampled_radialCurvature (R : ℝ → NormalMatrix) (t : ℝ) (N : ℕ) :
    sampledCurvature (radialCurvature R t) N = fun i : Fin N =>
      R (((i.val + 1 : ℕ) : ℝ) * meshStep t N) - 1 := by
  funext i
  dsimp [sampledCurvature, radialCurvature, meshStep]
  rw [Nat.cast_add, Nat.cast_one]
  congr 2
  ring

namespace RegularJacobi

variable {t : ℝ} (d : RegularJacobi t)

open scoped Matrix.Norms.Frobenius

/-- The Jacobi radial inequality follows from the ODE, trace normalization,
and preconjugacy. -/
theorem radial_determinant_comparison (ht : 0 < t) (htπ : t < Real.pi)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit (d.J s))
    (htrace : ∀ s, (d.R s).trace = 3)
    {L : ℝ} (hL : 0 ≤ L)
    (hc : Continuous (fun s => Averages.sineWeight s • radialCurvature d.R t s))
    (hLip : ∀ s r,
      ‖Averages.sineWeight s • radialCurvature d.R t s -
        Averages.sineWeight r • radialCurvature d.R t r‖ ≤ L * |s - r|) :
    (d.J t).det ≤ Real.sin t ^ 3 * ((1 : NormalMatrix) -
      (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) •
        (∫ s in (0 : ℝ)..1, Averages.sineWeight s • radialCurvature d.R t s)).det := by
  apply continuous_radial_comparison ht htπ (radialCurvature d.R t)
    (fun s => by simp [radialCurvature, Matrix.trace_sub, htrace]) hL hc hLip
  · simpa only [sampled_radialCurvature] using d.curvatureDirichlet_eventually_posDef ht hpre
  · simpa only [sampled_radialCurvature, meshStep] using d.curvatureDirichlet_det_tendsto ht hpre
  · exact reference_determinant_tendsto ht htπ

/-- The limiting compression is positive semidefinite, including a singular
limit; this is the spectral input for the subsequent determinant deficit. -/
theorem radial_compression_posSemidef (ht : 0 < t) (htπ : t < Real.pi)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit (d.J s))
    {L : ℝ} (hL : 0 ≤ L)
    (hc : Continuous (fun s => Averages.sineWeight s • radialCurvature d.R t s))
    (hLip : ∀ s r,
      ‖Averages.sineWeight s • radialCurvature d.R t s -
        Averages.sineWeight r • radialCurvature d.R t r‖ ≤ L * |s - r|) :
    ((1 : NormalMatrix) - (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) •
      (∫ s in (0 : ℝ)..1, Averages.sineWeight s • radialCurvature d.R t s)).PosSemidef := by
  apply continuous_radial_compression_posSemidef ht.le htπ _ hL hc hLip
  simpa only [sampled_radialCurvature] using d.curvatureDirichlet_eventually_posDef ht hpre

end RegularJacobi

end

end PositiveEinsteinFour.Jacobi

end OAI
