import OAI.Geometry.EinsteinFour.ReferenceCompression
import OAI.Geometry.EinsteinFour.ModeAverageLimit
import OAI.Geometry.EinsteinFour.JacobiDeterminant

namespace OAI

/-! Passing the actual first-mode Dirichlet comparison to the radial limit. -/

namespace PositiveEinsteinFour.Jacobi

open Filter
open scoped Matrix.Norms.Frobenius

noncomputable section

def sampledCurvature (A : ℝ → NormalMatrix) (N : ℕ) : Fin N → NormalMatrix :=
  fun i => A ((i.val + 1) / ((N : ℝ) + 1))

/-- The finite comparison passes to the actual sine-weighted curvature
integral. The two determinant convergence premises are supplied by the
Jacobi approximation, while positivity is supplied by preconjugacy. -/
theorem continuous_radial_comparison {t D : ℝ} (ht : 0 < t) (htπ : t < Real.pi)
    (A : ℝ → NormalMatrix) (htrace : ∀ s, (A s).trace = 0)
    {L : ℝ} (hL : 0 ≤ L)
    (hc : Continuous (fun s => Averages.sineWeight s • A s))
    (hLip : ∀ s r, ‖Averages.sineWeight s • A s - Averages.sineWeight r • A r‖ ≤
      L * |s - r|)
    (hpos : ∀ᶠ N in atTop, (curvatureDirichlet t (sampledCurvature A N)).PosDef)
    (hdet : Tendsto (fun N : ℕ => (t / (N + 1)) ^ 3 *
      (curvatureDirichlet t (sampledCurvature A N)).det) atTop (nhds D))
    (href : Tendsto (fun N : ℕ => (t / (N + 1)) ^ 3 * (referenceMatrix t N).det ^ 3)
      atTop (nhds (Real.sin t ^ 3))) :
    D ≤ Real.sin t ^ 3 * ((1 : NormalMatrix) -
      (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) •
        (∫ s in (0 : ℝ)..1, Averages.sineWeight s • A s)).det := by
  have hs : 0 < Real.sin t ^ 3 := pow_pos (Real.sin_pos_of_pos_of_lt_pi ht htπ) 3
  have hmode := modeAverage_tendsto hL hc hLip
  have hcompression : Tendsto (fun N : ℕ => (1 : NormalMatrix) -
      ((t / (N + 1)) ^ 2 / firstEigenvalue t N) • modeAverage A N) atTop
      (nhds ((1 : NormalMatrix) - (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) •
        (∫ s in (0 : ℝ)..1, Averages.sineWeight s • A s))) :=
    tendsto_const_nhds.sub ((first_mode_coefficient_tendsto ht.le htπ).smul hmode)
  apply compression_comparison_limit hs hdet href hcompression
  filter_upwards [hpos, firstEigenvalue_eventually_pos ht.le htπ,
    eventually_gt_atTop (0 : ℕ)] with N hN heig hNpos
  have hcomp := reference_determinant_comparison hNpos t (sampledCurvature A N)
    (fun i => htrace _) heig hN
  have hstep : (t / (N + 1 : ℝ)) ^ 3 ≠ 0 := by positivity
  have hratio : ((t / (N + 1)) ^ 3 *
      (curvatureDirichlet t (sampledCurvature A N)).det) /
      ((t / (N + 1)) ^ 3 * (referenceMatrix t N).det ^ 3) =
      (curvatureDirichlet t (sampledCurvature A N)).det / (referenceMatrix t N).det ^ 3 := by
    exact mul_div_mul_left _ _ hstep
  rw [hratio]
  exact hcomp

end

end PositiveEinsteinFour.Jacobi

end OAI
