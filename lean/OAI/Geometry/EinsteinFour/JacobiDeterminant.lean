import OAI.Geometry.EinsteinFour.JacobiApproximation
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Instances.Matrix

namespace OAI

/-! Passing the discrete Jacobi comparison to its determinant limit. -/

namespace PositiveEinsteinFour.Jacobi

open Filter
open scoped Matrix.Norms.Frobenius

noncomputable section

/-- The position error estimate gives the exact cubic determinant scaling
for a three-dimensional normal Jacobi matrix. -/
theorem scaled_determinant_limit {Y : ℕ → Matrix (Fin 3) (Fin 3) ℝ}
    {J : Matrix (Fin 3) (Fin 3) ℝ} {t C : ℝ}
    (herror : ∀ᶠ (N : ℕ) in atTop, ‖(t / N) • Y N - J‖ ≤ C / N) :
    Tendsto (fun N => (t / N) ^ 3 * (Y N).det) atTop (nhds J.det) := by
  have hzero : ∀ᶠ (N : ℕ) in atTop,
      ‖(t / N) • Y N - J‖ + ‖(0 : Matrix (Fin 3) (Fin 3) ℝ) - 0‖ ≤ C / N := by
    simpa using herror
  have hconv := (converges_of_inverse_mesh_error hzero).1
  have hc : Continuous (fun A : Matrix (Fin 3) (Fin 3) ℝ => A.det) :=
    continuous_id.matrix_det
  convert (hc.tendsto J).comp hconv using 1
  funext N
  change (t / (N : ℝ)) ^ 3 * (Y N).det = ((t / (N : ℝ)) • Y N).det
  rw [Matrix.det_smul, Fintype.card_fin]

/-- A finite determinant compression remains valid in the limit, including
when the limiting three-dimensional compression is singular. -/
theorem compression_comparison_limit
    {a b : ℕ → ℝ} {P : ℕ → Matrix (Fin 3) (Fin 3) ℝ}
    {D d : ℝ} {Q : Matrix (Fin 3) (Fin 3) ℝ}
    (hd : 0 < d) (ha : Tendsto a atTop (nhds D)) (hb : Tendsto b atTop (nhds d))
    (hP : Tendsto P atTop (nhds Q))
    (hcomp : ∀ᶠ (N : ℕ) in atTop, a N / b N ≤ (P N).det) :
    D ≤ d * Q.det := by
  have hc : Continuous (fun A : Matrix (Fin 3) (Fin 3) ℝ => A.det) :=
    continuous_id.matrix_det
  have hlim := le_of_tendsto_of_tendsto (ha.div hb hd.ne') ((hc.tendsto Q).comp hP) hcomp
  have hm := (div_le_iff₀ hd).mp hlim
  simpa only [mul_comm] using hm

end

end PositiveEinsteinFour.Jacobi

end OAI
