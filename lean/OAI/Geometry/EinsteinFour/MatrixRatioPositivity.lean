import OAI.Geometry.EinsteinFour.JacobiRatioLimit
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace OAI

/-! Translating the operator-norm mesh criterion into positive matrices. -/

namespace PositiveEinsteinFour.Jacobi

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

theorem matrix_posDef_of_quadratic {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hsym : Aᵀ = A)
    (hpos : ∀ x : EuclideanSpace ℝ n, x ≠ 0 →
      0 < inner ℝ ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) A x) x) : A.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hsym
  · intro y hy
    have hx : WithLp.toLp 2 y ≠ (0 : EuclideanSpace ℝ n) := by
      intro he
      apply hy
      exact congrArg WithLp.ofLp he
    have hp := hpos (WithLp.toLp 2 y) hx
    rw [real_inner_comm, Matrix.inner_toEuclideanCLM] at hp
    simpa using hp

/-- A symmetric matrix ratio is eventually positive at every mesh node
once its coefficient converges uniformly to the normalized Jacobi curve. -/
theorem eventually_matrix_ratio_posDef {n : Type*} [Fintype n] [DecidableEq n]
    {t : ℝ} (ht : 0 < t) {C : ℝ → Matrix n n ℝ}
    (hC : ContinuousOn C (Set.Icc 0 t)) (hC0 : C 0 = 1)
    {P : ℕ → ℕ → Matrix n n ℝ} {e : ℕ → ℝ}
    (he : Tendsto e atTop (nhds 0))
    (happrox : ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, 0 < i → i ≤ N →
      ‖P N i - C ((i : ℝ) * (t / (N + 1)))‖ ≤ e N)
    (hsym : ∀ N i : ℕ, ((1 : Matrix n n ℝ) + ((1 : ℝ) / i) • P N i)ᵀ =
      1 + ((1 : ℝ) / i) • P N i) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, 0 < i → i ≤ N →
      ((1 : Matrix n n ℝ) + ((1 : ℝ) / i) • P N i).PosDef := by
  have hc : ContinuousOn (fun s => (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) (C s)) (Set.Icc 0 t) := by
    have hi : Isometry (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) :=
      AddMonoidHomClass.isometry_of_norm
        (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)).toAlgEquiv.toAddEquiv (fun _ => rfl)
    exact hi.continuous.comp_continuousOn hC
  have hc0 : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) (C 0) = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ n) := by
    rw [hC0, map_one]
    rfl
  have ha : ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, 0 < i → i ≤ N →
      ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) (P N i) -
        (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) (C ((i : ℝ) * (t / (N + 1))))‖ ≤ e N := by
    filter_upwards [happrox] with N hN i hi hiN
    simpa only [← map_sub, Matrix.l2_opNorm_toEuclideanCLM] using hN i hi hiN
  have hp := eventually_mesh_ratio_positive ht hc hc0 he ha
  filter_upwards [hp] with N hN i hi hiN
  apply matrix_posDef_of_quadratic (hsym N i)
  intro x hx
  simpa only [map_add, map_one, map_smul, ContinuousLinearMap.one_def] using hN i hi hiN x hx

end

end PositiveEinsteinFour.Jacobi

end OAI
