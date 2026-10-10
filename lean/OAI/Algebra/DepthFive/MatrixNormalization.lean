import OAI.Algebra.DepthFive.TraceRank

namespace OAI

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace Problem335

section DiagonalScaling

variable {ι κ K : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Field K]

/-- Nonzero row and column rescalings preserve the rank of a rectangular matrix. -/
theorem rank_diagonal_mul_mul_diagonal (A : Matrix κ ι K)
    (r : κ → K) (c : ι → K) (hr : ∀ i, r i ≠ 0) (hc : ∀ j, c j ≠ 0) :
    (Matrix.diagonal r * A * Matrix.diagonal c).rank = A.rank := by
  have hr' : IsUnit (Matrix.diagonal r).det := by
    simp only [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hr i)
  have hc' : IsUnit (Matrix.diagonal c).det := by
    simp only [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hc i)
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hc',
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hr']

/-- Entrywise nonzero row/column normalization does not change rank. -/
theorem rank_entrywise_scaling (A : Matrix κ ι K)
    (r : κ → K) (c : ι → K) (hr : ∀ i, r i ≠ 0) (hc : ∀ j, c j ≠ 0) :
    Matrix.rank (fun i j => r i * A i j * c j : Matrix κ ι K) = A.rank := by
  have heq : (fun i j => r i * A i j * c j : Matrix κ ι K) =
      Matrix.diagonal r * A * Matrix.diagonal c := by
    ext i j
    simp
  rw [heq]
  exact rank_diagonal_mul_mul_diagonal A r c hr hc

end DiagonalScaling

section BasisNormalization

variable {ι κ K M N : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [CommSemiring K] [AddCommMonoid M] [AddCommMonoid N]
    [Module K M] [Module K N]

/-- Rescaling source and target basis vectors rescales matrix columns and rows,
with inverse target weights. This identifies normalized-monomial matrices. -/
theorem toMatrix_unitsSMul_apply (f : M →ₗ[K] N)
    (b : Module.Basis ι K M) (c : Module.Basis κ K N)
    (u : ι → Kˣ) (v : κ → Kˣ) (i : κ) (j : ι) :
    LinearMap.toMatrix (b.unitsSMul u) (c.unitsSMul v) f i j =
      (↑((v i)⁻¹) : K) * LinearMap.toMatrix b c f i j * (u j : K) := by
  simp [LinearMap.toMatrix_apply, Module.Basis.unitsSMul_apply,
    Module.Basis.repr_unitsSMul, Units.smul_def, mul_comm]

end BasisNormalization

/-- The square-root rescaling used by factorial-normalized monomial bases
preserves rank whenever all normalization weights are positive. -/
theorem rank_sqrt_normalization {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix κ ι ℂ)
    (r : κ → ℝ) (c : ι → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) :
    Matrix.rank (fun i j => (Real.sqrt (r i) : ℂ) * A i j /
      (Real.sqrt (c j) : ℂ)) = A.rank := by
  apply rank_entrywise_scaling A (fun i => (Real.sqrt (r i) : ℂ))
    (fun j => (Real.sqrt (c j) : ℂ)⁻¹)
  · intro i
    exact_mod_cast (Real.sqrt_pos.2 (hr i)).ne'
  · intro j
    exact inv_ne_zero (by exact_mod_cast (Real.sqrt_pos.2 (hc j)).ne')

section MomentComparison

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- Comparing the first two normalized trace moments gives the rank bound used
in the IMM argument. Here `w` contains the path count and local moment factor. -/
theorem rank_lower_bound_of_trace_moment_bounds (A : Matrix κ ι ℂ)
    {D w δ ε : ℝ} (hD : 0 < D) (hw : 0 < w)
    (hfirst : D * w * Real.exp (-δ) ≤ (Aᴴ * A).trace.re)
    (hsecond : (((Aᴴ * A) ^ 2).trace.re) ≤ D * w ^ 2 * Real.exp ε) :
    D * Real.exp (-(2 * δ + ε)) ≤ (A.rank : ℝ) := by
  let T := (Aᴴ * A).trace.re
  let T₂ := (((Aᴴ * A) ^ 2).trace.re)
  let L := D * w * Real.exp (-δ)
  let U := D * w ^ 2 * Real.exp ε
  have hL : 0 < L := by dsimp [L]; positivity
  have hT : 0 < T := lt_of_lt_of_le hL hfirst
  have hHne : Aᴴ * A ≠ 0 := by
    intro hz
    simp [T, hz] at hT
  have hT₂ : 0 < T₂ :=
    hermitian_trace_sq_pos (Matrix.isHermitian_conjTranspose_mul_self A) hHne
  have hU : 0 < U := lt_of_lt_of_le hT₂ hsecond
  have hsq : L ^ 2 ≤ T ^ 2 := by nlinarith [hfirst]
  have hratio : L ^ 2 / U ≤ (A.rank : ℝ) := calc
    L ^ 2 / U ≤ T ^ 2 / U := div_le_div_of_nonneg_right hsq hU.le
    _ ≤ T ^ 2 / T₂ := div_le_div_of_nonneg_left (sq_nonneg T) hT₂ hsecond
    _ ≤ (A.rank : ℝ) := gram_rank_ge_trace_ratio A hT₂
  have hexp : Real.exp (-(2 * δ + ε)) * Real.exp ε = Real.exp (-δ) ^ 2 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have heq : D * Real.exp (-(2 * δ + ε)) = L ^ 2 / U := by
    apply (eq_div_iff (ne_of_gt hU)).2
    dsimp [L, U]
    calc
      D * Real.exp (-(2 * δ + ε)) * (D * w ^ 2 * Real.exp ε) =
          D ^ 2 * w ^ 2 * (Real.exp (-(2 * δ + ε)) * Real.exp ε) := by ring
      _ = D ^ 2 * w ^ 2 * Real.exp (-δ) ^ 2 := by rw [hexp]
      _ = (D * w * Real.exp (-δ)) ^ 2 := by ring
  rw [heq]
  exact hratio

end MomentComparison

end Problem335

end

end OAI
