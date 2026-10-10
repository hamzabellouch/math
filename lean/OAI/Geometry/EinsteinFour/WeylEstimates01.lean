import OAI.Geometry.EinsteinFour.ActualRicciContraction
import OAI.Geometry.EinsteinFour.AngularClifford
import OAI.Geometry.EinsteinFour.CoordinateSecondBianchi
import OAI.Geometry.EinsteinFour.CubicWeight
import OAI.Geometry.EinsteinFour.CurvatureContraction
import OAI.Geometry.EinsteinFour.CurvatureFirstBianchi
import OAI.Geometry.EinsteinFour.CurvatureForm
import OAI.Geometry.EinsteinFour.FrameBundle
import OAI.Geometry.EinsteinFour.FrameFlow
import OAI.Geometry.EinsteinFour.FrameOrientation
import OAI.Geometry.EinsteinFour.GeneralMatrixCompression
import OAI.Geometry.EinsteinFour.HVarianceApproximation
import OAI.Geometry.EinsteinFour.HessianAssembly
import OAI.Geometry.EinsteinFour.HighestGram
import OAI.Geometry.EinsteinFour.MatrixSlotCompression
import OAI.Geometry.EinsteinFour.MatrixSlotLaplacian
import OAI.Geometry.EinsteinFour.MetricBianchi
import OAI.Geometry.EinsteinFour.MetricCurvatureGreen
import OAI.Geometry.EinsteinFour.MetricHessian
import OAI.Geometry.EinsteinFour.MetricMatrixGreen
import OAI.Geometry.EinsteinFour.MetricMinusGreen
import OAI.Geometry.EinsteinFour.MinusProjectionCost
import OAI.Geometry.EinsteinFour.QuaternionGenerators
import OAI.Geometry.EinsteinFour.QuaternionLifts
import OAI.Geometry.EinsteinFour.QuaternionReflections
import OAI.Geometry.EinsteinFour.RealVectorCost
import OAI.Geometry.EinsteinFour.RicciGradient
import OAI.Geometry.EinsteinFour.Spectral
import OAI.Geometry.EinsteinFour.TraceSubtraction
import OAI.Geometry.EinsteinFour.Variance
import OAI.Geometry.EinsteinFour.WeylEstimates00
import OAI.Geometry.EinsteinFour.WeylMatrixEquation
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.TangentCone.DimOne
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Order.LeftRightNhds

namespace OAI


section

/-! Differentiate the invariant matrix Weyl equation before choosing a
diagonal frame. The derivative of its quadratic term is exactly twice
the concrete matrix-slot operator. -/

namespace PositiveEinsteinFour.TraceHessian

open Matrix PositiveEinsteinFour.Geometry
open scoped BigOperators

noncomputable section

local instance : NormedRing Mat := Matrix.frobeniusNormedRing
local instance : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

def matrixTraceMap : Mat →L[ℝ] ℝ :=
  (Matrix.traceLinearMap (Fin 3) ℝ ℝ).toContinuousLinearMap

theorem hasDerivAt_matrixTrace {T : ℝ → Mat} {Z : Mat} {t : ℝ}
    (hT : HasDerivAt T Z t) :
    HasDerivAt (fun r => Matrix.trace (T r)) (Matrix.trace Z) t := by
  convert! (matrixTraceMap.hasFDerivAt.comp_hasDerivAt t hT) using 1

theorem matrixSlotAction_derivative (M Z : Mat) :
    Z * M + M * Z - (Matrix.trace (Z * M + M * Z) / 3) • (1 : Mat) =
      (2 : ℝ) • matrixSlotAction M Z := by
  rw [matrixSlotAction_eq, Matrix.trace_add, Matrix.trace_mul_comm Z M]
  ext a b
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem hasDerivAt_traceFreeSquare {T : ℝ → Mat} {Z : Mat} {t : ℝ}
    (hT : HasDerivAt T Z t) :
    HasDerivAt (fun r => traceFreeSquare (T r))
      ((2 : ℝ) • matrixSlotAction (T t) Z) t := by
  have hP := hT.mul hT
  have htr := hasDerivAt_matrixTrace hP
  have h := hP.sub ((htr.div_const 3).smul_const (1 : Mat))
  convert! h using 1
  exact (matrixSlotAction_derivative (T t) Z).symm

/-- The differentiated weak Weyl equation is `6Z - 12 B_F(T)Z` in a
parallel frame, without differentiating eigenvectors or eigenvalues. -/
theorem hasDerivAt_weylLaplacian {T : ℝ → Mat} {Z : Mat} {t : ℝ}
    (hT : HasDerivAt T Z t) :
    HasDerivAt (fun r => weylLaplacian (T r))
      ((6 : ℝ) • Z - (12 : ℝ) • matrixSlotAction (T t) Z) t := by
  have h := (hT.sub (hasDerivAt_traceFreeSquare hT)).const_smul (6 : ℝ)
  convert! h using 1
  module

/-- Along a parallel frame, differentiate the Weyl equation derived from
Bianchi and the raw curvature commutator. The trace of the third derivative
is therefore a conclusion rather than another geometric input. -/
theorem third_trace_eq_of_bianchi_commutator
    (T : ℝ → Mat) (X : ℝ → Hessian) (D : Fin 4 → Mat) (Z : Mat) (r : ℝ)
    (hs : ∀ t, symmetric (T t)) (ht : ∀ t, traceFree (T t))
    (hm : ∀ t i j, symmetric (X t i j) ∧ traceFree (X t i j))
    (hb : ∀ t i s, HighestHessian.divergence (X t) i s = 0)
    (hc : ∀ t i j a b, X t i j a b - X t j i a b =
      bundleCurvatureAction (T t) i j (T t) a b)
    (hT : HasDerivAt T Z r)
    (hX : ∀ i, HasDerivAt (fun t => X t i i) (D i) r) :
    (∑ i, D i) = (6 : ℝ) • Z - (12 : ℝ) • matrixSlotAction (T r) Z := by
  have he : (fun t => ∑ i, X t i i) = fun t => weylLaplacian (T t) := by
    funext t
    exact weyl_trace_eq_of_bianchi_commutator (T t) (hs t) (ht t)
      (X t) (hm t) (hb t) (hc t)
  have hd : HasDerivAt (fun t => ∑ i, X t i i) (∑ i, D i) r :=
    HasDerivAt.fun_sum (fun i _ => hX i)
  rw [he] at hd
  exact hd.unique (hasDerivAt_weylLaplacian hT)

end
end PositiveEinsteinFour.TraceHessian
end


section

/-! Evaluate both terms of the varying matrix-slot Green formula. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open TraceHessian Bianchi

noncomputable section

def matrixSlotAt (Z : GradientVector) : Mat →ₗ[ℝ] GradientVector where
  toFun A := matrixSlotOperator A Z
  map_add' A B := congrArg (fun F : GradientVector →L[ℝ] GradientVector => F Z)
    (matrixSlotOperatorLinear.map_add A B)
  map_smul' r A := congrArg (fun F : GradientVector →L[ℝ] GradientVector => F Z)
    (matrixSlotOperatorLinear.map_smul r A)

theorem matrixSlotAt_weylLaplacian (T : Mat) (Z : GradientVector) :
    matrixSlotOperator (weylLaplacian T) Z =
      (6 : ℝ) • matrixSlotOperator T Z -
        (6 : ℝ) • matrixSlotOperator (traceFreeSquare T) Z := by
  change matrixSlotAt Z ((6 : ℝ) • (T - traceFreeSquare T)) = _
  rw [map_smul, map_sub]
  change (6 : ℝ) • (matrixSlotOperator T Z - matrixSlotOperator (traceFreeSquare T) Z) = _
  module

theorem matrixSlotAt_sum_trace (X : Hessian) (Z : GradientVector) :
    (∑ i, matrixSlotOperator (X i i) Z) = matrixSlotOperator (hessianTrace X) Z := by
  change (∑ i, matrixSlotAt Z (X i i)) = matrixSlotAt Z (∑ i, X i i)
  rw [map_sum]

/-- The Laplacian correction contributes `3B - 3C`; together with the
Ricci term `-13B + 20E` this gives the matrix-slot polynomial. -/
theorem matrix_green_main_terms (T : Mat) (hT : symmetric T)
    (Z L : GradientVector) (E : ℝ)
    (hL : inner ℝ (matrixSlotOperator T Z) L =
      13 * inner ℝ (matrixSlotOperator T Z) Z - 20 * E) :
    -inner ℝ Z (matrixSlotOperator T L) +
        (1 / 2 : ℝ) * inner ℝ Z (matrixSlotOperator (weylLaplacian T) Z) =
      -10 * inner ℝ (matrixSlotOperator T Z) Z -
        3 * inner ℝ (matrixSlotOperator (traceFreeSquare T) Z) Z + 20 * E := by
  rw [← matrixSlotOperator_selfadjoint T hT, hL, matrixSlotAt_weylLaplacian,
    inner_sub_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_comm Z (matrixSlotOperator T Z),
    real_inner_comm Z (matrixSlotOperator (traceFreeSquare T) Z)]
  ring

theorem curvatureBilinear_self (S : Shape) (v : ℝ) (Z : Tensor) :
    curvatureBilinear S v Z Z = curvatureContraction S v Z := by
  simp only [curvatureBilinear, curvatureContraction, real_inner_self_eq_norm_sq]

theorem matrixSlot_diagonal_raw (t : Fin 3 → ℝ) (Z : Tensor) (hz : Z.traceFree) :
    matrixSlotOperator (Matrix.diagonal t) (tensorGradientVector Z) =
      rawGradientVector (rawMatrixCurvature t Z) := by
  have htrace (i : Fin 4) : (∑ a, tensorGradientVector Z (i, a, a)) = 0 := by
    have h := congrArg (fun z : Vec => z i) hz
    simpa [tensorGradientVector, rawGradientVector, rawCoordinates,
      Tensor.traceFree, Tensor.matrix, Fin.sum_univ_three] using h
  ext p
  rcases p with ⟨i, a, b⟩
  rw [matrixSlotOperator_on_traceFree _ _ htrace]
  change matrixSlotAction (Matrix.diagonal t) (fun c d => Z.matrix c d i) a b =
    rawMatrixCurvature t Z a b i
  exact (congrArg (fun M : Mat => M a b)
    (matrixSlotAction_diagonal t (show Mat from fun c d => Z.matrix c d i))).trans
      (rawMatrixCurvature_component t Z a b i).symm

theorem matrixSlot_diagonal_self (t : Fin 3 → ℝ) (Z : Tensor) (hz : Z.traceFree) :
    inner ℝ (matrixSlotOperator (Matrix.diagonal t) (tensorGradientVector Z))
      (tensorGradientVector Z) = diagonalGradientForm t Z := by
  rw [matrixSlot_diagonal_raw t Z hz]
  change inner ℝ (rawGradientVector (rawMatrixCurvature t Z)) (rawGradientVector Z.matrix) = _
  rw [inner_rawGradientVector, rawMatrixCurvature_pairing t Z Z hz]
  simp only [diagonalGradientPairing, diagonalGradientForm, real_inner_self_eq_norm_sq]

theorem diagonalGradientForm_eq_entries (t : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (Z : Tensor) :
    diagonalGradientForm t Z = (∑ a, t a * ‖Z.diagonal a‖ ^ 2) -
      ∑ a, t a * ‖Z.off a‖ ^ 2 := by
  have h := ht
  simp only [Fin.sum_univ_three] at h
  simp [diagonalGradientForm, Tensor.matrix, Fin.sum_univ_three]
  linear_combination (‖Z.off 0‖ ^ 2 + ‖Z.off 1‖ ^ 2 + ‖Z.off 2‖ ^ 2) * h

theorem traceFreeSquare_diagonal_shape (S : Shape) (v : ℝ) :
    traceFreeSquare (Matrix.diagonal (fun s => v * S.s s)) =
      Matrix.diagonal (fun s => v ^ 2 * S.squareWeight s) := by
  have htr : Matrix.trace (Matrix.diagonal (fun s => v * S.s s) *
      Matrix.diagonal (fun s => v * S.s s)) = 6 * v ^ 2 := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    calc
      _ = v ^ 2 * ∑ s, S.s s ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ = _ := by rw [S.square]; ring
  unfold traceFreeSquare
  rw [htr, Matrix.diagonal_mul_diagonal]
  ext a b
  simp only [Matrix.sub_apply, Matrix.smul_apply,
    Matrix.diagonal_apply, Matrix.one_apply,
    smul_eq_mul]
  by_cases hab : a = b
  · subst b
    simp only [ite_true, mul_one, Shape.squareWeight]
    ring
  · simp only [hab, ite_false, mul_zero, sub_self]

theorem matrixSlot_square_self (S : Shape) (v : ℝ) (Z : Tensor) (hz : Z.traceFree) :
    inner ℝ (matrixSlotOperator (traceFreeSquare (Matrix.diagonal (fun s => v * S.s s)))
      (tensorGradientVector Z)) (tensorGradientVector Z) / 6 =
        squareCurvatureContraction S v Z := by
  have ht : (∑ s, v ^ 2 * S.squareWeight s) = 0 := by
    simp only [Shape.squareWeight, mul_sub, Finset.sum_sub_distrib,
      ← Finset.mul_sum, S.square, Fin.sum_univ_three]
    ring
  rw [traceFreeSquare_diagonal_shape, matrixSlot_diagonal_self _ Z hz,
    diagonalGradientForm_eq_entries _ ht]
  simp only [squareCurvatureContraction, mul_assoc, ← Finset.mul_sum]
  ring

/-- This specialization supplies the exact normalized matrix-slot main
term in the Hessian assembly from the raw Ricci equation. -/
theorem matrix_green_main_parameters (S : Shape) (v : ℝ) (p k l : Vec)
    (L : Tensor) (hLz : L.traceFree) (hLb : L.bianchi)
    (hL : L.matrix = ricciGradient (fun s => v * S.s s) (parameters S p k l)) :
    let T := Matrix.diagonal (fun s => v * S.s s)
    let Z := tensorGradientVector (parameters S p k l)
    (-inner ℝ Z (matrixSlotOperator T (tensorGradientVector L)) +
      (1 / 2 : ℝ) * inner ℝ Z (matrixSlotOperator (weylLaplacian T) Z)) / 6 =
        -10 * curvatureContraction S v (parameters S p k l) -
          3 * (inner ℝ (matrixSlotOperator (traceFreeSquare T) Z) Z / 6) +
          20 * ((curvatureAction S v p k l).squaredNorm / 6) := by
  dsimp only
  have hT : symmetric (Matrix.diagonal (fun s => v * S.s s)) := by
    intro a b
    by_cases hab : a = b
    · subst b; rfl
    · simp [Matrix.diagonal, hab, Ne.symm hab]
  have hB := matrixSlotOperator_pairing S v (parameters S p k l) (parameters S p k l)
    (parameters_traceFree S p k l) (parameters_traceFree S p k l)
  rw [curvatureBilinear_self] at hB
  have hR := matrixSlotOperator_ricci_pairing S v p k l L hLz hLb hL
  rw [curvatureBilinear_self, ← hB] at hR
  rw [matrix_green_main_terms _ hT _ _ _ hR, hB]
  ring

theorem matrix_green_main_scalar (S : Shape) (v : ℝ) (p k l : Vec)
    (L : Tensor) (hLz : L.traceFree) (hLb : L.bianchi)
    (hL : L.matrix = ricciGradient (fun s => v * S.s s) (parameters S p k l)) :
    let T := Matrix.diagonal (fun s => v * S.s s)
    let Z := tensorGradientVector (parameters S p k l)
    (-inner ℝ Z (matrixSlotOperator T (tensorGradientVector L)) +
      (1 / 2 : ℝ) * inner ℝ Z (matrixSlotOperator (weylLaplacian T) Z)) / 6 =
        -10 * curvatureContraction S v (parameters S p k l) -
          3 * squareCurvatureContraction S v (parameters S p k l) +
          20 * ((curvatureAction S v p k l).squaredNorm / 6) := by
  dsimp only
  rw [matrix_green_main_parameters S v p k l L hLz hLb hL,
    matrixSlot_square_self S v _ (parameters_traceFree S p k l)]

/-- The derivative of the matrix coefficient is the actual cubic trace,
with no eigenframe or parallel-coefficient premise. -/
theorem matrixSlot_weight_cubic (a : Fin 4 → ℝ) (Z : Angular.Gradient)
    (hs : ∀ j, symmetric (Z j)) (ht : ∀ j, traceFree (Z j)) :
    (∑ i, a i * inner ℝ (gradientVector Z)
      (matrixSlotOperator (Z i) (gradientVector Z))) =
      ∑ i, a i * Matrix.trace (Z i * (∑ j, Z j * Z j)) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm, matrixSlot_cubic_trace (Z i) Z hs ht]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Realize the invariant Weyl equation and its derivative on the actual
metric tensors. The inputs are the pointwise covariant Bianchi and Ricci
identities (Petersen, third edition, Section 3.1.1) and ordinary parallel
frame differentiation. No Weyl Laplacian equation is an input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance metricWeylNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricWeylNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricWeylNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The precise algebraic and covariant identities used from the classical
Einstein/Weyl calculus, specialized to the plus block and Ricci `3g`.
All fields refer to the metric's actual tensors. -/
structure WeylCovariantIdentities (g : SmoothMetric M) : Prop where
  symmetric : ∀ e : FrameBundle g, TraceHessian.symmetric (plusWeyl g e.base e.frame)
  traceFree : ∀ e : FrameBundle g, TraceHessian.traceFree (plusWeyl g e.base e.frame)
  hessianMatrix : ∀ (e : FrameBundle g) i j,
    TraceHessian.symmetric (plusWeylHessian g e.base e.frame i j) ∧
      TraceHessian.traceFree (plusWeylHessian g e.base e.frame i j)
  hessianBianchi : ∀ (e : FrameBundle g) i r,
    HighestHessian.divergence (plusWeylHessian g e.base e.frame) i r = 0
  hessianCommutator : ∀ (e : FrameBundle g) i j a b,
    plusWeylHessian g e.base e.frame i j a b -
      plusWeylHessian g e.base e.frame j i a b =
        bundleCurvatureAction (plusWeyl g e.base e.frame) i j
          (plusWeyl g e.base e.frame) a b

theorem metric_weyl_trace (g : SmoothMetric M) (h : WeylCovariantIdentities g)
    (e : FrameBundle g) :
    hessianTrace (plusWeylHessian g e.base e.frame) =
      weylLaplacian (plusWeyl g e.base e.frame) :=
  weyl_trace_eq_of_bianchi_commutator _ (h.symmetric e) (h.traceFree e)
    _ (h.hessianMatrix e) (h.hessianBianchi e) (h.hessianCommutator e)

/-- Differentiate on parallel frames and then evaluate at any requested
frame. Surjectivity of the flow equivalence suffices; no chosen eigenframe
is differentiated. -/
theorem metric_weyl_third_trace (g : SmoothMetric M)
    (h : WeylCovariantIdentities g) {μ : Measure (FrameBundle g)}
    (φ : Fin 4 → FrameFlow g μ)
    (hT : ∀ k t e, HasDerivAt
      (fun s => plusWeyl g ((φ k).map s e).base ((φ k).map s e).frame)
      (plusWeylGradient g ((φ k).map t e).base ((φ k).map t e).frame k) t)
    (hX : ∀ k i t e, HasDerivAt
      (fun s => plusWeylHessian g ((φ k).map s e).base ((φ k).map s e).frame i i)
      (plusWeylThirdDerivative g ((φ k).map t e).base ((φ k).map t e).frame k i i) t)
    (k : Fin 4) (e : FrameBundle g) :
    (∑ i, plusWeylThirdDerivative g e.base e.frame k i i) =
      (6 : ℝ) • plusWeylGradient g e.base e.frame k -
        (12 : ℝ) • matrixSlotAction (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame k) := by
  obtain ⟨e₀, he⟩ := ((φ k).map 0).surjective e
  change (φ k).map 0 e₀ = e at he
  have hthird := third_trace_eq_of_bianchi_commutator
    (fun t => plusWeyl g ((φ k).map t e₀).base ((φ k).map t e₀).frame)
    (fun t => plusWeylHessian g ((φ k).map t e₀).base ((φ k).map t e₀).frame)
    (fun i => plusWeylThirdDerivative g ((φ k).map 0 e₀).base
      ((φ k).map 0 e₀).frame k i i)
    (plusWeylGradient g ((φ k).map 0 e₀).base ((φ k).map 0 e₀).frame k) 0
    (fun t => h.symmetric ((φ k).map t e₀))
    (fun t => h.traceFree ((φ k).map t e₀))
    (fun t => h.hessianMatrix ((φ k).map t e₀))
    (fun t => h.hessianBianchi ((φ k).map t e₀))
    (fun t => h.hessianCommutator ((φ k).map t e₀))
    (hT k 0 e₀) (fun i => hX k i 0 e₀)
  rw [he] at hthird
  exact hthird

end
end PositiveEinsteinFour.Geometry
end


section

/-! Contract the two ordinary covariant commutation identities. These are
the slotwise Ricci identities of Petersen, Section 3.1.1; the new compressed
gradient equation is a consequence, not an assumed differential equation. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open TraceHessian Bianchi

noncomputable section

def rawMatrixSlice (Z : RawGradient) (j : Fin 4) : Mat := fun a b => Z a b j

theorem matrixRotation_slice (Z : Tensor) (s : Fin 3) (j : Fin 4) (a b : Fin 3) :
    matrixAction s (rawMatrixSlice Z.matrix j) a b = matrixRotation s Z a b j := by
  simp [rawMatrixSlice, matrixAction, matrixRotation, Fin.sum_univ_three]
  ring

theorem bundleCurvatureAction_diagonal (t : Fin 3 → ℝ) (i j : Fin 4) (N : Mat)
    (a b : Fin 3) :
    bundleCurvatureAction (Matrix.diagonal t) i j N a b =
      (1 / 2 : ℝ) * ∑ s, (1 + t s) * quaternionMatrix s i j * matrixAction s N a b := by
  simp [bundleCurvatureAction, Matrix.diagonal, Fin.sum_univ_three]
  ring

/-- The factor two from Ricci commutation cancels the half in the bundle
curvature. Its sign comes from the covector quaternion's skew symmetry. -/
theorem bundleCurvatureAction_sum (t : Fin 3 → ℝ) (Z : Tensor)
    (j : Fin 4) (a b : Fin 3) :
    2 * (∑ i, bundleCurvatureAction (Matrix.diagonal t) i j
      (rawMatrixSlice Z.matrix i) a b) =
        -(∑ s, (1 + t s) * mixedGradient s Z a b j) := by
  simp only [bundleCurvatureAction_diagonal, matrixRotation_slice]
  calc
    _ = ∑ i, ∑ s, (1 + t s) * quaternionMatrix s i j * matrixRotation s Z a b i := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = ∑ s, ∑ i, (1 + t s) * quaternionMatrix s i j * matrixRotation s Z a b i :=
      Finset.sum_comm
    _ = _ := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro s _
      change _ = -((1 + t s) * quaternion s (matrixRotation s Z a b) j)
      rw [← quaternionMatrix_apply, Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [quaternionMatrix_skew s i j]
      ring

def rawThirdLaplacian (D : Fin 4 → Fin 4 → Fin 4 → Mat) : RawGradient := fun a b =>
  WithLp.toLp 2 (fun j => ∑ i, D i i j a b)

/-- The raw gradient equation follows from the two tensor-slot Ricci
identities, divergence freedom, and the differentiated invariant matrix
equation. The conclusion still retains the uncompressed bundle action. -/
theorem rawThirdLaplacian_eq_ricciGradient (t : Fin 3 → ℝ) (Z : Tensor)
    (D V : Fin 4 → Fin 4 → Fin 4 → Mat)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hinner : ∀ i k j, D i k j - D i j k = V i k j +
      bundleCurvatureAction (Matrix.diagonal t) k j (rawMatrixSlice Z.matrix i))
    (houter : ∀ i k j, D i k j - D k i j =
      bundleCurvatureAction (Matrix.diagonal t) i k (rawMatrixSlice Z.matrix j) +
        ∑ h, R i k j h • rawMatrixSlice Z.matrix h)
    (hdiv : ∀ j, (∑ i, V i i j) = 0)
    (hRic : ∀ j h, (∑ i, R i j i h) = if j = h then 3 else 0)
    (htrace : ∀ j, (∑ i, D j i i) = (6 : ℝ) • rawMatrixSlice Z.matrix j -
      (12 : ℝ) • matrixSlotAction (Matrix.diagonal t) (rawMatrixSlice Z.matrix j)) :
    rawThirdLaplacian D = ricciGradient t Z := by
  funext a b
  ext j
  have hi (i : Fin 4) : D i i j a b = D j i i a b + V i i j a b +
      2 * bundleCurvatureAction (Matrix.diagonal t) i j (rawMatrixSlice Z.matrix i) a b +
        ∑ h, R i j i h * Z.matrix a b h := by
    have h1 := congrArg (fun A : Mat => A a b) (hinner i i j)
    have h2 := congrArg (fun A : Mat => A a b) (houter i j i)
    simp only [Matrix.sub_apply, Matrix.add_apply] at h1
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, rawMatrixSlice] at h2
    linarith
  have hv := congrArg (fun A : Mat => A a b) (hdiv j)
  have ht := congrArg (fun A : Mat => A a b) (htrace j)
  simp only [Matrix.sum_apply, Matrix.zero_apply] at hv
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, rawMatrixSlice] at ht
  have hr : (∑ i, ∑ h, R i j i h * Z.matrix a b h) = 3 * Z.matrix a b j := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hRic, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  change (∑ i, D i i j a b) = _
  simp only [hi, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hv, hr, ht, bundleCurvatureAction_sum, add_zero]
  change 6 * Z.matrix a b j -
      12 * matrixSlotAction (Matrix.diagonal t) (rawMatrixSlice Z.matrix j) a b -
        (∑ s, (1 + t s) * mixedGradient s Z a b j) + 3 * Z.matrix a b j = _
  have hB : matrixSlotAction (Matrix.diagonal t) (rawMatrixSlice Z.matrix j) a b =
      rawMatrixCurvature t Z a b j := by
    exact (congrArg (fun A : Mat => A a b)
      (matrixSlotAction_diagonal t (rawMatrixSlice Z.matrix j))).trans
        (rawMatrixCurvature_component t Z a b j).symm
  simp only [ricciGradient, Pi.sub_apply, Pi.smul_apply, WithLp.ofLp_sub,
    PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]
  rw [hB]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The derivative of bundle curvature is divergence free by the
differential Bianchi equation for the actual Weyl gradient. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open TraceHessian

noncomputable section

/-- Differentiate the matrix coefficient in the bundle curvature action,
keeping the tensor acted on fixed in a parallel frame. -/
def bundleCurvatureDerivative (A : Mat) (i j : Fin 4) (N : Mat) : Mat :=
  (1 / 2 : ℝ) • ∑ r, quaternionMatrix r i j • ∑ s, A r s • matrixAction s N

theorem bundleCurvatureDerivative_divergence (Z : Angular.Gradient)
    (hb : ∀ r i, gradientDivergence Z r i = 0) (j : Fin 4) (N : Mat) :
    (∑ i, bundleCurvatureDerivative (Z i) i j N) = 0 := by
  ext a b
  simp only [Matrix.sum_apply, bundleCurvatureDerivative, Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum, Matrix.zero_apply]
  calc
    _ = ∑ i, ∑ s, ∑ r, (1 / 2 : ℝ) *
        (quaternionMatrix r i j * (Z i r s * matrixAction s N a b)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ s, ∑ i, ∑ r, (1 / 2 : ℝ) *
        (quaternionMatrix r i j * (Z i r s * matrixAction s N a b)) := Finset.sum_comm
    _ = ∑ s, ∑ r, ∑ i, (1 / 2 : ℝ) *
        (quaternionMatrix r i j * (Z i r s * matrixAction s N a b)) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
    _ = ∑ s, -(1 / 2 : ℝ) * gradientDivergence Z s j * matrixAction s N a b := by
      apply Finset.sum_congr rfl
      intro s _
      simp only [gradientDivergence, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro i _
      rw [quaternionMatrix_skew r i j]
      ring
    _ = 0 := by simp only [hb, mul_zero, zero_mul, Finset.sum_const_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The weighted tensor forms and the actual Green integrands use the same
normalization, including the unsymmetrized weight derivative. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem rawSlice_weightTensor (a : Vec) (Z : Tensor) (i : Fin 4) :
    rawSlice (weightTensor a Z) i = a i • Z.matrix := by
  funext b c
  ext j
  rfl

theorem gradientVector_rawSlice (X : Hessian) (i : Fin 4) :
    rawGradientVector (rawSlice X i) = gradientVector (X i) := rfl

theorem hessianPairing_weightTensor (X : Hessian) (a : Vec) (Z : Tensor) :
    hessianPairing X (weightTensor a Z) =
      ∑ i, a i * inner ℝ (tensorGradientVector Z) (gradientVector (X i)) := by
  rw [hessianPairing_slices]
  simp_rw [rawSlice_weightTensor, rawPairing_smul_right,
    ← inner_rawGradientVector, gradientVector_rawSlice]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm]
  rfl

/-- The identity-operator term of the local weighted square is precisely
one sixth of the actual rough-Laplacian Green integrand. -/
theorem weightedQuadratic_identity_green (X : Hessian) (a : Vec) (Z : Tensor) (m : ℝ) :
    weightedQuadratic hessianNormSq m X (weightTensor a Z) =
      (m * hessianNormSq X +
        ∑ i, a i * inner ℝ (tensorGradientVector Z) (gradientVector (X i))) / 6 := by
  rw [weightedQuadratic_identity, hessianPairing_weightTensor]

theorem matrixPairing_weight_trace (N : Mat) (a : Vec) (Z : Tensor) :
    matrixPairing N (hessianTrace (weightTensor a Z)) =
      ∑ i, a i * matrixPairing N (rawMatrixSlice Z.matrix i) := by
  rw [weightTensor_trace]
  simp only [matrixPairing, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    rawMatrixSlice, Finset.mul_sum]
  calc
    _ = ∑ b : Fin 3, ∑ i : Fin 4, ∑ c : Fin 3,
        N b c * (Z.matrix b c i * a i) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      ring

/-- Both trace subtractions are the single trace Green integrand with
coefficient `−5/12`. The equality `traceCurvatureBlock t M = 6 • N`
is the finite-dimensional curvature identity for the prescribed trace. -/
theorem traceCorrection_green (t u : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (M N : Mat) (hsM : symmetric M) (htM : traceFree M)
    (hN : traceCurvatureBlock t M = (6 : ℝ) • N)
    (a : Vec) (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) (m : ℝ) :
    traceCorrection t u M m (weightTensor a Z) =
      -(5 / 12 : ℝ) * (m * matrixPairing N M +
        ∑ i, a i * matrixPairing N (rawMatrixSlice Z.matrix i)) := by
  have hD := traceComponent_curvaturePairing t u ht M hsM htM (traceComponent M)
    (fun i j => ⟨traceComponent_symmetric M hsM htM i j,
      traceComponent_traceFree M hsM htM i j⟩)
    (traceComponent_divergence M hsM htM)
  rw [trace_traceComponent, hN] at hD
  have hL := weightTensor_matrix_bianchi a Z hz hb
  have hW := traceComponent_curvaturePairing t u ht M hsM htM
    (weightTensor a Z) hL.1 hL.2
  rw [hN] at hW
  have hs (P : Mat) : matrixPairing ((6 : ℝ) • N) P = 6 * matrixPairing N P := by
    simp only [matrixPairing, Matrix.smul_apply, smul_eq_mul, mul_assoc,
      ← Finset.mul_sum]
  rw [hs] at hD hW
  rw [matrixPairing_weight_trace] at hW
  unfold traceCorrection
  rw [hD, hW]
  ring

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! Contract the raw bundle and covector actions appearing in the
derivative-slot Green identity. These are finite tensor contractions,
before integration and before any estimate. -/

namespace PositiveEinsteinFour.CurvatureContraction

open scoped BigOperators
open TraceHessian Bianchi PositiveEinsteinFour.Geometry

noncomputable section

def matrixPairingLinear (N : Mat) : Mat →ₗ[ℝ] ℝ where
  toFun M := matrixPairing M N
  map_add' M P := by
    simp only [matrixPairing, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r M := by
    simp only [matrixPairing, Matrix.smul_apply, smul_eq_mul,
      mul_assoc, ← Finset.mul_sum, RingHom.id_apply]

theorem bundleCurvatureAction_diagonal_matrix (t : Fin 3 → ℝ)
    (i k : Fin 4) (N : Mat) :
    bundleCurvatureAction (Matrix.diagonal t) i k N =
      (1 / 2 : ℝ) • ∑ s, ((1 + t s) * quaternionMatrix s i k) • matrixAction s N := by
  ext a b
  simpa only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc] using bundleCurvatureAction_diagonal t i k N a b

theorem matrixPairing_bundle_diagonal (t : Fin 3 → ℝ)
    (i k : Fin 4) (N P : Mat) :
    matrixPairing (bundleCurvatureAction (Matrix.diagonal t) i k N) P =
      (1 / 2 : ℝ) * ∑ s, (1 + t s) * quaternionMatrix s i k *
        matrixPairing (matrixAction s N) P := by
  change matrixPairingLinear P _ = _
  rw [bundleCurvatureAction_diagonal_matrix, map_smul, map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

/-- Pairing with a curvature coefficient uses just its three two-form
contractions. This isolates the normalization before the Bianchi step. -/
theorem weighted_bundle_pairing (A : Fin 4 → Fin 4 → ℝ) (b t : Fin 3 → ℝ)
    (hA : ∀ s, (∑ i, ∑ k, A i k * quaternionMatrix s i k) = b s)
    (N P : Mat) :
    (∑ i, ∑ k, A i k *
      matrixPairing (bundleCurvatureAction (Matrix.diagonal t) i k N) P) =
      (1 / 2 : ℝ) * ∑ s, b s * (1 + t s) *
        matrixPairing (matrixAction s N) P := by
  simp only [matrixPairing_bundle_diagonal, Finset.mul_sum]
  calc
    _ = ∑ i, ∑ s, ∑ k, A i k * ((1 / 2 : ℝ) *
        ((1 + t s) * quaternionMatrix s i k * matrixPairing (matrixAction s N) P)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ s, ∑ i, ∑ k, A i k * ((1 / 2 : ℝ) *
        ((1 + t s) * quaternionMatrix s i k * matrixPairing (matrixAction s N) P)) :=
      Finset.sum_comm
    _ = ∑ s, (1 / 2 : ℝ) * (1 + t s) *
        matrixPairing (matrixAction s N) P * (∑ i, ∑ k, A i k * quaternionMatrix s i k) := by
      apply Finset.sum_congr rfl
      intro s _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      simp only [hA]
      apply Finset.sum_congr rfl
      intro s _
      ring

theorem plus_bundle_pairing (a t : Fin 3 → ℝ) (j l : Fin 4) (N P : Mat) :
    (∑ i, ∑ k, plusCoefficient a i k j l *
      matrixPairing (bundleCurvatureAction (Matrix.diagonal t) i k N) P) =
      ∑ s, a s * (1 + t s) * quaternionMatrix s j l *
        matrixPairing (matrixAction s N) P := by
  rw [weighted_bundle_pairing _ (fun s => 2 * a s * quaternionMatrix s j l) t
    (fun s => plus_oneForm_pairing a s j l)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem minus_bundle_pairing (a t : Fin 3 → ℝ) (j l : Fin 4) (N P : Mat) :
    (∑ i, ∑ k, minusCoefficient a i k j l *
      matrixPairing (bundleCurvatureAction (Matrix.diagonal t) i k N) P) = 0 := by
  rw [weighted_bundle_pairing _ (fun _ => 0) t
    (fun s => minus_oneForm_pairing a s j l)]
  simp

private theorem sum_pair_blocks {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  have h := (Equiv.prodComm (α × β) (γ × δ)).sum_comp
    (fun p : (γ × δ) × (α × β) => f p.2.1 p.2.2 p.1.1 p.1.2)
  simpa only [Fintype.sum_prod_type, Equiv.prodComm_apply, Prod.swap_prod_mk] using h

private theorem quaternion_pairing_sum (s : Fin 3) (r z : Vec) :
    (∑ j, ∑ l, quaternionMatrix s j l * r j * z l) =
      -inner ℝ (quaternion s r) z := by
  rw [Finset.sum_comm]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [← quaternionMatrix_apply, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [quaternionMatrix_skew s j l]
  ring

/-- The derivative index of the matrix-bundle curvature gives the mixed
Bianchi form with its covector sign. -/
theorem matrixAction_slices_pairing (s : Fin 3) (Z : Tensor) :
    (∑ j, ∑ l, quaternionMatrix s j l *
      matrixPairing (matrixAction s (rawMatrixSlice Z.matrix j))
        (rawMatrixSlice Z.matrix l)) = -mixedCouplingForm s Z := by
  simp only [matrixPairing, Finset.mul_sum, rawMatrixSlice, matrixRotation_slice]
  rw [sum_pair_blocks]
  simp only [← mul_assoc, quaternion_pairing_sum, Finset.sum_neg_distrib,
    mixedCouplingForm]

def bundleGreenContraction (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (t : Fin 3 → ℝ) (Z : Tensor) : ℝ :=
  (1 / 2 : ℝ) * ∑ j, ∑ l, ∑ i, ∑ k, A i k j l *
    matrixPairing (bundleCurvatureAction (Matrix.diagonal t) i k
      (rawMatrixSlice Z.matrix j)) (rawMatrixSlice Z.matrix l)

theorem plus_bundleGreenContraction (a t : Fin 3 → ℝ) (Z : Tensor) :
    bundleGreenContraction (plusCoefficient a) t Z =
      -(1 / 2 : ℝ) * ∑ s, a s * (1 + t s) * mixedCouplingForm s Z := by
  unfold bundleGreenContraction
  simp_rw [plus_bundle_pairing]
  have hs : (∑ j, ∑ l, ∑ s, a s * (1 + t s) * quaternionMatrix s j l *
      matrixPairing (matrixAction s (rawMatrixSlice Z.matrix j))
        (rawMatrixSlice Z.matrix l)) =
      -(∑ s, a s * (1 + t s) * mixedCouplingForm s Z) := by
    calc
      _ = ∑ j, ∑ s, ∑ l, a s * (1 + t s) * quaternionMatrix s j l *
          matrixPairing (matrixAction s (rawMatrixSlice Z.matrix j))
            (rawMatrixSlice Z.matrix l) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
      _ = ∑ s, ∑ j, ∑ l, a s * (1 + t s) * quaternionMatrix s j l *
          matrixPairing (matrixAction s (rawMatrixSlice Z.matrix j))
            (rawMatrixSlice Z.matrix l) := Finset.sum_comm
      _ = _ := by
        simp only [mul_assoc, ← Finset.mul_sum, matrixAction_slices_pairing,
          mul_neg, Finset.sum_neg_distrib]
  rw [hs]
  ring

theorem minus_bundleGreenContraction (a t : Fin 3 → ℝ) (Z : Tensor) :
    bundleGreenContraction (minusCoefficient a) t Z = 0 := by
  simp only [bundleGreenContraction, minus_bundle_pairing, Finset.sum_const_zero, mul_zero]

def covectorGreenContraction (A R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (Z : Tensor) : ℝ :=
  ∑ l, ∑ h, ((1 / 2 : ℝ) * ∑ j, ∑ i, ∑ k, A i k j l * R i k j h) *
    matrixPairing (rawMatrixSlice Z.matrix h) (rawMatrixSlice Z.matrix l)

theorem matrixSlice_self_sum (Z : Tensor) :
    (∑ j, matrixPairing (rawMatrixSlice Z.matrix j) (rawMatrixSlice Z.matrix j)) =
      Z.squaredNorm := by
  calc
    _ = rawPairing Z.matrix Z.matrix := by
      simp only [matrixPairing, rawMatrixSlice, rawPairing, rawCoordinates,
        Fintype.sum_prod_type]
    _ = Z.squaredNorm := by
      simp only [rawPairing_vectors, real_inner_self_eq_norm_sq, Tensor.squaredNorm]

theorem plus_covectorGreenContraction (t u : Fin 3 → ℝ)
    (ht : ∑ s, t s = 0) (Z : Tensor) :
    covectorGreenContraction (plusCoefficient t) (einsteinCoefficient t u) Z =
      ((∑ s, t s ^ 2) / 2) * Z.squaredNorm := by
  simp only [covectorGreenContraction, plus_ricci_contraction t u ht]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.mul_sum, matrixSlice_self_sum]

theorem minus_covectorGreenContraction (t u : Fin 3 → ℝ)
    (hu : ∑ s, u s = 0) (Z : Tensor) :
    covectorGreenContraction (minusCoefficient u) (einsteinCoefficient t u) Z =
      ((∑ s, u s ^ 2) / 2) * Z.squaredNorm := by
  simp only [covectorGreenContraction, minus_ricci_contraction t u hu]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.mul_sum, matrixSlice_self_sum]

/-- Both parts of the raw Ricci commutator give the polynomial in the
self-dual derivative-slot Green term. -/
theorem plus_green_polynomial (t u : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    bundleGreenContraction (plusCoefficient t) t Z +
      covectorGreenContraction (plusCoefficient t) (einsteinCoefficient t u) Z =
        (7 / 6 : ℝ) * (∑ s, t s ^ 2) * Z.squaredNorm -
          4 * diagonalGradientForm t Z -
          4 * diagonalGradientForm (fun s => t s ^ 2 - (∑ r, t r ^ 2) / 3) Z := by
  rw [plus_bundleGreenContraction, plus_covectorGreenContraction t u ht]
  have h := plus_commutator_scalar t ht Z hz hb
  linarith

/-- The opposite block contributes only the covector Ricci contraction. -/
theorem minus_green_polynomial (t u : Fin 3 → ℝ) (hu : ∑ s, u s = 0)
    (Z : Tensor) :
    bundleGreenContraction (minusCoefficient u) t Z +
      covectorGreenContraction (minusCoefficient u) (einsteinCoefficient t u) Z =
        ((∑ s, u s ^ 2) / 2) * Z.squaredNorm := by
  rw [minus_bundleGreenContraction, zero_add, minus_covectorGreenContraction t u hu]

end
end PositiveEinsteinFour.CurvatureContraction
end


section

/-! The complete raw Ricci commutator in the derivative-slot Green
integrand. The bundle and covector contractions are both retained. -/

namespace PositiveEinsteinFour.CurvatureContraction

open scoped BigOperators
open TraceHessian Bianchi PositiveEinsteinFour.Geometry MeasureTheory

noncomputable section

theorem matrixPairing_add_left (A B N : Mat) :
    matrixPairing (A + B) N = matrixPairing A N + matrixPairing B N :=
  (matrixPairingLinear N).map_add A B

theorem matrixPairing_sub_left (A B N : Mat) :
    matrixPairing (A - B) N = matrixPairing A N - matrixPairing B N :=
  (matrixPairingLinear N).map_sub A B

theorem matrixPairing_sum_smul_left {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (A : ι → Mat) (N : Mat) :
    matrixPairing (∑ i, c i • A i) N = ∑ i, c i * matrixPairing (A i) N := by
  change matrixPairingLinear N _ = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

private theorem sum_pair_swap {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  have h := (Equiv.prodComm (α × β) (γ × δ)).sum_comp
    (fun p : (γ × δ) × (α × β) => f p.2.1 p.2.2 p.1.1 p.1.2)
  simpa only [Fintype.sum_prod_type, Equiv.prodComm_apply, Prod.swap_prod_mk] using h

private theorem sum_last_first {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := by
  calc
    _ = ∑ a, ∑ b, ∑ d, ∑ c, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

def rawCurvatureCommutator (t : Fin 3 → ℝ)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (Z : Tensor)
    (i k j : Fin 4) : Mat :=
  bundleCurvatureAction (Matrix.diagonal t) i k (rawMatrixSlice Z.matrix j) +
    ∑ h, R i k j h • rawMatrixSlice Z.matrix h

def derivativeGreenContraction
    (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (C : Fin 4 → Fin 4 → Fin 4 → Mat) (Z : Tensor) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ k, ∑ j, ∑ l, A i k j l *
    matrixPairing (C i k j) (rawMatrixSlice Z.matrix l)

/-- The full half-commutator splits into its two explicitly computed
curvature actions. This is a finite identity, with no PDE estimate. -/
theorem rawGreen_decomposition
    (A R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (t : Fin 3 → ℝ) (Z : Tensor) :
    derivativeGreenContraction A (rawCurvatureCommutator t R Z) Z =
      bundleGreenContraction A t Z + covectorGreenContraction A R Z := by
  unfold derivativeGreenContraction
  rw [sum_pair_swap]
  simp only [rawCurvatureCommutator, matrixPairing_add_left,
    matrixPairing_sum_smul_left, mul_add, Finset.sum_add_distrib]
  change bundleGreenContraction A t Z + _ = _
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hs (l : Fin 4) :
      (∑ j, ∑ i, ∑ k, ∑ h, (1 / 2 : ℝ) * (A i k j l *
        (R i k j h * matrixPairing (rawMatrixSlice Z.matrix h) (rawMatrixSlice Z.matrix l)))) =
      ∑ h, ∑ j, ∑ i, ∑ k, (1 / 2 : ℝ) * (A i k j l *
        (R i k j h * matrixPairing (rawMatrixSlice Z.matrix h) (rawMatrixSlice Z.matrix l))) :=
    sum_last_first _
  simp only [hs, covectorGreenContraction, Finset.mul_sum, Finset.sum_mul, mul_assoc]

theorem plus_rawGreen (t u : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    derivativeGreenContraction (plusCoefficient t)
      (rawCurvatureCommutator t (einsteinCoefficient t u) Z) Z =
        (7 / 6 : ℝ) * (∑ s, t s ^ 2) * Z.squaredNorm -
          4 * diagonalGradientForm t Z -
          4 * diagonalGradientForm (fun s => t s ^ 2 - (∑ r, t r ^ 2) / 3) Z := by
  rw [rawGreen_decomposition, plus_green_polynomial t u ht Z hz hb]

theorem minus_rawGreen (t u : Fin 3 → ℝ) (hu : ∑ s, u s = 0) (Z : Tensor) :
    derivativeGreenContraction (minusCoefficient u)
      (rawCurvatureCommutator t (einsteinCoefficient t u) Z) Z =
        ((∑ s, u s ^ 2) / 2) * Z.squaredNorm := by
  rw [rawGreen_decomposition, minus_green_polynomial t u hu]

/-- Substituting precisely the ordinary Ricci identity computes the
self-dual Green integrand. -/
theorem plus_derivativeGreen_of_commutator (t u : Fin 3 → ℝ)
    (ht : ∑ s, t s = 0) (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi)
    (D : Fin 4 → Fin 4 → Fin 4 → Mat)
    (hD : ∀ i k j, D i k j - D k i j =
      rawCurvatureCommutator t (einsteinCoefficient t u) Z i k j) :
    derivativeGreenContraction (plusCoefficient t) (fun i k j => D i k j - D k i j) Z =
      (7 / 6 : ℝ) * (∑ s, t s ^ 2) * Z.squaredNorm -
        4 * diagonalGradientForm t Z -
        4 * diagonalGradientForm (fun s => t s ^ 2 - (∑ r, t r ^ 2) / 3) Z := by
  have he : (fun i k j => D i k j - D k i j) =
      rawCurvatureCommutator t (einsteinCoefficient t u) Z := by
    funext i k j
    exact hD i k j
  rw [he, plus_rawGreen t u ht Z hz hb]

theorem integral_derivativeGreen {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (m : Ω → ℝ)
    (A : Ω → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (C : Ω → Fin 4 → Fin 4 → Fin 4 → Mat) (Z : Ω → Tensor) :
    (1 / 2 : ℝ) * (∫ x, ∑ p : Averages.CurvatureIndex,
      m x * A x p.1.1 p.1.2 p.2.1 p.2.2 *
        matrixPairing (C x p.1.1 p.1.2 p.2.1) (rawMatrixSlice (Z x).matrix p.2.2) ∂μ) =
      ∫ x, m x * derivativeGreenContraction (A x) (C x) (Z x) ∂μ := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [derivativeGreenContraction, Fintype.sum_prod_type,
    Finset.mul_sum, mul_assoc, mul_left_comm (m x) (1 / 2 : ℝ)]

/-- The self-dual half-commutator in the metric Green formula has the
claimed scalar integral as a consequence of the raw Ricci identity. -/
theorem integral_plusGreen_of_commutator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (m : Ω → ℝ) (t u : Ω → Fin 3 → ℝ) (Z : Ω → Tensor)
    (D : Ω → Fin 4 → Fin 4 → Fin 4 → Mat)
    (ht : ∀ x, ∑ s, t x s = 0) (hz : ∀ x, (Z x).traceFree)
    (hb : ∀ x, (Z x).bianchi)
    (hD : ∀ x i k j, D x i k j - D x k i j =
      rawCurvatureCommutator (t x) (einsteinCoefficient (t x) (u x)) (Z x) i k j) :
    (1 / 2 : ℝ) * (∫ x, ∑ p : Averages.CurvatureIndex,
      m x * plusCoefficient (t x) p.1.1 p.1.2 p.2.1 p.2.2 *
        matrixPairing (D x p.1.1 p.1.2 p.2.1 - D x p.1.2 p.1.1 p.2.1)
          (rawMatrixSlice (Z x).matrix p.2.2) ∂μ) =
      ∫ x, m x * ((7 / 6 : ℝ) * (∑ s, t x s ^ 2) * (Z x).squaredNorm -
        4 * diagonalGradientForm (t x) (Z x) -
        4 * diagonalGradientForm (fun s => t x s ^ 2 - (∑ r, t x r ^ 2) / 3) (Z x)) ∂μ := by
  rw [integral_derivativeGreen μ m (fun x => plusCoefficient (t x))
    (fun x i k j => D x i k j - D x k i j) Z]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [plus_derivativeGreen_of_commutator (t x) (u x) (ht x) (Z x)
    (hz x) (hb x) (D x) (hD x)]

theorem integral_minusGreen_of_commutator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (m : Ω → ℝ) (t u : Ω → Fin 3 → ℝ) (Z : Ω → Tensor)
    (D : Ω → Fin 4 → Fin 4 → Fin 4 → Mat)
    (hu : ∀ x, ∑ s, u x s = 0)
    (hD : ∀ x i k j, D x i k j - D x k i j =
      rawCurvatureCommutator (t x) (einsteinCoefficient (t x) (u x)) (Z x) i k j) :
    (1 / 2 : ℝ) * (∫ x, ∑ p : Averages.CurvatureIndex,
      m x * minusCoefficient (u x) p.1.1 p.1.2 p.2.1 p.2.2 *
        matrixPairing (D x p.1.1 p.1.2 p.2.1 - D x p.1.2 p.1.1 p.2.1)
          (rawMatrixSlice (Z x).matrix p.2.2) ∂μ) =
      ∫ x, m x * (((∑ s, u x s ^ 2) / 2) * (Z x).squaredNorm) ∂μ := by
  rw [integral_derivativeGreen μ m (fun x => minusCoefficient (u x))
    (fun x i k j => D x i k j - D x k i j) Z]
  apply integral_congr_ae
  filter_upwards [] with x
  have he : (fun i k j => D x i k j - D x k i j) =
      rawCurvatureCommutator (t x) (einsteinCoefficient (t x) (u x)) (Z x) := by
    funext i k j
    exact hD x i k j
  rw [he, minus_rawGreen (t x) (u x) (hu x)]

theorem ricciGradient_self_pairing (t : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    rawPairing (ricciGradient t Z) Z.matrix =
      13 * Z.squaredNorm - 20 * diagonalGradientForm t Z := by
  rw [ricciGradient_pairing t ht Z Z hz hb hz hb,
    rawMatrixCurvature_pairing t Z Z hz, rawPairing_vectors]
  simp only [real_inner_self_eq_norm_sq, Tensor.squaredNorm,
    diagonalGradientPairing, diagonalGradientForm]

/-- The scalar rough-Laplacian term is evaluated using the equation
already derived from the two raw Ricci identities. -/
theorem integral_identityGreen_of_ricci {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (m : Ω → ℝ) (t : Ω → Fin 3 → ℝ) (Z : Ω → Tensor)
    (L : Ω → RawGradient) (ht : ∀ x, ∑ s, t x s = 0)
    (hz : ∀ x, (Z x).traceFree) (hb : ∀ x, (Z x).bianchi)
    (hL : ∀ x, L x = ricciGradient (t x) (Z x)) :
    -(∫ x, m x * rawPairing (L x) (Z x).matrix ∂μ) =
      ∫ x, m x * (-13 * (Z x).squaredNorm + 20 * diagonalGradientForm (t x) (Z x)) ∂μ := by
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [hL, ricciGradient_self_pairing (t x) (ht x) (Z x) (hz x) (hb x)]
  ring

end
end PositiveEinsteinFour.CurvatureContraction
end


section

/-! Polarization of the actual derivative-slot Green integrands. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Bianchi TraceHessian PositiveEinsteinFour.Geometry
open CurvatureContraction

noncomputable section

abbrev DerivativeCoefficient := Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ

def derivativePairing (A : DerivativeCoefficient) (X Y : Hessian) : ℝ :=
  ∑ p : Averages.CurvatureIndex,
    A p.1.1 p.1.2 p.2.1 p.2.2 * matrixPairing (X p.1.1 p.2.1) (Y p.1.2 p.2.2)

private theorem matrix_pairing_comm (X Y : Mat) : matrixPairing X Y = matrixPairing Y X := by
  simp only [matrixPairing, mul_comm]

private theorem matrix_pairing_add_left (X Y Z : Mat) :
    matrixPairing (X + Y) Z = matrixPairing X Z + matrixPairing Y Z := by
  simp only [matrixPairing, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

private theorem matrix_pairing_add_right (X Y Z : Mat) :
    matrixPairing X (Y + Z) = matrixPairing X Y + matrixPairing X Z := by
  simp only [matrixPairing, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem derivativePairing_add_left (A : DerivativeCoefficient) (X Y Z : Hessian) :
    derivativePairing A (X + Y) Z = derivativePairing A X Z + derivativePairing A Y Z := by
  simp only [derivativePairing, Pi.add_apply, matrix_pairing_add_left,
    mul_add, Finset.sum_add_distrib]

theorem derivativePairing_add_right (A : DerivativeCoefficient) (X Y Z : Hessian) :
    derivativePairing A X (Y + Z) = derivativePairing A X Y + derivativePairing A X Z := by
  simp only [derivativePairing, Pi.add_apply, matrix_pairing_add_right,
    mul_add, Finset.sum_add_distrib]

theorem derivativePairing_comm (A : DerivativeCoefficient)
    (hA : ∀ i k j l, A k i l j = A i k j l) (X Y : Hessian) :
    derivativePairing A X Y = derivativePairing A Y X := by
  let swap : Averages.CurvatureIndex ≃ Averages.CurvatureIndex :=
    Equiv.prodCongr (Equiv.prodComm _ _) (Equiv.prodComm _ _)
  unfold derivativePairing
  calc
    _ = ∑ p : Averages.CurvatureIndex,
        A (swap p).1.1 (swap p).1.2 (swap p).2.1 (swap p).2.2 *
          matrixPairing (X (swap p).1.1 (swap p).2.1) (Y (swap p).1.2 (swap p).2.2) :=
      (swap.sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      change A p.1.2 p.1.1 p.2.2 p.2.1 * matrixPairing (X p.1.2 p.2.2) (Y p.1.1 p.2.1) = _
      rw [hA, matrix_pairing_comm]

theorem weightedQuadratic_derivativePairing (A : DerivativeCoefficient)
    (hA : ∀ i k j l, A k i l j = A i k j l) (m : ℝ) (X Y : Hessian) :
    weightedQuadratic (fun W => derivativePairing A W W) m X Y =
      (m * derivativePairing A X X + derivativePairing A X Y) / 6 := by
  unfold weightedQuadratic
  dsimp only
  rw [derivativePairing_add_left, derivativePairing_add_right,
    derivativePairing_add_right, derivativePairing_comm A hA Y X]
  ring

theorem derivativePairing_weightTensor (A : DerivativeCoefficient)
    (X : Hessian) (a : Vec) (Z : Tensor) :
    derivativePairing A X (weightTensor a Z) =
      ∑ p : Averages.CurvatureIndex,
        a p.1.2 * A p.1.1 p.1.2 p.2.1 p.2.2 *
          matrixPairing (X p.1.1 p.2.1) (rawMatrixSlice Z.matrix p.2.2) := by
  apply Finset.sum_congr rfl
  intro p _
  change A p.1.1 p.1.2 p.2.1 p.2.2 *
      (∑ b, ∑ c, X p.1.1 p.2.1 b c * (a p.1.2 * Z.matrix b c p.2.2)) = _
  simp only [matrixPairing, rawMatrixSlice, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- The unsymmetrized weight tensor gives exactly the derivative-of-weight
term in the geometric Green formula, with no outer-slot symmetry premise. -/
theorem weightedQuadratic_derivative_green (A : DerivativeCoefficient)
    (hA : ∀ i k j l, A k i l j = A i k j l)
    (m : ℝ) (X : Hessian) (a : Vec) (Z : Tensor) :
    weightedQuadratic (fun W => derivativePairing A W W) m X (weightTensor a Z) =
      (∑ p : Averages.CurvatureIndex,
        (m * A p.1.1 p.1.2 p.2.1 p.2.2 *
          matrixPairing (X p.1.1 p.2.1) (X p.1.2 p.2.2) +
          a p.1.2 * A p.1.1 p.1.2 p.2.1 p.2.2 *
            matrixPairing (X p.1.1 p.2.1) (rawMatrixSlice Z.matrix p.2.2))) / 6 := by
  rw [weightedQuadratic_derivativePairing A hA, derivativePairing_weightTensor]
  simp only [derivativePairing, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

theorem blockCoefficient_pair_swap (Q : Fin 3 → Mat4)
    (hQ : ∀ s i j, Q s j i = -Q s i j) (t : Fin 3 → ℝ) (i k j l : Fin 4) :
    blockCoefficient Q t k i l j = blockCoefficient Q t i k j l := by
  unfold blockCoefficient
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [hQ s i k, hQ s j l]
  ring

theorem plusDerivativeQuadratic_eq_derivativePairing (t : Fin 3 → ℝ) (X : Hessian) :
    plusDerivativeQuadratic t X = derivativePairing (plusCoefficient t) X X := by
  unfold plusDerivativeQuadratic derivativeSlotForm derivativePairing
    plusCoefficient blockCoefficient
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (f := fun p : Averages.CurvatureIndex => _)]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm (f := fun j : Fin 4 => _)]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  rw [matrix_pairing_comm]
  ring

/-- The self-dual piece of the local square is precisely the normalized
geometric derivative-slot Green integrand. -/
theorem weightedQuadratic_plus_green (t : Fin 3 → ℝ)
    (m : ℝ) (X : Hessian) (a : Vec) (Z : Tensor) :
    weightedQuadratic (plusDerivativeQuadratic t) m X (weightTensor a Z) =
      (∑ p : Averages.CurvatureIndex,
        (m * plusCoefficient t p.1.1 p.1.2 p.2.1 p.2.2 *
          matrixPairing (X p.1.1 p.2.1) (X p.1.2 p.2.2) +
          a p.1.2 * plusCoefficient t p.1.1 p.1.2 p.2.1 p.2.2 *
            matrixPairing (X p.1.1 p.2.1) (rawMatrixSlice Z.matrix p.2.2))) / 6 := by
  have hform : plusDerivativeQuadratic t =
      fun W => derivativePairing (plusCoefficient t) W W := by
    funext W
    exact plusDerivativeQuadratic_eq_derivativePairing t W
  rw [hform]
  exact weightedQuadratic_derivative_green _
    (blockCoefficient_pair_swap quaternionMatrix (fun s i j => quaternionMatrix_skew s j i) t)
    m X a Z

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! The matrix-slot Hessian quadratic form is exactly the left side of
the varying-operator Green identity, including the unsymmetrized weight. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem gradientVector_add (Z W : Angular.Gradient) :
    gradientVector (Z + W) = gradientVector Z + gradientVector W := by
  ext p
  rfl

theorem gradientVector_innerSlice (X : Hessian) (i : Fin 4)
    (hs : ∀ j, symmetric (X i j)) :
    tensorGradientVector (innerSlice X i) = gradientVector (X i) := by
  ext p
  rcases p with ⟨j, a, b⟩
  change (innerSlice X i).matrix a b j = X i j a b
  rw [innerSlice_matrix X i hs]

def matrixHessianPairing (A : Mat) (X Y : Hessian) : ℝ :=
  ∑ i, inner ℝ (gradientVector (X i))
    (matrixSlotOperator A (gradientVector (Y i)))

theorem matrixHessianPairing_add_left (A : Mat) (X Y Z : Hessian) :
    matrixHessianPairing A (X + Y) Z =
      matrixHessianPairing A X Z + matrixHessianPairing A Y Z := by
  simp only [matrixHessianPairing, Pi.add_apply, gradientVector_add,
    inner_add_left, Finset.sum_add_distrib]

theorem matrixHessianPairing_add_right (A : Mat) (X Y Z : Hessian) :
    matrixHessianPairing A X (Y + Z) =
      matrixHessianPairing A X Y + matrixHessianPairing A X Z := by
  simp only [matrixHessianPairing, Pi.add_apply, gradientVector_add,
    map_add, inner_add_right, Finset.sum_add_distrib]

theorem matrixHessianPairing_comm (A : Mat) (hA : symmetric A) (X Y : Hessian) :
    matrixHessianPairing A X Y = matrixHessianPairing A Y X := by
  apply Finset.sum_congr rfl
  intro i _
  rw [← matrixSlotOperator_selfadjoint A hA, real_inner_comm]

theorem matrixSlotQuadratic_eq_matrixHessianPairing
    (t : Fin 3 → ℝ) (X : Hessian)
    (hs : ∀ i j, symmetric (X i j)) (ht : ∀ i j, traceFree (X i j)) :
    matrixSlotQuadratic t X = matrixHessianPairing (Matrix.diagonal t) X X := by
  have hpoint (i : Fin 4) :
      inner ℝ (gradientVector (X i))
        (matrixSlotOperator (Matrix.diagonal t) (gradientVector (X i))) =
      ∑ s, t s * ∑ b, ‖rawSlice X i s b‖ ^ 2 := by
    rw [real_inner_comm, ← gradientVector_innerSlice X i (hs i),
      matrixSlot_diagonal_self t _ (innerSlice_traceFree X i (ht i))]
    simp only [diagonalGradientForm, rawSlice_eq_innerSlice X hs i]
  simp only [matrixSlotQuadratic, matrixSlotForm_slices, matrixHessianPairing, hpoint]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

theorem weightedQuadratic_matrixHessianPairing (A : Mat) (hA : symmetric A)
    (m : ℝ) (X Y : Hessian) :
    weightedQuadratic (fun W => matrixHessianPairing A W W) m X Y =
      (m * matrixHessianPairing A X X + matrixHessianPairing A X Y) / 6 := by
  unfold weightedQuadratic
  dsimp only
  rw [matrixHessianPairing_add_left, matrixHessianPairing_add_right,
    matrixHessianPairing_add_right, matrixHessianPairing_comm A hA Y X]
  ring

theorem gradientVector_weightTensor (a : Vec) (Z : Tensor) (i : Fin 4) :
    gradientVector (weightTensor a Z i) = a i • tensorGradientVector Z := by
  ext p
  rfl

theorem matrixHessianPairing_weightTensor (A : Mat) (hA : symmetric A)
    (X : Hessian) (a : Vec) (Z : Tensor) :
    matrixHessianPairing A X (weightTensor a Z) =
      ∑ i, a i * inner ℝ (tensorGradientVector Z)
        (matrixSlotOperator A (gradientVector (X i))) := by
  simp only [matrixHessianPairing, gradientVector_weightTensor, map_smul,
    real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  rw [← matrixSlotOperator_selfadjoint A hA, real_inner_comm]

/-- Arbitrary-frame matrix form, before pointwise diagonalization. -/
theorem weightedQuadratic_matrix_green (A : Mat) (hA : symmetric A)
    (m : ℝ) (X : Hessian) (a : Vec) (Z : Tensor) :
    weightedQuadratic (fun W => matrixHessianPairing A W W) m X (weightTensor a Z) =
      (m * (∑ i, inner ℝ (gradientVector (X i))
          (matrixSlotOperator A (gradientVector (X i)))) +
        ∑ i, a i * inner ℝ (tensorGradientVector Z)
          (matrixSlotOperator A (gradientVector (X i)))) / 6 := by
  rw [weightedQuadratic_matrixHessianPairing A hA,
    matrixHessianPairing_weightTensor A hA]
  rfl

/-- In a single diagonal frame the local polynomial quadratic equals the
same arbitrary-frame form. This assertion does not select a global frame. -/
theorem weightedQuadratic_matrixSlot_green
    (t : Fin 3 → ℝ) (m : ℝ) (X : Hessian)
    (hs : ∀ i j, symmetric (X i j)) (ht : ∀ i j, traceFree (X i j))
    (a : Vec) (Z : Tensor) (hz : Z.traceFree) :
    weightedQuadratic (matrixSlotQuadratic t) m X (weightTensor a Z) =
      (m * (∑ i, inner ℝ (gradientVector (X i))
          (matrixSlotOperator (Matrix.diagonal t) (gradientVector (X i)))) +
        ∑ i, a i * inner ℝ (tensorGradientVector Z)
          (matrixSlotOperator (Matrix.diagonal t) (gradientVector (X i)))) / 6 := by
  have hAs : symmetric (Matrix.diagonal t) := by
    intro i j
    by_cases h : i = j
    · subst j; rfl
    · simp [Matrix.diagonal, h, Ne.symm h]
  have hY : ∀ i j, symmetric (weightTensor a Z i j) ∧
      traceFree (weightTensor a Z i j) := fun i j =>
    ⟨fun b c => by
        change a i * Z.matrix b c j = a i * Z.matrix c b j
        rw [Z.matrix_symmetric],
      by
        change (∑ b, a i * Z.matrix b b j) = 0
        rw [← Finset.mul_sum]
        have hh := congrArg (fun v : Vec => v j) hz
        have hd (b : Fin 3) : Z.matrix b b = Z.diagonal b := by fin_cases b <;> rfl
        simp only [hd, WithLp.ofLp_sum, Finset.sum_apply] at *
        rw [hh]
        simp⟩
  have hadd : ∀ i j, symmetric ((X + weightTensor a Z) i j) ∧
      traceFree ((X + weightTensor a Z) i j) := by
    intro i j
    constructor
    · intro b c
      change X i j b c + weightTensor a Z i j b c =
        X i j c b + weightTensor a Z i j c b
      rw [hs i j, (hY i j).1]
    · change (∑ b, (X i j b b + weightTensor a Z i j b b)) = 0
      rw [Finset.sum_add_distrib, ht i j, (hY i j).2, add_zero]
  unfold weightedQuadratic
  rw [matrixSlotQuadratic_eq_matrixHessianPairing t X hs ht,
    matrixSlotQuadratic_eq_matrixHessianPairing t _
      (fun i j => (hadd i j).1) (fun i j => (hadd i j).2),
    matrixSlotQuadratic_eq_matrixHessianPairing t _
      (fun i j => (hY i j).1) (fun i j => (hY i j).2)]
  exact weightedQuadratic_matrix_green _ hAs m X a Z

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! The prescribed-trace coefficient and its ordinary derivative in an
arbitrary frame. No derivative of a matrix eigenframe is used. -/

namespace PositiveEinsteinFour.Geometry

open Matrix TraceHessian HighestHessian Bianchi
open scoped BigOperators

noncomputable section

local instance traceCoefficientNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance traceCoefficientNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance traceCoefficientNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

def traceCoefficient (A : Mat) : Mat :=
  (4 + Matrix.trace (A * A) / 6) • A - (5 : ℝ) • traceFreeSquare A

def traceCoefficientDerivative (A Z : Mat) : Mat :=
  (4 + Matrix.trace (A * A) / 6) • Z +
    (Matrix.trace (A * Z) / 3) • A - (10 : ℝ) • matrixSlotAction A Z

private theorem trace_coefficient_coordinates (a b c d e : ℝ) :
    (4 : ℝ) • weylLaplacian (ofCoordinates a b c d e) -
      matrixSlotAction (ofCoordinates a b c d e)
        (weylLaplacian (ofCoordinates a b c d e)) =
    (6 : ℝ) • traceCoefficient (ofCoordinates a b c d e) := by
  ext i j
  simp only [weylLaplacian, traceCoefficient, traceFreeSquare, matrixSlotAction,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.trace, Matrix.diag, smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    norm_num [ofCoordinates, Matrix.one_apply, Fin.sum_univ_three] <;> ring

/-- The trace operator applied to the derived Weyl Laplacian is six
times the coefficient used in the trace Green identity. -/
theorem trace_coefficient_eq (A : Mat) (hs : symmetric A) (ht : traceFree A) :
    (4 : ℝ) • weylLaplacian A - matrixSlotAction A (weylLaplacian A) =
      (6 : ℝ) • traceCoefficient A := by
  simpa only [coordinates_eq A hs ht] using
    trace_coefficient_coordinates (A 0 0) (A 1 1) (A 0 1) (A 0 2) (A 1 2)

theorem traceCurvatureBlock_weylLaplacian (t : Fin 3 → ℝ) (ht : ∑ s, t s = 0) :
    traceCurvatureBlock t (weylLaplacian (Matrix.diagonal t)) =
      (6 : ℝ) • traceCoefficient (Matrix.diagonal t) := by
  have hs : symmetric (Matrix.diagonal t) := by
    intro i j
    by_cases h : i = j
    · subst j; rfl
    · simp [Matrix.diagonal, h, Ne.symm h]
  have htr : traceFree (Matrix.diagonal t) := by
    simpa only [traceFree, Matrix.diagonal_apply_eq] using ht
  simpa only [traceCurvatureBlock, matrixSlotAction_diagonal] using
    trace_coefficient_eq (Matrix.diagonal t) hs htr

/-- Differentiate the invariant polynomial coefficient, retaining its
radial derivative term. -/
theorem hasDerivAt_traceCoefficient {A : ℝ → Mat} {Z : Mat} {r : ℝ}
    (hA : HasDerivAt A Z r) :
    HasDerivAt (fun t => traceCoefficient (A t))
      (traceCoefficientDerivative (A r) Z) r := by
  have hp := hasDerivAt_matrixTrace (hA.mul hA)
  have h := (((hasDerivAt_const r (4 : ℝ)).add (hp.div_const 6)).smul hA).sub
    ((hasDerivAt_traceFreeSquare hA).const_smul (5 : ℝ))
  convert! h using 1
  simp only [traceCoefficientDerivative, Matrix.trace_add,
    Matrix.trace_mul_comm Z (A r), zero_add, Pi.add_apply, Pi.mul_apply]
  have hscalar : (Matrix.trace (A r * Z) + Matrix.trace (A r * Z)) / 6 =
      Matrix.trace (A r * Z) / 3 := by ring
  rw [hscalar]
  module

/-- At positive norm the radial derivative is read off from the usual
Frobenius contraction, exactly as in the scalar trace calculation. -/
theorem traceCoefficientDerivative_radial (A Z : Mat) (v p : ℝ)
    (hZ : symmetric Z) (hv : Matrix.trace (A * A) = 6 * v ^ 2)
    (hp : matrixPairing A Z = 6 * v * p) :
    traceCoefficientDerivative A Z =
      (4 + v ^ 2) • Z + (2 * v * p) • A - (10 : ℝ) • matrixSlotAction A Z := by
  have hzt : Zᵀ = Z := by ext i j; exact hZ j i
  rw [matrixPairing_eq_trace, hzt] at hp
  unfold traceCoefficientDerivative
  rw [hv, hp]
  congr 2 <;> ring_nf

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Ricci-commuted gradient equation for the actual metric. The two
classical slot identities remain explicit, while the differentiated trace
and curvature-divergence equations are derived. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance metricRicciNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricRicciNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricRicciNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

theorem rawMatrixSlice_gradientTensor (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) (j : Fin 4) :
    rawMatrixSlice (gradientTensor Z).matrix j = Z j := by
  ext a b
  simp only [rawMatrixSlice, gradientTensor_matrix Z hs]

theorem tensorGradientVector_gradientTensor (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) :
    tensorGradientVector (gradientTensor Z) = gradientVector Z := by
  ext p
  rcases p with ⟨i, a, b⟩
  change (gradientTensor Z).matrix a b i = Z i a b
  rw [gradientTensor_matrix Z hs]

theorem rawThirdLaplacian_vector (D : Fin 4 → Fin 4 → Fin 4 → Mat) :
    rawGradientVector (rawThirdLaplacian D) = ∑ i, gradientVector (D i i) := by
  ext p
  rcases p with ⟨j, a, b⟩
  simp only [rawGradientVector, rawCoordinates, rawThirdLaplacian,
    gradientVector, WithLp.ofLp_sum, Finset.sum_apply]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem metric_ricci_gradient (g : SmoothMetric M) (h : WeylCovariantIdentities g)
    {μ : Measure (FrameBundle g)} (φ : Fin 4 → FrameFlow g μ)
    (hT : ∀ k r e, HasDerivAt
      (fun s => plusWeyl g ((φ k).map s e).base ((φ k).map s e).frame)
      (plusWeylGradient g ((φ k).map r e).base ((φ k).map r e).frame k) r)
    (hX : ∀ k i r e, HasDerivAt
      (fun s => plusWeylHessian g ((φ k).map s e).base ((φ k).map s e).frame i i)
      (plusWeylThirdDerivative g ((φ k).map r e).base ((φ k).map r e).frame k i i) r)
    (e : FrameBundle g) (t : Fin 3 → ℝ)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hdiag : plusWeyl g e.base e.frame = Matrix.diagonal t)
    (hs : ∀ i, symmetric (plusWeylGradient g e.base e.frame i))
    (hb : ∀ r i, gradientDivergence (plusWeylGradient g e.base e.frame) r i = 0)
    (hinner : ∀ i k j,
      plusWeylThirdDerivative g e.base e.frame i k j -
        plusWeylThirdDerivative g e.base e.frame i j k =
      bundleCurvatureDerivative (plusWeylGradient g e.base e.frame i) k j
        (plusWeyl g e.base e.frame) +
      bundleCurvatureAction (plusWeyl g e.base e.frame) k j
        (plusWeylGradient g e.base e.frame i))
    (houter : ∀ i k j,
      plusWeylThirdDerivative g e.base e.frame i k j -
        plusWeylThirdDerivative g e.base e.frame k i j =
      bundleCurvatureAction (plusWeyl g e.base e.frame) i k
        (plusWeylGradient g e.base e.frame j) +
      ∑ a, R i k j a • plusWeylGradient g e.base e.frame a)
    (hRic : ∀ j a, (∑ i, R i j i a) = if j = a then 3 else 0) :
    rawThirdLaplacian (plusWeylThirdDerivative g e.base e.frame) =
      ricciGradient t (plusGradientTensor g e.base e.frame) := by
  have hslice (j : Fin 4) :
      rawMatrixSlice (plusGradientTensor g e.base e.frame).matrix j =
        plusWeylGradient g e.base e.frame j :=
    rawMatrixSlice_gradientTensor _ hs j
  apply rawThirdLaplacian_eq_ricciGradient t (plusGradientTensor g e.base e.frame)
    (plusWeylThirdDerivative g e.base e.frame)
    (fun i k j => bundleCurvatureDerivative (plusWeylGradient g e.base e.frame i)
      k j (plusWeyl g e.base e.frame)) R
  · intro i k j
    simpa only [hslice, ← hdiag] using hinner i k j
  · intro i k j
    simpa only [hslice, ← hdiag] using houter i k j
  · intro j
    exact bundleCurvatureDerivative_divergence _ hb j _
  · exact hRic
  · intro j
    simpa only [hslice, ← hdiag] using metric_weyl_third_trace g h φ hT hX j e

/-- Convert the raw equation into the exact vector Laplacian used by the
metric Green identity, without changing any tensor component. -/
theorem frameGradientLaplacian_of_raw_ricci (g : SmoothMetric M) (e : FrameBundle g)
    (t : Fin 3 → ℝ)
    (hraw : rawThirdLaplacian (plusWeylThirdDerivative g e.base e.frame) =
      ricciGradient t (plusGradientTensor g e.base e.frame)) :
    frameGradientLaplacian g e =
      rawGradientVector (ricciGradient t (plusGradientTensor g e.base e.frame)) := by
  rw [← hraw, rawThirdLaplacian_vector]
  rfl

/-- The ordinary gradient/Laplacian contraction agrees with the scalar
term used in the identity Green calculation at this frame. -/
theorem metric_identity_contraction (g : SmoothMetric M) (e : FrameBundle g)
    (t : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (hs : ∀ i, symmetric (plusWeylGradient g e.base e.frame i))
    (hz : ∀ i, traceFree (plusWeylGradient g e.base e.frame i))
    (hb : ∀ r i, gradientDivergence (plusWeylGradient g e.base e.frame) r i = 0)
    (hraw : rawThirdLaplacian (plusWeylThirdDerivative g e.base e.frame) =
      ricciGradient t (plusGradientTensor g e.base e.frame)) :
    inner ℝ (frameGradientVector g e) (frameGradientLaplacian g e) =
      13 * (plusGradientTensor g e.base e.frame).squaredNorm -
        20 * diagonalGradientForm t (plusGradientTensor g e.base e.frame) := by
  have hvec : frameGradientVector g e =
      tensorGradientVector (plusGradientTensor g e.base e.frame) :=
    (tensorGradientVector_gradientTensor _ hs).symm
  rw [frameGradientLaplacian_of_raw_ricci g e t hraw, hvec]
  change inner ℝ (rawGradientVector (plusGradientTensor g e.base e.frame).matrix)
    (rawGradientVector (ricciGradient t (plusGradientTensor g e.base e.frame))) = _
  rw [real_inner_comm, inner_rawGradientVector]
  exact CurvatureContraction.ricciGradient_self_pairing t ht _
    (gradientTensor_traceFree _ hz) (gradientTensor_bianchi _ hs hb)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The full prescribed-trace Green identity for the actual metric,
derived by differentiating its invariant polynomial coefficient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance metricTraceNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricTraceNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricTraceNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

def matrixVectorMap : Mat →L[ℝ] MatrixVector :=
  ({ toFun := matrixVector
     map_add' := fun A B => by ext p; rfl
     map_smul' := fun r A => by ext p; rfl } : Mat →ₗ[ℝ] MatrixVector).toContinuousLinearMap

theorem hasDerivAt_matrixVector {T : ℝ → Mat} {Z : Mat} {r : ℝ}
    (hT : HasDerivAt T Z r) :
    HasDerivAt (fun t => matrixVector (T t)) (matrixVector Z) r := by
  convert! matrixVectorMap.hasFDerivAt.comp_hasDerivAt r hT using 1

theorem continuous_traceCoefficient : Continuous traceCoefficient := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [traceCoefficient, traceFreeSquare, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.mul_apply, Matrix.trace, Matrix.diag, smul_eq_mul]
  fun_prop

theorem continuous_traceCoefficientDerivative :
    Continuous (fun p : Mat × Mat => traceCoefficientDerivative p.1 p.2) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [traceCoefficientDerivative, matrixSlotAction, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.trace,
    Matrix.diag, smul_eq_mul]
  by_cases hab : a = b
  · simp only [hab, ite_true]
    fun_prop
  · simp only [hab, ite_false]
    fun_prop

def traceCoefficientVectorMap : C(Mat, MatrixVector) :=
  ⟨fun A => matrixVector (traceCoefficient A),
    matrixVectorMap.continuous.comp continuous_traceCoefficient⟩

def traceCoefficientDerivativeVectorMap : C(Mat × Mat, MatrixVector) :=
  ⟨fun p => matrixVector (traceCoefficientDerivative p.1 p.2),
    matrixVectorMap.continuous.comp continuous_traceCoefficientDerivative⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Before any scalar contraction, both trace subtractions give this
identity on the actual frame bundle. The coefficient is a polynomial in
the actual Weyl matrix and its derivative is derived above. -/
theorem weighted_metric_trace_green
    (g : SmoothMetric M) {μ : Measure (FrameBundle g)}
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (φ : Fin 4 → FrameFlow g μ)
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hT : Continuous (fun e : FrameBundle g => plusWeyl g e.base e.frame))
    (hDT : ∀ i, Continuous (fun e : FrameBundle g => plusWeylGradient g e.base e.frame i))
    (hX : ∀ i, Continuous (frameHessianSlice g i i))
    (hm : ∀ i t e, HasDerivAt (fun s => m ((φ i).map s e))
      (dm i ((φ i).map t e)) t)
    (hTd : ∀ i t e, HasDerivAt
      (fun s => plusWeyl g ((φ i).map s e).base ((φ i).map s e).frame)
      (plusWeylGradient g ((φ i).map t e).base ((φ i).map t e).frame i) t)
    (hZd : ∀ i t e, HasDerivAt (fun s => frameGradientSlice g i ((φ i).map s e))
      (frameHessianSlice g i i ((φ i).map t e)) t) :
    -(5 / 12 : ℝ) * (∫ e, m e *
      matrixPairing (traceCoefficient (plusWeyl g e.base e.frame))
        (hessianTrace (plusWeylHessian g e.base e.frame)) +
      ∑ i, dm i e * matrixPairing (traceCoefficient (plusWeyl g e.base e.frame))
        (plusWeylGradient g e.base e.frame i) ∂μ) =
      (5 / 12 : ℝ) * (∫ e, m e * ∑ i,
        matrixPairing (traceCoefficientDerivative (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame i))
          (plusWeylGradient g e.base e.frame i) ∂μ) := by
  let T : C(FrameBundle g, Mat) := ⟨fun e => plusWeyl g e.base e.frame, hT⟩
  let DT (i : Fin 4) : C(FrameBundle g, Mat) :=
    ⟨fun e => plusWeylGradient g e.base e.frame i, hDT i⟩
  let B : C(FrameBundle g, MatrixVector) := traceCoefficientVectorMap.comp T
  let dB (i : Fin 4) : C(FrameBundle g, MatrixVector) :=
    traceCoefficientDerivativeVectorMap.comp (T.prodMk (DT i))
  let Z (i : Fin 4) : C(FrameBundle g, MatrixVector) :=
    ⟨frameGradientSlice g i, matrixVectorMap.continuous.comp (hDT i)⟩
  let X (i : Fin 4) : C(FrameBundle g, MatrixVector) := ⟨frameHessianSlice g i i, hX i⟩
  have h := Averages.weighted_trace_green μ
    (fun i => (φ i).map) (fun i => (φ i).continuous) (fun i => (φ i).preserves)
    m dm B dB Z X hm
    (fun i t e => hasDerivAt_matrixVector (hasDerivAt_traceCoefficient (hTd i t e))) hZd
  have hsum (e : FrameBundle g) :
      (∑ i, frameHessianSlice g i i e) =
        matrixVector (hessianTrace (plusWeylHessian g e.base e.frame)) := by
    ext p
    simp only [frameHessianSlice, hessianTrace, matrixVector, WithLp.ofLp_sum,
      Finset.sum_apply, Matrix.sum_apply]
  simp only [B, dB, T, DT, Z, X, traceCoefficientVectorMap,
    traceCoefficientDerivativeVectorMap, ContinuousMap.comp_apply, ContinuousMap.prod_eval,
    ContinuousMap.coe_mk, hsum] at h
  change (∫ e, m e * inner ℝ
      (matrixVector (traceCoefficient (plusWeyl g e.base e.frame)))
      (matrixVector (hessianTrace (plusWeylHessian g e.base e.frame))) +
      ∑ i, dm i e * inner ℝ
        (matrixVector (traceCoefficient (plusWeyl g e.base e.frame)))
        (matrixVector (plusWeylGradient g e.base e.frame i)) ∂μ) =
    -(∫ e, m e * ∑ i, inner ℝ
      (matrixVector (traceCoefficientDerivative (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i)))
      (matrixVector (plusWeylGradient g e.base e.frame i)) ∂μ) at h
  simp only [inner_matrixVector] at h
  rw [h]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Match the opposite-block Hessian quadratic with the same covector
ordering used by the actual curvature Green identity. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

theorem oppositeMatrix_eq_neg_rightQuaternion (s : Fin 3) (i j : Fin 4) :
    Angular.oppositeMatrix s i j = -rightQuaternion s i j := by
  fin_cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [Angular.oppositeMatrix, oppositeQuaternion, quaternionMatrix, rightQuaternion]

private theorem sum_four_two_swap
    (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 3 → Fin 3 → ℝ) :
    (∑ i, ∑ k, ∑ j, ∑ l, ∑ a, ∑ b, f i k j l a b) =
      ∑ a, ∑ b, ∑ i, ∑ k, ∑ j, ∑ l, f i k j l a b := by
  have h := (Equiv.prodComm ((Fin 4 × Fin 4) × (Fin 4 × Fin 4))
    (Fin 3 × Fin 3)).sum_comp
      (fun p => f p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2 p.1.1 p.1.2)
  simpa only [Fintype.sum_prod_type, Equiv.prodComm_apply, Prod.swap_prod_mk] using h

private theorem rightDerivativeSlotForm_matrix (s : Fin 3) (X : Hessian) :
    (∑ i, ∑ k, ∑ j, ∑ l, rightQuaternion s i k * rightQuaternion s j l *
      matrixPairing (X i j) (X k l)) = rightDerivativeSlotForm s X := by
  simp only [matrixPairing, Finset.mul_sum]
  rw [sum_four_two_swap]
  unfold rightDerivativeSlotForm
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem minusDerivativeCurvatureForm_eq_derivativePairing
    (u : Fin 3 → ℝ) (X : Hessian) :
    minusDerivativeCurvatureForm u X = derivativePairing (minusCoefficient u) X X := by
  unfold derivativePairing minusCoefficient blockCoefficient
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (f := fun p : Averages.CurvatureIndex => _)]
  unfold minusDerivativeCurvatureForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Fintype.sum_prod_type, oppositeMatrix_eq_neg_rightQuaternion]
  have h := rightDerivativeSlotForm_matrix s X
  calc
    (1 / 2 : ℝ) * (u s * rightDerivativeSlotForm s X) =
        (1 / 2 : ℝ) * u s *
          (∑ i, ∑ k, ∑ j, ∑ l, rightQuaternion s i k * rightQuaternion s j l *
            matrixPairing (X i j) (X k l)) := by rw [h]; ring
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      ring

theorem weightedQuadratic_minus_green (u : Fin 3 → ℝ)
    (m : ℝ) (X : Hessian) (a : Vec) (Z : Tensor) :
    weightedQuadratic (minusDerivativeCurvatureForm u) m X (weightTensor a Z) =
      (∑ p : Averages.CurvatureIndex,
        (m * minusCoefficient u p.1.1 p.1.2 p.2.1 p.2.2 *
          matrixPairing (X p.1.1 p.2.1) (X p.1.2 p.2.2) +
          a p.1.2 * minusCoefficient u p.1.1 p.1.2 p.2.1 p.2.2 *
            matrixPairing (X p.1.1 p.2.1) (rawMatrixSlice Z.matrix p.2.2))) / 6 := by
  have hform : minusDerivativeCurvatureForm u =
      fun W => derivativePairing (minusCoefficient u) W W := by
    funext W
    exact minusDerivativeCurvatureForm_eq_derivativePairing u W
  rw [hform]
  apply weightedQuadratic_derivative_green
  exact blockCoefficient_pair_swap Angular.oppositeMatrix
    (fun s i j => by
      rw [oppositeMatrix_eq_neg_rightQuaternion,
        oppositeMatrix_eq_neg_rightQuaternion, rightQuaternion_skew s j i]) u

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! Differentiate the actual normalized Weyl norm on its positive set. -/

namespace PositiveEinsteinFour.Geometry

open Matrix TraceHessian
open scoped BigOperators

noncomputable section

local instance weylNormNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance weylNormNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance weylNormNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

theorem trace_square_eq_six_norm_sq (A : Mat) (hA : symmetric A) :
    Matrix.trace (A * A) = 6 * normalizedBlockNorm A ^ 2 := by
  rw [normalizedBlockNorm_sq]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  have hsum : (∑ i, ∑ j, A i j * A j i) = ∑ i, ∑ j, A i j ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hA j i, pow_two]
  rw [hsum]
  ring

theorem normalizedBlockNorm_eq_sqrt_trace (A : Mat) (hA : symmetric A) :
    normalizedBlockNorm A = Real.sqrt (Matrix.trace (A * A) / 6) := by
  rw [trace_square_eq_six_norm_sq A hA]
  have hcancel : 6 * normalizedBlockNorm A ^ 2 / 6 = normalizedBlockNorm A ^ 2 := by ring
  rw [hcancel, Real.sqrt_sq (normalizedBlockNorm_nonneg A)]

theorem hasDerivAt_normalizedBlockNorm {A : ℝ → Mat} {Z : Mat} {r : ℝ}
    (hA : HasDerivAt A Z r) (hs : ∀ t, symmetric (A t))
    (hv : 0 < normalizedBlockNorm (A r)) :
    HasDerivAt (fun t => normalizedBlockNorm (A t))
      (Matrix.trace (A r * Z) / (6 * normalizedBlockNorm (A r))) r := by
  have hd := (hasDerivAt_matrixTrace (hA.mul hA)).div_const 6
  have hn : Matrix.trace (A r * A r) / 6 ≠ 0 := by
    rw [trace_square_eq_six_norm_sq _ (hs r)]
    positivity
  have hroot := hd.sqrt hn
  change HasDerivAt (fun t => Real.sqrt (Matrix.trace (A t * A t) / 6))
    (Matrix.trace (Z * A r + A r * Z) / 6 /
      (2 * Real.sqrt (Matrix.trace (A r * A r) / 6))) r at hroot
  have heq : (fun t => Real.sqrt (Matrix.trace (A t * A t) / 6)) =
      fun t => normalizedBlockNorm (A t) := by
    funext t
    exact (normalizedBlockNorm_eq_sqrt_trace _ (hs t)).symm
  rw [heq] at hroot
  convert! hroot using 1
  rw [Matrix.trace_add, Matrix.trace_mul_comm Z (A r),
    ← normalizedBlockNorm_eq_sqrt_trace _ (hs r)]
  ring

/-- The radial coefficient needed by the trace Green formula is forced
by the derivative of the actual norm, rather than supplied independently. -/
theorem matrixPairing_eq_radial_derivative {A : ℝ → Mat} {Z : Mat} {r p : ℝ}
    (hA : HasDerivAt A Z r) (hs : ∀ t, symmetric (A t)) (hZ : symmetric Z)
    (hv : 0 < normalizedBlockNorm (A r))
    (hp : HasDerivAt (fun t => normalizedBlockNorm (A t)) p r) :
    matrixPairing (A r) Z = 6 * normalizedBlockNorm (A r) * p := by
  have h := hp.unique (hasDerivAt_normalizedBlockNorm hA hs hv)
  have hzt : Zᵀ = Z := by ext i j; exact hZ j i
  rw [matrixPairing_eq_trace, hzt]
  have hne : 6 * normalizedBlockNorm (A r) ≠ 0 := by positivity
  exact (eq_div_iff hne).mp h |>.symm.trans (mul_comm p _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Ricci commutation before any pointwise spectral decomposition. All
matrix and derivative slots stay in the same arbitrary orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

/-- The uncompressed Ricci right side in an arbitrary frame. The first
coefficient is `6 + 3`; the remaining two terms are the differentiated
matrix equation and the full bundle curvature contribution. -/
def invariantRicciGradient (A : Mat) (Z : Angular.Gradient) : Angular.Gradient :=
  fun j => (9 : ℝ) • Z j - (12 : ℝ) • matrixSlotAction A (Z j) +
    (2 : ℝ) • ∑ i, bundleCurvatureAction A i j (Z i)

theorem third_laplacian_eq_invariantRicciGradient
    (A : Mat) (Z : Angular.Gradient)
    (D V : Fin 4 → Fin 4 → Fin 4 → Mat)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hinner : ∀ i k j, D i k j - D i j k =
      V i k j + bundleCurvatureAction A k j (Z i))
    (houter : ∀ i k j, D i k j - D k i j =
      bundleCurvatureAction A i k (Z j) + ∑ a, R i k j a • Z a)
    (hdiv : ∀ j, (∑ i, V i i j) = 0)
    (hRic : ∀ j a, (∑ i, R i j i a) = if j = a then 3 else 0)
    (htrace : ∀ j, (∑ i, D j i i) =
      (6 : ℝ) • Z j - (12 : ℝ) • matrixSlotAction A (Z j)) :
    (fun j => ∑ i, D i i j) = invariantRicciGradient A Z := by
  funext j
  ext a b
  have hi (i : Fin 4) : D i i j a b = D j i i a b + V i i j a b +
      2 * bundleCurvatureAction A i j (Z i) a b +
        ∑ k, R i j i k * Z k a b := by
    have h1 := congrArg (fun N : Mat => N a b) (hinner i i j)
    have h2 := congrArg (fun N : Mat => N a b) (houter i j i)
    simp only [Matrix.sub_apply, Matrix.add_apply] at h1
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul] at h2
    linarith
  have hv := congrArg (fun N : Mat => N a b) (hdiv j)
  have ht := congrArg (fun N : Mat => N a b) (htrace j)
  simp only [Matrix.sum_apply, Matrix.zero_apply] at hv
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul] at ht
  have hr : (∑ i, ∑ k, R i j i k * Z k a b) = 3 * Z j a b := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hRic, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [Matrix.sum_apply, hi, Finset.sum_add_distrib, ← Finset.mul_sum,
    invariantRicciGradient, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [hv, hr, ht]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The actual Ricci equation uses just the ordinary covariant slot
identities and parallel differentiation. In particular it has no choice
of eigenframe among its hypotheses. -/
theorem metric_invariant_ricci_gradient
    (g : SmoothMetric M) (h : WeylCovariantIdentities g)
    {μ : Measure (FrameBundle g)} (φ : Fin 4 → FrameFlow g μ)
    (hT : ∀ k r e, HasDerivAt
      (fun s => plusWeyl g ((φ k).map s e).base ((φ k).map s e).frame)
      (plusWeylGradient g ((φ k).map r e).base ((φ k).map r e).frame k) r)
    (hX : ∀ k i r e, HasDerivAt
      (fun s => plusWeylHessian g ((φ k).map s e).base ((φ k).map s e).frame i i)
      (plusWeylThirdDerivative g ((φ k).map r e).base ((φ k).map r e).frame k i i) r)
    (e : FrameBundle g) (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hb : ∀ r i, gradientDivergence (plusWeylGradient g e.base e.frame) r i = 0)
    (hinner : ∀ i k j,
      plusWeylThirdDerivative g e.base e.frame i k j -
        plusWeylThirdDerivative g e.base e.frame i j k =
      bundleCurvatureDerivative (plusWeylGradient g e.base e.frame i) k j
        (plusWeyl g e.base e.frame) +
      bundleCurvatureAction (plusWeyl g e.base e.frame) k j
        (plusWeylGradient g e.base e.frame i))
    (houter : ∀ i k j,
      plusWeylThirdDerivative g e.base e.frame i k j -
        plusWeylThirdDerivative g e.base e.frame k i j =
      bundleCurvatureAction (plusWeyl g e.base e.frame) i k
        (plusWeylGradient g e.base e.frame j) +
      ∑ a, R i k j a • plusWeylGradient g e.base e.frame a)
    (hRic : ∀ j a, (∑ i, R i j i a) = if j = a then 3 else 0) :
    (fun j => ∑ i, plusWeylThirdDerivative g e.base e.frame i i j) =
      invariantRicciGradient (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) := by
  apply third_laplacian_eq_invariantRicciGradient _ _ _
    (fun i k j => bundleCurvatureDerivative (plusWeylGradient g e.base e.frame i)
      k j (plusWeyl g e.base e.frame)) R hinner houter
  · intro j
    exact bundleCurvatureDerivative_divergence _ hb j _
  · exact hRic
  · exact fun j => metric_weyl_third_trace g h φ hT hX j e

/-- Conversion to the Euclidean vector used in the actual Green formula. -/
theorem frameGradientLaplacian_of_invariant_ricci
    (g : SmoothMetric M) (e : FrameBundle g)
    (hraw : (fun j => ∑ i, plusWeylThirdDerivative g e.base e.frame i i j) =
      invariantRicciGradient (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame)) :
    frameGradientLaplacian g e = gradientVector
      (invariantRicciGradient (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame)) := by
  rw [← hraw]
  ext p
  rcases p with ⟨j, a, b⟩
  simp only [frameGradientLaplacian, frameThirdVector, gradientVector,
    WithLp.ofLp_sum, Finset.sum_apply, Matrix.sum_apply]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth norm regularization for the actual squared Weyl weight.
The positive regularization parameter allows the Green identities to be
used at Weyl zeros as well as on the positive-norm set. -/

namespace PositiveEinsteinFour.Geometry

open Matrix TraceHessian Filter
open scoped Topology

noncomputable section

local instance smoothWeylNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance smoothWeylNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance smoothWeylNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

def regularizedBlockNorm (ε : ℝ) (A : Mat) : ℝ :=
  Real.sqrt (normalizedBlockNorm A ^ 2 + ε ^ 2)

def regularizedRadialDerivative (ε : ℝ) (A Z : Mat) : ℝ :=
  Matrix.trace (A * Z) / (6 * regularizedBlockNorm ε A)

def regularizedWeylWeight (ε : ℝ) (A B : Mat) : ℝ :=
  (1 - (3 / 8 : ℝ) * (regularizedBlockNorm ε A - regularizedBlockNorm ε B)) ^ 2

def regularizedWeylWeightDerivative (ε : ℝ) (A B Z V : Mat) : ℝ :=
  -(3 / 4 : ℝ) *
    (1 - (3 / 8 : ℝ) * (regularizedBlockNorm ε A - regularizedBlockNorm ε B)) *
    (regularizedRadialDerivative ε A Z - regularizedRadialDerivative ε B V)

theorem regularizedWeylWeightDerivative_add (ε : ℝ) (A B Z₁ Z₂ V₁ V₂ : Mat) :
    regularizedWeylWeightDerivative ε A B (Z₁ + Z₂) (V₁ + V₂) =
      regularizedWeylWeightDerivative ε A B Z₁ V₁ +
        regularizedWeylWeightDerivative ε A B Z₂ V₂ := by
  simp only [regularizedWeylWeightDerivative, regularizedRadialDerivative,
    mul_add, Matrix.trace_add, add_div]
  ring

/-- Mixed entries of the quadratic cost reduce to the diagonal costs of
two directions and their sum, which suffices for the integral limit. -/
theorem regularized_weight_cost_polarization (ε : ℝ) (A B Z₁ Z₂ V₁ V₂ : Mat) :
    2 * regularizedWeylWeightDerivative ε A B Z₁ V₁ *
        regularizedWeylWeightDerivative ε A B Z₂ V₂ / regularizedWeylWeight ε A B =
      (regularizedWeylWeightDerivative ε A B (Z₁ + Z₂) (V₁ + V₂) ^ 2 -
        regularizedWeylWeightDerivative ε A B Z₁ V₁ ^ 2 -
        regularizedWeylWeightDerivative ε A B Z₂ V₂ ^ 2) / regularizedWeylWeight ε A B := by
  rw [regularizedWeylWeightDerivative_add]
  ring

theorem regularizedBlockNorm_zero (A : Mat) :
    regularizedBlockNorm 0 A = normalizedBlockNorm A := by
  simp [regularizedBlockNorm, Real.sqrt_sq (normalizedBlockNorm_nonneg A)]

theorem regularizedBlockNorm_pos (ε : ℝ) (hε : 0 < ε) (A : Mat) :
    0 < regularizedBlockNorm ε A := by
  unfold regularizedBlockNorm
  positivity

theorem norm_le_regularizedBlockNorm (ε : ℝ) (A : Mat) :
    normalizedBlockNorm A ≤ regularizedBlockNorm ε A := by
  unfold regularizedBlockNorm
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg ε]

theorem regularizedBlockNorm_le (ε : ℝ) (hε : 0 ≤ ε) (A : Mat) :
    regularizedBlockNorm ε A ≤ normalizedBlockNorm A + ε := by
  rw [regularizedBlockNorm, Real.sqrt_le_left (add_nonneg (normalizedBlockNorm_nonneg A) hε)]
  nlinarith [normalizedBlockNorm_nonneg A]

theorem continuous_regularizedBlockNorm (ε : ℝ) :
    Continuous (regularizedBlockNorm ε) := by
  unfold regularizedBlockNorm normalizedBlockNorm
  fun_prop

theorem continuous_normalizedBlockNorm : Continuous normalizedBlockNorm := by
  have heq : regularizedBlockNorm 0 = normalizedBlockNorm :=
    funext regularizedBlockNorm_zero
  rw [← heq]
  exact continuous_regularizedBlockNorm 0

theorem tendsto_regularizedBlockNorm (A : Mat) :
    Tendsto (fun ε => regularizedBlockNorm ε A) (𝓝 0) (𝓝 (normalizedBlockNorm A)) := by
  have hc : Continuous (fun ε => regularizedBlockNorm ε A) := by
    unfold regularizedBlockNorm
    fun_prop
  simpa only [regularizedBlockNorm_zero] using hc.tendsto 0

theorem tendsto_regularizedRadialDerivative (A Z : Mat) :
    Tendsto (fun ε => regularizedRadialDerivative ε A Z) (𝓝 0)
      (𝓝 (Matrix.trace (A * Z) / (6 * normalizedBlockNorm A))) := by
  by_cases ha : normalizedBlockNorm A = 0
  · have hA : A = 0 := (normalizedBlockNorm_eq_zero_iff A).mp ha
    subst A
    simp [regularizedRadialDerivative]
  · exact tendsto_const_nhds.div
      (tendsto_const_nhds.mul (tendsto_regularizedBlockNorm A))
      (mul_ne_zero (by norm_num) ha)

theorem tendsto_regularizedWeylWeight (A B : Mat) :
    Tendsto (fun ε => regularizedWeylWeight ε A B) (𝓝 0)
      (𝓝 ((1 - (3 / 8 : ℝ) * (normalizedBlockNorm A - normalizedBlockNorm B)) ^ 2)) := by
  exact (tendsto_const_nhds.sub (tendsto_const_nhds.mul
    ((tendsto_regularizedBlockNorm A).sub (tendsto_regularizedBlockNorm B)))).pow 2

theorem tendsto_regularizedWeylWeightDerivative (A B Z V : Mat) :
    Tendsto (fun ε => regularizedWeylWeightDerivative ε A B Z V) (𝓝 0)
      (𝓝 (-(3 / 4 : ℝ) *
        (1 - (3 / 8 : ℝ) * (normalizedBlockNorm A - normalizedBlockNorm B)) *
        (Matrix.trace (A * Z) / (6 * normalizedBlockNorm A) -
          Matrix.trace (B * V) / (6 * normalizedBlockNorm B)))) := by
  exact (tendsto_const_nhds.mul (tendsto_const_nhds.sub (tendsto_const_nhds.mul
    ((tendsto_regularizedBlockNorm A).sub (tendsto_regularizedBlockNorm B))))).mul
      ((tendsto_regularizedRadialDerivative A Z).sub
        (tendsto_regularizedRadialDerivative B V))

theorem continuous_regularizedRadialDerivative {Ω : Type*} [TopologicalSpace Ω]
    (ε : ℝ) (hε : 0 < ε) (A Z : Ω → Mat) (hA : Continuous A) (hZ : Continuous Z) :
    Continuous (fun x => regularizedRadialDerivative ε (A x) (Z x)) := by
  have ht : Continuous (fun x => Matrix.trace (A x * Z x)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    fun_prop
  exact ht.div (continuous_const.mul ((continuous_regularizedBlockNorm ε).comp hA))
    (fun x => ne_of_gt (mul_pos (by norm_num) (regularizedBlockNorm_pos ε hε (A x))))

theorem continuous_regularizedWeylWeight {Ω : Type*} [TopologicalSpace Ω]
    (ε : ℝ) (A B : Ω → Mat) (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun x => regularizedWeylWeight ε (A x) (B x)) := by
  exact (continuous_const.sub (continuous_const.mul
    (((continuous_regularizedBlockNorm ε).comp hA).sub
      ((continuous_regularizedBlockNorm ε).comp hB)))).pow 2

theorem continuous_regularizedWeylWeightDerivative {Ω : Type*} [TopologicalSpace Ω]
    (ε : ℝ) (hε : 0 < ε) (A B Z V : Ω → Mat)
    (hA : Continuous A) (hB : Continuous B) (hZ : Continuous Z) (hV : Continuous V) :
    Continuous (fun x => regularizedWeylWeightDerivative ε (A x) (B x) (Z x) (V x)) := by
  exact (continuous_const.mul (continuous_const.sub (continuous_const.mul
    (((continuous_regularizedBlockNorm ε).comp hA).sub
      ((continuous_regularizedBlockNorm ε).comp hB))))).mul
        ((continuous_regularizedRadialDerivative ε hε A Z hA hZ).sub
          (continuous_regularizedRadialDerivative ε hε B V hB hV))

theorem hasDerivAt_regularizedBlockNorm {A : ℝ → Mat} {Z : Mat} {r ε : ℝ}
    (hA : HasDerivAt A Z r) (hs : ∀ t, symmetric (A t)) (hε : 0 < ε) :
    HasDerivAt (fun t => regularizedBlockNorm ε (A t))
      (regularizedRadialDerivative ε (A r) Z) r := by
  have hd := ((hasDerivAt_matrixTrace (hA.mul hA)).div_const 6).add_const (ε ^ 2)
  have hn : Matrix.trace (A r * A r) / 6 + ε ^ 2 ≠ 0 := by
    rw [trace_square_eq_six_norm_sq _ (hs r)]
    positivity
  have hroot := hd.sqrt hn
  change HasDerivAt (fun t => Real.sqrt (Matrix.trace (A t * A t) / 6 + ε ^ 2))
    (Matrix.trace (Z * A r + A r * Z) / 6 /
      (2 * Real.sqrt (Matrix.trace (A r * A r) / 6 + ε ^ 2))) r at hroot
  have heq : (fun t => Real.sqrt (Matrix.trace (A t * A t) / 6 + ε ^ 2)) =
      fun t => regularizedBlockNorm ε (A t) := by
    funext t
    unfold regularizedBlockNorm
    rw [trace_square_eq_six_norm_sq _ (hs t)]
    congr 2
    ring
  rw [heq] at hroot
  convert! hroot using 1
  unfold regularizedRadialDerivative regularizedBlockNorm
  rw [Matrix.trace_add, Matrix.trace_mul_comm Z (A r),
    trace_square_eq_six_norm_sq _ (hs r)]
  ring_nf

theorem hasDerivAt_regularizedWeylWeight {A B : ℝ → Mat} {Z V : Mat} {r ε : ℝ}
    (hA : HasDerivAt A Z r) (hB : HasDerivAt B V r)
    (hsA : ∀ t, symmetric (A t)) (hsB : ∀ t, symmetric (B t)) (hε : 0 < ε) :
    HasDerivAt (fun t => regularizedWeylWeight ε (A t) (B t))
      (regularizedWeylWeightDerivative ε (A r) (B r) Z V) r := by
  have h := ((hasDerivAt_const r (1 : ℝ)).sub
    (((hasDerivAt_regularizedBlockNorm hA hsA hε).sub
      (hasDerivAt_regularizedBlockNorm hB hsB hε)).const_mul (3 / 8 : ℝ))).pow 2
  convert! h using 1
  unfold regularizedWeylWeightDerivative
  simp only [Pi.sub_apply]
  ring

theorem regularized_weight_factor_lower (ε : ℝ) (hε : 0 ≤ ε) (he : ε ≤ 1 / 3)
    (A B : Mat) (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    1 / 8 < 1 - (3 / 8 : ℝ) * (regularizedBlockNorm ε A - regularizedBlockNorm ε B) := by
  have ha := regularizedBlockNorm_le ε hε A
  have hb := Real.sqrt_nonneg (normalizedBlockNorm B ^ 2 + ε ^ 2)
  have hnb := normalizedBlockNorm_nonneg B
  change 0 ≤ regularizedBlockNorm ε B at hb
  nlinarith

theorem regularizedWeylWeight_pos (ε : ℝ) (hε : 0 ≤ ε) (he : ε ≤ 1 / 3)
    (A B : Mat) (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    0 < regularizedWeylWeight ε A B := by
  have h := regularized_weight_factor_lower ε hε he A B hpinch
  unfold regularizedWeylWeight
  exact sq_pos_of_pos (by linarith)

theorem matrixPairing_self_norm (A : Mat) :
    matrixPairing A A = 6 * normalizedBlockNorm A ^ 2 := by
  rw [normalizedBlockNorm_sq]
  simp only [matrixPairing, pow_two]
  ring

theorem abs_trace_mul_le_norm (A Z : Mat) (hZ : symmetric Z) :
    |Matrix.trace (A * Z)| ≤ 6 * normalizedBlockNorm A * normalizedBlockNorm Z := by
  have hzt : Zᵀ = Z := by ext i j; exact hZ j i
  have hp : matrixPairing A Z = Matrix.trace (A * Z) := by
    rw [matrixPairing_eq_trace, hzt]
  have h := real_inner_mul_inner_self_le (matrixVector A) (matrixVector Z)
  simp only [inner_matrixVector, matrixPairing_self_norm, hp] at h
  apply abs_le_of_sq_le_sq _
    (mul_nonneg (mul_nonneg (by norm_num) (normalizedBlockNorm_nonneg A))
      (normalizedBlockNorm_nonneg Z))
  nlinarith only [h]

/-- The regularized derivative has a bound independent of the smoothing
parameter. This is the domination needed at Weyl zeros. -/
theorem abs_regularizedRadialDerivative_le (ε : ℝ) (hε : 0 < ε)
    (A Z : Mat) (hZ : symmetric Z) :
    |regularizedRadialDerivative ε A Z| ≤ normalizedBlockNorm Z := by
  have hn := regularizedBlockNorm_pos ε hε A
  rw [regularizedRadialDerivative, abs_div, abs_of_pos (mul_pos (by norm_num) hn),
    div_le_iff₀ (mul_pos (by norm_num) hn)]
  calc
    _ ≤ 6 * normalizedBlockNorm A * normalizedBlockNorm Z := abs_trace_mul_le_norm A Z hZ
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (norm_le_regularizedBlockNorm ε A)
        (normalizedBlockNorm_nonneg Z)
      nlinarith only [h]

theorem regularized_weight_factor_upper (ε : ℝ) (hε : 0 ≤ ε) (he : ε ≤ 1 / 3)
    (A B : Mat) (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    1 - (3 / 8 : ℝ) * (regularizedBlockNorm ε A - regularizedBlockNorm ε B) < 2 := by
  have hb := regularizedBlockNorm_le ε hε B
  have ha := Real.sqrt_nonneg (normalizedBlockNorm A ^ 2 + ε ^ 2)
  have hna := normalizedBlockNorm_nonneg A
  change 0 ≤ regularizedBlockNorm ε A at ha
  nlinarith

theorem regularizedWeylWeight_bounds (ε : ℝ) (hε : 0 ≤ ε) (he : ε ≤ 1 / 3)
    (A B : Mat) (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    1 / 64 ≤ regularizedWeylWeight ε A B ∧ regularizedWeylWeight ε A B ≤ 4 := by
  have hlo := regularized_weight_factor_lower ε hε he A B hpinch
  have hhi := regularized_weight_factor_upper ε hε he A B hpinch
  unfold regularizedWeylWeight
  constructor <;> nlinarith

theorem abs_regularizedWeylWeightDerivative_le (ε : ℝ) (hε : 0 < ε) (he : ε ≤ 1 / 3)
    (A B Z V : Mat) (hZ : symmetric Z) (hV : symmetric V)
    (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    |regularizedWeylWeightDerivative ε A B Z V| ≤
      (3 / 2 : ℝ) * (normalizedBlockNorm Z + normalizedBlockNorm V) := by
  have hlo := regularized_weight_factor_lower ε hε.le he A B hpinch
  have hhi := regularized_weight_factor_upper ε hε.le he A B hpinch
  have habs : |1 - (3 / 8 : ℝ) *
      (regularizedBlockNorm ε A - regularizedBlockNorm ε B)| ≤ 2 := by
    rw [abs_of_pos (by linarith)]
    exact hhi.le
  have hrad : |regularizedRadialDerivative ε A Z - regularizedRadialDerivative ε B V| ≤
      normalizedBlockNorm Z + normalizedBlockNorm V :=
    (abs_sub _ _).trans (add_le_add (abs_regularizedRadialDerivative_le ε hε A Z hZ)
      (abs_regularizedRadialDerivative_le ε hε B V hV))
  unfold regularizedWeylWeightDerivative
  rw [abs_mul, abs_mul]
  norm_num only [abs_neg, abs_div]
  calc
    _ ≤ (3 / 4 : ℝ) * 2 * (normalizedBlockNorm Z + normalizedBlockNorm V) := by
      gcongr
    _ = _ := by ring

theorem regularized_weight_cost_le (ε : ℝ) (hε : 0 < ε) (he : ε ≤ 1 / 3)
    (A B Z V : Mat) (hZ : symmetric Z) (hV : symmetric V)
    (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    regularizedWeylWeightDerivative ε A B Z V ^ 2 / regularizedWeylWeight ε A B ≤
      144 * (normalizedBlockNorm Z + normalizedBlockNorm V) ^ 2 := by
  have hd := abs_regularizedWeylWeightDerivative_le ε hε he A B Z V hZ hV hpinch
  have hsum : 0 ≤ normalizedBlockNorm Z + normalizedBlockNorm V :=
    add_nonneg (normalizedBlockNorm_nonneg Z) (normalizedBlockNorm_nonneg V)
  have hd2 := (sq_le_sq₀ (abs_nonneg (regularizedWeylWeightDerivative ε A B Z V))
    (mul_nonneg (by norm_num) hsum)).2 hd
  rw [sq_abs] at hd2
  have hm := mul_le_mul_of_nonneg_left
    (regularizedWeylWeight_bounds ε hε.le he A B hpinch).1
    (show 0 ≤ 144 * (normalizedBlockNorm Z + normalizedBlockNorm V) ^ 2 by positivity)
  rw [div_le_iff₀ (regularizedWeylWeight_pos ε hε.le he A B hpinch)]
  nlinarith only [hd2, hm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A pointwise spectral basis in the positive Weyl block lifts to an
orientation-preserving orthogonal change in four dimensions. The harmless
common sign in the three-dimensional basis cancels from matrix conjugation. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

abbrev ThreeSpace := EuclideanSpace ℝ (Fin 3)

/-- Matrix of a three-dimensional orthogonal change in the fixed Euclidean basis. -/
def frameMatrix (φ : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) : Mat :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis φ.toLinearMap

@[simp] theorem frameMatrix_one : frameMatrix (1 : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) = 1 := by
  exact LinearMap.toMatrix_one _

theorem frameMatrix_mul (φ ψ : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) :
    frameMatrix (φ * ψ) = frameMatrix φ * frameMatrix ψ := by
  exact LinearMap.toMatrix_mul _ φ.toLinearMap ψ.toLinearMap

theorem frameMatrix_apply (φ : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) (i j : Fin 3) :
    frameMatrix φ i j = φ ((EuclideanSpace.basisFun (Fin 3) ℝ) j) i := by
  simp only [frameMatrix, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  rfl

theorem frameMatrix_orthogonal (φ : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) :
    (frameMatrix φ)ᵀ * frameMatrix φ = 1 := by
  ext i j
  have h := φ.inner_map_map ((EuclideanSpace.basisFun (Fin 3) ℝ) j)
    ((EuclideanSpace.basisFun (Fin 3) ℝ) i)
  rw [EuclideanSpace.basisFun_inner] at h
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, frameMatrix_apply,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    EuclideanSpace.basisFun_apply, PiLp.single_apply, Matrix.one_apply, eq_comm] using h

theorem frameMatrix_axisReflection (u : ThreeSpace) (hu : ‖u‖ = 1) :
    frameMatrix (Submodule.reflection (ℝ ∙ u)) = axisReflection u := by
  ext i j
  rw [frameMatrix_apply]
  have h := congrArg (fun x : ThreeSpace => x i)
    (axisReflection_apply u ((EuclideanSpace.basisFun (Fin 3) ℝ) j) hu)
  simpa [Matrix.mulVec, dotProduct] using h.symm

theorem frameMatrix_orthogonalReflection (u : ThreeSpace) (hu : ‖u‖ = 1) :
    frameMatrix (Submodule.reflection (ℝ ∙ u)ᗮ) = -axisReflection u := by
  ext i j
  rw [frameMatrix_apply, Submodule.reflection_orthogonal_apply]
  change -Submodule.reflection (ℝ ∙ u) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) i = _
  rw [← frameMatrix_apply, frameMatrix_axisReflection u hu]
  rfl

private theorem normalized_span (v : ThreeSpace) (hv : v ≠ 0) :
    (ℝ ∙ ((‖v‖⁻¹ : ℝ) • v)) = ℝ ∙ v := by
  exact Submodule.span_singleton_smul_eq
    (isUnit_iff_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr hv))) v

/-- Each reflection used by Cartan--Dieudonné has a concrete quaternion
lift after multiplying its three-dimensional matrix by a common sign. -/
theorem reflection_has_signed_lift (v : ThreeSpace) :
    ∃ c : ℝ, c ^ 2 = 1 ∧ Nonempty
      (QuaternionLift quaternionMatrix Angular.oppositeMatrix
        (c • frameMatrix (Submodule.reflection (ℝ ∙ v)ᗮ))) := by
  by_cases hv : v = 0
  · subst v
    refine ⟨1, by norm_num, ?_⟩
    have htop : Submodule.reflection (⊤ : Submodule ℝ ThreeSpace) = 1 := by
      ext x : 1
      exact Submodule.reflection_mem_subspace_eq_self
        (K := (⊤ : Submodule ℝ ThreeSpace)) (show x ∈ (⊤ : Submodule ℝ ThreeSpace) by trivial)
    simpa only [Submodule.span_zero_singleton, Submodule.bot_orthogonal_eq_top,
      htop, frameMatrix_one, one_smul] using
        (show Nonempty (QuaternionLift quaternionMatrix Angular.oppositeMatrix (1 : Mat)) from
          ⟨QuaternionLift.one _ _⟩)
  · let u : ThreeSpace := (‖v‖⁻¹ : ℝ) • v
    have hu : ‖u‖ = 1 := norm_smul_inv_norm hv
    have hus : (ℝ ∙ u) = ℝ ∙ v := normalized_span v hv
    have huq : ∑ r, u r ^ 2 = 1 := by
      simpa only [hu, one_pow] using (EuclideanSpace.real_norm_sq_eq u).symm
    refine ⟨-1, by norm_num, ?_⟩
    have hf : frameMatrix (Submodule.reflection (ℝ ∙ v)ᗮ) = -axisReflection u := by
      simpa only [hus] using frameMatrix_orthogonalReflection u hu
    have hm : (-1 : ℝ) • frameMatrix (Submodule.reflection (ℝ ∙ v)ᗮ) =
        axisReflection u := by
      rw [hf, neg_one_smul, neg_neg]
    rw [hm]
    exact ⟨QuaternionLift.leftAxis u huq⟩

private theorem signed_matrix_mul (c d : ℝ) (A B : Mat) :
    (c • A) * (d • B) = (c * d) • (A * B) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

private theorem reflection_list_has_signed_lift (l : List ThreeSpace) :
    ∃ c : ℝ, c ^ 2 = 1 ∧ Nonempty
      (QuaternionLift quaternionMatrix Angular.oppositeMatrix
        (c • frameMatrix (l.map fun v => Submodule.reflection (ℝ ∙ v)ᗮ).prod)) := by
  induction l with
  | nil =>
      refine ⟨1, by norm_num, ?_⟩
      simpa only [List.map_nil, List.prod_nil, frameMatrix_one, one_smul] using
        (show Nonempty (QuaternionLift quaternionMatrix Angular.oppositeMatrix (1 : Mat)) from
          ⟨QuaternionLift.one _ _⟩)
  | cons v l ih =>
      obtain ⟨c, hc, ⟨P⟩⟩ := reflection_has_signed_lift v
      obtain ⟨d, hd, ⟨R⟩⟩ := ih
      refine ⟨c * d, by rw [mul_pow, hc, hd, one_mul], ?_⟩
      have h := P.mul R
      rw [signed_matrix_mul, ← frameMatrix_mul] at h
      simpa only [List.map_cons, List.prod_cons] using
        (show Nonempty _ from ⟨h⟩)

/-- Every orthogonal spectral basis admits the required oriented four-frame
lift. The common sign disappears from conjugation of the Weyl matrix. -/
theorem exists_signed_left_lift (φ : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) :
    ∃ c : ℝ, c ^ 2 = 1 ∧ Nonempty
      (QuaternionLift quaternionMatrix Angular.oppositeMatrix (c • frameMatrix φ)) := by
  obtain ⟨l, _, hφ⟩ := φ.reflections_generate_dim
  rw [hφ]
  exact reflection_list_has_signed_lift l

/-- The harmless sign in the lifted three-dimensional basis cancels from
both matrix slots, exactly as needed for diagonalization. -/
theorem signed_conjugation (c : ℝ) (hc : c ^ 2 = 1) (R A : Mat) :
    (c • R)ᵀ * A * (c • R) = Rᵀ * A * R := by
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  simp only [← pow_two, hc, one_smul]


private theorem matrix_spectral_square (A : Mat) (hA : A.IsHermitian) :
    (∑ i, hA.eigenvalues i ^ 2) = Matrix.trace (A * A) := by
  let V := hA.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ Mat (star V)
  have hd : φ A = Matrix.diagonal hA.eigenvalues := by
    simpa only [φ, V, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  have htrace (B : Mat) : Matrix.trace (φ B) = Matrix.trace B := by
    rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, Matrix.one_mul]
  calc
    _ = Matrix.trace (Matrix.diagonal hA.eigenvalues *
        Matrix.diagonal hA.eigenvalues) := by
      simp [Matrix.diagonal_mul_diagonal, pow_two]
    _ = Matrix.trace (φ (A * A)) := by rw [map_mul, hd]
    _ = Matrix.trace (A * A) := htrace _

/-- A nonzero symmetric trace-free Weyl block has the paper's normalized
shape in an actual orthogonal eigenbasis. -/
theorem exists_spectral_shape (A : Mat) (hA : symmetric A) (ht : traceFree A)
    (hv : 0 < normalizedBlockNorm A) :
    ∃ φ : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace, ∃ S : Shape,
      (frameMatrix φ)ᵀ * A * frameMatrix φ =
        Matrix.diagonal (fun i => normalizedBlockNorm A * S.s i) := by
  have hherm : A.IsHermitian := by
    ext i j
    exact hA j i
  let φ := (EuclideanSpace.basisFun (Fin 3) ℝ).equiv
    hherm.eigenvectorBasis (Equiv.refl (Fin 3))
  have hφ : frameMatrix φ = (hherm.eigenvectorUnitary : Mat) := by
    ext i j
    rw [frameMatrix_apply]
    simp only [φ, OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply]
  have htrace : ∑ i, hherm.eigenvalues i = 0 := by
    have h := hherm.trace_eq_sum_eigenvalues
    calc
      _ = Matrix.trace A := by simpa using h.symm
      _ = 0 := ht
  have hsquare : ∑ i, hherm.eigenvalues i ^ 2 =
      6 * normalizedBlockNorm A ^ 2 := by
    rw [matrix_spectral_square A hherm, trace_square_eq_six_norm_sq A hA]
  let S : Shape := {
    s := fun i => hherm.eigenvalues i / normalizedBlockNorm A
    trace := by simp only [← Finset.sum_div, htrace, zero_div]
    square := by
      simp only [div_pow, ← Finset.sum_div, hsquare]
      field_simp [ne_of_gt hv]
  }
  refine ⟨φ, S, ?_⟩
  rw [hφ]
  have hd : (hherm.eigenvectorUnitary : Mat)ᵀ * A * hherm.eigenvectorUnitary =
      Matrix.diagonal hherm.eigenvalues := by
    simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose,
      Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hherm.conjStarAlgAut_star_eigenvectorUnitary
  rw [hd]
  apply congrArg Matrix.diagonal
  funext i
  change hherm.eigenvalues i = normalizedBlockNorm A *
    (hherm.eigenvalues i / normalizedBlockNorm A)
  field_simp [ne_of_gt hv]

/-- The local spectral shape is realized by a genuine oriented
four-dimensional quaternion lift. The possible global sign on the
three-dimensional eigenbasis cancels from both matrix slots. -/
theorem exists_lifted_spectral_shape (A : Mat) (hA : symmetric A) (ht : traceFree A)
    (hv : 0 < normalizedBlockNorm A) :
    ∃ R : Mat, Rᵀ * R = 1 ∧
      Nonempty (QuaternionLift quaternionMatrix Angular.oppositeMatrix R) ∧
      ∃ S : Shape, Rᵀ * A * R =
        Matrix.diagonal (fun i => normalizedBlockNorm A * S.s i) := by
  obtain ⟨φ, S, hS⟩ := exists_spectral_shape A hA ht hv
  obtain ⟨c, hc, hP⟩ := exists_signed_left_lift φ
  refine ⟨c • frameMatrix φ, ?_, hP, S, ?_⟩
  · rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← pow_two, hc, one_smul, frameMatrix_orthogonal]
  · rw [signed_conjugation c hc, hS]

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! Differentiate the actual Hessian constraints to show that its rough
Laplacian remains a symmetric trace-free Bianchi gradient. -/

namespace PositiveEinsteinFour.Geometry

open Matrix TraceHessian EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance thirdBianchiNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance thirdBianchiNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance thirdBianchiNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

def matrixEntryMap (a b : Fin 3) : Mat →L[ℝ] ℝ :=
  ({ toFun := fun A => A a b
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Mat →ₗ[ℝ] ℝ).toContinuousLinearMap

theorem hasDerivAt_matrixEntry {A : ℝ → Mat} {Z : Mat} {t : ℝ}
    (hA : HasDerivAt A Z t) (a b : Fin 3) :
    HasDerivAt (fun r => A r a b) (Z a b) t := by
  convert! (matrixEntryMap a b).hasFDerivAt.comp_hasDerivAt t hA using 1

theorem symmetric_of_hasDerivAt {A : ℝ → Mat} {Z : Mat} {t : ℝ}
    (hA : HasDerivAt A Z t) (hs : ∀ r, symmetric (A r)) : symmetric Z := by
  intro a b
  have h1 := hasDerivAt_matrixEntry hA a b
  have h2 := hasDerivAt_matrixEntry hA b a
  have heq : (fun r => A r a b) = fun r => A r b a := funext (fun r => hs r a b)
  rw [heq] at h1
  exact h1.unique h2

theorem traceFree_of_hasDerivAt {A : ℝ → Mat} {Z : Mat} {t : ℝ}
    (hA : HasDerivAt A Z t) (ht : ∀ r, traceFree (A r)) : traceFree Z := by
  have h := hasDerivAt_matrixTrace hA
  have heq : (fun r => Matrix.trace (A r)) = fun _ => (0 : ℝ) := funext ht
  rw [heq] at h
  exact h.unique (hasDerivAt_const t 0)

theorem hasDerivAt_gradientDivergence {A : ℝ → Angular.Gradient}
    {Z : Angular.Gradient} {t : ℝ}
    (hA : ∀ j, HasDerivAt (fun r => A r j) (Z j) t) (a : Fin 3) (b : Fin 4) :
    HasDerivAt (fun r => gradientDivergence (A r) a b) (gradientDivergence Z a b) t := by
  exact HasDerivAt.fun_sum (fun s _ => HasDerivAt.fun_sum (fun j _ =>
    (hasDerivAt_matrixEntry (hA j) s a).const_mul (quaternionMatrix s b j)))

theorem gradientDivergence_of_hasDerivAt {A : ℝ → Angular.Gradient}
    {Z : Angular.Gradient} {t : ℝ}
    (hA : ∀ j, HasDerivAt (fun r => A r j) (Z j) t)
    (hb : ∀ r a b, gradientDivergence (A r) a b = 0) :
    ∀ a b, gradientDivergence Z a b = 0 := by
  intro a b
  have h := hasDerivAt_gradientDivergence hA a b
  have heq : (fun r => gradientDivergence (A r) a b) = fun _ => (0 : ℝ) :=
    funext (fun r => hb r a b)
  rw [heq] at h
  exact h.unique (hasDerivAt_const t 0)

theorem hessian_divergence_eq (X : Hessian) (i b : Fin 4) (a : Fin 3) :
    HighestHessian.divergence X i a b = gradientDivergence (X i) a b := by
  simp only [HighestHessian.divergence, WithLp.ofLp_sum, Finset.sum_apply,
    gradientDivergence]
  apply Finset.sum_congr rfl
  intro s _
  exact (quaternionMatrix_apply s (WithLp.toLp 2 (fun j => X i j s a)) b).symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def frameLaplacianMatrix (g : SmoothMetric M) (e : FrameBundle g) : Angular.Gradient :=
  fun j => ∑ i, plusWeylThirdDerivative g e.base e.frame i i j

/-- All three constraints follow from differentiating the corresponding
Hessian identities along parallel frame flow; none is an extra Ricci input. -/
theorem frameLaplacianMatrix_constraints
    (g : SmoothMetric M) (h : WeylCovariantIdentities g)
    {μ : Measure (FrameBundle g)} (φ : Fin 4 → FrameFlow g μ)
    (hX : ∀ i j t e, HasDerivAt
      (fun s => plusWeylHessian g ((φ i).map s e).base ((φ i).map s e).frame i j)
      (plusWeylThirdDerivative g ((φ i).map t e).base ((φ i).map t e).frame i i j) t)
    (e : FrameBundle g) :
    (∀ j, symmetric (frameLaplacianMatrix g e j)) ∧
    (∀ j, traceFree (frameLaplacianMatrix g e j)) ∧
    (∀ a b, gradientDivergence (frameLaplacianMatrix g e) a b = 0) := by
  have hD (i : Fin 4) :
      (∀ j, symmetric (plusWeylThirdDerivative g e.base e.frame i i j)) ∧
      (∀ j, traceFree (plusWeylThirdDerivative g e.base e.frame i i j)) ∧
      (∀ a b, gradientDivergence (plusWeylThirdDerivative g e.base e.frame i i) a b = 0) := by
    obtain ⟨e₀, he⟩ := ((φ i).map 0).surjective e
    change (φ i).map 0 e₀ = e at he
    have hs (j : Fin 4) := symmetric_of_hasDerivAt (hX i j 0 e₀)
      (fun t => (h.hessianMatrix ((φ i).map t e₀) i j).1)
    have ht (j : Fin 4) := traceFree_of_hasDerivAt (hX i j 0 e₀)
      (fun t => (h.hessianMatrix ((φ i).map t e₀) i j).2)
    have hb := gradientDivergence_of_hasDerivAt (fun j => hX i j 0 e₀)
      (fun t a b => (hessian_divergence_eq _ i b a).symm.trans
        (congrArg (fun q : Bianchi.Vec => q b) (h.hessianBianchi ((φ i).map t e₀) i a)))
    rw [he] at hs ht hb
    exact ⟨hs, ht, hb⟩
  refine ⟨?_, ?_, ?_⟩
  · intro j a b
    simp only [frameLaplacianMatrix, Matrix.sum_apply]
    exact Finset.sum_congr rfl (fun i _ => (hD i).1 j a b)
  · intro j
    change Matrix.trace (∑ i, plusWeylThirdDerivative g e.base e.frame i i j) = 0
    rw [Matrix.trace_sum]
    exact Finset.sum_eq_zero (fun i _ => (hD i).2.1 j)
  · intro a b
    simp only [gradientDivergence, frameLaplacianMatrix, Matrix.sum_apply, Finset.mul_sum]
    calc
      _ = ∑ s, ∑ i, ∑ j, quaternionMatrix s b j *
          plusWeylThirdDerivative g e.base e.frame i i j s a := by
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.sum_comm]
      _ = ∑ i, ∑ s, ∑ j, quaternionMatrix s b j *
          plusWeylThirdDerivative g e.base e.frame i i j s a := Finset.sum_comm
      _ = 0 := Finset.sum_eq_zero (fun i _ => (hD i).2.2 a b)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The full trace Green term as invariant polynomial contractions.
This expression has no division by a Weyl norm and is valid at its zeros. -/

namespace PositiveEinsteinFour.Geometry

open Matrix TraceHessian EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance traceScalarNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance traceScalarNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance traceScalarNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

def weylGradientEnergy (Z : Fin 4 → Mat) : ℝ :=
  (∑ i, matrixPairing (Z i) (Z i)) / 6

def weylMatrixEnergy (A : Mat) (Z : Fin 4 → Mat) : ℝ :=
  (∑ i, matrixPairing (matrixSlotAction A (Z i)) (Z i)) / 6

def weylRadialSquare (A : Mat) (Z : Fin 4 → Mat) : ℝ :=
  (∑ i, Matrix.trace (A * Z i) ^ 2) / 36

theorem traceCoefficientDerivative_pairing (A Z : Mat) (hZ : symmetric Z) :
    matrixPairing (traceCoefficientDerivative A Z) Z =
      (4 + Matrix.trace (A * A) / 6) * matrixPairing Z Z -
        10 * matrixPairing (matrixSlotAction A Z) Z + Matrix.trace (A * Z) ^ 2 / 3 := by
  have hzt : Zᵀ = Z := by ext i j; exact hZ j i
  have hp : matrixPairing A Z = Matrix.trace (A * Z) := by
    rw [matrixPairing_eq_trace, hzt]
  change CurvatureContraction.matrixPairingLinear Z _ = _
  rw [traceCoefficientDerivative, map_sub, map_add, map_smul, map_smul, map_smul]
  change (4 + Matrix.trace (A * A) / 6) * matrixPairing Z Z +
    (Matrix.trace (A * Z) / 3) * matrixPairing A Z -
      10 * matrixPairing (matrixSlotAction A Z) Z = _
  rw [hp]
  ring

theorem traceCoefficientDerivative_sum (A : Mat) (hA : symmetric A)
    (Z : Fin 4 → Mat) (hZ : ∀ i, symmetric (Z i)) :
    (5 / 12 : ℝ) * (∑ i, matrixPairing (traceCoefficientDerivative A (Z i)) (Z i)) =
      (10 + (5 / 2 : ℝ) * normalizedBlockNorm A ^ 2) * weylGradientEnergy Z -
        25 * weylMatrixEnergy A Z + 5 * weylRadialSquare A Z := by
  simp_rw [traceCoefficientDerivative_pairing A _ (hZ _)]
  rw [trace_square_eq_six_norm_sq A hA]
  simp only [weylGradientEnergy, weylMatrixEnergy, weylRadialSquare,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_div]
  ring

theorem weylRadialSquare_eq_norm_gradient (A : Mat) (Z : Fin 4 → Mat)
    (p : Fin 4 → ℝ) (hp : ∀ i, Matrix.trace (A * Z i) = 6 * normalizedBlockNorm A * p i) :
    weylRadialSquare A Z = normalizedBlockNorm A ^ 2 * ∑ i, p i ^ 2 := by
  unfold weylRadialSquare
  simp_rw [hp, mul_pow]
  simp only [← Finset.mul_sum]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The actual trace subtraction gives the scalar term of the weighted
Hessian estimate in every frame, including at Weyl zeros. -/
theorem weighted_metric_trace_scalar
    (g : SmoothMetric M) {μ : Measure (FrameBundle g)}
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (φ : Fin 4 → FrameFlow g μ)
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hT : Continuous (fun e : FrameBundle g => plusWeyl g e.base e.frame))
    (hDT : ∀ i, Continuous (fun e : FrameBundle g => plusWeylGradient g e.base e.frame i))
    (hX : ∀ i, Continuous (frameHessianSlice g i i))
    (hsT : ∀ e : FrameBundle g, symmetric (plusWeyl g e.base e.frame))
    (hsZ : ∀ e : FrameBundle g, ∀ i, symmetric (plusWeylGradient g e.base e.frame i))
    (hm : ∀ i t e, HasDerivAt (fun s => m ((φ i).map s e))
      (dm i ((φ i).map t e)) t)
    (hTd : ∀ i t e, HasDerivAt
      (fun s => plusWeyl g ((φ i).map s e).base ((φ i).map s e).frame)
      (plusWeylGradient g ((φ i).map t e).base ((φ i).map t e).frame i) t)
    (hZd : ∀ i t e, HasDerivAt (fun s => frameGradientSlice g i ((φ i).map s e))
      (frameHessianSlice g i i ((φ i).map t e)) t) :
    -(5 / 12 : ℝ) * (∫ e, m e *
      matrixPairing (traceCoefficient (plusWeyl g e.base e.frame))
        (hessianTrace (plusWeylHessian g e.base e.frame)) +
      ∑ i, dm i e * matrixPairing (traceCoefficient (plusWeyl g e.base e.frame))
        (plusWeylGradient g e.base e.frame i) ∂μ) =
      ∫ e, m e *
        ((10 + (5 / 2 : ℝ) * normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2) *
          weylGradientEnergy (plusWeylGradient g e.base e.frame) -
        25 * weylMatrixEnergy (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame) +
        5 * weylRadialSquare (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame)) ∂μ := by
  rw [weighted_metric_trace_green g φ m dm hT hDT hX hm hTd hZd,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with e
  calc
    _ = m e * ((5 / 12 : ℝ) * ∑ i,
        matrixPairing (traceCoefficientDerivative (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame i))
          (plusWeylGradient g e.base e.frame i)) := by ring
    _ = _ := by rw [traceCoefficientDerivative_sum _ (hsT e) _ (hsZ e)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The invariant Ricci equation has the actual Bianchi compression in
every orthonormal frame, without imposing a diagonal Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open Bianchi TraceHessian

noncomputable section

private theorem quaternion_skew_sum (r : Fin 3) (j : Fin 4) (q : Vec) :
    (∑ i, quaternionMatrix r i j * q i) = -quaternion r q j := by
  rw [← quaternionMatrix_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [quaternionMatrix_skew r i j]
  ring

/-- The full bundle term is the unweighted Bianchi coupling plus the
mixed action of the entire symmetric matrix. -/
theorem bundleCurvatureAction_general_sum (A : Mat) (Z : Tensor)
    (j : Fin 4) (a b : Fin 3) :
    2 * (∑ i, bundleCurvatureAction A i j (rawMatrixSlice Z.matrix i) a b) =
      -(rawCoupling Z.matrix a b j + generalMixedAction A Z.matrix a b j) := by
  have hr (r : Fin 3) :
      (∑ i, quaternionMatrix r i j *
        (matrixRotation r Z a b i + ∑ s, A r s * matrixRotation s Z a b i)) =
        -quaternion r (matrixRotation r Z a b) j -
          ∑ s, A r s * quaternion r (matrixRotation s Z a b) j := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [quaternion_skew_sum, Finset.sum_comm]
    have hpart (s : Fin 3) :
        (∑ i, quaternionMatrix r i j * (A r s * matrixRotation s Z a b i)) =
          -(A r s * quaternion r (matrixRotation s Z a b) j) := by
      calc
        _ = A r s * (∑ i, quaternionMatrix r i j * matrixRotation s Z a b i) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [quaternion_skew_sum]; ring
    simp_rw [hpart]
    rw [Finset.sum_neg_distrib]
    ring
  simp only [bundleCurvatureAction, Matrix.smul_apply, Matrix.sum_apply,
    Matrix.add_apply, smul_eq_mul, matrixRotation_slice]
  calc
    _ = ∑ i, ∑ r, quaternionMatrix r i j *
        (matrixRotation r Z a b i + ∑ s, A r s * matrixRotation s Z a b i) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = ∑ r, ∑ i, quaternionMatrix r i j *
        (matrixRotation r Z a b i + ∑ s, A r s * matrixRotation s Z a b i) :=
      Finset.sum_comm
    _ = _ := by
      simp_rw [hr]
      simp only [rawCoupling, generalMixedAction, rawMatrixRotation_matrix,
        Finset.sum_apply, PiLp.smul_apply, WithLp.ofLp_sum,
        Finset.sum_sub_distrib, Finset.sum_neg_distrib, smul_eq_mul]
      ring

/-- The arbitrary coefficient action specializes to the earlier diagonal
formula without changing the underlying matrix-slot operator. -/
theorem generalMatrixAction_diagonal (t : Fin 3 → ℝ) (Z : Tensor) :
    generalMatrixAction (Matrix.diagonal t) Z.matrix = rawMatrixCurvature t Z := by
  funext a b
  ext j
  change matrixSlotAction (Matrix.diagonal t) (rawMatrixSlice Z.matrix j) a b = _
  rw [matrixSlotAction_diagonal]
  exact (rawMatrixCurvature_component t Z a b j).symm

/-- The actual invariant Ricci right side is the compressed expression
13Z−20P(B_F(A)Z), as an equality of all matrix and tangent entries. -/
theorem invariantRicciGradient_compressed (A : Mat)
    (hA : symmetric A) (hAt : traceFree A)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    invariantRicciGradient A (fun j => rawMatrixSlice Z.matrix j) =
      fun j => rawMatrixSlice ((13 : ℝ) • Z.matrix -
        (20 : ℝ) • rawBianchiProjection (generalMatrixAction A Z.matrix)) j := by
  funext j
  ext a b
  have h := congrArg (fun W : RawGradient => W a b j)
    (generalRicci_compression A hA hAt Z hz hb)
  have hc := congrArg (fun q : Vec => q j) (gradientCoupling_eq Z hb a b)
  change rawCoupling Z.matrix a b j = -4 * Z.matrix a b j at hc
  change 13 * Z.matrix a b j - 12 * generalMatrixAction A Z.matrix a b j -
    generalMixedAction A Z.matrix a b j = _ at h
  simp only [invariantRicciGradient, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [bundleCurvatureAction_general_sum]
  change 9 * Z.matrix a b j - 12 * generalMatrixAction A Z.matrix a b j -
    (rawCoupling Z.matrix a b j + generalMixedAction A Z.matrix a b j) = _
  rw [hc]
  dsimp only [rawMatrixSlice]
  linarith only [h]

/-- The coefficient 20 holds against every genuine Bianchi test tensor
in an arbitrary frame. This is the bilinear form needed by both scalar
and varying matrix-slot Green identities. -/
theorem invariantRicciGradient_pairing (A : Mat)
    (hA : symmetric A) (hAt : traceFree A)
    (Z W : Tensor) (hz : Z.traceFree) (hbz : Z.bianchi) (hbw : W.bianchi) :
    inner ℝ (gradientVector (invariantRicciGradient A
      (fun j => rawMatrixSlice Z.matrix j))) (tensorGradientVector W) =
      13 * rawPairing Z.matrix W.matrix -
        20 * rawPairing (generalMatrixAction A Z.matrix) W.matrix := by
  rw [invariantRicciGradient_compressed A hA hAt Z hz hbz]
  change inner ℝ (rawGradientVector ((13 : ℝ) • Z.matrix -
    (20 : ℝ) • rawBianchiProjection (generalMatrixAction A Z.matrix)))
    (rawGradientVector W.matrix) = _
  rw [inner_rawGradientVector, rawPairing_sub_left, rawPairing_smul_left,
    rawPairing_smul_left, rawBianchiProjection_pairing _ W hbw]

private def ricciCompressionTensor (Z L : Tensor) : Tensor where
  diagonal i := (1 / 20 : ℝ) • ((13 : ℝ) • Z.diagonal i - L.diagonal i)
  off i := (1 / 20 : ℝ) • ((13 : ℝ) • Z.off i - L.off i)

private theorem ricciCompressionTensor_matrix (Z L : Tensor) :
    (ricciCompressionTensor Z L).matrix =
      (1 / 20 : ℝ) • ((13 : ℝ) • Z.matrix - L.matrix) := by
  funext a b
  fin_cases a <;> fin_cases b <;> rfl

private theorem ricciCompressionTensor_bianchi (Z L : Tensor)
    (hZ : Z.bianchi) (hL : L.bianchi) : (ricciCompressionTensor Z L).bianchi := by
  intro i
  rw [Tensor.divergence_eq_sum]
  simp only [ricciCompressionTensor_matrix, sub_eq_add_neg,
    Pi.smul_apply, Pi.add_apply, Pi.neg_apply, quaternion_add, quaternion_neg, quaternion_smul,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.smul_sum,
    ← Tensor.divergence_eq_sum, hZ i, hL i, smul_zero, neg_zero, add_zero]

/-- A Bianchi rough Laplacian is enough to identify the compression energy.
No separate assertion that the projector has the desired range is needed. -/
theorem compressed_energy_of_bianchi_ricci (A : Mat) (Z L : Tensor)
    (hZ : Z.bianchi) (hL : L.bianchi)
    (hRicci : L.matrix = (13 : ℝ) • Z.matrix -
      (20 : ℝ) • rawBianchiProjection (generalMatrixAction A Z.matrix)) :
    rawPairing (generalMatrixAction A Z.matrix)
      (rawBianchiProjection (generalMatrixAction A Z.matrix)) =
        rawPairing (rawBianchiProjection (generalMatrixAction A Z.matrix))
          (rawBianchiProjection (generalMatrixAction A Z.matrix)) := by
  have hm : (ricciCompressionTensor Z L).matrix =
      rawBianchiProjection (generalMatrixAction A Z.matrix) := by
    rw [ricciCompressionTensor_matrix, hRicci]
    module
  have hp := rawBianchiProjection_pairing (generalMatrixAction A Z.matrix)
    (ricciCompressionTensor Z L) (ricciCompressionTensor_bianchi Z L hZ hL)
  rw [hm] at hp
  exact hp.symm

/-- The concrete vector-valued matrix action is the bounded matrix-slot
operator used in the metric Green identity. -/
theorem matrixSlotOperator_generalTensor (A : Mat) (Z : Tensor) (hz : Z.traceFree) :
    matrixSlotOperator A (tensorGradientVector Z) =
      rawGradientVector (generalMatrixAction A Z.matrix) := by
  have htrace (i : Fin 4) : (∑ a, tensorGradientVector Z (i, a, a)) = 0 := by
    have h := congrArg (fun v : Vec => v i) hz
    simpa [tensorGradientVector, rawGradientVector, rawCoordinates,
      Tensor.traceFree, Tensor.matrix, Fin.sum_univ_three] using h
  ext p
  rcases p with ⟨i, a, b⟩
  rw [matrixSlotOperator_on_traceFree A _ htrace]
  rfl

theorem matrixSlotOperator_general_pairing (A : Mat) (Z : Tensor) (hz : Z.traceFree) :
    inner ℝ (matrixSlotOperator A (tensorGradientVector Z)) (tensorGradientVector Z) =
      rawPairing (generalMatrixAction A Z.matrix) Z.matrix := by
  rw [matrixSlotOperator_generalTensor A Z hz]
  exact inner_rawGradientVector _ _

/-- The varying-operator Green main term has the coefficient 20 times
the true compression norm, once the actual rough Laplacian is Bianchi. -/
theorem matrixSlot_laplacian_pairing (A : Mat) (Z L : Tensor)
    (hz : Z.traceFree) (hZ : Z.bianchi) (hL : L.bianchi)
    (hRicci : L.matrix = (13 : ℝ) • Z.matrix -
      (20 : ℝ) • rawBianchiProjection (generalMatrixAction A Z.matrix)) :
    inner ℝ (tensorGradientVector L) (matrixSlotOperator A (tensorGradientVector Z)) =
      13 * rawPairing (generalMatrixAction A Z.matrix) Z.matrix -
        20 * rawPairing (rawBianchiProjection (generalMatrixAction A Z.matrix))
          (rawBianchiProjection (generalMatrixAction A Z.matrix)) := by
  rw [matrixSlotOperator_generalTensor A Z hz]
  change inner ℝ (rawGradientVector L.matrix)
    (rawGradientVector (generalMatrixAction A Z.matrix)) = _
  rw [inner_rawGradientVector, hRicci, rawPairing_sub_left,
    rawPairing_smul_left, rawPairing_smul_left,
    rawPairing_comm Z.matrix, rawPairing_comm (rawBianchiProjection _),
    compressed_energy_of_bianchi_ricci A Z L hZ hL hRicci]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Ordinary differentiation and compact bounds for the specific polynomial
multiplier of equation (15), with both Weyl norms varying. -/

namespace PositiveEinsteinFour.Geometry

open Potential Quadratic TraceHessian Filter
open scoped Topology

noncomputable section

local instance kappaNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance kappaNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance kappaNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

theorem hasDerivAt_kappa_comp {v b : ℝ → ℝ} {p q t : ℝ}
    (hv : HasDerivAt v p t) (hb : HasDerivAt b q t) :
    HasDerivAt (fun s => kappa (v s) (b s))
      (kappaV (v t) (b t) * p + kappaB (v t) (b t) * q) t := by
  have ha := hv.sub_const 1
  have hs := hb.sub_const 1
  have h0 := (ha.sub hs).const_mul (-(158 / 6 : ℝ))
  have h1 := h0.add ((ha.pow 2).const_mul (-(43 / 4 : ℝ)))
  have h2 := h1.add ((ha.mul hs).const_mul (61 / 18 : ℝ))
  have h3 := h2.add ((hs.pow 2).const_mul (-(45 / 4 : ℝ)))
  have h4 := h3.add ((hs.pow 3).const_mul (-(63 / 4 : ℝ)))
  have h5 := h4.add ((ha.mul (hs.pow 2)).const_mul (21 / 4 : ℝ))
  have h6 := h5.add (((ha.pow 2).mul hs).const_mul (183 / 4 : ℝ))
  have h7 := h6.add ((ha.pow 3).const_mul (208 / 4 : ℝ))
  have h8 := h7.add ((hs.pow 4).const_mul (61 / 4 : ℝ))
  have h9 := h8.add ((ha.mul (hs.pow 3)).const_mul (46 / 4 : ℝ))
  have h10 := h9.add (((ha.pow 2).mul (hs.pow 2)).const_mul (101 / 4 : ℝ))
  have h11 := h10.add (((ha.pow 3).mul hs).const_mul (79 / 4 : ℝ))
  have h12 := h11.add ((ha.pow 4).const_mul (-(41 / 4 : ℝ)))
  convert! h12 using 1
  · funext s
    simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.mul_apply]
    unfold kappa
    ring
  · unfold kappaV kappaB
    simp only [Pi.pow_apply]
    ring

theorem continuous_kappa : Continuous (fun x : ℝ × ℝ => kappa x.1 x.2) := by
  unfold kappa
  fun_prop

theorem continuous_kappaV : Continuous (fun x : ℝ × ℝ => kappaV x.1 x.2) := by
  unfold kappaV
  fun_prop

theorem continuous_kappaB : Continuous (fun x : ℝ × ℝ => kappaB x.1 x.2) := by
  unfold kappaB
  fun_prop

theorem kappa_rectangle_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ v b : ℝ, 0 ≤ v → v ≤ 3 → 0 ≤ b → b ≤ 3 →
      |kappa v b| ≤ C ∧ |kappaV v b| ≤ C ∧ |kappaB v b| ≤ C := by
  let K : Set (ℝ × ℝ) := Set.Icc 0 3 ×ˢ Set.Icc 0 3
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C₀, h₀⟩ := hK.exists_bound_of_continuousOn continuous_kappa.continuousOn
  obtain ⟨C₁, h₁⟩ := hK.exists_bound_of_continuousOn continuous_kappaV.continuousOn
  obtain ⟨C₂, h₂⟩ := hK.exists_bound_of_continuousOn continuous_kappaB.continuousOn
  refine ⟨|C₀| + |C₁| + |C₂|, by positivity, ?_⟩
  intro v b hv hv3 hb hb3
  have hx : (v, b) ∈ K := ⟨⟨hv, hv3⟩, ⟨hb, hb3⟩⟩
  have h0 := h₀ (v, b) hx
  have h1 := h₁ (v, b) hx
  have h2 := h₂ (v, b) hx
  simp only [Real.norm_eq_abs] at h0 h1 h2
  exact ⟨h0.trans (by linarith [le_abs_self C₀, abs_nonneg C₁, abs_nonneg C₂]),
    h1.trans (by linarith [le_abs_self C₁, abs_nonneg C₀, abs_nonneg C₂]),
    h2.trans (by linarith [le_abs_self C₂, abs_nonneg C₀, abs_nonneg C₁])⟩

def regularizedKappa (ε : ℝ) (A B : Mat) : ℝ :=
  kappa (regularizedBlockNorm ε A) (regularizedBlockNorm ε B)

def regularizedKappaDerivative (ε : ℝ) (A B Z V : Mat) : ℝ :=
  kappaV (regularizedBlockNorm ε A) (regularizedBlockNorm ε B) *
    regularizedRadialDerivative ε A Z +
  kappaB (regularizedBlockNorm ε A) (regularizedBlockNorm ε B) *
    regularizedRadialDerivative ε B V

theorem continuous_regularizedKappa {Ω : Type*} [TopologicalSpace Ω]
    (ε : ℝ) (A B : Ω → Mat) (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun e => regularizedKappa ε (A e) (B e)) := by
  simpa only [regularizedKappa, Function.comp_def] using
    continuous_kappa.comp (((continuous_regularizedBlockNorm ε).comp hA).prodMk
      ((continuous_regularizedBlockNorm ε).comp hB))

theorem continuous_regularizedKappaDerivative {Ω : Type*} [TopologicalSpace Ω]
    (ε : ℝ) (hε : 0 < ε) (A B Z V : Ω → Mat)
    (hA : Continuous A) (hB : Continuous B) (hZ : Continuous Z) (hV : Continuous V) :
    Continuous (fun e => regularizedKappaDerivative ε (A e) (B e) (Z e) (V e)) := by
  have hAB := ((continuous_regularizedBlockNorm ε).comp hA).prodMk
    ((continuous_regularizedBlockNorm ε).comp hB)
  convert! ((continuous_kappaV.comp hAB).mul
    (continuous_regularizedRadialDerivative ε hε A Z hA hZ)).add
      ((continuous_kappaB.comp hAB).mul
        (continuous_regularizedRadialDerivative ε hε B V hB hV)) using 1

theorem hasDerivAt_regularizedKappa {A B : ℝ → Mat} {Z V : Mat} {t ε : ℝ}
    (hA : HasDerivAt A Z t) (hB : HasDerivAt B V t)
    (hsA : ∀ t, symmetric (A t)) (hsB : ∀ t, symmetric (B t)) (hε : 0 < ε) :
    HasDerivAt (fun s => regularizedKappa ε (A s) (B s))
      (regularizedKappaDerivative ε (A t) (B t) Z V) t :=
  hasDerivAt_kappa_comp (hasDerivAt_regularizedBlockNorm hA hsA hε)
    (hasDerivAt_regularizedBlockNorm hB hsB hε)

theorem regularizedNorm_rectangle {ε : ℝ} (hε : 0 ≤ ε) (he : ε ≤ 1)
    (A B : Mat) (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    0 ≤ regularizedBlockNorm ε A ∧ regularizedBlockNorm ε A ≤ 3 ∧
    0 ≤ regularizedBlockNorm ε B ∧ regularizedBlockNorm ε B ≤ 3 := by
  have hA := regularizedBlockNorm_le ε hε A
  have hB := regularizedBlockNorm_le ε hε B
  refine ⟨Real.sqrt_nonneg _, ?_, Real.sqrt_nonneg _, ?_⟩
  · linarith [normalizedBlockNorm_nonneg B]
  · linarith [normalizedBlockNorm_nonneg A]

theorem regularizedKappa_bounds (C : ℝ)
    (hC : ∀ v b : ℝ, 0 ≤ v → v ≤ 3 → 0 ≤ b → b ≤ 3 →
      |kappa v b| ≤ C ∧ |kappaV v b| ≤ C ∧ |kappaB v b| ≤ C)
    {ε : ℝ} (hε : 0 < ε) (he : ε ≤ 1)
    (A B Z V : Mat) (hZ : symmetric Z) (hV : symmetric V)
    (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    |regularizedKappa ε A B| ≤ C ∧ |regularizedKappaDerivative ε A B Z V| ≤
      C * (normalizedBlockNorm Z + normalizedBlockNorm V) := by
  obtain ⟨hA0, hA3, hB0, hB3⟩ := regularizedNorm_rectangle hε.le he A B hpinch
  obtain ⟨hk, hkV, hkB⟩ := hC _ _ hA0 hA3 hB0 hB3
  refine ⟨hk, ?_⟩
  have hC0 : 0 ≤ C := (abs_nonneg _).trans hk
  unfold regularizedKappaDerivative
  calc
    _ ≤ |kappaV (regularizedBlockNorm ε A) (regularizedBlockNorm ε B) *
        regularizedRadialDerivative ε A Z| +
        |kappaB (regularizedBlockNorm ε A) (regularizedBlockNorm ε B) *
        regularizedRadialDerivative ε B V| := abs_add_le _ _
    _ ≤ C * normalizedBlockNorm Z + C * normalizedBlockNorm V := by
      simp only [abs_mul]
      exact add_le_add
        (mul_le_mul hkV (abs_regularizedRadialDerivative_le ε hε A Z hZ) (abs_nonneg _) hC0)
        (mul_le_mul hkB (abs_regularizedRadialDerivative_le ε hε B V hV) (abs_nonneg _) hC0)
    _ = _ := by ring

theorem tendsto_regularizedKappa (A B : Mat) :
    Tendsto (fun ε => regularizedKappa ε A B) (𝓝 0) (𝓝 (regularizedKappa 0 A B)) := by
  simpa only [regularizedKappa, regularizedBlockNorm_zero, Function.comp_def] using
    continuous_kappa.continuousAt.tendsto.comp
      ((tendsto_regularizedBlockNorm A).prodMk_nhds (tendsto_regularizedBlockNorm B))

theorem tendsto_regularizedKappaDerivative (A B Z V : Mat) :
    Tendsto (fun ε => regularizedKappaDerivative ε A B Z V) (𝓝 0)
      (𝓝 (regularizedKappaDerivative 0 A B Z V)) := by
  have hp := (tendsto_regularizedBlockNorm A).prodMk_nhds (tendsto_regularizedBlockNorm B)
  have hz : Tendsto (fun ε => regularizedRadialDerivative ε A Z) (𝓝 0)
      (𝓝 (regularizedRadialDerivative 0 A Z)) := by
    simpa only [regularizedRadialDerivative, regularizedBlockNorm_zero] using
      tendsto_regularizedRadialDerivative A Z
  have hv : Tendsto (fun ε => regularizedRadialDerivative ε B V) (𝓝 0)
      (𝓝 (regularizedRadialDerivative 0 B V)) := by
    simpa only [regularizedRadialDerivative, regularizedBlockNorm_zero] using
      tendsto_regularizedRadialDerivative B V
  simpa only [regularizedKappaDerivative, regularizedBlockNorm_zero, Function.comp_def] using
    ((continuous_kappaV.continuousAt.tendsto.comp hp).mul hz).add
      ((continuous_kappaB.continuousAt.tendsto.comp hp).mul hv)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The raw classical parallel-frame calculus used by the weighted Green
argument. Every field refers to the actual metric tensors. No compressed
Ricci equation or integral estimate is a field of this structure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance greenDataNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance greenDataNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance greenDataNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Petersen's tensor commutators and ordinary differentiation in parallel
frames, with Brin--Karcher measure-preserving flows. Ricci is normalized to
`3g`; the last two curvature entries are reversed for the covector action.
The normalization of an arbitrary Einstein metric is separate. -/
structure MetricGreenData (g : SmoothMetric M) (μ : Measure (FrameBundle g)) where
  flow : Fin 4 → FrameFlow g μ
  weyl : WeylCovariantIdentities g
  continuousWeyl : Continuous (fun e : FrameBundle g => plusWeyl g e.base e.frame)
  continuousGradient : ∀ i, Continuous
    (fun e : FrameBundle g => plusWeylGradient g e.base e.frame i)
  continuousHessian : ∀ i j, Continuous
    (fun e : FrameBundle g => plusWeylHessian g e.base e.frame i j)
  continuousThird : ∀ i j k, Continuous
    (fun e : FrameBundle g => plusWeylThirdDerivative g e.base e.frame i j k)
  derivativeWeyl : ∀ k t e, HasDerivAt
    (fun s => plusWeyl g ((flow k).map s e).base ((flow k).map s e).frame)
    (plusWeylGradient g ((flow k).map t e).base ((flow k).map t e).frame k) t
  derivativeGradient : ∀ k j t e, HasDerivAt
    (fun s => plusWeylGradient g ((flow k).map s e).base ((flow k).map s e).frame j)
    (plusWeylHessian g ((flow k).map t e).base ((flow k).map t e).frame k j) t
  derivativeHessian : ∀ k i j t e, HasDerivAt
    (fun s => plusWeylHessian g ((flow k).map s e).base ((flow k).map s e).frame i j)
    (plusWeylThirdDerivative g ((flow k).map t e).base ((flow k).map t e).frame k i j) t
  gradientBianchi : ∀ (e : FrameBundle g) r i,
    gradientDivergence (plusWeylGradient g e.base e.frame) r i = 0
  innerCommutator : ∀ (e : FrameBundle g) i k j,
    plusWeylThirdDerivative g e.base e.frame i k j -
      plusWeylThirdDerivative g e.base e.frame i j k =
    bundleCurvatureDerivative (plusWeylGradient g e.base e.frame i) k j
      (plusWeyl g e.base e.frame) +
    bundleCurvatureAction (plusWeyl g e.base e.frame) k j
      (plusWeylGradient g e.base e.frame i)
  outerCommutator : ∀ (e : FrameBundle g) i k j,
    plusWeylThirdDerivative g e.base e.frame i k j -
      plusWeylThirdDerivative g e.base e.frame k i j =
    bundleCurvatureAction (plusWeyl g e.base e.frame) i k
      (plusWeylGradient g e.base e.frame j) +
    ∑ a, frameCurvature g e.base e.frame i k a j • plusWeylGradient g e.base e.frame a
  ricci : ∀ (e : FrameBundle g) j a,
    (∑ i, frameCurvature g e.base e.frame i j a i) = if j = a then 3 else 0

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

/-- Matrix symmetry and trace constraints on the first derivative are
consequences of parallel differentiation of the actual Weyl block. -/
theorem gradientConstraints (d : MetricGreenData g μ) (e : FrameBundle g) :
    (∀ i, symmetric (plusWeylGradient g e.base e.frame i)) ∧
    (∀ i, traceFree (plusWeylGradient g e.base e.frame i)) := by
  have hi (i : Fin 4) : symmetric (plusWeylGradient g e.base e.frame i) ∧
      traceFree (plusWeylGradient g e.base e.frame i) := by
    obtain ⟨e₀, he⟩ := ((d.flow i).map 0).surjective e
    change (d.flow i).map 0 e₀ = e at he
    have hs := symmetric_of_hasDerivAt (d.derivativeWeyl i 0 e₀)
      (fun t => d.weyl.symmetric ((d.flow i).map t e₀))
    have ht := traceFree_of_hasDerivAt (d.derivativeWeyl i 0 e₀)
      (fun t => d.weyl.traceFree ((d.flow i).map t e₀))
    rw [he] at hs ht
    exact ⟨hs, ht⟩
  exact ⟨fun i => (hi i).1, fun i => (hi i).2⟩

theorem laplacianConstraints (d : MetricGreenData g μ) (e : FrameBundle g) :
    (∀ j, symmetric (frameLaplacianMatrix g e j)) ∧
    (∀ j, traceFree (frameLaplacianMatrix g e j)) ∧
    (∀ a b, gradientDivergence (frameLaplacianMatrix g e) a b = 0) :=
  frameLaplacianMatrix_constraints g d.weyl d.flow
    (fun i j t e => d.derivativeHessian i i j t e) e

theorem ricciGradient (d : MetricGreenData g μ) (e : FrameBundle g) :
    frameLaplacianMatrix g e = invariantRicciGradient (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame) :=
  metric_invariant_ricci_gradient g d.weyl d.flow d.derivativeWeyl
    (fun k i t e => d.derivativeHessian k i i t e) e
    (fun i k j a => frameCurvature g e.base e.frame i k a j) (d.gradientBianchi e)
    (d.innerCommutator e) (d.outerCommutator e) (d.ricci e)

end MetricGreenData

/-- Reindexing the derivative and matrix components is continuous. -/
def gradientVectorMap : (Fin 4 → Mat) →L[ℝ] GradientVector :=
  ({ toFun := gradientVector
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : (Fin 4 → Mat) →ₗ[ℝ] GradientVector).toContinuousLinearMap

theorem hasDerivAt_gradientVector {Z : ℝ → Fin 4 → Mat} {X : Fin 4 → Mat} {t : ℝ}
    (h : ∀ i, HasDerivAt (fun s => Z s i) (X i) t) :
    HasDerivAt (fun s => gradientVector (Z s)) (gradientVector X) t := by
  exact gradientVectorMap.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_pi.mpr h)

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem laplacianVector (_d : MetricGreenData g μ) (e : FrameBundle g) :
    frameGradientLaplacian g e = gradientVector (frameLaplacianMatrix g e) := by
  ext p
  rcases p with ⟨j, a, b⟩
  simp only [frameGradientLaplacian, frameThirdVector, frameLaplacianMatrix,
    gradientVector, WithLp.ofLp_sum, Finset.sum_apply, Matrix.sum_apply]

theorem continuousGradientVector (d : MetricGreenData g μ) :
    Continuous (frameGradientVector g) :=
  gradientVectorMap.continuous.comp (continuous_pi d.continuousGradient)

theorem continuousHessianVector (d : MetricGreenData g μ) (i : Fin 4) :
    Continuous (frameHessianVector g i) :=
  gradientVectorMap.continuous.comp (continuous_pi (d.continuousHessian i))

theorem continuousThirdVector (d : MetricGreenData g μ) (i j : Fin 4) :
    Continuous (frameThirdVector g i j) :=
  gradientVectorMap.continuous.comp (continuous_pi (d.continuousThird i j))

theorem derivativeGradientVector (d : MetricGreenData g μ) (i : Fin 4) (t : ℝ)
    (e : FrameBundle g) :
    HasDerivAt (fun s => frameGradientVector g ((d.flow i).map s e))
      (frameHessianVector g i ((d.flow i).map t e)) t :=
  hasDerivAt_gradientVector (fun j => d.derivativeGradient i j t e)

theorem derivativeHessianVector (d : MetricGreenData g μ) (i : Fin 4) (t : ℝ)
    (e : FrameBundle g) :
    HasDerivAt (fun s => frameHessianVector g i ((d.flow i).map s e))
      (frameThirdVector g i i ((d.flow i).map t e)) t :=
  hasDerivAt_gradientVector (fun j => d.derivativeHessian i i j t e)

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Supply the smooth weights used by the metric Green identities from
the actual two Weyl blocks and their actual first covariant derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TraceHessian
open scoped Manifold ContDiff

noncomputable section

local instance metricWeightNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricWeightNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricWeightNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def frameRegularizedWeight (g : SmoothMetric M) (ε : ℝ)
    (hT : Continuous (fun e : FrameBundle g => plusWeyl g e.base e.frame))
    (hU : Continuous (fun e : FrameBundle g => minusWeyl g e.base e.frame)) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => regularizedWeylWeight ε (plusWeyl g e.base e.frame)
    (minusWeyl g e.base e.frame), continuous_regularizedWeylWeight ε _ _ hT hU⟩

def frameRegularizedWeightDerivative (g : SmoothMetric M) (ε : ℝ) (hε : 0 < ε)
    (hT : Continuous (fun e : FrameBundle g => plusWeyl g e.base e.frame))
    (hU : Continuous (fun e : FrameBundle g => minusWeyl g e.base e.frame))
    (hZ : ∀ i, Continuous (fun e : FrameBundle g => plusWeylGradient g e.base e.frame i))
    (hV : ∀ i, Continuous (fun e : FrameBundle g => minusWeylGradient g e.base e.frame i))
    (i : Fin 4) : C(FrameBundle g, ℝ) :=
  ⟨fun e => regularizedWeylWeightDerivative ε (plusWeyl g e.base e.frame)
      (minusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame i)
      (minusWeylGradient g e.base e.frame i),
    continuous_regularizedWeylWeightDerivative ε hε _ _ _ _ hT hU (hZ i) (hV i)⟩

/-- The derivative assumption on a Green weight follows from ordinary
parallel-frame differentiation of the two Weyl blocks. -/
theorem frameRegularizedWeight_hasDerivAt
    (g : SmoothMetric M) {μ : Measure (FrameBundle g)} (φ : Fin 4 → FrameFlow g μ)
    (ε : ℝ) (hε : 0 < ε)
    (hT : Continuous (fun e : FrameBundle g => plusWeyl g e.base e.frame))
    (hU : Continuous (fun e : FrameBundle g => minusWeyl g e.base e.frame))
    (hZ : ∀ i, Continuous (fun e : FrameBundle g => plusWeylGradient g e.base e.frame i))
    (hV : ∀ i, Continuous (fun e : FrameBundle g => minusWeylGradient g e.base e.frame i))
    (hsT : ∀ e : FrameBundle g, symmetric (plusWeyl g e.base e.frame))
    (hsU : ∀ e : FrameBundle g, symmetric (minusWeyl g e.base e.frame))
    (hdT : ∀ i t e, HasDerivAt
      (fun s => plusWeyl g ((φ i).map s e).base ((φ i).map s e).frame)
      (plusWeylGradient g ((φ i).map t e).base ((φ i).map t e).frame i) t)
    (hdU : ∀ i t e, HasDerivAt
      (fun s => minusWeyl g ((φ i).map s e).base ((φ i).map s e).frame)
      (minusWeylGradient g ((φ i).map t e).base ((φ i).map t e).frame i) t) :
    ∀ i t e, HasDerivAt
      (fun s => frameRegularizedWeight g ε hT hU ((φ i).map s e))
      (frameRegularizedWeightDerivative g ε hε hT hU hZ hV i ((φ i).map t e)) t := by
  intro i t e
  exact hasDerivAt_regularizedWeylWeight (hdT i t e) (hdU i t e)
    (fun s => hsT ((φ i).map s e)) (fun s => hsU ((φ i).map s e)) hε

theorem frameRegularizedWeight_pos (g : SmoothMetric M) (ε : ℝ) (hε : 0 ≤ ε)
    (he : ε ≤ 1 / 3)
    (hT : Continuous (fun e : FrameBundle g => plusWeyl g e.base e.frame))
    (hU : Continuous (fun e : FrameBundle g => minusWeyl g e.base e.frame))
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) (e : FrameBundle g) :
    0 < frameRegularizedWeight g ε hT hU e :=
  regularizedWeylWeight_pos ε hε he _ _ (hpinch e)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Passage from smooth norm weights to the manuscript's Lipschitz weight.
Uniform domination is proved from the actual tensor norms. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter TraceHessian
open scoped Topology

noncomputable section

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  (μ : Measure Ω) [IsFiniteMeasure μ]

theorem integral_regularizedWeight_tendsto
    (A B : Ω → Mat) (F : Ω → ℝ)
    (hA : Continuous A) (hB : Continuous B) (hF : Continuous F)
    (hpinch : ∀ x, normalizedBlockNorm (A x) + normalizedBlockNorm (B x) < 2)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (he : ∀ n, ε n ≤ 1 / 3)
    (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, regularizedWeylWeight (ε n) (A x) (B x) * F x ∂μ) atTop
      (𝓝 (∫ x, (1 - (3 / 8 : ℝ) *
        (normalizedBlockNorm (A x) - normalizedBlockNorm (B x))) ^ 2 * F x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => 4 * |F x|)
  · intro n
    exact ((continuous_regularizedWeylWeight (ε n) A B hA hB).mul hF).aestronglyMeasurable
  · exact (hF.abs.const_mul 4).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · intro n
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_pos (regularizedWeylWeight_pos (ε n) (hε n).le (he n) _ _ (hpinch x))]
    exact mul_le_mul_of_nonneg_right
      (regularizedWeylWeight_bounds (ε n) (hε n).le (he n) _ _ (hpinch x)).2 (abs_nonneg _)
  · filter_upwards [] with x
    exact ((tendsto_regularizedWeylWeight (A x) (B x)).comp hlim).mul tendsto_const_nhds

theorem integral_regularizedWeightDerivative_tendsto
    (A B Z V : Ω → Mat) (F : Ω → ℝ)
    (hA : Continuous A) (hB : Continuous B) (hZ : Continuous Z) (hV : Continuous V)
    (hF : Continuous F) (hsZ : ∀ x, symmetric (Z x)) (hsV : ∀ x, symmetric (V x))
    (hpinch : ∀ x, normalizedBlockNorm (A x) + normalizedBlockNorm (B x) < 2)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (he : ∀ n, ε n ≤ 1 / 3)
    (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x,
      regularizedWeylWeightDerivative (ε n) (A x) (B x) (Z x) (V x) * F x ∂μ) atTop
      (𝓝 (∫ x, -(3 / 4 : ℝ) *
        (1 - (3 / 8 : ℝ) * (normalizedBlockNorm (A x) - normalizedBlockNorm (B x))) *
        (Matrix.trace (A x * Z x) / (6 * normalizedBlockNorm (A x)) -
          Matrix.trace (B x * V x) / (6 * normalizedBlockNorm (B x))) * F x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun x => (3 / 2 : ℝ) * (normalizedBlockNorm (Z x) + normalizedBlockNorm (V x)) * |F x|)
  · intro n
    exact ((continuous_regularizedWeylWeightDerivative (ε n) (hε n)
      A B Z V hA hB hZ hV).mul hF).aestronglyMeasurable
  · have hc : Continuous (fun x => (3 / 2 : ℝ) *
        (normalizedBlockNorm (Z x) + normalizedBlockNorm (V x)) * |F x|) :=
      (continuous_const.mul ((continuous_normalizedBlockNorm.comp hZ).add
        (continuous_normalizedBlockNorm.comp hV))).mul hF.abs
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro n
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_regularizedWeylWeightDerivative_le
      (ε n) (hε n) (he n) _ _ _ _ (hsZ x) (hsV x) (hpinch x)) (abs_nonneg _)
  · filter_upwards [] with x
    exact ((tendsto_regularizedWeylWeightDerivative (A x) (B x) (Z x) (V x)).comp hlim).mul
      tendsto_const_nhds

/-- The quadratic weight cost also passes to the limit, with a bound
independent of the regularization parameter. -/
theorem integral_regularizedWeightCost_tendsto
    (A B Z V : Ω → Mat) (F : Ω → ℝ)
    (hA : Continuous A) (hB : Continuous B) (hZ : Continuous Z) (hV : Continuous V)
    (hF : Continuous F) (hsZ : ∀ x, symmetric (Z x)) (hsV : ∀ x, symmetric (V x))
    (hpinch : ∀ x, normalizedBlockNorm (A x) + normalizedBlockNorm (B x) < 2)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (he : ∀ n, ε n ≤ 1 / 3)
    (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x,
      regularizedWeylWeightDerivative (ε n) (A x) (B x) (Z x) (V x) ^ 2 /
        regularizedWeylWeight (ε n) (A x) (B x) * F x ∂μ) atTop
      (𝓝 (∫ x, regularizedWeylWeightDerivative 0 (A x) (B x) (Z x) (V x) ^ 2 /
        regularizedWeylWeight 0 (A x) (B x) * F x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun x => 144 * (normalizedBlockNorm (Z x) + normalizedBlockNorm (V x)) ^ 2 * |F x|)
  · intro n
    have hm := continuous_regularizedWeylWeight (ε n) A B hA hB
    have hd := continuous_regularizedWeylWeightDerivative (ε n) (hε n) A B Z V hA hB hZ hV
    exact (((hd.pow 2).div hm (fun x => ne_of_gt
      (regularizedWeylWeight_pos (ε n) (hε n).le (he n) _ _ (hpinch x)))).mul hF).aestronglyMeasurable
  · have hc : Continuous (fun x => 144 *
        (normalizedBlockNorm (Z x) + normalizedBlockNorm (V x)) ^ 2 * |F x|) :=
      (continuous_const.mul (((continuous_normalizedBlockNorm.comp hZ).add
        (continuous_normalizedBlockNorm.comp hV)).pow 2)).mul hF.abs
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro n
    filter_upwards [] with x
    have hp := regularizedWeylWeight_pos (ε n) (hε n).le (he n) (A x) (B x) (hpinch x)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg
      (div_nonneg (sq_nonneg _) hp.le)]
    exact mul_le_mul_of_nonneg_right
      (regularized_weight_cost_le (ε n) (hε n) (he n) _ _ _ _ (hsZ x) (hsV x) (hpinch x))
      (abs_nonneg _)
  · filter_upwards [] with x
    have hd : Tendsto (fun n => regularizedWeylWeightDerivative (ε n) (A x) (B x) (Z x) (V x))
        atTop (𝓝 (regularizedWeylWeightDerivative 0 (A x) (B x) (Z x) (V x))) := by
      simpa only [Function.comp_def, regularizedWeylWeightDerivative,
        regularizedRadialDerivative, regularizedBlockNorm_zero] using
        (tendsto_regularizedWeylWeightDerivative (A x) (B x) (Z x) (V x)).comp hlim
    have hm : Tendsto (fun n => regularizedWeylWeight (ε n) (A x) (B x))
        atTop (𝓝 (regularizedWeylWeight 0 (A x) (B x))) := by
      simpa only [Function.comp_def, regularizedWeylWeight, regularizedBlockNorm_zero] using
        (tendsto_regularizedWeylWeight (A x) (B x)).comp hlim
    exact ((hd.pow 2).div hm (ne_of_gt
      (regularizedWeylWeight_pos 0 (by norm_num) (by norm_num) _ _ (hpinch x)))).mul
        tendsto_const_nhds

end
end PositiveEinsteinFour.Geometry
end


section

/-! Curvature contractions with the entire symmetric Weyl matrix.
No moving eigenframe enters these identities. -/

namespace PositiveEinsteinFour.CurvatureContraction

open scoped BigOperators
open Matrix TraceHessian Bianchi PositiveEinsteinFour.Geometry

noncomputable section

def generalGradientForm (A : Mat) (Z : Tensor) : ℝ :=
  rawPairing (generalMatrixAction A Z.matrix) Z.matrix

theorem generalGradientForm_diagonal (t : Fin 3 → ℝ) (Z : Tensor) (hz : Z.traceFree) :
    generalGradientForm (Matrix.diagonal t) Z = diagonalGradientForm t Z := by
  rw [generalGradientForm, generalMatrixAction_diagonal, rawMatrixCurvature_pairing t Z Z hz]
  simp only [diagonalGradientPairing, diagonalGradientForm, real_inner_self_eq_norm_sq]

theorem generalMixedAction_add (A B : Mat) (Z : RawGradient) :
    generalMixedAction (A + B) Z = generalMixedAction A Z + generalMixedAction B Z := by
  funext a b
  simp only [generalMixedAction, Matrix.add_apply, add_smul, Finset.sum_add_distrib,
    Pi.add_apply]

theorem generalMixedAction_smul (r : ℝ) (A : Mat) (Z : RawGradient) :
    generalMixedAction (r • A) Z = r • generalMixedAction A Z := by
  funext a b
  simp only [generalMixedAction, Matrix.smul_apply, smul_eq_mul, mul_smul,
    ← Finset.smul_sum, Pi.smul_apply]

theorem generalMixedAction_one (Z : RawGradient) :
    generalMixedAction 1 Z = rawCoupling Z := by
  funext a b
  simp only [generalMixedAction, Matrix.one_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, rawCoupling]

theorem generalMixedAction_self_pairing (A : Mat)
    (hs : symmetric A) (ht : traceFree A)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    rawPairing (generalMixedAction A Z.matrix) Z.matrix = 8 * generalGradientForm A Z :=
  generalMixedAction_pairing A hs ht Z Z hz hb hb

theorem rawCoupling_self_pairing (Z : Tensor) (hb : Z.bianchi) :
    rawPairing (rawCoupling Z.matrix) Z.matrix = -4 * Z.squaredNorm := by
  have hC : rawCoupling Z.matrix = (-4 : ℝ) • Z.matrix := by
    funext a b
    exact gradientCoupling_eq Z hb a b
  rw [hC, rawPairing_smul_left, rawPairing_vectors]
  simp only [real_inner_self_eq_norm_sq, Tensor.squaredNorm]

theorem generalMixedAction_square_pairing (A : Mat)
    (hs : symmetric A) (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    rawPairing (generalMixedAction (A * A) Z.matrix) Z.matrix =
      8 * generalGradientForm (traceFreeSquare A) Z -
        (4 / 3 : ℝ) * Matrix.trace (A * A) * Z.squaredNorm := by
  have he : A * A = traceFreeSquare A + (Matrix.trace (A * A) / 3) • (1 : Mat) := by
    rw [traceFreeSquare]
    abel
  conv_lhs => rw [he]
  rw [generalMixedAction_add, generalMixedAction_smul, generalMixedAction_one,
    rawPairing_add_left, rawPairing_smul_left,
    generalMixedAction_self_pairing _ (traceFreeSquare_symmetric A hs)
      (traceFreeSquare_traceFree A) Z hz hb, rawCoupling_self_pairing Z hb]
  ring

/-- This is the full bundle polynomial before adding the covector curvature.
It is an arbitrary-matrix identity on the actual Bianchi gradient. -/
theorem generalMixedAction_linear_square_pairing (A : Mat)
    (hs : symmetric A) (ht : traceFree A)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    -(1 / 2 : ℝ) * rawPairing (generalMixedAction (A + A * A) Z.matrix) Z.matrix =
      (2 / 3 : ℝ) * Matrix.trace (A * A) * Z.squaredNorm -
        4 * generalGradientForm A Z - 4 * generalGradientForm (traceFreeSquare A) Z := by
  rw [generalMixedAction_add, rawPairing_add_left,
    generalMixedAction_self_pairing A hs ht Z hz hb,
    generalMixedAction_square_pairing A hs Z hz hb]
  ring

/-- Both matrix indices are kept in the actual curvature coefficient. -/
def generalCoefficient (Q : Fin 3 → Mat4) (A : Mat)
    (i k j l : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * ∑ r, ∑ s, A r s * Q r i k * Q s j l

theorem generalCoefficient_eq_blockTensor (Q : Fin 3 → Mat4) (A : Mat)
    (i k j l : Fin 4) :
    generalCoefficient Q A i k j l = Angular.blockTensor A Q i k l j := by
  simp only [generalCoefficient, Angular.blockTensor, Angular.twoFormProduct,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

private theorem sum_four_swap {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  have h := (Equiv.prodComm (α × β) (γ × δ)).sum_comp
    (fun p : (γ × δ) × (α × β) => f p.2.1 p.2.2 p.1.1 p.1.2)
  simpa only [Fintype.sum_prod_type, Equiv.prodComm_apply, Prod.swap_prod_mk] using h

private theorem generalCoefficient_oneForm
    (Q P : Fin 3 → Mat4)
    (hQP : ∀ r t, (∑ i, ∑ k, Q r i k * P t i k) =
      if r = t then (4 : ℝ) else 0)
    (A : Mat) (t : Fin 3) (j l : Fin 4) :
    (∑ i, ∑ k, generalCoefficient Q A i k j l * P t i k) =
      2 * ∑ s, A t s * Q s j l := by
  simp only [generalCoefficient, Finset.mul_sum, Finset.sum_mul]
  rw [sum_four_swap]
  have hterm (r s : Fin 3) :
      (∑ i, ∑ k, (1 / 2 : ℝ) * (A r s * Q r i k * Q s j l) * P t i k) =
        (1 / 2 : ℝ) * A r s * Q s j l * (∑ i, ∑ k, Q r i k * P t i k) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [hterm, hQP]
  rw [Finset.sum_comm]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem generalCoefficient_plus_oneForm (A : Mat) (r : Fin 3) (j l : Fin 4) :
    (∑ i, ∑ k, generalCoefficient quaternionMatrix A i k j l * quaternionMatrix r i k) =
      2 * ∑ s, A r s * quaternionMatrix s j l :=
  generalCoefficient_oneForm _ _ plus_twoForm_pairing A r j l

theorem generalCoefficient_minus_oneForm (A : Mat) (r : Fin 3) (j l : Fin 4) :
    (∑ i, ∑ k, generalCoefficient Angular.oppositeMatrix A i k j l *
      quaternionMatrix r i k) = 0 := by
  simp only [generalCoefficient, Finset.mul_sum, Finset.sum_mul]
  rw [sum_four_swap]
  have hterm (s t : Fin 3) :
      (∑ i, ∑ k, (1 / 2 : ℝ) *
        (A s t * Angular.oppositeMatrix s i k * Angular.oppositeMatrix t j l) *
        quaternionMatrix r i k) =
      (1 / 2 : ℝ) * A s t * Angular.oppositeMatrix t j l *
        (∑ i, ∑ k, quaternionMatrix r i k * Angular.oppositeMatrix s i k) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [hterm, mixed_twoForm_pairing]
  simp

private theorem matrixPairing_bundle_general (A : Mat)
    (i k : Fin 4) (N P : Mat) :
    matrixPairing (bundleCurvatureAction A i k N) P =
      (1 / 2 : ℝ) * ∑ r, quaternionMatrix r i k *
        (matrixPairing (matrixAction r N) P +
          ∑ s, A r s * matrixPairing (matrixAction s N) P) := by
  change matrixPairingLinear P _ = _
  rw [bundleCurvatureAction, map_smul, map_sum]
  simp only [map_smul, map_add, map_sum, smul_eq_mul]
  rfl

/-- The two-form contraction is performed before the remaining
matrix-bundle action, so no diagonalization is used. -/
theorem weighted_bundle_general_pairing (K : Fin 4 → Fin 4 → ℝ)
    (b : Fin 3 → ℝ)
    (hK : ∀ r, (∑ i, ∑ k, K i k * quaternionMatrix r i k) = b r)
    (A : Mat) (N P : Mat) :
    (∑ i, ∑ k, K i k * matrixPairing (bundleCurvatureAction A i k N) P) =
      (1 / 2 : ℝ) * ∑ r, b r *
        (matrixPairing (matrixAction r N) P +
          ∑ s, A r s * matrixPairing (matrixAction s N) P) := by
  simp only [matrixPairing_bundle_general, Finset.mul_sum]
  calc
    _ = ∑ i, ∑ r, ∑ k, K i k * ((1 / 2 : ℝ) * quaternionMatrix r i k *
        (matrixPairing (matrixAction r N) P +
          ∑ s, A r s * matrixPairing (matrixAction s N) P)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ r, ∑ i, ∑ k, K i k * ((1 / 2 : ℝ) * quaternionMatrix r i k *
        (matrixPairing (matrixAction r N) P +
          ∑ s, A r s * matrixPairing (matrixAction s N) P)) := Finset.sum_comm
    _ = ∑ r, (1 / 2 : ℝ) *
        (matrixPairing (matrixAction r N) P +
          ∑ s, A r s * matrixPairing (matrixAction s N) P) *
        (∑ i, ∑ k, K i k * quaternionMatrix r i k) := by
      apply Finset.sum_congr rfl
      intro r _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      simp only [hK]
      apply Finset.sum_congr rfl
      intro r _
      ring


theorem generalCoefficient_bundle_pairing (K A : Mat)
    (j l : Fin 4) (N P : Mat) :
    (∑ i, ∑ k, generalCoefficient quaternionMatrix K i k j l *
      matrixPairing (bundleCurvatureAction A i k N) P) =
      ∑ r, ∑ s, K r s * quaternionMatrix s j l *
        (matrixPairing (matrixAction r N) P +
          ∑ t, A r t * matrixPairing (matrixAction t N) P) := by
  rw [weighted_bundle_general_pairing _
    (fun r => 2 * ∑ s, K r s * quaternionMatrix s j l)
    (fun r => generalCoefficient_plus_oneForm K r j l)]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem generalCoefficient_minus_bundle_pairing (K A : Mat)
    (j l : Fin 4) (N P : Mat) :
    (∑ i, ∑ k, generalCoefficient Angular.oppositeMatrix K i k j l *
      matrixPairing (bundleCurvatureAction A i k N) P) = 0 := by
  rw [weighted_bundle_general_pairing _ (fun _ => 0)
    (fun r => generalCoefficient_minus_oneForm K r j l)]
  simp

private theorem symmetric_product_expansion (A : Mat) (hs : symmetric A)
    (Q F : Fin 3 → ℝ) :
    (∑ r, ∑ s, A r s * Q s * (F r + ∑ t, A r t * F t)) =
      ∑ s, ∑ t, (A + A * A) s t * Q s * F t := by
  simp only [Fin.sum_univ_three, Matrix.add_apply, Matrix.mul_apply,
    hs 1 0, hs 2 0, hs 2 1]
  ring

/-- The product of the full Weyl block with the curvature connection
produces exactly A+A². -/
theorem plus_bundle_general_pairing (A : Mat) (hs : symmetric A)
    (j l : Fin 4) (N P : Mat) :
    (∑ i, ∑ k, generalCoefficient quaternionMatrix A i k j l *
      matrixPairing (bundleCurvatureAction A i k N) P) =
      ∑ r, ∑ s, (A + A * A) r s * quaternionMatrix r j l *
        matrixPairing (matrixAction s N) P := by
  rw [generalCoefficient_bundle_pairing]
  exact symmetric_product_expansion A hs (fun r => quaternionMatrix r j l)
    (fun s => matrixPairing (matrixAction s N) P)

private theorem quaternion_pairing_sum_general (r : Fin 3) (x y : Vec) :
    (∑ j, ∑ l, quaternionMatrix r j l * x j * y l) =
      -inner ℝ (quaternion r x) y := by
  rw [Finset.sum_comm]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [← quaternionMatrix_apply, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [quaternionMatrix_skew r j l]
  ring

private theorem matrixAction_mixed_slices_pairing (r s : Fin 3) (Z : Tensor) :
    (∑ j, ∑ l, quaternionMatrix r j l *
      matrixPairing (matrixAction s (rawMatrixSlice Z.matrix j))
        (rawMatrixSlice Z.matrix l)) =
      -(∑ a, ∑ b, inner ℝ (quaternion r (matrixRotation s Z a b)) (Z.matrix a b)) := by
  simp only [matrixPairing, Finset.mul_sum, rawMatrixSlice, matrixRotation_slice]
  rw [sum_four_swap]
  simp only [← mul_assoc, quaternion_pairing_sum_general, Finset.sum_neg_distrib]

theorem generalMixedAction_pairing_sum (A : Mat) (Z : Tensor) :
    rawPairing (generalMixedAction A Z.matrix) Z.matrix =
      ∑ r, ∑ s, A r s *
        (∑ a, ∑ b, inner ℝ (quaternion r (matrixRotation s Z a b)) (Z.matrix a b)) := by
  simp only [rawPairing_vectors, generalMixedAction, rawMatrixRotation_matrix,
    sum_inner, real_inner_smul_left]
  rw [sum_four_swap]
  simp only [Finset.mul_sum]

def generalBundleGreenContraction
    (K : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (A : Mat) (Z : Tensor) : ℝ :=
  (1 / 2 : ℝ) * ∑ j, ∑ l, ∑ i, ∑ k, K i k j l *
    matrixPairing (bundleCurvatureAction A i k (rawMatrixSlice Z.matrix j))
      (rawMatrixSlice Z.matrix l)

/-- The complete bundle half-commutator in an arbitrary orthonormal frame. -/
theorem generalBundleGreenContraction_plus (A : Mat) (hs : symmetric A) (Z : Tensor) :
    generalBundleGreenContraction (generalCoefficient quaternionMatrix A) A Z =
      -(1 / 2 : ℝ) * rawPairing (generalMixedAction (A + A * A) Z.matrix) Z.matrix := by
  simp only [generalBundleGreenContraction, plus_bundle_general_pairing A hs]
  rw [sum_four_swap]
  have hterm (r s : Fin 3) :
      (∑ j, ∑ l, (A + A * A) r s * quaternionMatrix r j l *
        matrixPairing (matrixAction s (rawMatrixSlice Z.matrix j))
          (rawMatrixSlice Z.matrix l)) =
      -((A + A * A) r s *
        (∑ a, ∑ b, inner ℝ (quaternion r (matrixRotation s Z a b)) (Z.matrix a b))) := by
    calc
      _ = (A + A * A) r s * (∑ j, ∑ l, quaternionMatrix r j l *
          matrixPairing (matrixAction s (rawMatrixSlice Z.matrix j))
            (rawMatrixSlice Z.matrix l)) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = _ := by rw [matrixAction_mixed_slices_pairing]; ring
  simp_rw [hterm]
  simp only [Finset.sum_neg_distrib]
  rw [generalMixedAction_pairing_sum]
  ring

theorem generalBundleGreenContraction_minus (U A : Mat) (Z : Tensor) :
    generalBundleGreenContraction (generalCoefficient Angular.oppositeMatrix U) A Z = 0 := by
  simp only [generalBundleGreenContraction, generalCoefficient_minus_bundle_pairing,
    Finset.sum_const_zero, mul_zero]

theorem generalBundleGreenContraction_polynomial (A : Mat)
    (hs : symmetric A) (ht : traceFree A)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    generalBundleGreenContraction (generalCoefficient quaternionMatrix A) A Z =
      (2 / 3 : ℝ) * Matrix.trace (A * A) * Z.squaredNorm -
        4 * generalGradientForm A Z - 4 * generalGradientForm (traceFreeSquare A) Z := by
  rw [generalBundleGreenContraction_plus A hs]
  exact generalMixedAction_linear_square_pairing A hs ht Z hz hb

private theorem clifford_column_pairing
    (Q : Fin 3 → Mat4)
    (hskew : ∀ s, (Q s)ᵀ = -Q s)
    (hanti : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Mat4))
    (r s : Fin 3) (l h : Fin 4) :
    (∑ j, Q r j l * Q s j h) + (∑ j, Q s j l * Q r j h) =
      (if r = s then (2 : ℝ) else 0) * (if l = h then 1 else 0) := by
  have hs (t : Fin 3) (j : Fin 4) : Q t l j = -Q t j l := by
    have hx := congrArg (fun M : Mat4 => M j l) (hskew t)
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using hx
  have ha := congrArg (fun M : Mat4 => M l h) (hanti r s)
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, hs, neg_mul, Finset.sum_neg_distrib] at ha
  by_cases hrs : r = s <;> simp only [hrs, ite_true, ite_false] at * <;> linarith

/-- A symmetric coefficient contracts the Clifford product to its trace.
This includes all off-diagonal matrix entries. -/
theorem symmetric_clifford_column_contraction
    (Q : Fin 3 → Mat4)
    (hskew : ∀ s, (Q s)ᵀ = -Q s)
    (hanti : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Mat4))
    (C : Mat) (hC : symmetric C) (l h : Fin 4) :
    (∑ r, ∑ s, C r s * (∑ j, Q r j l * Q s j h)) =
      Matrix.trace C * (if l = h then 1 else 0) := by
  have hswap : (∑ r, ∑ s, C r s * (∑ j, Q s j l * Q r j h)) =
      ∑ r, ∑ s, C r s * (∑ j, Q r j l * Q s j h) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [hC s r]
  have hd : (∑ r, ∑ s, C r s *
      ((∑ j, Q r j l * Q s j h) + (∑ j, Q s j l * Q r j h))) =
      2 * Matrix.trace C * (if l = h then 1 else 0) := by
    simp_rw [clifford_column_pairing Q hskew hanti]
    by_cases hlh : l = h
    · simp only [hlh, ite_true, mul_one, mul_ite, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, Matrix.trace, Matrix.diag]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    · simp only [hlh, ite_false, mul_zero, Finset.sum_const_zero]
  simp only [mul_add, Finset.sum_add_distrib, hswap] at hd
  linarith

private theorem pair_generalCoefficient (K : Mat4) (Q : Fin 3 → Mat4)
    (B : Mat) (h n : Fin 4) :
    (∑ i, ∑ k, K i k * generalCoefficient Q B i k h n) =
      (1 / 2 : ℝ) * ∑ r, ∑ s, B r s * Q s h n *
        (∑ i, ∑ k, K i k * Q r i k) := by
  simp only [generalCoefficient, Finset.mul_sum]
  rw [sum_four_swap]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem generalCoefficient_pairing
    (Q : Fin 3 → Mat4)
    (hQ : ∀ r s, (∑ i, ∑ k, Q r i k * Q s i k) =
      if r = s then (4 : ℝ) else 0)
    (A B : Mat) (j l h n : Fin 4) :
    (∑ i, ∑ k, generalCoefficient Q A i k j l * generalCoefficient Q B i k h n) =
      ∑ r, ∑ s, (Aᵀ * B) r s * Q r j l * Q s h n := by
  rw [pair_generalCoefficient (fun i k => generalCoefficient Q A i k j l) Q B h n]
  simp_rw [generalCoefficient_oneForm Q Q hQ]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  ring

private theorem generalCoefficient_pairing_zero
    (Q P : Fin 3 → Mat4)
    (hQP : ∀ r s, (∑ i, ∑ k, Q r i k * P s i k) = 0)
    (A B : Mat) (j l h n : Fin 4) :
    (∑ i, ∑ k, generalCoefficient Q A i k j l * generalCoefficient P B i k h n) = 0 := by
  rw [pair_generalCoefficient (fun i k => generalCoefficient Q A i k j l) P B h n]
  have hz (r : Fin 3) :
      (∑ i, ∑ k, generalCoefficient Q A i k j l * P r i k) = 0 := by
    simp only [generalCoefficient, Finset.mul_sum, Finset.sum_mul]
    rw [sum_four_swap]
    have ht (s t : Fin 3) :
        (∑ i, ∑ k, (1 / 2 : ℝ) * (A s t * Q s i k * Q t j l) * P r i k) =
          (1 / 2 : ℝ) * A s t * Q t j l * (∑ i, ∑ k, Q s i k * P r i k) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring
    simp_rw [ht, hQP]
    simp
  simp only [hz, mul_zero, Finset.sum_const_zero]

private theorem generalCoefficient_ricci
    (Q : Fin 3 → Mat4)
    (hQ : ∀ r s, (∑ i, ∑ k, Q r i k * Q s i k) =
      if r = s then (4 : ℝ) else 0)
    (hskew : ∀ s, (Q s)ᵀ = -Q s)
    (hanti : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Mat4))
    (A B : Mat) (hAB : symmetric (Aᵀ * B)) (l h : Fin 4) :
    (∑ j, ∑ i, ∑ k, generalCoefficient Q A i k j l * generalCoefficient Q B i k j h) =
      Matrix.trace (Aᵀ * B) * (if l = h then 1 else 0) := by
  simp_rw [generalCoefficient_pairing Q hQ]
  calc
    _ = ∑ r, ∑ j, ∑ s, (Aᵀ * B) r s * Q r j l * Q s j h := Finset.sum_comm
    _ = ∑ r, ∑ s, (Aᵀ * B) r s * (∑ j, Q r j l * Q s j h) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum, mul_assoc]
    _ = _ := symmetric_clifford_column_contraction Q hskew hanti _ hAB l h

private theorem transpose_mul_one_add (A : Mat) (hs : symmetric A) :
    Aᵀ * (1 + A) = A + A * A := by
  have hAt : Aᵀ = A := by ext a b; exact hs b a
  rw [hAt, Matrix.mul_add, Matrix.mul_one]

private theorem symmetric_add_square (A : Mat) (hs : symmetric A) :
    symmetric (A + A * A) := by
  have hAt : Aᵀ = A := by ext a b; exact hs b a
  have h := show (A + A * A)ᵀ = A + A * A by
    simp only [Matrix.transpose_add, Matrix.transpose_mul, hAt]
  intro a b
  exact congrArg (fun M : Mat => M b a) h

/-- The covector contraction of the full plus block gives its squared
matrix norm, including all off-diagonal entries. -/
theorem plus_generalCoefficient_ricci (A U : Mat)
    (hs : symmetric A) (ht : traceFree A) (l h : Fin 4) :
    (1 / 2 : ℝ) * (∑ j, ∑ i, ∑ k, generalCoefficient quaternionMatrix A i k j l *
      (generalCoefficient quaternionMatrix (1 + A) i k j h +
        generalCoefficient Angular.oppositeMatrix (1 + U) i k j h)) =
      (Matrix.trace (A * A) / 2) * (if l = h then 1 else 0) := by
  simp only [mul_add, Finset.sum_add_distrib]
  have hz (j : Fin 4) := generalCoefficient_pairing_zero _ _ mixed_twoForm_pairing
    A (1 + U) j l j h
  simp_rw [hz]
  simp only [Finset.sum_const_zero, mul_zero, add_zero]
  have hAB : symmetric (Aᵀ * (1 + A)) := by
    rw [transpose_mul_one_add A hs]
    exact symmetric_add_square A hs
  rw [generalCoefficient_ricci quaternionMatrix plus_twoForm_pairing
    Angular.quaternionMatrix_transpose Angular.quaternionMatrix_anticommutator _ _ hAB,
    transpose_mul_one_add A hs, Matrix.trace_add]
  have htrace : Matrix.trace A = 0 := ht
  rw [htrace]
  ring

private theorem oppositeMatrix_transpose (r : Fin 3) :
    (Angular.oppositeMatrix r)ᵀ = -Angular.oppositeMatrix r := by
  ext i j
  change Geometry.oppositeQuaternion r j i = -Geometry.oppositeQuaternion r i j
  fin_cases r <;> fin_cases i <;> fin_cases j <;>
    norm_num [Geometry.oppositeQuaternion, quaternionMatrix]

theorem minus_generalCoefficient_ricci (A U : Mat)
    (hs : symmetric U) (ht : traceFree U) (l h : Fin 4) :
    (1 / 2 : ℝ) * (∑ j, ∑ i, ∑ k, generalCoefficient Angular.oppositeMatrix U i k j l *
      (generalCoefficient quaternionMatrix (1 + A) i k j h +
        generalCoefficient Angular.oppositeMatrix (1 + U) i k j h)) =
      (Matrix.trace (U * U) / 2) * (if l = h then 1 else 0) := by
  simp only [mul_add, Finset.sum_add_distrib]
  have hQP (r s : Fin 3) :
      (∑ i, ∑ k, Angular.oppositeMatrix r i k * quaternionMatrix s i k) = 0 := by
    simpa only [mul_comm] using mixed_twoForm_pairing s r
  have hz (j : Fin 4) := generalCoefficient_pairing_zero _ _ hQP
    U (1 + A) j l j h
  simp_rw [hz]
  simp only [Finset.sum_const_zero, mul_zero, zero_add]
  have hAB : symmetric (Uᵀ * (1 + U)) := by
    rw [transpose_mul_one_add U hs]
    exact symmetric_add_square U hs
  rw [generalCoefficient_ricci Angular.oppositeMatrix opposite_twoForm_pairing
    oppositeMatrix_transpose Angular.oppositeMatrix_anticommutator _ _ hAB,
    transpose_mul_one_add U hs, Matrix.trace_add]
  have htrace : Matrix.trace U = 0 := ht
  rw [htrace]
  ring

def generalEinsteinCoefficient (A U : Mat) (i k j l : Fin 4) : ℝ :=
  generalCoefficient quaternionMatrix (1 + A) i k j l +
    generalCoefficient Angular.oppositeMatrix (1 + U) i k j l

theorem generalEinsteinCoefficient_eq_tensor (A U : Mat) (i k j l : Fin 4) :
    generalEinsteinCoefficient A U i k j l =
      Angular.einsteinCurvatureTensor A U i k l j := by
  simp only [generalEinsteinCoefficient, generalCoefficient_eq_blockTensor,
    Angular.einsteinCurvatureTensor, Pi.add_apply]

theorem generalCovectorGreenContraction_plus (A U : Mat)
    (hs : symmetric A) (ht : traceFree A) (Z : Tensor) :
    covectorGreenContraction (generalCoefficient quaternionMatrix A)
      (generalEinsteinCoefficient A U) Z =
        (Matrix.trace (A * A) / 2) * Z.squaredNorm := by
  simp only [covectorGreenContraction, generalEinsteinCoefficient,
    plus_generalCoefficient_ricci A U hs ht]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.mul_sum, matrixSlice_self_sum]

theorem generalCovectorGreenContraction_minus (A U : Mat)
    (hs : symmetric U) (ht : traceFree U) (Z : Tensor) :
    covectorGreenContraction (generalCoefficient Angular.oppositeMatrix U)
      (generalEinsteinCoefficient A U) Z =
        (Matrix.trace (U * U) / 2) * Z.squaredNorm := by
  simp only [covectorGreenContraction, generalEinsteinCoefficient,
    minus_generalCoefficient_ricci A U hs ht]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.mul_sum, matrixSlice_self_sum]

/-- Both actual curvature actions in the plus derivative Green term,
with the full symmetric Weyl coefficient matrix. -/
theorem general_plus_green_polynomial (A U : Mat)
    (hs : symmetric A) (ht : traceFree A)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    generalBundleGreenContraction (generalCoefficient quaternionMatrix A) A Z +
      covectorGreenContraction (generalCoefficient quaternionMatrix A)
        (generalEinsteinCoefficient A U) Z =
      (7 / 6 : ℝ) * Matrix.trace (A * A) * Z.squaredNorm -
        4 * generalGradientForm A Z - 4 * generalGradientForm (traceFreeSquare A) Z := by
  rw [generalBundleGreenContraction_polynomial A hs ht Z hz hb,
    generalCovectorGreenContraction_plus A U hs ht]
  ring

theorem general_minus_green_polynomial (A U : Mat)
    (hs : symmetric U) (ht : traceFree U) (Z : Tensor) :
    generalBundleGreenContraction (generalCoefficient Angular.oppositeMatrix U) A Z +
      covectorGreenContraction (generalCoefficient Angular.oppositeMatrix U)
        (generalEinsteinCoefficient A U) Z =
        (Matrix.trace (U * U) / 2) * Z.squaredNorm := by
  rw [generalBundleGreenContraction_minus, zero_add,
    generalCovectorGreenContraction_minus A U hs ht]


/-- The two raw curvature actions in the commutator of a covariant
Weyl gradient, with an arbitrary matrix in the Weyl bundle slot. -/
def generalRawCurvatureCommutator (A : Mat)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (Z : Tensor)
    (i k j : Fin 4) : Mat :=
  bundleCurvatureAction A i k (rawMatrixSlice Z.matrix j) +
    ∑ h, R i k j h • rawMatrixSlice Z.matrix h

private theorem sum_last_first_general {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := by
  calc
    _ = ∑ a, ∑ b, ∑ d, ∑ c, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

/-- The actual raw commutator contracts to the already computed bundle
and covector terms before any scalar estimate is applied. -/
theorem general_rawGreen_decomposition
    (K R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (A : Mat) (Z : Tensor) :
    derivativeGreenContraction K (generalRawCurvatureCommutator A R Z) Z =
      generalBundleGreenContraction K A Z + covectorGreenContraction K R Z := by
  unfold derivativeGreenContraction
  rw [sum_four_swap]
  simp only [generalRawCurvatureCommutator, matrixPairing_add_left,
    matrixPairing_sum_smul_left, mul_add, Finset.sum_add_distrib]
  change generalBundleGreenContraction K A Z + _ = _
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hs (l : Fin 4) :
      (∑ j, ∑ i, ∑ k, ∑ h, (1 / 2 : ℝ) * (K i k j l *
        (R i k j h * matrixPairing (rawMatrixSlice Z.matrix h) (rawMatrixSlice Z.matrix l)))) =
      ∑ h, ∑ j, ∑ i, ∑ k, (1 / 2 : ℝ) * (K i k j l *
        (R i k j h * matrixPairing (rawMatrixSlice Z.matrix h) (rawMatrixSlice Z.matrix l))) :=
    sum_last_first_general _
  simp only [hs, covectorGreenContraction, Finset.mul_sum, Finset.sum_mul, mul_assoc]

/-- The complete self-dual raw Green contraction has the invariant
polynomial required by the weighted Hessian estimate. -/
theorem general_plus_rawGreen (A U : Mat)
    (hs : symmetric A) (ht : traceFree A)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    derivativeGreenContraction (generalCoefficient quaternionMatrix A)
      (generalRawCurvatureCommutator A (generalEinsteinCoefficient A U) Z) Z =
      (7 / 6 : ℝ) * Matrix.trace (A * A) * Z.squaredNorm -
        4 * generalGradientForm A Z - 4 * generalGradientForm (traceFreeSquare A) Z := by
  rw [general_rawGreen_decomposition]
  exact general_plus_green_polynomial A U hs ht Z hz hb

theorem general_minus_rawGreen (A U : Mat)
    (hs : symmetric U) (ht : traceFree U) (Z : Tensor) :
    derivativeGreenContraction (generalCoefficient Angular.oppositeMatrix U)
      (generalRawCurvatureCommutator A (generalEinsteinCoefficient A U) Z) Z =
        (Matrix.trace (U * U) / 2) * Z.squaredNorm := by
  rw [general_rawGreen_decomposition]
  exact general_minus_green_polynomial A U hs ht Z

end
end PositiveEinsteinFour.CurvatureContraction
end


section

/-! The Ricci equation and its identity and varying-matrix Green
contractions in the actual arbitrary orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance metricContractionNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricContractionNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricContractionNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

theorem gradientVector_pairing (Z W : Angular.Gradient) :
    inner ℝ (gradientVector Z) (gradientVector W) = ∑ i, matrixPairing (Z i) (W i) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    gradientVector, Fintype.sum_prod_type, matrixPairing]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem gradientTensor_pairing (Z W : Angular.Gradient)
    (hZ : ∀ i, symmetric (Z i)) (hW : ∀ i, symmetric (W i)) :
    rawPairing (gradientTensor Z).matrix (gradientTensor W).matrix =
      ∑ i, matrixPairing (Z i) (W i) := by
  rw [← inner_rawGradientVector]
  change inner ℝ (tensorGradientVector (gradientTensor Z))
    (tensorGradientVector (gradientTensor W)) = _
  rw [tensorGradientVector_gradientTensor Z hZ, tensorGradientVector_gradientTensor W hW,
    gradientVector_pairing]

theorem generalMatrixAction_gradientVector (A : Mat) (Z : Angular.Gradient)
    (hZ : ∀ i, symmetric (Z i)) :
    rawGradientVector (generalMatrixAction A (gradientTensor Z).matrix) =
      gradientVector (fun i => matrixSlotAction A (Z i)) := by
  ext p
  rcases p with ⟨i, a, b⟩
  change matrixSlotAction A (rawMatrixSlice (gradientTensor Z).matrix i) a b = _
  rw [rawMatrixSlice_gradientTensor Z hZ]
  rfl

theorem generalMatrixAction_gradient_pairing (A : Mat) (Z : Angular.Gradient)
    (hZ : ∀ i, symmetric (Z i)) :
    rawPairing (generalMatrixAction A (gradientTensor Z).matrix) (gradientTensor Z).matrix =
      6 * weylMatrixEnergy A Z := by
  rw [← inner_rawGradientVector, generalMatrixAction_gradientVector A Z hZ]
  change inner ℝ (gradientVector (fun i => matrixSlotAction A (Z i)))
    (tensorGradientVector (gradientTensor Z)) = _
  rw [tensorGradientVector_gradientTensor Z hZ, gradientVector_pairing]
  unfold weylMatrixEnergy
  ring

/-- The true Bianchi compression energy, before any spectral coordinates. -/
def weylCompressionEnergy (A : Mat) (Z : Angular.Gradient) : ℝ :=
  rawPairing (rawBianchiProjection (generalMatrixAction A (gradientTensor Z).matrix))
    (rawBianchiProjection (generalMatrixAction A (gradientTensor Z).matrix)) / 6

theorem gradientTensor_ricci_compressed (A : Mat) (hA : symmetric A) (hAt : traceFree A)
    (Z L : Angular.Gradient) (hZ : ∀ i, symmetric (Z i))
    (htZ : ∀ i, traceFree (Z i)) (hbZ : ∀ a b, gradientDivergence Z a b = 0)
    (hL : ∀ i, symmetric (L i)) (hRicci : L = invariantRicciGradient A Z) :
    (gradientTensor L).matrix = (13 : ℝ) • (gradientTensor Z).matrix -
      (20 : ℝ) • rawBianchiProjection (generalMatrixAction A (gradientTensor Z).matrix) := by
  have hc := invariantRicciGradient_compressed A hA hAt (gradientTensor Z)
    (gradientTensor_traceFree Z htZ) (gradientTensor_bianchi Z hZ hbZ)
  have hs : (fun i => rawMatrixSlice (gradientTensor Z).matrix i) = Z :=
    funext (rawMatrixSlice_gradientTensor Z hZ)
  rw [hs] at hc
  have he := hRicci.trans hc
  funext a b
  ext i
  rw [gradientTensor_matrix L hL]
  exact congrArg (fun F : Angular.Gradient => F i a b) he

/-- The identity contraction is valid without diagonalizing the Weyl block. -/
theorem invariant_ricci_identity_scalar (A : Mat) (hA : symmetric A) (hAt : traceFree A)
    (Z L : Angular.Gradient) (hZ : ∀ i, symmetric (Z i))
    (htZ : ∀ i, traceFree (Z i)) (hbZ : ∀ a b, gradientDivergence Z a b = 0)
    (hRicci : L = invariantRicciGradient A Z) :
    inner ℝ (gradientVector Z) (gradientVector L) / 6 =
      13 * weylGradientEnergy Z - 20 * weylMatrixEnergy A Z := by
  have hc := invariantRicciGradient_pairing A hA hAt (gradientTensor Z) (gradientTensor Z)
    (gradientTensor_traceFree Z htZ) (gradientTensor_bianchi Z hZ hbZ)
    (gradientTensor_bianchi Z hZ hbZ)
  have hs : (fun i => rawMatrixSlice (gradientTensor Z).matrix i) = Z :=
    funext (rawMatrixSlice_gradientTensor Z hZ)
  rw [hs, tensorGradientVector_gradientTensor Z hZ,
    gradientTensor_pairing Z Z hZ hZ, generalMatrixAction_gradient_pairing A Z hZ] at hc
  rw [hRicci, real_inner_comm, hc]
  unfold weylGradientEnergy
  ring

/-- The normalized varying-matrix main term, with its actual projected
energy and no diagonal-frame or extra compression-energy premise. -/
theorem invariant_ricci_matrix_scalar (A : Mat) (hA : symmetric A) (hAt : traceFree A)
    (Z L : Angular.Gradient) (hZ : ∀ i, symmetric (Z i))
    (htZ : ∀ i, traceFree (Z i)) (hbZ : ∀ a b, gradientDivergence Z a b = 0)
    (hL : ∀ i, symmetric (L i)) (hbL : ∀ a b, gradientDivergence L a b = 0)
    (hRicci : L = invariantRicciGradient A Z) :
    (-inner ℝ (gradientVector Z) (matrixSlotOperator A (gradientVector L)) +
      (1 / 2 : ℝ) * inner ℝ (gradientVector Z)
        (matrixSlotOperator (weylLaplacian A) (gradientVector Z))) / 6 =
      -10 * weylMatrixEnergy A Z - 3 * weylMatrixEnergy (traceFreeSquare A) Z +
        20 * weylCompressionEnergy A Z := by
  have hc := matrixSlot_laplacian_pairing A (gradientTensor Z) (gradientTensor L)
    (gradientTensor_traceFree Z htZ) (gradientTensor_bianchi Z hZ hbZ)
    (gradientTensor_bianchi L hL hbL)
    (gradientTensor_ricci_compressed A hA hAt Z L hZ htZ hbZ hL hRicci)
  rw [tensorGradientVector_gradientTensor L hL, tensorGradientVector_gradientTensor Z hZ,
    generalMatrixAction_gradient_pairing A Z hZ] at hc
  have hslot (B : Mat) :
      inner ℝ (matrixSlotOperator B (gradientVector Z)) (gradientVector Z) =
        6 * weylMatrixEnergy B Z := by
    rw [← tensorGradientVector_gradientTensor Z hZ,
      matrixSlotOperator_general_pairing B _ (gradientTensor_traceFree Z htZ),
      generalMatrixAction_gradient_pairing B Z hZ]
  have hm := matrix_green_main_terms A hA (gradientVector Z) (gradientVector L)
    (rawPairing (rawBianchiProjection (generalMatrixAction A (gradientTensor Z).matrix))
      (rawBianchiProjection (generalMatrixAction A (gradientTensor Z).matrix)))
    (by rw [real_inner_comm, hslot A]; exact hc)
  rw [hm, hslot A, hslot (traceFreeSquare A)]
  unfold weylCompressionEnergy
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem identityScalar (d : MetricGreenData g μ) (e : FrameBundle g) :
    inner ℝ (frameGradientVector g e) (frameGradientLaplacian g e) / 6 =
      13 * weylGradientEnergy (plusWeylGradient g e.base e.frame) -
        20 * weylMatrixEnergy (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame) := by
  rw [d.laplacianVector e]
  exact invariant_ricci_identity_scalar _ (d.weyl.symmetric e) (d.weyl.traceFree e)
    _ _ (d.gradientConstraints e).1 (d.gradientConstraints e).2
    (d.gradientBianchi e) (d.ricciGradient e)

theorem matrixScalar (d : MetricGreenData g μ) (e : FrameBundle g) :
    (-inner ℝ (frameGradientVector g e)
        (matrixSlotOperator (frameWeylMatrix g e) (frameGradientLaplacian g e)) +
      (1 / 2 : ℝ) * inner ℝ (frameGradientVector g e)
        (∑ i, matrixSlotOperator (frameWeylHessianMatrix g i i e)
          (frameGradientVector g e))) / 6 =
      -10 * weylMatrixEnergy (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) -
      3 * weylMatrixEnergy (traceFreeSquare (plusWeyl g e.base e.frame))
        (plusWeylGradient g e.base e.frame) +
      20 * weylCompressionEnergy (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) := by
  rw [d.laplacianVector e]
  have hx : (∑ i, matrixSlotOperator (frameWeylHessianMatrix g i i e)
      (frameGradientVector g e)) =
      matrixSlotOperator (weylLaplacian (plusWeyl g e.base e.frame))
        (frameGradientVector g e) := by
    change (∑ i, matrixSlotOperator (plusWeylHessian g e.base e.frame i i)
      (frameGradientVector g e)) = _
    rw [matrixSlotAt_sum_trace, metric_weyl_trace g d.weyl e]
  rw [hx]
  exact invariant_ricci_matrix_scalar _ (d.weyl.symmetric e) (d.weyl.traceFree e)
    _ _ (d.gradientConstraints e).1 (d.gradientConstraints e).2
    (d.gradientBianchi e) (d.laplacianConstraints e).1
    (d.laplacianConstraints e).2.2 (d.ricciGradient e)

/-- The first Green integral for the metric Hessian, with the invariant
first-derivative scalar substituted. -/
theorem identityGreen (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hm : ∀ i t e, HasDerivAt (fun s => m ((d.flow i).map s e))
      (dm i ((d.flow i).map t e)) t) :
    (∫ e, weightedQuadratic hessianNormSq (m e) (plusWeylHessian g e.base e.frame)
      (weightTensor (WithLp.toLp 2 (fun i => dm i e))
        (plusGradientTensor g e.base e.frame)) ∂μ) =
    ∫ e, m e * (-13 * weylGradientEnergy (plusWeylGradient g e.base e.frame) +
      20 * weylMatrixEnergy (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame)) ∂μ := by
  have hgreen := weighted_metric_hessian_green g d.flow m dm
    d.continuousGradientVector d.continuousHessianVector
    (fun i => d.continuousThirdVector i i) hm
    d.derivativeGradientVector d.derivativeHessianVector
  calc
    _ = (1 / 6 : ℝ) * (∫ e, m e * hessianNormSq (plusWeylHessian g e.base e.frame) +
        ∑ i, dm i e * inner ℝ (frameGradientVector g e) (frameHessianVector g i e) ∂μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with e
      rw [weightedQuadratic_identity_green]
      simp only [plusGradientTensor, tensorGradientVector_gradientTensor _
        (d.gradientConstraints e).1]
      simp only [frameGradientVector, frameHessianVector]
      ring
    _ = (1 / 6 : ℝ) * (-(∫ e, m e *
        inner ℝ (frameGradientVector g e) (frameGradientLaplacian g e) ∂μ)) := by rw [hgreen]
    _ = _ := by
      rw [mul_neg, ← integral_const_mul, ← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with e
      have h := d.identityScalar e
      linear_combination -(m e) * h

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth approximation of the scalar deficit δ=2-v-b used in the
energy Bochner identity. -/

namespace PositiveEinsteinFour.Geometry

open TraceHessian Filter
open scoped Topology

noncomputable section

local instance deficitNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance deficitNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance deficitNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

def regularizedDeficit (ε : ℝ) (A B : Mat) : ℝ :=
  2 - regularizedBlockNorm ε A - regularizedBlockNorm ε B

def regularizedDeficitDerivative (ε : ℝ) (A B Z V : Mat) : ℝ :=
  -regularizedRadialDerivative ε A Z - regularizedRadialDerivative ε B V

theorem hasDerivAt_regularizedDeficit {A B : ℝ → Mat} {Z V : Mat} {t ε : ℝ}
    (hA : HasDerivAt A Z t) (hB : HasDerivAt B V t)
    (hsA : ∀ t, symmetric (A t)) (hsB : ∀ t, symmetric (B t)) (hε : 0 < ε) :
    HasDerivAt (fun s => regularizedDeficit ε (A s) (B s))
      (regularizedDeficitDerivative ε (A t) (B t) Z V) t := by
  convert! ((hasDerivAt_const t (2 : ℝ)).sub (hasDerivAt_regularizedBlockNorm hA hsA hε)).sub
    (hasDerivAt_regularizedBlockNorm hB hsB hε) using 1
  simp only [regularizedDeficitDerivative, zero_sub]

theorem abs_regularizedDeficit_le {ε : ℝ} (hε : 0 ≤ ε) (he : ε ≤ 1)
    (A B : Mat) (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    |regularizedDeficit ε A B| ≤ 6 := by
  have ha := regularizedBlockNorm_le ε hε A
  have hb := regularizedBlockNorm_le ε hε B
  have ha0 : 0 ≤ regularizedBlockNorm ε A := Real.sqrt_nonneg _
  have hb0 : 0 ≤ regularizedBlockNorm ε B := Real.sqrt_nonneg _
  have h := (abs_sub (2 - regularizedBlockNorm ε A) (regularizedBlockNorm ε B)).trans
    (add_le_add (abs_sub (2 : ℝ) (regularizedBlockNorm ε A)) (le_refl _))
  simp only [abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
    abs_of_nonneg ha0, abs_of_nonneg hb0] at h
  exact h.trans (by linarith)

theorem abs_regularizedDeficitDerivative_le {ε : ℝ} (hε : 0 < ε)
    (A B Z V : Mat) (hZ : symmetric Z) (hV : symmetric V) :
    |regularizedDeficitDerivative ε A B Z V| ≤ normalizedBlockNorm Z + normalizedBlockNorm V := by
  unfold regularizedDeficitDerivative
  exact (abs_sub _ _).trans (by
    rw [abs_neg]
    exact add_le_add (abs_regularizedRadialDerivative_le ε hε A Z hZ)
      (abs_regularizedRadialDerivative_le ε hε B V hV))

theorem tendsto_regularizedDeficit (A B : Mat) :
    Tendsto (fun ε => regularizedDeficit ε A B) (𝓝 0) (𝓝 (regularizedDeficit 0 A B)) := by
  simpa only [regularizedDeficit, regularizedBlockNorm_zero] using
    (tendsto_const_nhds.sub (tendsto_regularizedBlockNorm A)).sub (tendsto_regularizedBlockNorm B)

theorem tendsto_regularizedDeficitDerivative (A B Z V : Mat) :
    Tendsto (fun ε => regularizedDeficitDerivative ε A B Z V) (𝓝 0)
      (𝓝 (regularizedDeficitDerivative 0 A B Z V)) := by
  simpa only [regularizedDeficitDerivative, regularizedRadialDerivative, regularizedBlockNorm_zero] using
    (tendsto_regularizedRadialDerivative A Z).neg.sub (tendsto_regularizedRadialDerivative B V)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Mixed entries of the regularized weight cost. These are the finite
matrix entries needed by the actual orthogonal-projection quadratic form. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter TraceHessian
open scoped Topology

noncomputable section

local instance mixedWeightNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance mixedWeightNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance mixedWeightNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

theorem regularized_weight_mixed_cost_le
    (ε : ℝ) (hε : 0 < ε) (he : ε ≤ 1 / 3) (A B Z₁ Z₂ V₁ V₂ : Mat)
    (hsZ₁ : symmetric Z₁) (hsZ₂ : symmetric Z₂)
    (hsV₁ : symmetric V₁) (hsV₂ : symmetric V₂)
    (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    |regularizedWeylWeightDerivative ε A B Z₁ V₁ *
      regularizedWeylWeightDerivative ε A B Z₂ V₂ / regularizedWeylWeight ε A B| ≤
      144 * (normalizedBlockNorm Z₁ + normalizedBlockNorm V₁) *
        (normalizedBlockNorm Z₂ + normalizedBlockNorm V₂) := by
  have hp := regularizedWeylWeight_pos ε hε.le he A B hpinch
  have hm := (regularizedWeylWeight_bounds ε hε.le he A B hpinch).1
  have h₁ := abs_regularizedWeylWeightDerivative_le ε hε he A B Z₁ V₁ hsZ₁ hsV₁ hpinch
  have h₂ := abs_regularizedWeylWeightDerivative_le ε hε he A B Z₂ V₂ hsZ₂ hsV₂ hpinch
  have hn₁ : 0 ≤ normalizedBlockNorm Z₁ + normalizedBlockNorm V₁ :=
    add_nonneg (normalizedBlockNorm_nonneg _) (normalizedBlockNorm_nonneg _)
  have hn₂ : 0 ≤ normalizedBlockNorm Z₂ + normalizedBlockNorm V₂ :=
    add_nonneg (normalizedBlockNorm_nonneg _) (normalizedBlockNorm_nonneg _)
  rw [abs_div, abs_mul, abs_of_pos hp, div_le_iff₀ hp]
  calc
    _ ≤ ((3 / 2 : ℝ) * (normalizedBlockNorm Z₁ + normalizedBlockNorm V₁)) *
        ((3 / 2 : ℝ) * (normalizedBlockNorm Z₂ + normalizedBlockNorm V₂)) :=
      mul_le_mul h₁ h₂ (abs_nonneg _) (mul_nonneg (by norm_num) hn₁)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hm (mul_nonneg hn₁ hn₂)
      nlinarith

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  (μ : Measure Ω) [IsFiniteMeasure μ]

theorem integral_regularizedWeightMixedCost_tendsto
    (A B Z₁ Z₂ V₁ V₂ : Ω → Mat) (F : Ω → ℝ)
    (hA : Continuous A) (hB : Continuous B)
    (hZ₁ : Continuous Z₁) (hZ₂ : Continuous Z₂)
    (hV₁ : Continuous V₁) (hV₂ : Continuous V₂) (hF : Continuous F)
    (hsZ₁ : ∀ x, symmetric (Z₁ x)) (hsZ₂ : ∀ x, symmetric (Z₂ x))
    (hsV₁ : ∀ x, symmetric (V₁ x)) (hsV₂ : ∀ x, symmetric (V₂ x))
    (hpinch : ∀ x, normalizedBlockNorm (A x) + normalizedBlockNorm (B x) < 2)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (he : ∀ n, ε n ≤ 1 / 3)
    (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x,
      regularizedWeylWeightDerivative (ε n) (A x) (B x) (Z₁ x) (V₁ x) *
        regularizedWeylWeightDerivative (ε n) (A x) (B x) (Z₂ x) (V₂ x) /
          regularizedWeylWeight (ε n) (A x) (B x) * F x ∂μ) atTop
      (𝓝 (∫ x,
        regularizedWeylWeightDerivative 0 (A x) (B x) (Z₁ x) (V₁ x) *
          regularizedWeylWeightDerivative 0 (A x) (B x) (Z₂ x) (V₂ x) /
            regularizedWeylWeight 0 (A x) (B x) * F x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun x => 144 * (normalizedBlockNorm (Z₁ x) + normalizedBlockNorm (V₁ x)) *
      (normalizedBlockNorm (Z₂ x) + normalizedBlockNorm (V₂ x)) * |F x|)
  · intro n
    have hd₁ := continuous_regularizedWeylWeightDerivative (ε n) (hε n)
      A B Z₁ V₁ hA hB hZ₁ hV₁
    have hd₂ := continuous_regularizedWeylWeightDerivative (ε n) (hε n)
      A B Z₂ V₂ hA hB hZ₂ hV₂
    exact ((((hd₁.mul hd₂).div (continuous_regularizedWeylWeight (ε n) A B hA hB)
      (fun x => ne_of_gt (regularizedWeylWeight_pos (ε n) (hε n).le (he n) _ _
        (hpinch x)))).mul hF)).aestronglyMeasurable
  · have hc : Continuous (fun x =>
        144 * (normalizedBlockNorm (Z₁ x) + normalizedBlockNorm (V₁ x)) *
          (normalizedBlockNorm (Z₂ x) + normalizedBlockNorm (V₂ x)) * |F x|) :=
      ((continuous_const.mul ((continuous_normalizedBlockNorm.comp hZ₁).add
        (continuous_normalizedBlockNorm.comp hV₁))).mul
          ((continuous_normalizedBlockNorm.comp hZ₂).add
            (continuous_normalizedBlockNorm.comp hV₂))).mul hF.abs
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro n
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (regularized_weight_mixed_cost_le
      (ε n) (hε n) (he n) _ _ _ _ _ _ (hsZ₁ x) (hsZ₂ x) (hsV₁ x) (hsV₂ x)
      (hpinch x)) (abs_nonneg _)
  · filter_upwards [] with x
    have hd (Z V : Mat) :
        Tendsto (fun n => regularizedWeylWeightDerivative (ε n) (A x) (B x) Z V) atTop
          (𝓝 (regularizedWeylWeightDerivative 0 (A x) (B x) Z V)) := by
      simpa only [Function.comp_def, regularizedWeylWeightDerivative,
        regularizedRadialDerivative, regularizedBlockNorm_zero] using
        (tendsto_regularizedWeylWeightDerivative (A x) (B x) Z V).comp hlim
    have hm : Tendsto (fun n => regularizedWeylWeight (ε n) (A x) (B x)) atTop
        (𝓝 (regularizedWeylWeight 0 (A x) (B x))) := by
      simpa only [Function.comp_def, regularizedWeylWeight, regularizedBlockNorm_zero] using
        (tendsto_regularizedWeylWeight (A x) (B x)).comp hlim
    exact (((hd (Z₁ x) (V₁ x)).mul (hd (Z₂ x) (V₂ x))).div hm (ne_of_gt
      (regularizedWeylWeight_pos 0 (by norm_num) (by norm_num) _ _ (hpinch x)))).mul
        tendsto_const_nhds

end
end PositiveEinsteinFour.Geometry
end


section

/-! Derivatives vanish almost everywhere on a level set. Countability of
the isolated points gives the one-dimensional statement; Fubini and
preservation of frame measure transfer it to the actual Weyl gradient. -/

namespace PositiveEinsteinFour.Geometry

open Filter Set MeasureTheory EinsteinFour TraceHessian
open scoped Topology Manifold ContDiff

noncomputable section

/-- At a non-isolated point of a level set, the ordinary derivative is zero. -/
theorem derivative_zero_at_level_accPt {f : ℝ → ℝ} {x c v : ℝ}
    (hd : HasDerivAt f v x) (hx : f x = c)
    (ha : AccPt x (𝓟 {y | f y = c})) : v = 0 := by
  have hc : HasDerivWithinAt f 0 {y | f y = c} x :=
    (hasDerivWithinAt_const x {y | f y = c} c).congr
      (fun y hy => hy) hx
  exact ha.uniqueDiffWithinAt.eq_deriv _ hd.hasDerivWithinAt hc

/-- Nonzero derivatives on any one level form a countable set. -/
theorem countable_nonzero_derivative_on_level (f df : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt f (df x) x) (c : ℝ) :
    {x | f x = c ∧ df x ≠ 0}.Countable := by
  let s : Set ℝ := {x | f x = c}
  apply (countable_setOfPred_isolated_right_within (s := s)).mono
  intro x hx
  refine ⟨hx.1, ?_⟩
  have ha : ¬AccPt x (𝓟 s) := fun ha =>
    hx.2 (derivative_zero_at_level_accPt (hd x) hx.1 ha)
  have hb : 𝓝[s \ {x}] x = ⊥ := by
    simpa only [accPt_principal_iff_clusterPt, ClusterPt, nhdsWithin, not_neBot] using ha
  apply le_bot_iff.mp
  rw [← hb]
  apply nhdsWithin_mono
  intro y hy
  exact ⟨hy.1, by simp only [mem_singleton_iff]; exact ne_of_gt hy.2⟩

/-- Lebesgue almost everywhere, an ordinary derivative vanishes whenever
its function lies on a specified level. -/
theorem ae_derivative_zero_on_level (f df : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt f (df x) x) (c : ℝ) :
    ∀ᵐ x, f x = c → df x = 0 := by
  rw [ae_iff]
  simpa only [not_imp, not_not] using
    (countable_nonzero_derivative_on_level f df hd c).measure_zero volume

/-- A measure-preserving flow transfers the one-dimensional level-set
statement to its base measure; no measure-zero assertion is a premise. -/
theorem ae_flow_derivative_zero_on_level
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    (μ : Measure Ω) [SFinite μ]
    (φ : ℝ → Ω ≃ᵐ Ω)
    (hφ : Continuous (fun p : ℝ × Ω => φ p.1 p.2))
    (hp : ∀ t, MeasurePreserving (φ t) μ μ)
    (f df : Ω → ℝ) (hf : Continuous f) (hdf : Continuous df)
    (hd : ∀ t x, HasDerivAt (fun s => f (φ s x)) (df (φ t x)) t)
    (c : ℝ) : ∀ᵐ x ∂μ, f x = c → df x = 0 := by
  have hfc : Continuous (fun p : Ω × ℝ => f (φ p.2 p.1)) :=
    hf.comp (hφ.comp continuous_swap)
  have hdc : Continuous (fun p : Ω × ℝ => df (φ p.2 p.1)) :=
    hdf.comp (hφ.comp continuous_swap)
  have hP : MeasurableSet {p : Ω × ℝ | f (φ p.2 p.1) = c → df (φ p.2 p.1) = 0} := by
    simp only [imp_iff_not_or]
    exact (measurableSet_eq_fun hfc.measurable measurable_const).compl.union
      (measurableSet_eq_fun hdc.measurable measurable_const)
  have hline : ∀ᵐ x ∂μ, ∀ᵐ t : ℝ, f (φ t x) = c → df (φ t x) = 0 :=
    Filter.Eventually.of_forall (fun x => ae_derivative_zero_on_level
      (fun t => f (φ t x)) (fun t => df (φ t x)) (fun t => hd t x) c)
  obtain ⟨t, ht⟩ := ((Measure.ae_ae_comm hP).mp hline).exists
  rw [ae_iff] at ht ⊢
  calc
    μ {x | ¬(f x = c → df x = 0)} =
        μ ((φ t) ⁻¹' {x | ¬(f x = c → df x = 0)}) :=
      ((hp t).measure_preimage_equiv _).symm
    _ = 0 := ht

local instance zeroLevelNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance zeroLevelNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance zeroLevelNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The actual covariant Weyl gradient vanishes almost everywhere on the
zero set of its block. This justifies the zero-set case in the norm-weight
limit without assuming either Weyl block is everywhere nonzero. -/
theorem MetricGreenData.gradient_zero_ae_on_zero
    {g : SmoothMetric M} {μ : Measure (FrameBundle g)} [SFinite μ]
    (d : MetricGreenData g μ) :
    ∀ᵐ e ∂μ, plusWeyl g e.base e.frame = 0 →
      ∀ i, plusWeylGradient g e.base e.frame i = 0 := by
  have hc (i : Fin 4) (a b : Fin 3) :
      ∀ᵐ e ∂μ, plusWeyl g e.base e.frame a b = 0 →
        plusWeylGradient g e.base e.frame i a b = 0 :=
    ae_flow_derivative_zero_on_level μ (fun t => (d.flow i).map t)
      (d.flow i).continuous (d.flow i).preserves
      (fun e => plusWeyl g e.base e.frame a b)
      (fun e => plusWeylGradient g e.base e.frame i a b)
      ((matrixEntryMap a b).continuous.comp d.continuousWeyl)
      ((matrixEntryMap a b).continuous.comp (d.continuousGradient i))
      (fun t e => hasDerivAt_matrixEntry (d.derivativeWeyl i t e) a b) 0
  have hall : ∀ᵐ e ∂μ, ∀ i a b, plusWeyl g e.base e.frame a b = 0 →
      plusWeylGradient g e.base e.frame i a b = 0 :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun a => ae_all_iff.mpr (fun b => hc i a b)))
  filter_upwards [hall] with e he
  intro hz i
  ext a b
  apply he i a b
  exact congrArg (fun A : Mat => A a b) hz

end
end PositiveEinsteinFour.Geometry
end


section

/-! The original weighted-Hessian curvature form with complete Weyl matrices.
The contractions retain the full symmetric Weyl matrices. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

theorem hessianPairing_add_right (X Y Z : Hessian) :
    hessianPairing X (Y + Z) = hessianPairing X Y + hessianPairing X Z := by
  rw [hessianPairing_comm X, hessianPairing_add_left,
    hessianPairing_comm Y X, hessianPairing_comm Z X]

theorem hessianPairing_smul_right (c : ℝ) (X Y : Hessian) :
    hessianPairing X (c • Y) = c * hessianPairing X Y := by
  rw [hessianPairing_comm X, hessianPairing_smul_left, hessianPairing_comm Y X]

end
end PositiveEinsteinFour.TraceHessian

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

/-- The actual original curvature form, with the same contractions as the
four geometric Green identities. -/
def generalOriginalCurvatureForm (A U : Mat) (X : Hessian) : ℝ :=
  4 * hessianNormSq X -
    (5 / 6 : ℝ) * derivativePairing (generalCoefficient quaternionMatrix A) X X -
    (5 / 3 : ℝ) * matrixHessianPairing A X X -
    derivativePairing (generalCoefficient Angular.oppositeMatrix U) X X

/-- The symmetric elementary off-diagonal coefficient. -/
def symmetricUnit (r s : Fin 3) : Mat :=
  fun i j => (if i = r ∧ j = s then 1 else 0) + (if i = s ∧ j = r then 1 else 0)

theorem symmetricMatrix_expansion (A : Mat) (hA : symmetric A) :
    A = Matrix.diagonal (fun r => A r r) + A 0 1 • symmetricUnit 0 1 +
      A 0 2 • symmetricUnit 0 2 + A 1 2 • symmetricUnit 1 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetricUnit, hA 1 0, hA 2 0, hA 2 1]


end
end PositiveEinsteinFour.HighestHessian
end


section

/-! Evaluate the derivative-slot Green integral on actual metric tensors,
using the published raw curvature decomposition and Ricci commutator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian CurvatureContraction MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance curvatureIntegralNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance curvatureIntegralNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance curvatureIntegralNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

/-- The coefficient is a fixed bounded linear function of the Weyl block. -/
def generalCoefficientMap (Q : Fin 3 → Mat4) (i k j l : Fin 4) : Mat →L[ℝ] ℝ :=
  ({ toFun := fun A => generalCoefficient Q A i k j l
     map_add' A B := by
       simp only [generalCoefficient, Matrix.add_apply, add_mul,
         Finset.sum_add_distrib, mul_add]
     map_smul' c A := by
       simp only [generalCoefficient, Matrix.smul_apply, smul_eq_mul,
         mul_assoc, ← Finset.mul_sum, RingHom.id_apply]
       ring } : Mat →ₗ[ℝ] ℝ).toContinuousLinearMap

theorem generalCoefficient_pair_swap (Q : Fin 3 → Mat4)
    (hQ : ∀ s i j, Q s j i = -Q s i j) (A : Mat) (i k j l : Fin 4) :
    generalCoefficient Q A k i l j = generalCoefficient Q A i k j l := by
  unfold generalCoefficient
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [hQ r i k, hQ s j l]
  ring

theorem generalCoefficient_skew (Q : Fin 3 → Mat4)
    (hQ : ∀ s i j, Q s j i = -Q s i j) (A : Mat) (i k j l : Fin 4) :
    generalCoefficient Q A k i j l = -generalCoefficient Q A i k j l := by
  simp only [generalCoefficient, ← Finset.sum_neg_distrib, ← mul_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [hQ r i k]
  ring

theorem generalCoefficient_divergence (Q : Fin 3 → Mat4) (Z : Angular.Gradient)
    (hb : ∀ s i, (∑ r, ∑ k, Q r i k * Z k r s) = 0) (i j l : Fin 4) :
    (∑ k, generalCoefficient Q (Z k) i k j l) = 0 := by
  simp only [generalCoefficient, Finset.mul_sum]
  calc
    _ = ∑ s, (1 / 2 : ℝ) * Q s j l * (∑ r, ∑ k, Q r i k * Z k r s) := by
      simp only [Finset.mul_sum]
      calc
        _ = ∑ r, ∑ k, ∑ s, (1 / 2 : ℝ) * (Z k r s * Q r i k * Q s j l) :=
          Finset.sum_comm
        _ = ∑ r, ∑ s, ∑ k, (1 / 2 : ℝ) * (Z k r s * Q r i k * Q s j l) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.sum_comm]
        _ = _ := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro s _
          apply Finset.sum_congr rfl
          intro r _
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = 0 := by simp only [hb, mul_zero, Finset.sum_const_zero]

theorem inner_matrixVector_sub (A B C : Mat) :
    inner ℝ (matrixVector A - matrixVector B) (matrixVector C) =
      matrixPairing (A - B) C := by
  rw [inner_sub_left, inner_matrixVector, inner_matrixVector, matrixPairing_sub_left]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem continuousGradientSlice (d : MetricGreenData g μ) (i : Fin 4) :
    Continuous (frameGradientSlice g i) :=
  matrixVectorMap.continuous.comp (d.continuousGradient i)

theorem continuousHessianSlice (d : MetricGreenData g μ) (i j : Fin 4) :
    Continuous (frameHessianSlice g i j) :=
  matrixVectorMap.continuous.comp (d.continuousHessian i j)

theorem continuousThirdSlice (d : MetricGreenData g μ) (i j k : Fin 4) :
    Continuous (frameThirdSlice g i j k) :=
  matrixVectorMap.continuous.comp (d.continuousThird i j k)

/-- The actual plus-block derivative Green integral, before selecting any
pointwise spectral coordinates. The only new premise is the classical
curvature-block decomposition. -/
theorem plusCurvatureGreen (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hm : ∀ i t e, HasDerivAt (fun s => m ((d.flow i).map s e))
      (dm i ((d.flow i).map t e)) t) :
    (∫ e, weightedQuadratic
      (fun X => derivativePairing
        (generalCoefficient quaternionMatrix (plusWeyl g e.base e.frame)) X X)
      (m e) (plusWeylHessian g e.base e.frame)
      (weightTensor (WithLp.toLp 2 (fun i => dm i e))
        (plusGradientTensor g e.base e.frame)) ∂μ) =
    ∫ e, m e * (7 * normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 *
        weylGradientEnergy (plusWeylGradient g e.base e.frame) -
      4 * weylMatrixEnergy (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) -
      4 * weylMatrixEnergy (traceFreeSquare (plusWeyl g e.base e.frame))
        (plusWeylGradient g e.base e.frame)) ∂μ := by
  have hcoef (p : Averages.CurvatureIndex) (e : FrameBundle g) :
      framePlusCoefficient g p e =
        generalCoefficient quaternionMatrix (plusWeyl g e.base e.frame)
          p.1.1 p.1.2 p.2.1 p.2.2 :=
    (generalCoefficient_eq_blockTensor _ _ _ _ _ _).symm
  have hdcoef (p : Averages.CurvatureIndex) (e : FrameBundle g) :
      framePlusCoefficientDerivative g p e =
        generalCoefficient quaternionMatrix (plusWeylGradient g e.base e.frame p.1.2)
          p.1.1 p.1.2 p.2.1 p.2.2 :=
    (generalCoefficient_eq_blockTensor _ _ _ _ _ _).symm
  have hgreen := weighted_metric_curvature_green g d.flow m dm
    (fun p => by
      convert! (generalCoefficientMap quaternionMatrix p.1.1 p.1.2 p.2.1 p.2.2).continuous.comp
        d.continuousWeyl using 1
      funext e
      exact hcoef p e)
    (fun p => by
      convert! (generalCoefficientMap quaternionMatrix p.1.1 p.1.2 p.2.1 p.2.2).continuous.comp
        (d.continuousGradient p.1.2) using 1
      funext e
      exact hdcoef p e)
    d.continuousGradientSlice d.continuousHessianSlice d.continuousThirdSlice
    (by
      intro i j l e
      simp only [hdcoef]
      exact generalCoefficient_divergence quaternionMatrix _ (d.gradientBianchi e) i j l)
    (by
      intro i k j l e
      simp only [hcoef]
      exact generalCoefficient_skew quaternionMatrix (fun s i j => quaternionMatrix_skew s j i) _ i k j l)
    hm
    (by
      intro p t e
      convert! (generalCoefficientMap quaternionMatrix p.1.1 p.1.2 p.2.1 p.2.2).hasFDerivAt.comp_hasDerivAt t
        (d.derivativeWeyl p.1.2 t e) using 1
      · funext s
        exact hcoef p ((d.flow p.1.2).map s e)
      · exact hdcoef p ((d.flow p.1.2).map t e))
    (fun k j t e => hasDerivAt_matrixVector (d.derivativeGradient k j t e))
    (fun k i j t e => hasDerivAt_matrixVector (d.derivativeHessian k i j t e))
  have hp (e : FrameBundle g) :
      derivativeGreenContraction
        (generalCoefficient quaternionMatrix (plusWeyl g e.base e.frame))
        (fun i k j => plusWeylThirdDerivative g e.base e.frame i k j -
          plusWeylThirdDerivative g e.base e.frame k i j)
        (plusGradientTensor g e.base e.frame) / 6 =
      7 * normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 *
        weylGradientEnergy (plusWeylGradient g e.base e.frame) -
      4 * weylMatrixEnergy (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) -
      4 * weylMatrixEnergy (traceFreeSquare (plusWeyl g e.base e.frame))
        (plusWeylGradient g e.base e.frame) := by
    have hr : (fun i k j => plusWeylThirdDerivative g e.base e.frame i k j -
        plusWeylThirdDerivative g e.base e.frame k i j) =
        generalRawCurvatureCommutator (plusWeyl g e.base e.frame)
          (generalEinsteinCoefficient (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
          (plusGradientTensor g e.base e.frame) := by
      funext i k j
      rw [d.outerCommutator e i k j]
      simp only [generalRawCurvatureCommutator, plusGradientTensor,
        rawMatrixSlice_gradientTensor _ (d.gradientConstraints e).1,
        generalEinsteinCoefficient_eq_tensor, ← hdecomp e]
    rw [hr]
    simp only [plusGradientTensor]
    rw [general_plus_rawGreen _ _ (d.weyl.symmetric e) (d.weyl.traceFree e) _
      (gradientTensor_traceFree _ (d.gradientConstraints e).2)
      (gradientTensor_bianchi _ (d.gradientConstraints e).1 (d.gradientBianchi e)),
      trace_square_eq_six_norm_sq _ (d.weyl.symmetric e),
      gradientTensor_squaredNorm _ (d.gradientConstraints e).1]
    simp only [generalGradientForm,
      generalMatrixAction_gradient_pairing _ _ (d.gradientConstraints e).1]
    have he : Angular.gradientSquareNorm (plusWeylGradient g e.base e.frame) =
        6 * weylGradientEnergy (plusWeylGradient g e.base e.frame) := by
      rw [← gradientVector_norm_sq, ← real_inner_self_eq_norm_sq, gradientVector_pairing]
      unfold weylGradientEnergy
      ring
    rw [he]
    ring
  calc
    _ = (1 / 6 : ℝ) * (∫ e, ∑ p : Averages.CurvatureIndex,
        (m e * framePlusCoefficient g p e *
          matrixPairing (plusWeylHessian g e.base e.frame p.1.1 p.2.1)
            (plusWeylHessian g e.base e.frame p.1.2 p.2.2) +
        dm p.1.2 e * framePlusCoefficient g p e *
          matrixPairing (plusWeylHessian g e.base e.frame p.1.1 p.2.1)
            (plusWeylGradient g e.base e.frame p.2.2)) ∂μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with e
      rw [weightedQuadratic_derivative_green _
        (generalCoefficient_pair_swap quaternionMatrix (fun s i j => quaternionMatrix_skew s j i) _)]
      simp only [hcoef, plusGradientTensor,
        rawMatrixSlice_gradientTensor _ (d.gradientConstraints e).1]
      ring
    _ = _ := by
      rw [hgreen, ← integral_const_mul, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with e
      have hh := hp e
      simp only [hcoef, frameThirdSlice, frameGradientSlice, inner_matrixVector_sub] at *
      simp only [derivativeGreenContraction, plusGradientTensor,
        rawMatrixSlice_gradientTensor _ (d.gradientConstraints e).1] at hh
      simp only [Fintype.sum_prod_type, mul_assoc, ← Finset.mul_sum]
      linear_combination (m e) * hh

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Assemble the varying matrix-slot Green integral using the actual
metric Ricci equation and the actual derivative of its coefficient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance matrixIntegralNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance matrixIntegralNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance matrixIntegralNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

private theorem integral_matrix_combination
    {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f h k : C(Ω, ℝ)) :
    (1 / 6 : ℝ) * (-(∫ x, f x ∂μ) + (1 / 2 : ℝ) * (∫ x, h x + k x ∂μ)) =
      ∫ x, (-f x + (1 / 2 : ℝ) * h x) / 6 + k x / 12 ∂μ := by
  have hf := f.continuous.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hh := h.continuous.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hk := k.continuous.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  rw [integral_add hh hk]
  calc
    _ = -(1 / 6 : ℝ) * (∫ x, f x ∂μ) +
        (1 / 12 : ℝ) * (∫ x, h x ∂μ) + (1 / 12 : ℝ) * (∫ x, k x ∂μ) := by ring
    _ = ∫ x, -(1 / 6 : ℝ) * f x + (1 / 12 : ℝ) * h x + (1 / 12 : ℝ) * k x ∂μ := by
      have h₁ := integral_add ((hf.const_mul (-(1 / 6 : ℝ))).add
        (hh.const_mul (1 / 12 : ℝ))) (hk.const_mul (1 / 12 : ℝ))
      have h₂ := integral_add (hf.const_mul (-(1 / 6 : ℝ))) (hh.const_mul (1 / 12 : ℝ))
      simp only [Pi.add_apply] at h₁ h₂
      rw [h₁, h₂, integral_const_mul, integral_const_mul, integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

/-- The varying-matrix term has the scalar coefficients of the Hessian
inequality, including its cubic correction. -/
theorem matrixGreen (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hm : ∀ i t e, HasDerivAt (fun s => m ((d.flow i).map s e))
      (dm i ((d.flow i).map t e)) t) :
    (∫ e, weightedQuadratic
      (fun X => matrixHessianPairing (plusWeyl g e.base e.frame) X X)
      (m e) (plusWeylHessian g e.base e.frame)
      (weightTensor (WithLp.toLp 2 (fun i => dm i e))
        (plusGradientTensor g e.base e.frame)) ∂μ) =
    ∫ e, m e * (-10 * weylMatrixEnergy (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame) -
        3 * weylMatrixEnergy (traceFreeSquare (plusWeyl g e.base e.frame))
          (plusWeylGradient g e.base e.frame) +
        20 * weylCompressionEnergy (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame)) +
      (∑ i, dm i e * Matrix.trace (plusWeylGradient g e.base e.frame i *
        (∑ j, plusWeylGradient g e.base e.frame j * plusWeylGradient g e.base e.frame j))) / 12 ∂μ := by
  have hZ := d.continuousGradientVector
  have hL : Continuous (frameGradientLaplacian g) := by
    unfold frameGradientLaplacian
    exact continuous_finsetSum _ (fun i _ => d.continuousThirdVector i i)
  have hOp : Continuous (fun e => matrixSlotOperator (frameWeylMatrix g e)
      (frameGradientLaplacian g e)) :=
    (matrixSlot.continuous.comp d.continuousWeyl).clm_apply hL
  have hTrace : Continuous (fun e => ∑ i, matrixSlotOperator (frameWeylHessianMatrix g i i e)
      (frameGradientVector g e)) :=
    continuous_finsetSum _ (fun i _ =>
      (matrixSlot.continuous.comp (d.continuousHessian i i)).clm_apply hZ)
  let f : C(FrameBundle g, ℝ) :=
    ⟨fun e => m e * inner ℝ (frameGradientVector g e)
      (matrixSlotOperator (frameWeylMatrix g e) (frameGradientLaplacian g e)),
      m.continuous.mul (hZ.inner hOp)⟩
  let h : C(FrameBundle g, ℝ) :=
    ⟨fun e => m e * inner ℝ (frameGradientVector g e)
      (∑ i, matrixSlotOperator (frameWeylHessianMatrix g i i e) (frameGradientVector g e)),
      m.continuous.mul (hZ.inner hTrace)⟩
  let k : C(FrameBundle g, ℝ) :=
    ⟨fun e => ∑ i, dm i e * inner ℝ (frameGradientVector g e)
      (matrixSlotOperator (frameWeylGradientMatrix g i e) (frameGradientVector g e)),
      continuous_finsetSum _ (fun i _ => (dm i).continuous.mul
        (hZ.inner ((matrixSlot.continuous.comp (d.continuousGradient i)).clm_apply hZ)))⟩
  have hgreen := weighted_metric_matrix_slot_green g d.flow m dm
    d.continuousWeyl d.continuousGradient (fun i => d.continuousHessian i i)
    d.continuousGradientVector d.continuousHessianVector
    (fun i => d.continuousThirdVector i i)
    (fun i e => (d.gradientConstraints e).1 i) hm d.derivativeWeyl
    (fun i t e => d.derivativeGradient i i t e)
    d.derivativeGradientVector d.derivativeHessianVector
  calc
    _ = (1 / 6 : ℝ) * (∫ e, m e * (∑ i,
        inner ℝ (frameHessianVector g i e)
          (matrixSlotOperator (frameWeylMatrix g e) (frameHessianVector g i e))) +
        ∑ i, dm i e * inner ℝ (frameGradientVector g e)
          (matrixSlotOperator (frameWeylMatrix g e) (frameHessianVector g i e)) ∂μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with e
      rw [weightedQuadratic_matrix_green _ (d.weyl.symmetric e)]
      simp only [plusGradientTensor, tensorGradientVector_gradientTensor _
        (d.gradientConstraints e).1]
      simp only [frameGradientVector, frameHessianVector, frameWeylMatrix]
      ring
    _ = (1 / 6 : ℝ) * (-(∫ e, f e ∂μ) + (1 / 2 : ℝ) * (∫ e, h e + k e ∂μ)) := by
      rw [hgreen]
      rfl
    _ = ∫ e, (-f e + (1 / 2 : ℝ) * h e) / 6 + k e / 12 ∂μ :=
      integral_matrix_combination μ f h k
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with e
      have hs := d.matrixScalar e
      have hc := matrixSlot_weight_cubic (fun i => dm i e)
        (plusWeylGradient g e.base e.frame)
        (d.gradientConstraints e).1 (d.gradientConstraints e).2
      change (-(m e * _) + (1 / 2 : ℝ) * (m e * _)) / 6 + k e / 12 = _
      have hk : k e = ∑ i, dm i e * Matrix.trace (plusWeylGradient g e.base e.frame i *
          (∑ j, plusWeylGradient g e.base e.frame j * plusWeylGradient g e.base e.frame j)) := hc
      rw [hk]
      linear_combination (m e) * hs

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual scalar derivatives in the same coordinate connection and frame
flow as the Weyl tensors. The data below contain only parallel differentiation,
Hessian symmetry and the ordinary covector Ricci commutator (Petersen,
Riemannian Geometry, §3.1.1 and Proposition 2.2.8). -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def scalarCoordinates (a : M → ℝ) (c : M) (z : FourSpace) : CovariantCoordinates 0 :=
  fun _ => a ((chartAt FourSpace c).symm z)

def scalarGradient (g : SmoothMetric M) (a : M → ℝ) (e : FrameBundle g) (i : Fin 4) : ℝ :=
  frameTensor e.frame.matrix
    (covariantDerivative g e.base (scalarCoordinates a e.base) (chartAt FourSpace e.base e.base)) ![i]

def scalarHessian (g : SmoothMetric M) (a : M → ℝ) (e : FrameBundle g) (i j : Fin 4) : ℝ :=
  frameTensor e.frame.matrix
    (covariantDerivative g e.base (covariantDerivative g e.base (scalarCoordinates a e.base))
      (chartAt FourSpace e.base e.base)) ![i, j]

def scalarThird (g : SmoothMetric M) (a : M → ℝ) (e : FrameBundle g) (i j k : Fin 4) : ℝ :=
  frameTensor e.frame.matrix
    (covariantDerivative g e.base (covariantDerivative g e.base
      (covariantDerivative g e.base (scalarCoordinates a e.base)))
      (chartAt FourSpace e.base e.base)) ![i, j, k]

def scalarLaplacian (g : SmoothMetric M) (a : M → ℝ) (e : FrameBundle g) : ℝ :=
  ∑ i, scalarHessian g a e i i

def scalarGradientVector (g : SmoothMetric M) (a : M → ℝ) (e : FrameBundle g) : Bianchi.Vec :=
  WithLp.toLp 2 (scalarGradient g a e)

def scalarTraceFreeHessian (g : SmoothMetric M) (a : M → ℝ) (e : FrameBundle g) : Mat4 :=
  fun i j => scalarHessian g a e i j - if i = j then scalarLaplacian g a e / 4 else 0

/-- Raw classical scalar calculus, stated on the actual metric tensors. -/
structure ScalarCovariantData {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (d : MetricGreenData g μ) (a : M → ℝ) where
  continuousValue : Continuous (fun e : FrameBundle g => a e.base)
  continuousGradient : ∀ i, Continuous (fun e : FrameBundle g => scalarGradient g a e i)
  continuousHessian : ∀ i j, Continuous (fun e : FrameBundle g => scalarHessian g a e i j)
  continuousThird : ∀ i j k, Continuous (fun e : FrameBundle g => scalarThird g a e i j k)
  derivativeValue : ∀ i t e, HasDerivAt (fun s => a ((d.flow i).map s e).base)
    (scalarGradient g a ((d.flow i).map t e) i) t
  derivativeGradient : ∀ i j t e, HasDerivAt
    (fun s => scalarGradient g a ((d.flow i).map s e) j)
    (scalarHessian g a ((d.flow i).map t e) i j) t
  derivativeHessian : ∀ i j k t e, HasDerivAt
    (fun s => scalarHessian g a ((d.flow i).map s e) j k)
    (scalarThird g a ((d.flow i).map t e) i j k) t
  hessianSymmetric : ∀ e i j, scalarHessian g a e i j = scalarHessian g a e j i
  commutator : ∀ e i j k, scalarThird g a e i j k - scalarThird g a e j i k =
    ∑ l, frameCurvature g e.base e.frame i j l k * scalarGradient g a e l

namespace ScalarCovariantData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)} {d : MetricGreenData g μ}
  {a : M → ℝ} (s : ScalarCovariantData d a)

include s

theorem continuousLaplacian : Continuous (scalarLaplacian g a) :=
  continuous_finsetSum _ (fun i _ => s.continuousHessian i i)

theorem continuousGradientVector : Continuous (scalarGradientVector g a) := by
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi s.continuousGradient)

theorem derivativeLaplacian (i : Fin 4) (t : ℝ) (e : FrameBundle g) :
    HasDerivAt (fun r => scalarLaplacian g a ((d.flow i).map r e))
      (∑ j, scalarThird g a ((d.flow i).map t e) i j j) t :=
  HasDerivAt.fun_sum (fun j _ => s.derivativeHessian i j j t e)

theorem third_symmetric (e : FrameBundle g) (i j k : Fin 4) :
    scalarThird g a e i j k = scalarThird g a e i k j := by
  obtain ⟨e₀, he⟩ := ((d.flow i).map 0).surjective e
  have h₁ := s.derivativeHessian i j k 0 e₀
  have h₂ := s.derivativeHessian i k j 0 e₀
  have hf : (fun t => scalarHessian g a ((d.flow i).map t e₀) j k) =
      (fun t => scalarHessian g a ((d.flow i).map t e₀) k j) :=
    funext (fun t => s.hessianSymmetric _ _ _)
  rw [hf] at h₁
  have h := h₁.unique h₂
  simpa only [he] using h

theorem laplacianGradient_commute (e : FrameBundle g) (j : Fin 4) :
    (∑ i, scalarThird g a e i i j) =
      (∑ i, scalarThird g a e j i i) + 3 * scalarGradient g a e j := by
  have hi (i : Fin 4) : scalarThird g a e i i j = scalarThird g a e j i i +
      ∑ l, frameCurvature g e.base e.frame i j l i * scalarGradient g a e l := by
    have hc := s.commutator e i j i
    rw [s.third_symmetric e i i j]
    linarith only [hc]
  simp_rw [hi, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, d.ricci]
  simp

end ScalarCovariantData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Matrix conjugation and the derivative-index change used at a single
spectral frame. All maps act on the actual matrix arrays; no smooth choice
of eigenvectors is involved. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

def conjugateMatrix (R A : Mat) : Mat := Rᵀ * A * R

theorem conjugateMatrix_add (R A B : Mat) :
    conjugateMatrix R (A + B) = conjugateMatrix R A + conjugateMatrix R B := by
  simp only [conjugateMatrix, Matrix.mul_add, Matrix.add_mul]

theorem conjugateMatrix_sub (R A B : Mat) :
    conjugateMatrix R (A - B) = conjugateMatrix R A - conjugateMatrix R B := by
  simp only [conjugateMatrix, Matrix.mul_sub, Matrix.sub_mul]

theorem conjugateMatrix_smul (R A : Mat) (c : ℝ) :
    conjugateMatrix R (c • A) = c • conjugateMatrix R A := by
  simp only [conjugateMatrix, Matrix.mul_smul, Matrix.smul_mul]

theorem conjugateMatrix_sum {ι : Type*} [Fintype ι] (R : Mat) (A : ι → Mat) :
    conjugateMatrix R (∑ i, A i) = ∑ i, conjugateMatrix R (A i) := by
  simp only [conjugateMatrix, Matrix.mul_sum, Matrix.sum_mul]

theorem conjugateMatrix_one (R : Mat) (hR : Rᵀ * R = 1) :
    conjugateMatrix R 1 = 1 := by
  simpa only [conjugateMatrix, Matrix.mul_one] using hR

theorem conjugateMatrix_mul (R : Mat) (hR : R * Rᵀ = 1) (A B : Mat) :
    conjugateMatrix R A * conjugateMatrix R B = conjugateMatrix R (A * B) := by
  simp only [conjugateMatrix]
  calc
    Rᵀ * A * R * (Rᵀ * B * R) = Rᵀ * A * (R * Rᵀ) * B * R := by
      simp only [Matrix.mul_assoc]
    _ = Rᵀ * (A * B) * R := by
      rw [hR, Matrix.mul_one]
      simp only [Matrix.mul_assoc]

theorem conjugateMatrix_trace (R : Mat) (hR : R * Rᵀ = 1) (A : Mat) :
    Matrix.trace (conjugateMatrix R A) = Matrix.trace A := by
  rw [conjugateMatrix, Matrix.trace_mul_cycle, hR, Matrix.one_mul]

theorem conjugateMatrix_transpose (R A : Mat) :
    (conjugateMatrix R A)ᵀ = conjugateMatrix R Aᵀ := by
  simp only [conjugateMatrix, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]

theorem conjugateMatrix_symmetric (R A : Mat) (hA : symmetric A) :
    symmetric (conjugateMatrix R A) := by
  have ht : Aᵀ = A := by ext i j; exact hA j i
  have h := conjugateMatrix_transpose R A
  rw [ht] at h
  intro i j
  exact (congrArg (fun N : Mat => N i j) h).symm

theorem conjugateMatrix_traceFree (R : Mat) (hR : R * Rᵀ = 1)
    (A : Mat) (hA : traceFree A) : traceFree (conjugateMatrix R A) := by
  change Matrix.trace (conjugateMatrix R A) = 0
  rw [conjugateMatrix_trace R hR]
  exact hA

theorem conjugateMatrix_pairing (R : Mat) (hR : R * Rᵀ = 1) (A B : Mat) :
    matrixPairing (conjugateMatrix R A) (conjugateMatrix R B) = matrixPairing A B := by
  rw [matrixPairing_eq_trace, conjugateMatrix_transpose,
    conjugateMatrix_mul R hR, conjugateMatrix_trace R hR, matrixPairing_eq_trace]

theorem conjugateMatrix_slot (R : Mat) (hR : Rᵀ * R = 1) (A B : Mat) :
    matrixSlotAction (conjugateMatrix R A) (conjugateMatrix R B) =
      conjugateMatrix R (matrixSlotAction A B) := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  simp only [matrixSlotAction_eq, conjugateMatrix_mul R hR',
    conjugateMatrix_trace R hR', conjugateMatrix_sub, conjugateMatrix_smul,
    conjugateMatrix_add, conjugateMatrix_one R hR]

theorem conjugateMatrix_traceFreeSquare (R : Mat) (hR : Rᵀ * R = 1) (A : Mat) :
    traceFreeSquare (conjugateMatrix R A) = conjugateMatrix R (traceFreeSquare A) := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  simp only [traceFreeSquare, conjugateMatrix_mul R hR',
    conjugateMatrix_trace R hR', conjugateMatrix_sub, conjugateMatrix_smul,
    conjugateMatrix_one R hR]

theorem conjugateMatrix_norm (R : Mat) (hR : R * Rᵀ = 1) (A : Mat) :
    normalizedBlockNorm (conjugateMatrix R A) = normalizedBlockNorm A := by
  have hp := conjugateMatrix_pairing R hR A A
  have hs : normalizedBlockNorm (conjugateMatrix R A) ^ 2 =
      normalizedBlockNorm A ^ 2 := by
    rw [normalizedBlockNorm_sq, normalizedBlockNorm_sq]
    simpa only [matrixPairing, pow_two] using
      congrArg (fun x : ℝ => x / 6) hp
  nlinarith [normalizedBlockNorm_nonneg (conjugateMatrix R A),
    normalizedBlockNorm_nonneg A]

/-- Passive rotation of all three slots of a matrix-valued covector. -/
def turnGradient (R : Mat) (P : Mat4) (Z : Angular.Gradient) : Angular.Gradient :=
  fun i => ∑ j, P j i • conjugateMatrix R (Z j)

theorem turnGradient_symmetric (R : Mat) (P : Mat4) (Z : Angular.Gradient)
    (hZ : ∀ i, symmetric (Z i)) (i : Fin 4) :
    symmetric (turnGradient R P Z i) := by
  intro a b
  simp only [turnGradient, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [conjugateMatrix_symmetric R (Z j) (hZ j) a b]

theorem turnGradient_traceFree (R : Mat) (hR : R * Rᵀ = 1) (P : Mat4)
    (Z : Angular.Gradient) (hZ : ∀ i, traceFree (Z i)) (i : Fin 4) :
    traceFree (turnGradient R P Z i) := by
  change Matrix.trace (∑ j, P j i • conjugateMatrix R (Z j)) = 0
  rw [Matrix.trace_sum]
  simp only [Matrix.trace_smul, conjugateMatrix_trace R hR,
    show ∀ j, Matrix.trace (Z j) = 0 from hZ, smul_zero, Finset.sum_const_zero]

private theorem matrixPairing_comm (A B : Mat) : matrixPairing A B = matrixPairing B A := by
  simp only [matrixPairing, mul_comm]

private theorem matrixPairing_sum_smul_right {ι : Type*} [Fintype ι]
    (A : Mat) (c : ι → ℝ) (B : ι → Mat) :
    matrixPairing A (∑ i, c i • B i) = ∑ i, c i * matrixPairing A (B i) := by
  rw [matrixPairing_comm, CurvatureContraction.matrixPairing_sum_smul_left]
  simp only [matrixPairing_comm]

private theorem orthogonal_sum_contraction (P : Mat4) (hP : P * Pᵀ = 1)
    (f : Fin 4 → Fin 4 → ℝ) :
    (∑ i, ∑ j, ∑ k, (P j i * P k i) * f j k) = ∑ j, f j j := by
  have hp (j k : Fin 4) : (∑ i, P j i * P k i) = if j = k then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      congrArg (fun N : Mat4 => N j k) hP
  calc
    _ = ∑ j, ∑ i, ∑ k, (P j i * P k i) * f j k := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, (P j i * P k i) * f j k := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ j, ∑ k, (if j = k then 1 else 0) * f j k := by
      simp only [← Finset.sum_mul, hp]
    _ = _ := by simp

/-- Every quadratic contraction is preserved by simultaneous changes of
the matrix basis and the covector basis. -/
theorem turnGradient_pairing (R : Mat) (hR : R * Rᵀ = 1)
    (P : Mat4) (hP : P * Pᵀ = 1) (Z W : Angular.Gradient) :
    (∑ i, matrixPairing (turnGradient R P Z i) (turnGradient R P W i)) =
      ∑ i, matrixPairing (Z i) (W i) := by
  simp only [turnGradient, CurvatureContraction.matrixPairing_sum_smul_left,
    matrixPairing_sum_smul_right, conjugateMatrix_pairing R hR, Finset.mul_sum]
  simp_rw [← mul_assoc]
  exact orthogonal_sum_contraction P hP _

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The finite four-by-four projection-cost kernel passes through the
smooth norm regularization, without any nonvanishing Weyl hypothesis. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter TraceHessian
open scoped BigOperators Topology

noncomputable section

local instance matrixWeightNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance matrixWeightNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance matrixWeightNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

def regularizedMatrixWeight (ε : ℝ) (A B : Mat) (Z V : Fin 4 → Mat)
    (K : Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ i, ∑ j, (regularizedWeylWeightDerivative ε A B (Z i) (V i) *
    regularizedWeylWeightDerivative ε A B (Z j) (V j) / regularizedWeylWeight ε A B) * K i j

theorem abs_regularizedMatrixWeight_le (ε : ℝ) (hε : 0 < ε) (he : ε ≤ 1 / 3)
    (A B : Mat) (Z V : Fin 4 → Mat) (K : Fin 4 → Fin 4 → ℝ)
    (hZ : ∀ i, symmetric (Z i)) (hV : ∀ i, symmetric (V i))
    (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    |regularizedMatrixWeight ε A B Z V K| ≤
      ∑ i, ∑ j, 144 * (normalizedBlockNorm (Z i) + normalizedBlockNorm (V i)) *
        (normalizedBlockNorm (Z j) + normalizedBlockNorm (V j)) * |K i j| := by
  unfold regularizedMatrixWeight
  calc
    _ ≤ ∑ i, |∑ j, (regularizedWeylWeightDerivative ε A B (Z i) (V i) *
        regularizedWeylWeightDerivative ε A B (Z j) (V j) / regularizedWeylWeight ε A B) * K i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (regularized_weight_mixed_cost_le ε hε he
        A B (Z i) (Z j) (V i) (V j) (hZ i) (hZ j) (hV i) (hV j) hpinch) (abs_nonneg _)

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

theorem integral_regularizedMatrixWeight_tendsto
    (A B : Ω → Mat) (Z V : Fin 4 → Ω → Mat) (K : Fin 4 → Fin 4 → Ω → ℝ)
    (hA : Continuous A) (hB : Continuous B) (hZ : ∀ i, Continuous (Z i))
    (hV : ∀ i, Continuous (V i)) (hK : ∀ i j, Continuous (K i j))
    (hsZ : ∀ i x, symmetric (Z i x)) (hsV : ∀ i x, symmetric (V i x))
    (hpinch : ∀ x, normalizedBlockNorm (A x) + normalizedBlockNorm (B x) < 2)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (he : ∀ n, ε n ≤ 1 / 3)
    (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, regularizedMatrixWeight (ε n) (A x) (B x)
      (fun i => Z i x) (fun i => V i x) (fun i j => K i j x) ∂μ) atTop
      (𝓝 (∫ x, regularizedMatrixWeight 0 (A x) (B x)
        (fun i => Z i x) (fun i => V i x) (fun i j => K i j x) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun x => ∑ i, ∑ j, 144 * (normalizedBlockNorm (Z i x) + normalizedBlockNorm (V i x)) *
      (normalizedBlockNorm (Z j x) + normalizedBlockNorm (V j x)) * |K i j x|)
  · intro n
    have hd (i : Fin 4) := continuous_regularizedWeylWeightDerivative (ε n) (hε n)
      A B (Z i) (V i) hA hB (hZ i) (hV i)
    have hw := continuous_regularizedWeylWeight (ε n) A B hA hB
    have hp x := ne_of_gt (regularizedWeylWeight_pos (ε n) (hε n).le (he n) _ _ (hpinch x))
    apply Continuous.aestronglyMeasurable
    unfold regularizedMatrixWeight
    exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
      (((hd i).mul (hd j)).div hw hp).mul (hK i j)))
  · have hc : Continuous (fun x => ∑ i, ∑ j,
        144 * (normalizedBlockNorm (Z i x) + normalizedBlockNorm (V i x)) *
          (normalizedBlockNorm (Z j x) + normalizedBlockNorm (V j x)) * |K i j x|) :=
      continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
        ((continuous_const.mul ((continuous_normalizedBlockNorm.comp (hZ i)).add
          (continuous_normalizedBlockNorm.comp (hV i)))).mul
          ((continuous_normalizedBlockNorm.comp (hZ j)).add
            (continuous_normalizedBlockNorm.comp (hV j)))).mul (hK i j).abs))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro n
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    exact abs_regularizedMatrixWeight_le (ε n) (hε n) (he n) _ _ _ _ _
      (fun i => hsZ i x) (fun i => hsV i x) (hpinch x)
  · filter_upwards [] with x
    have hd (i : Fin 4) :
        Tendsto (fun n => regularizedWeylWeightDerivative (ε n) (A x) (B x) (Z i x) (V i x))
          atTop (𝓝 (regularizedWeylWeightDerivative 0 (A x) (B x) (Z i x) (V i x))) := by
      simpa only [Function.comp_def, regularizedWeylWeightDerivative,
        regularizedRadialDerivative, regularizedBlockNorm_zero] using
        (tendsto_regularizedWeylWeightDerivative (A x) (B x) (Z i x) (V i x)).comp hlim
    have hw : Tendsto (fun n => regularizedWeylWeight (ε n) (A x) (B x)) atTop
        (𝓝 (regularizedWeylWeight 0 (A x) (B x))) := by
      simpa only [Function.comp_def, regularizedWeylWeight, regularizedBlockNorm_zero] using
        (tendsto_regularizedWeylWeight (A x) (B x)).comp hlim
    unfold regularizedMatrixWeight
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact (((hd i).mul (hd j)).div hw (ne_of_gt
      (regularizedWeylWeight_pos 0 (by norm_num) (by norm_num) _ _ (hpinch x)))).mul
        tendsto_const_nhds

end
end PositiveEinsteinFour.Geometry
end


section

/-! Full-matrix generator compression on the actual Bianchi gradient space.
This is the ingredient for retaining unsymmetrized inner-Bianchi Hessians. -/

namespace PositiveEinsteinFour.Bianchi

open scoped BigOperators
open Matrix TraceHessian HighestHessian CurvatureContraction

noncomputable section

private theorem quaternion_frame_inner (r s : Fin 3) (v : Vec) :
    inner ℝ (quaternion r v) (quaternion s v) =
      if r = s then ‖v‖ ^ 2 else 0 := by
  fin_cases r <;> fin_cases s <;>
    simp [quaternion, PiLp.inner_apply, RCLike.inner_apply,
      EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  all_goals ring

private theorem rawQuaternion_self_pairing (r s : Fin 3) (Z : Tensor) :
    rawPairing (rawQuaternion r Z.matrix) (rawQuaternion s Z.matrix) =
      if r = s then Z.squaredNorm else 0 := by
  rw [rawPairing_vectors]
  simp only [rawQuaternion, quaternion_frame_inner]
  by_cases h : r = s
  · simp only [h, ite_true, Tensor.squaredNorm]
  · simp only [h, ite_false, Finset.sum_const_zero]

private theorem weighted_rawQuaternion_self (A : Mat) (Z : Tensor) :
    (∑ r, ∑ s, A r s * rawPairing (rawQuaternion r Z.matrix)
      (rawQuaternion s Z.matrix)) = Matrix.trace A * Z.squaredNorm := by
  simp only [rawQuaternion_self_pairing, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Matrix.trace, Matrix.diag,
    Finset.sum_mul]

private theorem quaternion_matrix_pairing (r s : Fin 3) (Z : Tensor) :
    rawPairing (rawQuaternion r Z.matrix) (rawMatrixRotation s Z.matrix) =
      -(∑ a, ∑ b, inner ℝ (quaternion r (matrixRotation s Z a b)) (Z.matrix a b)) := by
  rw [rawPairing_vectors, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  change inner ℝ (quaternion r (Z.matrix a b)) (matrixRotation s Z a b) = _
  rw [quaternion_inner_skew, real_inner_comm]

private theorem weighted_quaternion_matrix_pairing (A : Mat) (Z : Tensor) :
    (∑ r, ∑ s, A r s * rawPairing (rawQuaternion r Z.matrix)
      (rawMatrixRotation s Z.matrix)) =
        -rawPairing (generalMixedAction A Z.matrix) Z.matrix := by
  simp_rw [quaternion_matrix_pairing]
  simp only [mul_neg, Finset.sum_neg_distrib]
  rw [generalMixedAction_pairing_sum]

/-- The full matrix generator energy follows from the actual one-fifth
Bianchi projection and the arbitrary-matrix mixed compression. -/
theorem general_generator_energy (A : Mat) (hA : symmetric A) (htA : traceFree A)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ r, ∑ s, A r s * rawPairing (rawGradientGenerator r Z.matrix)
      (rawGradientGenerator s Z.matrix)) = -40 * generalGradientForm A Z := by
  have hp (r s : Fin 3) :
      rawPairing (rawGradientGenerator r Z.matrix) (rawGradientGenerator s Z.matrix) =
        5 * rawPairing (rawQuaternion r Z.matrix) (rawGradientGenerator s Z.matrix) := by
    have h := derivativeQuaternion_pairing r Z (totalGradientTensor s Z) hb
      (totalGradientTensor_bianchi s Z hz hb)
    rw [totalGradientTensor_matrix s Z hz hb] at h
    change rawPairing (rawQuaternion r Z.matrix) (rawGradientGenerator s Z.matrix) = _ at h
    linarith
  have hgen (s : Fin 3) : rawGradientGenerator s Z.matrix =
      rawQuaternion s Z.matrix + rawMatrixRotation s Z.matrix := rfl
  have hs :
      (∑ r, ∑ s, A r s * rawPairing (rawGradientGenerator r Z.matrix)
        (rawGradientGenerator s Z.matrix)) =
      5 * ((∑ r, ∑ s, A r s * rawPairing (rawQuaternion r Z.matrix)
        (rawQuaternion s Z.matrix)) +
        (∑ r, ∑ s, A r s * rawPairing (rawQuaternion r Z.matrix)
          (rawMatrixRotation s Z.matrix))) := by
    simp_rw [hp, hgen, rawPairing_add_right]
    simp only [Fin.sum_univ_three]
    ring
  rw [hs, weighted_rawQuaternion_self, weighted_quaternion_matrix_pairing,
    generalMixedAction_self_pairing A hA htA Z hz hb]
  have ht : Matrix.trace A = 0 := htA
  rw [ht]
  ring

end
end PositiveEinsteinFour.Bianchi


namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian CurvatureContraction PositiveEinsteinFour.Geometry

noncomputable section

private theorem sum_rotate_three {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

/-- The actual matrix-slot operator is the sum of its four inner-slice forms. -/
theorem matrixHessianPairing_innerSlices (A : Mat) (X : Hessian)
    (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j)) :
    matrixHessianPairing A X X = ∑ i, generalGradientForm A (innerSlice X i) := by
  unfold matrixHessianPairing
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm, ← gradientVector_innerSlice X i (fun j => (hm i j).1),
    matrixSlotOperator_general_pairing A _ (innerSlice_traceFree X i (fun j => (hm i j).2))]
  rfl

/-- The full weighted inner-generator energy uses only each slice's Bianchi identity. -/
theorem general_innerAction_energy (A : Mat) (hA : symmetric A) (htA : traceFree A)
    (X : Hessian) (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hb : ∀ i r, divergence X i r = 0) :
    hessianGram A (fun r => innerAction r X) = -40 * matrixHessianPairing A X X := by
  simp only [hessianGram, hessianPairing_slices, innerAction_rawSlice, Finset.mul_sum]
  rw [sum_rotate_three]
  simp_rw [rawSlice_eq_innerSlice X (fun i j => (hm i j).1)]
  simp_rw [general_generator_energy A hA htA _
    (innerSlice_traceFree X _ (fun j => (hm _ j).2))
    (innerSlice_bianchi X _ (fun j => (hm _ j).1) (hb _))]
  rw [← Finset.mul_sum, matrixHessianPairing_innerSlices A X hm]

/-- The two actual derivative slots, before taking a trace-free coefficient. -/
def generalDerivativeSlot (Q : Fin 3 → Mat4) (r s : Fin 3) (X : Hessian) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, Q r i k * Q s j l * matrixPairing (X k l) (X i j)

private theorem generalDerivativeSlot_slices (r s : Fin 3) (X : Hessian) :
    generalDerivativeSlot quaternionMatrix r s X =
      ∑ i, ∑ k, quaternionMatrix r i k *
        rawPairing (rawQuaternion s (rawSlice X k)) (rawSlice X i) := by
  have hm (k l : Fin 4) : rawMatrixAt (rawSlice X k) l = X k l := rfl
  simp_rw [rawQuaternion_pairing, hm]
  simp only [Finset.mul_sum, mul_assoc, generalDerivativeSlot]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

private theorem hessianPairing_outer_inner_cross (r s : Fin 3) (X : Hessian) :
    hessianPairing (outerAction r X) (innerAction s X) =
      ∑ i, ∑ k, quaternionMatrix r i k *
        rawPairing (rawSlice X k) (rawGradientGenerator s (rawSlice X i)) := by
  rw [hessianPairing_slices]
  simp_rw [outerAction_rawSlice, rawPairing_sum_left, rawPairing_smul_left,
    innerAction_rawSlice]

/-- Off-diagonal as well as diagonal derivative-slot compression. -/
theorem generalDerivativeSlot_inner_cross (r s : Fin 3) (X : Hessian)
    (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hb : ∀ i t, divergence X i t = 0) :
    generalDerivativeSlot quaternionMatrix r s X =
      -(1 / 5 : ℝ) * hessianPairing (outerAction r X) (innerAction s X) := by
  have hr := rawSlice_eq_innerSlice X (fun i j => (hm i j).1)
  have hbianchi (i : Fin 4) : (innerSlice X i).bianchi :=
    innerSlice_bianchi X i (fun j => (hm i j).1) (hb i)
  have hc (i k : Fin 4) :
      rawPairing (rawQuaternion s (rawSlice X k)) (rawSlice X i) =
        (1 / 5 : ℝ) * rawPairing (rawGradientGenerator s (rawSlice X k))
          (rawSlice X i) := by
    simp_rw [hr]
    exact derivativeQuaternion_pairing s (innerSlice X k) (innerSlice X i)
      (hbianchi k) (hbianchi i)
  rw [generalDerivativeSlot_slices, hessianPairing_outer_inner_cross]
  simp_rw [hc]
  have hswap : (∑ i, ∑ k, quaternionMatrix r i k *
      rawPairing (rawGradientGenerator s (rawSlice X k)) (rawSlice X i)) =
        -(∑ i, ∑ k, quaternionMatrix r i k *
          rawPairing (rawSlice X k) (rawGradientGenerator s (rawSlice X i))) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [quaternionMatrix_skew r k i, rawPairing_comm]
    ring
  calc
    _ = (1 / 5 : ℝ) * (∑ i, ∑ k, quaternionMatrix r i k *
        rawPairing (rawGradientGenerator s (rawSlice X k)) (rawSlice X i)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [hswap]; ring


private theorem outerAction_pairing (r s : Fin 3) (X : Hessian) :
    hessianPairing (outerAction r X) (outerAction s X) =
      if r = s then hessianNormSq X else 0 := by
  have h (a b : Fin 3) (j : Fin 4) :
      (∑ i, outerAction r X i j a b * outerAction s X i j a b) =
        if r = s then ∑ i, X i j a b ^ 2 else 0 := by
    have hh := Bianchi.quaternion_frame_inner r s
      (WithLp.toLp 2 (fun i => X i j a b))
    simpa only [outerAction, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      EuclideanSpace.real_norm_sq_eq, mul_comm] using hh
  unfold hessianPairing hessianNormSq
  have hf (a b : Fin 3) :
      (∑ i, ∑ j, outerAction r X i j a b * outerAction s X i j a b) =
        if r = s then ∑ i, ∑ j, X i j a b ^ 2 else 0 := by
    rw [Finset.sum_comm]
    simp_rw [h]
    by_cases hrs : r = s
    · simp only [hrs, ite_true]
      exact Finset.sum_comm
    · simp [hrs]
  simp_rw [hf]
  by_cases hrs : r = s <;> simp [hrs]

private theorem general_outerAction_energy (A : Mat) (X : Hessian) (htA : traceFree A) :
    hessianGram A (fun r => outerAction r X) = 0 := by
  simp only [hessianGram, outerAction_pairing, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.sum_mul]
  change (∑ r, A r r) * hessianNormSq X = 0
  rw [htA, zero_mul]

private theorem sum_swap_last_two {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  exact Finset.sum_comm

/-- Reordering the actual derivative contraction and the two Weyl indices. -/
theorem generalDerivativePairing_eq (Q : Fin 3 → Mat4) (A : Mat) (X : Hessian) :
    derivativePairing (generalCoefficient Q A) X X =
      (1 / 2 : ℝ) * ∑ r, ∑ s, A r s * generalDerivativeSlot Q r s X := by
  simp only [derivativePairing, generalCoefficient, Finset.sum_mul, Finset.mul_sum]
  rw [sum_swap_last_two]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  simp only [Fintype.sum_prod_type, generalDerivativeSlot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  have hm : matrixPairing (X i j) (X k l) = matrixPairing (X k l) (X i j) := by
    simp only [matrixPairing, mul_comm]
  rw [hm]
  ring

private theorem general_cross_energy (A : Mat) (X : Hessian)
    (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hb : ∀ i r, divergence X i r = 0) :
    (∑ r, ∑ s, A r s * hessianPairing (outerAction r X) (innerAction s X)) =
      -10 * derivativePairing (generalCoefficient quaternionMatrix A) X X := by
  rw [generalDerivativePairing_eq]
  have hc (r s : Fin 3) := generalDerivativeSlot_inner_cross r s X hm hb
  have hh (r s : Fin 3) : hessianPairing (outerAction r X) (innerAction s X) =
      -5 * generalDerivativeSlot quaternionMatrix r s X := by linarith [hc r s]
  simp_rw [hh]
  simp only [Fin.sum_univ_three]
  ring

/-- No outer-slot symmetry is required for the full-matrix plus compression. -/
theorem general_plus_energy (A : Mat) (hA : symmetric A) (htA : traceFree A)
    (X : Hessian) (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hb : ∀ i r, divergence X i r = 0) :
    hessianGram A (fun r => totalPlus r X) =
      -40 * matrixHessianPairing A X X -
        20 * derivativePairing (generalCoefficient quaternionMatrix A) X X := by
  have hcross : (∑ r, ∑ s, A r s * hessianPairing (innerAction r X) (outerAction s X)) =
      ∑ r, ∑ s, A r s * hessianPairing (outerAction r X) (innerAction s X) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [hA s r, hessianPairing_comm]
  have hi := general_innerAction_energy A hA htA X hm hb
  have ho := general_outerAction_energy A X htA
  have hc := general_cross_energy A X hm hb
  unfold hessianGram at hi ho ⊢
  simp_rw [totalPlus_inner_outer, hessianPairing_add_left, hessianPairing_add_right]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hi, ho, hcross, hc]
  ring

private theorem totalMinus_pairing_slice (r s : Fin 3) (X : Hessian) (a b : Fin 3) :
    (∑ i, ∑ j, totalMinus r X i j a b * totalMinus s X i j a b) =
      (if r = s then 2 * ∑ i, ∑ j, X i j a b ^ 2 else 0) -
      (∑ i, ∑ j, ∑ k, ∑ l,
        rightQuaternion r i k * rightQuaternion s j l * X k l a b * X i j a b) -
      (∑ i, ∑ j, ∑ k, ∑ l,
        rightQuaternion s i k * rightQuaternion r j l * X k l a b * X i j a b) := by
  fin_cases r <;> fin_cases s <;>
    simp [totalMinus, rightQuaternion, Fin.sum_univ_four] <;> ring

private theorem sum_six_rotate
    (f : Fin 3 → Fin 3 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ i, ∑ j, ∑ k, ∑ l, f a b i j k l) =
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, ∑ b, f a b i j k l := by
  have h := (Equiv.prodComm (Fin 3 × Fin 3)
    (Fin 4 × Fin 4 × Fin 4 × Fin 4)).sum_comp
    (fun p => f p.2.1 p.2.2 p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2)
  simpa only [Fintype.sum_prod_type, Equiv.prodComm_apply, Prod.swap_prod_mk] using h

private theorem general_minus_energy_entry (r s : Fin 3) (X : Hessian) :
    hessianPairing (totalMinus r X) (totalMinus s X) =
      (if r = s then 2 * hessianNormSq X else 0) -
        generalDerivativeSlot rightQuaternion r s X - generalDerivativeSlot rightQuaternion s r X := by
  unfold hessianPairing
  simp_rw [totalMinus_pairing_slice]
  simp only [Finset.sum_sub_distrib]
  have hex (r s : Fin 3) :
      (∑ a, ∑ b, ∑ i, ∑ j, ∑ k, ∑ l,
        rightQuaternion r i k * rightQuaternion s j l * X k l a b * X i j a b) =
      generalDerivativeSlot rightQuaternion r s X := by
    unfold generalDerivativeSlot matrixPairing
    simp only [Finset.mul_sum]
    rw [sum_six_rotate]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hex, hex]
  by_cases hrs : r = s <;>
    simp only [hrs, ite_true, ite_false, hessianNormSq, ← Finset.mul_sum,
      Finset.sum_const_zero]

/-- The full-matrix opposite-block compression holds on every tensor. -/
theorem general_minus_energy (U : Mat) (hU : symmetric U) (htU : traceFree U)
    (X : Hessian) :
    hessianGram U (fun r => totalMinus r X) =
      -4 * derivativePairing (generalCoefficient Angular.oppositeMatrix U) X X := by
  have hQ (r s : Fin 3) : generalDerivativeSlot Angular.oppositeMatrix r s X =
      generalDerivativeSlot rightQuaternion r s X := by
    simp only [generalDerivativeSlot, oppositeMatrix_eq_neg_rightQuaternion, neg_mul_neg]
  have hc : (∑ r, ∑ s, U r s * generalDerivativeSlot rightQuaternion s r X) =
      ∑ r, ∑ s, U r s * generalDerivativeSlot rightQuaternion r s X := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [hU s r]
  rw [generalDerivativePairing_eq]
  simp_rw [hQ]
  simp only [hessianGram, general_minus_energy_entry, mul_sub, Finset.sum_sub_distrib]
  rw [hc]
  have hz : (∑ r, ∑ s, U r s * if r = s then 2 * hessianNormSq X else 0) = 0 := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      ← Finset.sum_mul]
    rw [show (∑ r, U r r) = 0 from htU, zero_mul]
  rw [hz]
  ring

/-- Exact equality on the full inner-Bianchi space, including the
unsymmetrized derivative of a scalar weight. -/
theorem generalOriginalCurvatureForm_eq_of_inner_bianchi (A U : Mat) (X : Hessian)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hb : ∀ i r, divergence X i r = 0) :
    generalOriginalCurvatureForm A U X = generalCasimirCurvatureForm A U X := by
  unfold generalOriginalCurvatureForm generalCasimirCurvatureForm
  rw [general_plus_energy A hA htA X hm hb, general_minus_energy U hU htU X]
  ring

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! Simultaneous dominated convergence for the scalar, cubic, and projection
terms of the weighted Hessian estimate. All derivative indices are the
four actual frame directions. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter TraceHessian
open scoped BigOperators Topology

noncomputable section

local instance hessianWeightNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance hessianWeightNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance hessianWeightNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

def regularizedHessianWeight (ε : ℝ) (A B : Mat) (Z V : Fin 4 → Mat)
    (F : ℝ) (G : Fin 4 → ℝ) (K : Fin 4 → Fin 4 → ℝ) : ℝ :=
  regularizedWeylWeight ε A B * F +
    (∑ i, regularizedWeylWeightDerivative ε A B (Z i) (V i) * G i) +
    regularizedMatrixWeight ε A B Z V K

theorem regularizedHessianWeight_bound (ε : ℝ) (hε : 0 < ε) (he : ε ≤ 1 / 3)
    (A B : Mat) (Z V : Fin 4 → Mat) (F : ℝ) (G : Fin 4 → ℝ)
    (K : Fin 4 → Fin 4 → ℝ) (hZ : ∀ i, symmetric (Z i)) (hV : ∀ i, symmetric (V i))
    (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    |regularizedHessianWeight ε A B Z V F G K| ≤
      4 * |F| + (∑ i, (3 / 2 : ℝ) *
        (normalizedBlockNorm (Z i) + normalizedBlockNorm (V i)) * |G i|) +
      ∑ i, ∑ j, 144 * (normalizedBlockNorm (Z i) + normalizedBlockNorm (V i)) *
        (normalizedBlockNorm (Z j) + normalizedBlockNorm (V j)) * |K i j| := by
  have hscalar : |regularizedWeylWeight ε A B * F| ≤ 4 * |F| := by
    rw [abs_mul, abs_of_pos (regularizedWeylWeight_pos ε hε.le he A B hpinch)]
    exact mul_le_mul_of_nonneg_right
      (regularizedWeylWeight_bounds ε hε.le he A B hpinch).2 (abs_nonneg _)
  have hlinear : |∑ i, regularizedWeylWeightDerivative ε A B (Z i) (V i) * G i| ≤
      ∑ i, (3 / 2 : ℝ) * (normalizedBlockNorm (Z i) + normalizedBlockNorm (V i)) * |G i| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_regularizedWeylWeightDerivative_le
      ε hε he A B (Z i) (V i) (hZ i) (hV i) hpinch) (abs_nonneg _)
  exact (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add hscalar hlinear))
    (abs_regularizedMatrixWeight_le ε hε he A B Z V K hZ hV hpinch))

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

theorem integral_regularizedHessianWeight_tendsto
    (A B : Ω → Mat) (Z V : Fin 4 → Ω → Mat) (F : Ω → ℝ)
    (G : Fin 4 → Ω → ℝ) (K : Fin 4 → Fin 4 → Ω → ℝ)
    (hA : Continuous A) (hB : Continuous B) (hZ : ∀ i, Continuous (Z i))
    (hV : ∀ i, Continuous (V i)) (hF : Continuous F)
    (hG : ∀ i, Continuous (G i)) (hK : ∀ i j, Continuous (K i j))
    (hsZ : ∀ i x, symmetric (Z i x)) (hsV : ∀ i x, symmetric (V i x))
    (hpinch : ∀ x, normalizedBlockNorm (A x) + normalizedBlockNorm (B x) < 2)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (he : ∀ n, ε n ≤ 1 / 3)
    (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, regularizedHessianWeight (ε n) (A x) (B x)
      (fun i => Z i x) (fun i => V i x) (F x) (fun i => G i x)
        (fun i j => K i j x) ∂μ) atTop
      (𝓝 (∫ x, regularizedHessianWeight 0 (A x) (B x)
        (fun i => Z i x) (fun i => V i x) (F x) (fun i => G i x)
          (fun i j => K i j x) ∂μ)) := by
  let N : Fin 4 → Ω → ℝ := fun i x => normalizedBlockNorm (Z i x) + normalizedBlockNorm (V i x)
  have hN (i) : Continuous (N i) :=
    (continuous_normalizedBlockNorm.comp (hZ i)).add
      (continuous_normalizedBlockNorm.comp (hV i))
  apply tendsto_integral_of_dominated_convergence
    (fun x => 4 * |F x| + (∑ i, (3 / 2 : ℝ) * N i x * |G i x|) +
      ∑ i, ∑ j, 144 * N i x * N j x * |K i j x|)
  · intro n
    have hd (i : Fin 4) := continuous_regularizedWeylWeightDerivative (ε n) (hε n)
      A B (Z i) (V i) hA hB (hZ i) (hV i)
    have hw := continuous_regularizedWeylWeight (ε n) A B hA hB
    have hp x := ne_of_gt (regularizedWeylWeight_pos (ε n) (hε n).le (he n) _ _ (hpinch x))
    apply Continuous.aestronglyMeasurable
    unfold regularizedHessianWeight regularizedMatrixWeight
    exact ((hw.mul hF).add (continuous_finsetSum _ (fun i _ => (hd i).mul (hG i)))).add
      (continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
        (((hd i).mul (hd j)).div hw hp).mul (hK i j))))
  · have hc : Continuous (fun x => 4 * |F x| + (∑ i, (3 / 2 : ℝ) * N i x * |G i x|) +
        ∑ i, ∑ j, 144 * N i x * N j x * |K i j x|) :=
      ((continuous_const.mul hF.abs).add (continuous_finsetSum _ (fun i _ =>
        (continuous_const.mul (hN i)).mul (hG i).abs))).add
        (continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
          ((continuous_const.mul (hN i)).mul (hN j)).mul (hK i j).abs)))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro n
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    exact regularizedHessianWeight_bound (ε n) (hε n) (he n) _ _ _ _ _ _ _
      (fun i => hsZ i x) (fun i => hsV i x) (hpinch x)
  · filter_upwards [] with x
    have hd (i : Fin 4) : Tendsto
        (fun n => regularizedWeylWeightDerivative (ε n) (A x) (B x) (Z i x) (V i x)) atTop
        (𝓝 (regularizedWeylWeightDerivative 0 (A x) (B x) (Z i x) (V i x))) := by
      simpa only [Function.comp_def, regularizedWeylWeightDerivative,
        regularizedRadialDerivative, regularizedBlockNorm_zero] using
        (tendsto_regularizedWeylWeightDerivative (A x) (B x) (Z i x) (V i x)).comp hlim
    have hw : Tendsto (fun n => regularizedWeylWeight (ε n) (A x) (B x)) atTop
        (𝓝 (regularizedWeylWeight 0 (A x) (B x))) := by
      simpa only [Function.comp_def, regularizedWeylWeight, regularizedBlockNorm_zero] using
        (tendsto_regularizedWeylWeight (A x) (B x)).comp hlim
    have hl : Tendsto (fun n => ∑ i,
        regularizedWeylWeightDerivative (ε n) (A x) (B x) (Z i x) (V i x) * G i x) atTop
        (𝓝 (∑ i, regularizedWeylWeightDerivative 0 (A x) (B x) (Z i x) (V i x) * G i x)) :=
      tendsto_finsetSum _ (fun i _ => (hd i).mul tendsto_const_nhds)
    have hk : Tendsto (fun n => regularizedMatrixWeight (ε n) (A x) (B x)
        (fun i => Z i x) (fun i => V i x) (fun i j => K i j x)) atTop
        (𝓝 (regularizedMatrixWeight 0 (A x) (B x)
          (fun i => Z i x) (fun i => V i x) (fun i j => K i j x))) := by
      unfold regularizedMatrixWeight
      apply tendsto_finsetSum
      intro i _
      apply tendsto_finsetSum
      intro j _
      exact (((hd i).mul (hd j)).div hw (ne_of_gt
        (regularizedWeylWeight_pos 0 (by norm_num) (by norm_num) _ _ (hpinch x)))).mul
          tendsto_const_nhds
    exact ((hw.mul tendsto_const_nhds).add hl).add hk

end
end PositiveEinsteinFour.Geometry
end


section

/-! The opposite Weyl block acts on the derivative slots of the plus
Hessian. All derivatives of the opposite coefficient are retained. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian CurvatureContraction MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance minusIntegralNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance minusIntegralNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance minusIntegralNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The same classical first-order calculus for the opposite Weyl block,
using the already specified actual parallel frame flow. -/
structure OppositeWeylData {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (d : MetricGreenData g μ) where
  symmetric : ∀ e : FrameBundle g, TraceHessian.symmetric (minusWeyl g e.base e.frame)
  traceFree : ∀ e : FrameBundle g, TraceHessian.traceFree (minusWeyl g e.base e.frame)
  continuousWeyl : Continuous (fun e : FrameBundle g => minusWeyl g e.base e.frame)
  continuousGradient : ∀ i, Continuous
    (fun e : FrameBundle g => minusWeylGradient g e.base e.frame i)
  derivativeWeyl : ∀ i t e, HasDerivAt
    (fun s => minusWeyl g ((d.flow i).map s e).base ((d.flow i).map s e).frame)
    (minusWeylGradient g ((d.flow i).map t e).base ((d.flow i).map t e).frame i) t
  gradientBianchi : ∀ (e : FrameBundle g) s i,
    (∑ r, ∑ k, Angular.oppositeMatrix r i k * minusWeylGradient g e.base e.frame k r s) = 0

private theorem oppositeMatrix_skew (s : Fin 3) (i j : Fin 4) :
    Angular.oppositeMatrix s j i = -Angular.oppositeMatrix s i j := by
  fin_cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [Angular.oppositeMatrix, oppositeQuaternion, quaternionMatrix]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem minusCurvatureGreen (d : MetricGreenData g μ) (o : OppositeWeylData d)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hm : ∀ i t e, HasDerivAt (fun s => m ((d.flow i).map s e))
      (dm i ((d.flow i).map t e)) t) :
    (∫ e, weightedQuadratic
      (fun X => derivativePairing
        (generalCoefficient Angular.oppositeMatrix (minusWeyl g e.base e.frame)) X X)
      (m e) (plusWeylHessian g e.base e.frame)
      (weightTensor (WithLp.toLp 2 (fun i => dm i e))
        (plusGradientTensor g e.base e.frame)) ∂μ) =
    ∫ e, m e * (3 * normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2 *
      weylGradientEnergy (plusWeylGradient g e.base e.frame)) ∂μ := by
  have hcoef (p : Averages.CurvatureIndex) (e : FrameBundle g) :
      frameMinusCoefficient g p e =
        generalCoefficient Angular.oppositeMatrix (minusWeyl g e.base e.frame)
          p.1.1 p.1.2 p.2.1 p.2.2 :=
    (generalCoefficient_eq_blockTensor _ _ _ _ _ _).symm
  have hdcoef (p : Averages.CurvatureIndex) (e : FrameBundle g) :
      frameMinusCoefficientDerivative g p e =
        generalCoefficient Angular.oppositeMatrix (minusWeylGradient g e.base e.frame p.1.2)
          p.1.1 p.1.2 p.2.1 p.2.2 :=
    (generalCoefficient_eq_blockTensor _ _ _ _ _ _).symm
  have hgreen := weighted_metric_minus_curvature_green g d.flow m dm
    (fun p => by
      convert! (generalCoefficientMap Angular.oppositeMatrix p.1.1 p.1.2 p.2.1 p.2.2).continuous.comp
        o.continuousWeyl using 1
      funext e
      exact hcoef p e)
    (fun p => by
      convert! (generalCoefficientMap Angular.oppositeMatrix p.1.1 p.1.2 p.2.1 p.2.2).continuous.comp
        (o.continuousGradient p.1.2) using 1
      funext e
      exact hdcoef p e)
    d.continuousGradientSlice d.continuousHessianSlice d.continuousThirdSlice
    (by
      intro i j l e
      simp only [hdcoef]
      exact generalCoefficient_divergence Angular.oppositeMatrix _ (o.gradientBianchi e) i j l)
    (by
      intro i k j l e
      simp only [hcoef]
      exact generalCoefficient_skew Angular.oppositeMatrix oppositeMatrix_skew _ i k j l)
    hm
    (by
      intro p t e
      convert! (generalCoefficientMap Angular.oppositeMatrix p.1.1 p.1.2 p.2.1 p.2.2).hasFDerivAt.comp_hasDerivAt t
        (o.derivativeWeyl p.1.2 t e) using 1
      · funext s
        exact hcoef p ((d.flow p.1.2).map s e)
      · exact hdcoef p ((d.flow p.1.2).map t e))
    (fun k j t e => hasDerivAt_matrixVector (d.derivativeGradient k j t e))
    (fun k i j t e => hasDerivAt_matrixVector (d.derivativeHessian k i j t e))
  have hp (e : FrameBundle g) :
      derivativeGreenContraction
        (generalCoefficient Angular.oppositeMatrix (minusWeyl g e.base e.frame))
        (fun i k j => plusWeylThirdDerivative g e.base e.frame i k j -
          plusWeylThirdDerivative g e.base e.frame k i j)
        (plusGradientTensor g e.base e.frame) / 6 =
      3 * normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2 *
        weylGradientEnergy (plusWeylGradient g e.base e.frame) := by
    have hr : (fun i k j => plusWeylThirdDerivative g e.base e.frame i k j -
        plusWeylThirdDerivative g e.base e.frame k i j) =
        generalRawCurvatureCommutator (plusWeyl g e.base e.frame)
          (generalEinsteinCoefficient (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
          (plusGradientTensor g e.base e.frame) := by
      funext i k j
      rw [d.outerCommutator e i k j]
      simp only [generalRawCurvatureCommutator, plusGradientTensor,
        rawMatrixSlice_gradientTensor _ (d.gradientConstraints e).1,
        generalEinsteinCoefficient_eq_tensor, ← hdecomp e]
    rw [hr, general_minus_rawGreen _ _ (o.symmetric e) (o.traceFree e),
      trace_square_eq_six_norm_sq _ (o.symmetric e),
      plusGradientTensor_squaredNorm _ _ _ (d.gradientConstraints e).1]
    have he : Angular.gradientSquareNorm (plusWeylGradient g e.base e.frame) =
        6 * weylGradientEnergy (plusWeylGradient g e.base e.frame) := by
      rw [← gradientVector_norm_sq, ← real_inner_self_eq_norm_sq, gradientVector_pairing]
      unfold weylGradientEnergy
      ring
    rw [he]
    ring
  calc
    _ = (1 / 6 : ℝ) * (∫ e, ∑ p : Averages.CurvatureIndex,
        (m e * frameMinusCoefficient g p e *
          matrixPairing (plusWeylHessian g e.base e.frame p.1.1 p.2.1)
            (plusWeylHessian g e.base e.frame p.1.2 p.2.2) +
        dm p.1.2 e * frameMinusCoefficient g p e *
          matrixPairing (plusWeylHessian g e.base e.frame p.1.1 p.2.1)
            (plusWeylGradient g e.base e.frame p.2.2)) ∂μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with e
      rw [weightedQuadratic_derivative_green _
        (generalCoefficient_pair_swap Angular.oppositeMatrix oppositeMatrix_skew _)]
      simp only [hcoef, plusGradientTensor,
        rawMatrixSlice_gradientTensor _ (d.gradientConstraints e).1]
      ring
    _ = _ := by
      rw [hgreen, ← integral_const_mul, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with e
      have hh := hp e
      simp only [hcoef, frameThirdSlice, frameGradientSlice, inner_matrixVector_sub] at *
      simp only [derivativeGreenContraction, plusGradientTensor,
        rawMatrixSlice_gradientTensor _ (d.gradientConstraints e).1] at hh
      simp only [Fintype.sum_prod_type, mul_assoc, ← Finset.mul_sum]
      linear_combination (m e) * hh

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar Green formulas obtained by differentiating the invariant frame
integral. All fields are the actual covariant derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ} [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

theorem scalar_flow_green (i : Fin 4)
    (f df h dh : C(FrameBundle g, ℝ))
    (hf : ∀ t e, HasDerivAt (fun r => f ((d.flow i).map r e)) (df ((d.flow i).map t e)) t)
    (hh : ∀ t e, HasDerivAt (fun r => h ((d.flow i).map r e)) (dh ((d.flow i).map t e)) t) :
    (∫ e, df e * h e ∂μ) = -(∫ e, f e * dh e ∂μ) := by
  have hg := Averages.weighted_flow_green μ (d.flow i).map (d.flow i).continuous
    (d.flow i).preserves (ContinuousMap.const _ 1) (ContinuousMap.const _ 0)
    f df h dh (fun t _ => hasDerivAt_const t 1) hf hh
  simpa only [ContinuousMap.coe_const, Function.const_apply, one_mul, zero_mul, add_zero,
    RCLike.inner_apply, conj_trivial, mul_comm] using hg

namespace ScalarCovariantData

variable {a b : M → ℝ} (s : ScalarCovariantData d a)

def valueField : C(FrameBundle g, ℝ) := ⟨fun e => a e.base, s.continuousValue⟩

def gradientField (i : Fin 4) : C(FrameBundle g, ℝ) :=
  ⟨fun e => scalarGradient g a e i, s.continuousGradient i⟩

def hessianField (i j : Fin 4) : C(FrameBundle g, ℝ) :=
  ⟨fun e => scalarHessian g a e i j, s.continuousHessian i j⟩

def thirdField (i j k : Fin 4) : C(FrameBundle g, ℝ) :=
  ⟨fun e => scalarThird g a e i j k, s.continuousThird i j k⟩

def laplacianField : C(FrameBundle g, ℝ) := ⟨scalarLaplacian g a, s.continuousLaplacian⟩

def laplacianDerivativeField (i : Fin 4) : C(FrameBundle g, ℝ) :=
  ⟨fun e => ∑ j, scalarThird g a e i j j,
    continuous_finsetSum _ (fun j _ => s.continuousThird i j j)⟩

include s

theorem scalar_pairing_green (t : ScalarCovariantData d b) :
    (∫ e, ∑ i, scalarGradient g a e i * scalarGradient g b e i ∂μ) =
      -(∫ e, a e.base * scalarLaplacian g b e ∂μ) := by
  have hi (i : Fin 4) := scalar_flow_green (d := d) i s.valueField (s.gradientField i)
    (t.gradientField i) (t.hessianField i i) (s.derivativeValue i) (t.derivativeGradient i i)
  have hl (i : Fin 4) : Integrable
      (fun e => scalarGradient g a e i * scalarGradient g b e i) μ :=
    ((s.continuousGradient i).mul (t.continuousGradient i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hr (i : Fin 4) : Integrable (fun e => a e.base * scalarHessian g b e i i) μ :=
    (s.continuousValue.mul (t.continuousHessian i i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun i _ => hl i)]
  simp only [valueField, gradientField, hessianField, ContinuousMap.coe_mk] at hi
  simp_rw [hi]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hr i)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with e
  exact (Finset.mul_sum _ _ _).symm

theorem laplacian_square_green :
    (∫ e, scalarLaplacian g a e ^ 2 ∂μ) =
      -(∫ e, ∑ j, scalarGradient g a e j * (∑ i, scalarThird g a e j i i) ∂μ) := by
  have hi (i : Fin 4) := scalar_flow_green (d := d) i s.laplacianField
    (s.laplacianDerivativeField i) (s.gradientField i) (s.hessianField i i)
    (s.derivativeLaplacian i) (s.derivativeGradient i i)
  have hl (i : Fin 4) : Integrable (fun e =>
      (∑ j, scalarThird g a e i j j) * scalarGradient g a e i) μ :=
    ((s.laplacianDerivativeField i).continuous.mul (s.continuousGradient i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hr (i : Fin 4) : Integrable (fun e =>
      scalarLaplacian g a e * scalarHessian g a e i i) μ :=
    (s.continuousLaplacian.mul (s.continuousHessian i i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have heq := congrArg (fun z : Fin 4 → ℝ => ∑ i, z i) (funext hi)
  simp only [laplacianField, laplacianDerivativeField, gradientField, hessianField,
    ContinuousMap.coe_mk, Finset.sum_neg_distrib] at heq
  rw [← integral_finsetSum _ (fun i _ => hl i),
    ← integral_finsetSum _ (fun i _ => hr i)] at heq
  have hrw : (fun e : FrameBundle g => ∑ i, scalarLaplacian g a e * scalarHessian g a e i i) =
      (fun e => scalarLaplacian g a e ^ 2) := by
    funext e
    rw [← Finset.mul_sum]
    exact (pow_two _).symm
  rw [hrw] at heq
  have hlw : (fun e : FrameBundle g => ∑ i, (∑ j, scalarThird g a e i j j) * scalarGradient g a e i) =
      (fun e => ∑ i, scalarGradient g a e i * (∑ j, scalarThird g a e i j j)) := by
    funext e
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [hlw] at heq
  linarith only [heq]

theorem hessian_square_green :
    (∫ e, ∑ j, ∑ i, scalarHessian g a e i j ^ 2 ∂μ) =
      -(∫ e, ∑ j, scalarGradient g a e j * (∑ i, scalarThird g a e i i j) ∂μ) := by
  have hi (j : Fin 4) := Averages.weighted_four_direction_green μ
    (fun i => (d.flow i).map) (fun i => (d.flow i).continuous) (fun i => (d.flow i).preserves)
    (ContinuousMap.const _ 1) (fun _ => ContinuousMap.const _ 0)
    (s.gradientField j) (fun i => s.hessianField i j) (fun i => s.thirdField i i j)
    (fun i t _ => hasDerivAt_const t 1) (fun i => s.derivativeGradient i j)
    (fun i => s.derivativeHessian i i j)
  simp only [ContinuousMap.coe_const, Function.const_apply, one_mul, zero_mul, Finset.sum_const_zero, add_zero,
    gradientField, hessianField, thirdField, ContinuousMap.coe_mk, Real.norm_eq_abs,
    sq_abs, RCLike.inner_apply, conj_trivial, mul_comm] at hi
  have hl (j : Fin 4) : Integrable (fun e => ∑ i, scalarHessian g a e i j ^ 2) μ :=
    (continuous_finsetSum _ (fun i _ => (s.continuousHessian i j).pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hr (j : Fin 4) : Integrable (fun e =>
      scalarGradient g a e j * (∑ i, scalarThird g a e i i j)) μ :=
    ((s.continuousGradient j).mul (continuous_finsetSum _
      (fun i _ => s.continuousThird i i j))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun j _ => hl j)]
  simp_rw [hi]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun j _ => hr j)]

end ScalarCovariantData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth scalar Poisson solvability and covariant differentiation.

Petersen, Riemannian Geometry, third edition author text, §9.1,
Theorem 9.1.2 proof (p.287): the orthogonal image/kernel decomposition
of the Hodge Laplacian. In degree zero on a closed connected manifold,
the kernel is the constants, so every smooth mean-zero function is in
the image. Our Laplacian has the opposite sign, which does not change
its image. The scalar-calculus statement specializes the classical parallel-frame
covariant derivative identities of §3.1.1. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

def PetersenScalarCalculusInput (d : MetricGreenData g μ) : Prop :=
  ∀ a : M → ℝ, ContMDiff I4 𝓘(ℝ, ℝ) ∞ a → Nonempty (ScalarCovariantData d a)

def PetersenPoissonInput (g : SmoothMetric M) (μ : Measure (FrameBundle g)) : Prop :=
  ∀ a : M → ℝ, ContMDiff I4 𝓘(ℝ, ℝ) ∞ a →
    ∃ φ : M → ℝ, ContMDiff I4 𝓘(ℝ, ℝ) ∞ φ ∧
      ∀ e : FrameBundle g, scalarLaplacian g φ e = a e.base - ∫ f, a f.base ∂μ

end
end PositiveEinsteinFour.Geometry

namespace PositiveEinsteinFour.Variance

open MeasureTheory

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem centered_product_integral (a : C(Ω, ℝ)) :
    (∫ x, a x * (a x - ∫ y, a y ∂μ) ∂μ) =
      ∫ x, (a x - ∫ y, a y ∂μ) ^ 2 ∂μ := by
  let m := ∫ x, a x ∂μ
  have hi : Integrable a μ := a.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hd : Integrable (fun x => a x - m) μ := hi.sub (integrable_const m)
  have hs : Integrable (fun x => (a x - m) ^ 2) μ :=
    ((a.continuous.sub continuous_const).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hz : (∫ x, a x - m ∂μ) = 0 := by
    rw [integral_sub hi (integrable_const m)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact sub_self m
  have heq (x : Ω) : a x * (a x - m) = (a x - m) ^ 2 + m * (a x - m) := by ring
  change (∫ x, a x * (a x - m) ∂μ) = ∫ x, (a x - m) ^ 2 ∂μ
  simp_rw [heq]
  rw [integral_add hs (hd.const_mul m), integral_const_mul, hz, mul_zero, add_zero]

end PositiveEinsteinFour.Variance
end


section

/-! The minimum of the constructed normalized spectrum gives exactly
the scalar parameter r in the closed spectral domain. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem shape_exists_minimum_parameter (S : Shape) :
    ∃ r : ℝ, 1 ≤ r ∧ r ≤ 2 ∧ S.sigma = (3 * r - r ^ 3) / 2 ∧
      (∀ i, -r ≤ S.s i) ∧ ∃ i, S.s i = -r := by
  obtain ⟨a, ha⟩ := Finite.exists_min S.s
  have ht := S.trace
  have hn := S.square
  simp only [Fin.sum_univ_three] at ht hn
  fin_cases a
  · obtain ⟨hr, hr2, _, hc⟩ := normalized_eigenvalue_parameter
      (-S.s 0) (S.s 1) (S.s 2) (by linarith only [ht])
      (by nlinarith only [hn]) (by simpa using ha 1) (by simpa using ha 2)
    refine ⟨-S.s 0, hr, hr2, ?_, ?_, 0, by ring⟩
    · unfold Shape.sigma
      simp only [Fin.sum_univ_three, neg_neg] at hc ⊢
      exact hc
    · intro i
      simpa using ha i
  · obtain ⟨hr, hr2, _, hc⟩ := normalized_eigenvalue_parameter
      (-S.s 1) (S.s 0) (S.s 2) (by linarith only [ht])
      (by nlinarith only [hn]) (by simpa using ha 0) (by simpa using ha 2)
    refine ⟨-S.s 1, hr, hr2, ?_, ?_, 1, by ring⟩
    · unfold Shape.sigma
      simp only [Fin.sum_univ_three, neg_neg] at hc ⊢
      linarith only [hc]
    · intro i
      simpa using ha i
  · obtain ⟨hr, hr2, _, hc⟩ := normalized_eigenvalue_parameter
      (-S.s 2) (S.s 0) (S.s 1) (by linarith only [ht])
      (by nlinarith only [hn]) (by simpa using ha 0) (by simpa using ha 1)
    refine ⟨-S.s 2, hr, hr2, ?_, ?_, 2, by ring⟩
    · unfold Shape.sigma
      simp only [Fin.sum_univ_three, neg_neg] at hc ⊢
      linarith only [hc]
    · intro i
      simpa using ha i

theorem conjugateMatrix_posSemidef (R A : Mat) (hA : A.PosSemidef) :
    (conjugateMatrix R A).PosSemidef := by
  simpa only [conjugateMatrix, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hA.conjTranspose_mul_mul_same R

theorem shape_shift_bounds (A R : Mat) (hR : Rᵀ * R = 1)
    (S : Shape) (v x : ℝ)
    (hdiag : conjugateMatrix R A = Matrix.diagonal (fun a => v * S.s a))
    (hAx : (A + x • (1 : Mat)).PosSemidef) :
    ∀ a, -x ≤ v * S.s a := by
  have h := conjugateMatrix_posSemidef R _ hAx
  rw [conjugateMatrix_add, conjugateMatrix_smul, conjugateMatrix_one R hR, hdiag] at h
  intro a
  have hd := h.diag_nonneg (i := a)
  simp only [Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one] at hd
  linarith only [hd]

theorem shape_minimum_parameter_bound (A R : Mat) (hR : Rᵀ * R = 1)
    (S : Shape) (v x r : ℝ)
    (hdiag : conjugateMatrix R A = Matrix.diagonal (fun a => v * S.s a))
    (hAx : (A + x • (1 : Mat)).PosSemidef) (hr : ∃ i, S.s i = -r) :
    v * r ≤ x := by
  obtain ⟨i, hi⟩ := hr
  have h := shape_shift_bounds A R hR S v x hdiag hAx i
  rw [hi] at h
  linarith only [h]

theorem shape_traceCube (A R : Mat) (hR : Rᵀ * R = 1)
    (S : Shape) (v : ℝ)
    (hdiag : conjugateMatrix R A = Matrix.diagonal (fun a => v * S.s a)) :
    Matrix.trace (A * (A * A)) = 6 * v ^ 3 * S.sigma := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  rw [← conjugateMatrix_trace R hR' (A * (A * A)),
    ← conjugateMatrix_mul R hR' A (A * A), ← conjugateMatrix_mul R hR' A A,
    hdiag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  calc
    _ = v ^ 3 * ∑ i, S.s i ^ 3 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by unfold Shape.sigma; ring

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The quadratic and radial scalar contractions are unchanged by the
pointwise spectral frame. These are identities on finite arrays. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem gradientTensor_energy (Z : Angular.Gradient) (hZ : ∀ i, symmetric (Z i)) :
    (gradientTensor Z).squaredNorm / 6 = weylGradientEnergy Z := by
  have h := gradientTensor_pairing Z Z hZ hZ
  rw [rawPairing_vectors] at h
  simp only [real_inner_self_eq_norm_sq] at h
  exact congrArg (fun x : ℝ => x / 6) h

private def slotLinear (A : Mat) : Mat →ₗ[ℝ] Mat where
  toFun := matrixSlotAction A
  map_add' B C := by
    simp only [matrixSlotAction_eq, Matrix.mul_add, Matrix.add_mul,
      Matrix.trace_add, add_div, add_smul]
    module
  map_smul' c B := by
    simp only [matrixSlotAction_eq, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul, smul_add, smul_sub, smul_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

theorem matrixSlotAction_sum_smul {ι : Type*} [Fintype ι]
    (A : Mat) (c : ι → ℝ) (B : ι → Mat) :
    matrixSlotAction A (∑ j, c j • B j) = ∑ j, c j • matrixSlotAction A (B j) := by
  change (slotLinear A) (∑ j, c j • B j) = _
  rw [map_sum]
  simp only [map_smul]
  rfl

theorem turnGradient_slot (R : Mat) (hR : Rᵀ * R = 1) (P : Mat4)
    (A : Mat) (Z : Angular.Gradient) :
    (fun i => matrixSlotAction (conjugateMatrix R A) (turnGradient R P Z i)) =
      turnGradient R P (fun i => matrixSlotAction A (Z i)) := by
  funext i
  rw [turnGradient, matrixSlotAction_sum_smul]
  simp_rw [conjugateMatrix_slot R hR]
  rfl

theorem weylGradientEnergy_turn (R : Mat) (hR : R * Rᵀ = 1)
    (P : Mat4) (hP : P * Pᵀ = 1) (Z : Angular.Gradient) :
    weylGradientEnergy (turnGradient R P Z) = weylGradientEnergy Z := by
  unfold weylGradientEnergy
  rw [turnGradient_pairing R hR P hP]

theorem weylMatrixEnergy_turn (R : Mat) (hR : Rᵀ * R = 1)
    (P : Mat4) (hP : P * Pᵀ = 1) (A : Mat) (Z : Angular.Gradient) :
    weylMatrixEnergy (conjugateMatrix R A) (turnGradient R P Z) =
      weylMatrixEnergy A Z := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  unfold weylMatrixEnergy
  have hs := turnGradient_slot R hR P A Z
  change (∑ i, matrixPairing
    ((fun i => matrixSlotAction (conjugateMatrix R A) (turnGradient R P Z i)) i)
    (turnGradient R P Z i)) / 6 = _
  rw [hs, turnGradient_pairing R hR' P hP]

theorem weylMatrixSquareEnergy_turn (R : Mat) (hR : Rᵀ * R = 1)
    (P : Mat4) (hP : P * Pᵀ = 1) (A : Mat) (Z : Angular.Gradient) :
    weylMatrixEnergy (traceFreeSquare (conjugateMatrix R A)) (turnGradient R P Z) =
      weylMatrixEnergy (traceFreeSquare A) Z := by
  rw [conjugateMatrix_traceFreeSquare R hR, weylMatrixEnergy_turn R hR P hP]

/-- The radial trace is a covector under the same actual four-frame change. -/
theorem trace_turnGradient (R : Mat) (hR : R * Rᵀ = 1) (P : Mat4)
    (A : Mat) (Z : Angular.Gradient) (i : Fin 4) :
    Matrix.trace (conjugateMatrix R A * turnGradient R P Z i) =
      ∑ j, P j i * Matrix.trace (A * Z j) := by
  simp only [turnGradient, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, conjugateMatrix_mul R hR, conjugateMatrix_trace R hR,
    smul_eq_mul]

theorem orthogonal_square_sum (P : Mat4) (hP : P * Pᵀ = 1)
    (a : Fin 4 → ℝ) :
    (∑ i, (∑ j, P j i * a j) ^ 2) = ∑ j, a j ^ 2 := by
  have hp (j k : Fin 4) : (∑ i, P j i * P k i) = if j = k then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      congrArg (fun N : Mat4 => N j k) hP
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ j, ∑ i, ∑ k, (P j i * P k i) * (a j * a k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ j, ∑ k, ∑ i, (P j i * P k i) * (a j * a k) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = _ := by simp only [← Finset.sum_mul, hp]; simp

theorem weylRadialSquare_turn (R : Mat) (hR : R * Rᵀ = 1)
    (P : Mat4) (hP : P * Pᵀ = 1) (A : Mat) (Z : Angular.Gradient) :
    weylRadialSquare (conjugateMatrix R A) (turnGradient R P Z) =
      weylRadialSquare A Z := by
  unfold weylRadialSquare
  simp_rw [trace_turnGradient R hR]
  rw [orthogonal_square_sum P hP]

private theorem orthogonal_matrix_contraction (P : Mat4) (hP : P * Pᵀ = 1)
    (f : Fin 4 → Fin 4 → Mat) :
    (∑ i, ∑ j, ∑ k, (P j i * P k i) • f j k) = ∑ j, f j j := by
  have hp (j k : Fin 4) : (∑ i, P j i * P k i) = if j = k then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      congrArg (fun N : Mat4 => N j k) hP
  calc
    _ = ∑ j, ∑ i, ∑ k, (P j i * P k i) • f j k := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, (P j i * P k i) • f j k := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ j, ∑ k, (if j = k then (1 : ℝ) else 0) • f j k := by
      simp only [← Finset.sum_smul, hp]
    _ = _ := by simp

theorem sum_squares_turnGradient (R : Mat) (hR : R * Rᵀ = 1)
    (P : Mat4) (hP : P * Pᵀ = 1) (Z : Angular.Gradient) :
    (∑ i, turnGradient R P Z i * turnGradient R P Z i) =
      conjugateMatrix R (∑ i, Z i * Z i) := by
  simp only [turnGradient, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul, Finset.smul_sum, smul_smul, conjugateMatrix_mul R hR]
  change (∑ i, ∑ j, ∑ k, (P j i * P k i) • conjugateMatrix R (Z k * Z j)) = _
  rw [orthogonal_matrix_contraction P hP, conjugateMatrix_sum]

theorem weighted_sum_turnGradient (R : Mat) (P : Mat4) (hP : P * Pᵀ = 1)
    (a : Fin 4 → ℝ) (Z : Angular.Gradient) :
    (∑ i, (∑ k, P k i * a k) • turnGradient R P Z i) =
      conjugateMatrix R (∑ j, a j • Z j) := by
  change (∑ i, (∑ k, P k i * a k) •
    (∑ j, P j i • conjugateMatrix R (Z j))) = _
  calc
    _ = ∑ i, ∑ k, ∑ j, (P k i * a k) •
        (P j i • conjugateMatrix R (Z j)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_smul]
      simp only [Finset.smul_sum]
    _ = ∑ i, ∑ k, ∑ j, (P k i * P j i) • (a k • conjugateMatrix R (Z j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      simp only [smul_smul]
      congr 1
      ring
    _ = ∑ j, a j • conjugateMatrix R (Z j) := orthogonal_matrix_contraction P hP _
    _ = _ := by simp only [conjugateMatrix_sum, conjugateMatrix_smul]

def weightedCubicField (a : Fin 4 → ℝ) (Z : Angular.Gradient) : ℝ :=
  ∑ i, a i * Matrix.trace (Z i * (∑ j, Z j * Z j))

theorem weightedCubicField_eq (a : Fin 4 → ℝ) (Z : Angular.Gradient) :
    weightedCubicField a Z =
      Matrix.trace ((∑ i, a i • Z i) * (∑ j, Z j * Z j)) := by
  simp only [weightedCubicField, Matrix.sum_mul, Matrix.smul_mul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]

/-- The full cubic trace, including its distinguished covector, is
preserved by the same local change of frame. -/
theorem weightedCubicField_turn (R : Mat) (hR : R * Rᵀ = 1)
    (P : Mat4) (hP : P * Pᵀ = 1) (a : Fin 4 → ℝ) (Z : Angular.Gradient) :
    weightedCubicField (fun i => ∑ k, P k i * a k) (turnGradient R P Z) =
      weightedCubicField a Z := by
  rw [weightedCubicField_eq, weighted_sum_turnGradient R P hP,
    sum_squares_turnGradient R hR P hP, conjugateMatrix_mul R hR,
    conjugateMatrix_trace R hR, weightedCubicField_eq]

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! Positivity of the original full-matrix weighted curvature form. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

theorem generalOriginalCurvatureForm_eq (A U : Mat) (X : Hessian)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (hX : condition X) :
    generalOriginalCurvatureForm A U X = generalCasimirCurvatureForm A U X :=
  generalOriginalCurvatureForm_eq_of_inner_bianchi A U X hA hU htA htU
    hX.2.1 hX.2.2.2

/-- The exact coercive constant for the original Green curvature form
holds in every orthonormal frame. -/
theorem generalOriginalCurvatureForm_lower (A U : Mat) (X : Hessian)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (hX : condition X) (x y : ℝ)
    (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) :
    (4 - 2 * x - 2 * y) * hessianNormSq X ≤ generalOriginalCurvatureForm A U X := by
  rw [generalOriginalCurvatureForm_eq A U X hA hU htA htU hX]
  exact generalCasimirCurvatureForm_lower A U X hX x y hAx hUy

/-- Positivity includes the closed sectional boundary, with no local or
global diagonalization hypothesis. -/
theorem generalOriginalCurvatureForm_nonneg (A U : Mat) (X : Hessian)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (hX : condition X) (x y : ℝ)
    (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2) :
    0 ≤ generalOriginalCurvatureForm A U X := by
  rw [generalOriginalCurvatureForm_eq A U X hA hU htA htU hX]
  exact generalCasimirCurvatureForm_nonneg A U X hX x y hAx hUy hxy

private theorem generalCasimir_add_smul (A U : Mat) (X Y : Hessian) (c : ℝ) :
    generalCasimirCurvatureForm A U (X + c • Y) =
      generalCasimirCurvatureForm A U X +
      c * (generalCasimirCurvatureForm A U (X + Y) -
        generalCasimirCurvatureForm A U X - generalCasimirCurvatureForm A U Y) +
      c ^ 2 * generalCasimirCurvatureForm A U Y := by
  unfold generalCasimirCurvatureForm hessianGram
  simp_rw [← hessianPairing_self, totalPlus_add, totalPlus_smul,
    totalMinus_add, totalMinus_smul, hessianPairing_add_left, hessianPairing_add_right,
    hessianPairing_smul_left, hessianPairing_smul_right]
  simp only [Fin.sum_univ_three]
  ring

/-- The local weighted square in the original arbitrary-matrix Green
form, before any projection cost or global integration. -/
theorem generalOriginal_weighted_square (A U : Mat) (X Y : Hessian)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (hX : condition X) (hY : condition Y) (x y m : ℝ) (hm : 0 < m)
    (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2) :
    0 ≤ weightedQuadratic (generalOriginalCurvatureForm A U) m X Y +
      generalOriginalCurvatureForm A U Y / (24 * m) := by
  obtain ⟨c, rfl⟩ := exists_highest X hX
  obtain ⟨d, rfl⟩ := exists_highest Y hY
  have hsum : condition (highest c + highest d) := by
    rw [← highest_add]
    exact highest_condition _
  have hscaled : condition (highest c + (1 / (2 * m)) • highest d) := by
    rw [← highest_smul, ← highest_add]
    exact highest_condition _
  have hp := generalOriginalCurvatureForm_nonneg A U _ hA hU htA htU hscaled
    x y hAx hUy hxy
  have he : (m / 6) * generalOriginalCurvatureForm A U
      (highest c + (1 / (2 * m)) • highest d) =
      weightedQuadratic (generalOriginalCurvatureForm A U) m (highest c) (highest d) +
      generalOriginalCurvatureForm A U (highest d) / (24 * m) := by
    unfold weightedQuadratic
    rw [generalOriginalCurvatureForm_eq A U _ hA hU htA htU hscaled,
      generalOriginalCurvatureForm_eq A U _ hA hU htA htU (highest_condition c),
      generalOriginalCurvatureForm_eq A U _ hA hU htA htU (highest_condition d),
      generalOriginalCurvatureForm_eq A U _ hA hU htA htU hsum,
      generalCasimir_add_smul]
    field_simp [hm.ne']
    ring
  rw [← he]
  exact mul_nonneg (by positivity) hp

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! The actual spectral minimum is itself an admissible curvature shift.
This permits the coefficient `y=b*s`, rather than an arbitrary
larger positive-semidefinite shift. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem conjugateMatrix_inverse (R : Mat) (hR : R * Rᵀ = 1) (A : Mat) :
    conjugateMatrix Rᵀ (conjugateMatrix R A) = A := by
  unfold conjugateMatrix
  rw [Matrix.transpose_transpose]
  calc
    R * (Rᵀ * A * R) * Rᵀ = (R * Rᵀ) * A * (R * Rᵀ) := by
      simp only [Matrix.mul_assoc]
    _ = A := by rw [hR, Matrix.one_mul, Matrix.mul_one]

/-- The lower bound on every normalized eigenvalue gives positive
semidefiniteness at the exact minimum shift. -/
theorem shape_minimum_shift_posSemidef (A R : Mat) (hR : Rᵀ * R = 1)
    (S : Shape) (v r : ℝ) (hv : 0 ≤ v)
    (hdiag : conjugateMatrix R A = Matrix.diagonal (fun i => v * S.s i))
    (hmin : ∀ i, -r ≤ S.s i) :
    (A + (v * r) • (1 : Mat)).PosSemidef := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  have hnon (i : Fin 3) : 0 ≤ v * S.s i + v * r := by
    have hp := mul_nonneg hv (show 0 ≤ S.s i + r by linarith only [hmin i])
    nlinarith only [hp]
  have hsum : Matrix.diagonal (fun i => v * S.s i + v * r) =
      Matrix.diagonal (fun i => v * S.s i) + (v * r) • (1 : Mat) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.add_apply, Matrix.smul_apply, hij]
  have hp : (conjugateMatrix R (A + (v * r) • (1 : Mat))).PosSemidef := by
    rw [conjugateMatrix_add, conjugateMatrix_smul, conjugateMatrix_one R hR, hdiag, ← hsum]
    exact Matrix.posSemidef_diagonal_iff.mpr hnon
  have hb := conjugateMatrix_posSemidef Rᵀ _ hp
  rw [conjugateMatrix_inverse R hR'] at hb
  exact hb

/-- Both constructed spectral minima remain within any admissible pair
of shifts. This is precisely the parameter domain `v*r+b*s<=2`. -/
theorem minimum_spectral_sum_le_two
    (A U R T : Mat) (hR : Rᵀ * R = 1) (hT : Tᵀ * T = 1)
    (S V : Shape) (v b r s x y : ℝ)
    (hA : conjugateMatrix R A = Matrix.diagonal (fun i => v * S.s i))
    (hU : conjugateMatrix T U = Matrix.diagonal (fun i => b * V.s i))
    (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2)
    (hr : ∃ i, S.s i = -r) (hs : ∃ i, V.s i = -s) :
    v * r + b * s ≤ 2 := by
  have ha := shape_minimum_parameter_bound A R hR S v x r hA hAx hr
  have hu := shape_minimum_parameter_bound U T hT V b y s hU hUy hs
  linarith only [ha, hu, hxy]

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! Polarized real-vector cost identities in twelve Bianchi coordinates,
including the three off-diagonal generator pairs. -/

namespace PositiveEinsteinFour.Bianchi

open scoped BigOperators
open TraceHessian HighestHessian

noncomputable section

def coordinatePairing (v w : Fin 3 → Vec) : ℝ :=
  10 * inner ℝ (v 0) (w 0) + 30 * inner ℝ (v 1) (w 1) + 6 * inner ℝ (v 2) (w 2)

private theorem coordinatePairing_comm (v w : Fin 3 → Vec) :
    coordinatePairing v w = coordinatePairing w v := by
  unfold coordinatePairing
  rw [real_inner_comm (v 0) (w 0), real_inner_comm (v 1) (w 1),
    real_inner_comm (v 2) (w 2)]

private theorem reverse_coefficient_pairing (s t : Fin 3) (v : Fin 3 → Vec)
    (h : (∑ r, coordinatePairing (costCoefficientCoordinates s r v)
      (costCoefficientCoordinates t r v)) =
        44 * coordinatePairing (generatorCoordinates s v) (generatorCoordinates t v)) :
    (∑ r, coordinatePairing (costCoefficientCoordinates t r v)
      (costCoefficientCoordinates s r v)) =
        44 * coordinatePairing (generatorCoordinates t v) (generatorCoordinates s v) := by
  calc
    _ = ∑ r, coordinatePairing (costCoefficientCoordinates s r v)
        (costCoefficientCoordinates t r v) := by
      apply Finset.sum_congr rfl
      intro r _
      exact coordinatePairing_comm _ _
    _ = 44 * coordinatePairing (generatorCoordinates s v) (generatorCoordinates t v) := h
    _ = _ := congrArg (fun z : ℝ => 44 * z) (coordinatePairing_comm _ _)

theorem rawPairing_eq_rawNorm (Z : RawGradient) : rawPairing Z Z = rawNorm Z := by
  rw [rawPairing_vectors]
  simp only [real_inner_self_eq_norm_sq, rawNorm]

theorem costParameters_pairing (v w : Fin 3 → Vec) :
    rawPairing (costParameters v).matrix (costParameters w).matrix =
      coordinatePairing v w := by
  have h : rawPairing (costParameters (v + w)).matrix (costParameters (v + w)).matrix =
      coordinateNorm (v + w) := by
    rw [rawPairing_eq_rawNorm, rawNorm_matrix, costParameters_norm]
  simp only [costParameters_matrix_add, rawPairing_add_left, rawPairing_add_right] at h
  rw [rawPairing_comm (costParameters w).matrix (costParameters v).matrix] at h
  simp only [rawPairing_eq_rawNorm, rawNorm_matrix, costParameters_norm] at h
  simp only [coordinateNorm, Pi.add_apply, norm_add_sq_real] at h
  unfold coordinatePairing
  linarith

private theorem coefficient_pairing_01 (v : Fin 3 → Vec) :
    (∑ r, coordinatePairing (costCoefficientCoordinates 0 r v)
      (costCoefficientCoordinates 1 r v)) =
      44 * coordinatePairing (generatorCoordinates 0 v) (generatorCoordinates 1 v) := by
  simp [coordinatePairing, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, next, previous, quaternion, PiLp.inner_apply,
    RCLike.inner_apply, Fin.sum_univ_three, Fin.sum_univ_four]
  ring

private theorem coefficient_pairing_02 (v : Fin 3 → Vec) :
    (∑ r, coordinatePairing (costCoefficientCoordinates 0 r v)
      (costCoefficientCoordinates 2 r v)) =
      44 * coordinatePairing (generatorCoordinates 0 v) (generatorCoordinates 2 v) := by
  simp [coordinatePairing, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, next, previous, quaternion, PiLp.inner_apply,
    RCLike.inner_apply, Fin.sum_univ_three, Fin.sum_univ_four]
  ring

private theorem coefficient_pairing_12 (v : Fin 3 → Vec) :
    (∑ r, coordinatePairing (costCoefficientCoordinates 1 r v)
      (costCoefficientCoordinates 2 r v)) =
      44 * coordinatePairing (generatorCoordinates 1 v) (generatorCoordinates 2 v) := by
  simp [coordinatePairing, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, next, previous, quaternion, PiLp.inner_apply,
    RCLike.inner_apply, Fin.sum_univ_three, Fin.sum_univ_four]
  ring

private theorem rawCostCoefficient_pairing_of_ne (s t : Fin 3) (hst : s ≠ t)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ r, rawPairing (rawCostCoefficient s r Z.matrix) (rawCostCoefficient t r Z.matrix)) =
      44 * rawPairing (rawGradientGenerator s Z.matrix) (rawGradientGenerator t Z.matrix) := by
  obtain ⟨v, rfl⟩ := exists_costParameters Z hz hb
  simp_rw [rawCostCoefficient_coordinates, generator_coordinates, costParameters_pairing]
  fin_cases s <;> fin_cases t
  · exact (hst rfl).elim
  · exact coefficient_pairing_01 v
  · exact coefficient_pairing_02 v
  · exact reverse_coefficient_pairing 0 1 v (coefficient_pairing_01 v)
  · exact (hst rfl).elim
  · exact coefficient_pairing_12 v
  · exact reverse_coefficient_pairing 0 2 v (coefficient_pairing_02 v)
  · exact reverse_coefficient_pairing 1 2 v (coefficient_pairing_12 v)
  · exact (hst rfl).elim

/-- The full polarized coefficient identity, including the trace term. -/
theorem rawCostCoefficient_pairing (s t : Fin 3)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ r, rawPairing (rawCostCoefficient s r Z.matrix) (rawCostCoefficient t r Z.matrix)) =
      (if s = t then 84 * Z.squaredNorm else 0) +
        44 * rawPairing (rawGradientGenerator s Z.matrix) (rawGradientGenerator t Z.matrix) := by
  by_cases hst : s = t
  · subst t
    simp only [ite_true, rawPairing_eq_rawNorm]
    have h := rawCostCoefficient_norm s Z hz hb
    linarith
  · simp only [hst, ite_false, zero_add]
    exact rawCostCoefficient_pairing_of_ne s t hst Z hz hb

end
end PositiveEinsteinFour.Bianchi
end


section

/-! The opposite Weyl block has the same derived gradient constraints and
zero-set calculus, using its actual parallel-frame derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff

noncomputable section

local instance oppositeZeroNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance oppositeZeroNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance oppositeZeroNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem OppositeWeylData.gradientConstraints {d : MetricGreenData g μ}
    (o : OppositeWeylData d) (e : FrameBundle g) :
    (∀ i, TraceHessian.symmetric (minusWeylGradient g e.base e.frame i)) ∧
    (∀ i, TraceHessian.traceFree (minusWeylGradient g e.base e.frame i)) := by
  have hi (i : Fin 4) : TraceHessian.symmetric (minusWeylGradient g e.base e.frame i) ∧
      TraceHessian.traceFree (minusWeylGradient g e.base e.frame i) := by
    obtain ⟨e₀, he⟩ := ((d.flow i).map 0).surjective e
    change (d.flow i).map 0 e₀ = e at he
    have hs := symmetric_of_hasDerivAt (o.derivativeWeyl i 0 e₀)
      (fun t => o.symmetric ((d.flow i).map t e₀))
    have ht := traceFree_of_hasDerivAt (o.derivativeWeyl i 0 e₀)
      (fun t => o.traceFree ((d.flow i).map t e₀))
    rw [he] at hs ht
    exact ⟨hs, ht⟩
  exact ⟨fun i => (hi i).1, fun i => (hi i).2⟩

theorem OppositeWeylData.gradient_zero_ae_on_zero {d : MetricGreenData g μ}
    [SFinite μ] (o : OppositeWeylData d) :
    ∀ᵐ e ∂μ, minusWeyl g e.base e.frame = 0 →
      ∀ i, minusWeylGradient g e.base e.frame i = 0 := by
  have hc (i : Fin 4) (a b : Fin 3) :
      ∀ᵐ e ∂μ, minusWeyl g e.base e.frame a b = 0 →
        minusWeylGradient g e.base e.frame i a b = 0 :=
    ae_flow_derivative_zero_on_level μ (fun t => (d.flow i).map t)
      (d.flow i).continuous (d.flow i).preserves
      (fun e => minusWeyl g e.base e.frame a b)
      (fun e => minusWeylGradient g e.base e.frame i a b)
      ((matrixEntryMap a b).continuous.comp o.continuousWeyl)
      ((matrixEntryMap a b).continuous.comp (o.continuousGradient i))
      (fun t e => hasDerivAt_matrixEntry (o.derivativeWeyl i t e) a b) 0
  have hall : ∀ᵐ e ∂μ, ∀ i a b, minusWeyl g e.base e.frame a b = 0 →
      minusWeylGradient g e.base e.frame i a b = 0 :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun a => ae_all_iff.mpr (fun b => hc i a b)))
  filter_upwards [hall] with e he
  intro hz i
  ext a b
  exact he i a b (congrArg (fun A : Mat => A a b) hz)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The small classical smooth-bundle input needed to use scalar Poisson
solutions on one oriented frame component. Smoothness of the squared norm
and invariance under oriented orthonormal frames are the ordinary metric
bundle calculus of Petersen §2.2 and §3.1.1. The scalar gradient identities
below are derived from parallel differentiation; no variance estimate is
included in the input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

structure PetersenOrientedNormInput (orientation : FrameOrientation g) : Prop where
  plusSquareSmooth : ContMDiff I4 𝓘(ℝ, ℝ) ∞ (fun c => plusNorm orientation c ^ 2)
  minusSquareSmooth : ContMDiff I4 𝓘(ℝ, ℝ) ∞ (fun c => minusNorm orientation c ^ 2)
  plusFrame : ∀ e ∈ orientation.positive,
    plusNorm orientation e.base = normalizedBlockNorm (plusWeyl g e.base e.frame)
  minusFrame : ∀ e ∈ orientation.positive,
    minusNorm orientation e.base = normalizedBlockNorm (minusWeyl g e.base e.frame)

def OrientationPreservingFlow (d : MetricGreenData g μ) (orientation : FrameOrientation g) : Prop :=
  ∀ i t e, (d.flow i).map t e ∈ orientation.positive ↔ e ∈ orientation.positive

def orientedNormRegularization (b : M → ℝ) (ε : ℝ) (c : M) : ℝ :=
  Real.sqrt (b c ^ 2 + ε ^ 2)

omit [IsManifold I4 ∞ M] in
theorem orientedNormRegularization_smooth {b : M → ℝ}
    (hb : ContMDiff I4 𝓘(ℝ, ℝ) ∞ (fun c => b c ^ 2)) {ε : ℝ} (hε : 0 < ε) :
    ContMDiff I4 𝓘(ℝ, ℝ) ∞ (orientedNormRegularization b ε) := by
  intro c
  have h : ContMDiffAt I4 𝓘(ℝ, ℝ) ∞ (fun c => b c ^ 2 + ε ^ 2) c :=
    (hb.add contMDiff_const).contMDiffAt
  have hp : 0 < b c ^ 2 + ε ^ 2 := by
    nlinarith [sq_nonneg (b c), sq_pos_of_pos hε]
  exact (Real.contDiffAt_sqrt (ne_of_gt hp)).comp_contMDiffAt
    (f := fun c : M => b c ^ 2 + ε ^ 2) h

theorem scalarGradient_eq_of_frame_derivative {d : MetricGreenData g μ}
    {a : M → ℝ} (s : ScalarCovariantData d a) (orientation : FrameOrientation g)
    (hflow : OrientationPreservingFlow d orientation)
    (F : FrameBundle g → ℝ) (Q : Fin 4 → FrameBundle g → ℝ)
    (hvalue : ∀ e ∈ orientation.positive, a e.base = F e)
    (hderiv : ∀ i t e, HasDerivAt (fun r => F ((d.flow i).map r e))
      (Q i ((d.flow i).map t e)) t)
    (e : FrameBundle g) (he : e ∈ orientation.positive) (i : Fin 4) :
    scalarGradient g a e i = Q i e := by
  obtain ⟨e₀, he₀⟩ := ((d.flow i).map 0).surjective e
  change (d.flow i).map 0 e₀ = e at he₀
  have hp : e₀ ∈ orientation.positive := (hflow i 0 e₀).mp (he₀.symm ▸ he)
  have hf : (fun r => a ((d.flow i).map r e₀).base) =
      fun r => F ((d.flow i).map r e₀) :=
    funext (fun r => hvalue _ ((hflow i r e₀).mpr hp))
  have hs := s.derivativeValue i 0 e₀
  rw [hf] at hs
  have hu := hs.unique (hderiv i 0 e₀)
  simpa only [he₀] using hu

theorem regularizedRadialDerivative_scale (ε : ℝ) (A Z : Mat) :
    regularizedRadialDerivative ε A Z =
      (normalizedBlockNorm A / regularizedBlockNorm ε A) *
        regularizedRadialDerivative 0 A Z := by
  by_cases ha : normalizedBlockNorm A = 0
  · have hA := (normalizedBlockNorm_eq_zero_iff A).mp ha
    subst A
    simp [regularizedRadialDerivative]
  · unfold regularizedRadialDerivative
    rw [regularizedBlockNorm_zero]
    field_simp

theorem scalarGradient_sub_of_data {d : MetricGreenData g μ} {a b : M → ℝ}
    (sa : ScalarCovariantData d a) (sb : ScalarCovariantData d b)
    (s : ScalarCovariantData d (fun c => a c - b c))
    (e : FrameBundle g) (i : Fin 4) :
    scalarGradient g (fun c => a c - b c) e i =
      scalarGradient g a e i - scalarGradient g b e i := by
  obtain ⟨e₀, he₀⟩ := ((d.flow i).map 0).surjective e
  change (d.flow i).map 0 e₀ = e at he₀
  have h := (s.derivativeValue i 0 e₀).unique
    ((sa.derivativeValue i 0 e₀).sub (sb.derivativeValue i 0 e₀))
  simpa only [he₀] using h

theorem scalarGradient_H_of_data {d : MetricGreenData g μ} {a : M → ℝ}
    (sa : ScalarCovariantData d a) (s : ScalarCovariantData d (fun c => MomentObstruction.H (a c)))
    (e : FrameBundle g) (he : 0 < a e.base) (i : Fin 4) :
    scalarGradient g (fun c => MomentObstruction.H (a c)) e i =
      (Variance.derivativeRatio (a e.base) / (2 * Real.sqrt (a e.base))) *
        scalarGradient g a e i := by
  obtain ⟨e₀, he₀⟩ := ((d.flow i).map 0).surjective e
  change (d.flow i).map 0 e₀ = e at he₀
  have hp : 0 < a ((d.flow i).map 0 e₀).base := he₀.symm ▸ he
  have hH : HasDerivAt MomentObstruction.H
      (Variance.derivativeRatio (a ((d.flow i).map 0 e₀).base) /
        (2 * Real.sqrt (a ((d.flow i).map 0 e₀).base))) (a ((d.flow i).map 0 e₀).base) :=
    Variance.hasDerivAt_H hp
  have hd := hH.comp 0 (sa.derivativeValue i 0 e₀)
  have h := (s.derivativeValue i 0 e₀).unique hd
  simpa only [he₀] using h

omit [IsManifold I4 ∞ M] in
theorem contMDiff_H_of_pos {a : M → ℝ} (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a)
    (hp : ∀ c, 0 < a c) : ContMDiff I4 𝓘(ℝ, ℝ) ∞ (fun c => MomentObstruction.H (a c)) := by
  have hs : ContMDiff I4 𝓘(ℝ, ℝ) ∞ (fun c => Real.sqrt (a c)) := by
    intro c
    exact (Real.contDiffAt_sqrt (ne_of_gt (hp c))).comp_contMDiffAt (f := a) ha.contMDiffAt
  unfold MomentObstruction.H
  exact hs.mul ((contMDiff_const.add ((ha.pow 2).div_const 40)).sub ((ha.pow 4).div_const 1152))

namespace PetersenOrientedNormInput

variable {orientation : FrameOrientation g} (h : PetersenOrientedNormInput orientation)
  {d : MetricGreenData g μ}

include h

theorem plus_regularized_gradient (hflow : OrientationPreservingFlow d orientation)
    {ε : ℝ} (hε : 0 < ε)
    (s : ScalarCovariantData d (orientedNormRegularization (plusNorm orientation) ε))
    (e : FrameBundle g) (he : e ∈ orientation.positive) (i : Fin 4) :
    scalarGradient g (orientedNormRegularization (plusNorm orientation) ε) e i =
      regularizedRadialDerivative ε (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) := by
  apply scalarGradient_eq_of_frame_derivative s orientation hflow
    (fun e => regularizedBlockNorm ε (plusWeyl g e.base e.frame))
    (fun i e => regularizedRadialDerivative ε (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i))
  · intro f hf
    unfold orientedNormRegularization regularizedBlockNorm
    rw [h.plusFrame f hf]
  · intro j t f
    exact hasDerivAt_regularizedBlockNorm (d.derivativeWeyl j t f)
      (fun r => d.weyl.symmetric ((d.flow j).map r f)) hε
  · exact he

theorem minus_regularized_gradient (o : OppositeWeylData d)
    (hflow : OrientationPreservingFlow d orientation) {ε : ℝ} (hε : 0 < ε)
    (s : ScalarCovariantData d (orientedNormRegularization (minusNorm orientation) ε))
    (e : FrameBundle g) (he : e ∈ orientation.positive) (i : Fin 4) :
    scalarGradient g (orientedNormRegularization (minusNorm orientation) ε) e i =
      regularizedRadialDerivative ε (minusWeyl g e.base e.frame)
        (minusWeylGradient g e.base e.frame i) := by
  apply scalarGradient_eq_of_frame_derivative s orientation hflow
    (fun e => regularizedBlockNorm ε (minusWeyl g e.base e.frame))
    (fun i e => regularizedRadialDerivative ε (minusWeyl g e.base e.frame)
      (minusWeylGradient g e.base e.frame i))
  · intro f hf
    unfold orientedNormRegularization regularizedBlockNorm
    rw [h.minusFrame f hf]
  · intro j t f
    exact hasDerivAt_regularizedBlockNorm (o.derivativeWeyl j t f)
      (fun r => o.symmetric ((d.flow j).map r f)) hε
  · exact he

end PetersenOrientedNormInput

end
end PositiveEinsteinFour.Geometry
end


section

/-! Covariance of the quaternionic Bianchi constraint under a genuine
oriented four-frame lift. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

def turnVector (P : Mat4) (v : Vec) : Vec := WithLp.toLp 2 (Pᵀ *ᵥ (v : Fin 4 → ℝ))

theorem turnVector_add (P : Mat4) (v w : Vec) :
    turnVector P (v + w) = turnVector P v + turnVector P w := by
  ext i
  simp only [turnVector, Matrix.mulVec, dotProduct, PiLp.add_apply,
    mul_add, Finset.sum_add_distrib]

theorem turnVector_smul (P : Mat4) (c : ℝ) (v : Vec) :
    turnVector P (c • v) = c • turnVector P v := by
  ext i
  simp only [turnVector, Matrix.mulVec, dotProduct, PiLp.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem turnVector_sum {ι : Type*} [Fintype ι] (P : Mat4) (v : ι → Vec) :
    turnVector P (∑ i, v i) = ∑ i, turnVector P (v i) := by
  ext j
  simp only [turnVector, Matrix.mulVec, dotProduct, WithLp.ofLp_sum,
    Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem turnVector_zero (P : Mat4) : turnVector P 0 = 0 := by
  ext i
  simp [turnVector]

theorem turnVector_norm (P : Mat4) (hP : P * Pᵀ = 1) (v : Vec) :
    ‖turnVector P v‖ = ‖v‖ := by
  have hs : ‖turnVector P v‖ ^ 2 = ‖v‖ ^ 2 := by
    simpa only [EuclideanSpace.real_norm_sq_eq, turnVector, Matrix.mulVec,
      Matrix.transpose_apply, dotProduct] using orthogonal_square_sum P hP v
  nlinarith [norm_nonneg (turnVector P v), norm_nonneg v]

/-- The passive vector change intertwines each imaginary quaternion
with its rotated linear combination. -/
theorem QuaternionLift.quaternion_turnVector {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (s : Fin 3) (v : Vec) :
    quaternion s (turnVector P.matrix v) =
      turnVector P.matrix (∑ r, R r s • quaternion r v) := by
  have hp : quaternionMatrix s * P.matrixᵀ =
      P.matrixᵀ * (∑ r, R r s • quaternionMatrix r) := by
    calc
      _ = (P.matrixᵀ * P.matrix) * (quaternionMatrix s * P.matrixᵀ) := by
        rw [P.orthogonal, Matrix.one_mul]
      _ = P.matrixᵀ * (P.matrix * quaternionMatrix s) * P.matrixᵀ := by
        simp only [Matrix.mul_assoc]
      _ = P.matrixᵀ * ((∑ r, R r s • quaternionMatrix r) * P.matrix) * P.matrixᵀ := by
        rw [P.intertwines]
      _ = P.matrixᵀ * (∑ r, R r s • quaternionMatrix r) *
          (P.matrix * P.matrixᵀ) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [P.mul_transpose, Matrix.mul_one]
  have hsum : (∑ r, R r s • quaternionMatrix r) *ᵥ (v : Fin 4 → ℝ) =
      ((∑ r, R r s • quaternion r v : Vec) : Fin 4 → ℝ) := by
    ext j
    simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply,
      Pi.smul_apply, WithLp.ofLp_sum, PiLp.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [← quaternionMatrix_apply]
    rfl
  ext i
  calc
    _ = (quaternionMatrix s *ᵥ (P.matrixᵀ *ᵥ (v : Fin 4 → ℝ))) i := by
      rw [← quaternionMatrix_apply]
      rfl
    _ = ((quaternionMatrix s * P.matrixᵀ) *ᵥ (v : Fin 4 → ℝ)) i := by
      rw [Matrix.mulVec_mulVec]
    _ = ((P.matrixᵀ * (∑ r, R r s • quaternionMatrix r)) *ᵥ (v : Fin 4 → ℝ)) i := by rw [hp]
    _ = _ := by rw [← Matrix.mulVec_mulVec, hsum]; rfl

/-- Orthogonality contracts the changed quaternion row against the
changed matrix row. -/
theorem QuaternionLift.quaternion_row_contraction {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (hR : R * Rᵀ = 1) (r : Fin 3) (v : Vec) :
    (∑ a, R r a • quaternion a (turnVector P.matrix v)) =
      turnVector P.matrix (quaternion r v) := by
  have hr (t : Fin 3) : (∑ a, R r a * R t a) = if r = t then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      congrArg (fun N : Mat => N r t) hR
  simp_rw [P.quaternion_turnVector, ← turnVector_smul]
  rw [← turnVector_sum]
  congr 1
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hr, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

def turnRawGradient (R : Mat) (P : Mat4) (Z : RawGradient) : RawGradient :=
  fun a b => turnVector P (∑ r, ∑ s, (R r a * R s b) • Z r s)

theorem turnRawGradient_field (R : Mat) (P : Mat4) (Z : Angular.Gradient) (a b : Fin 3) :
    turnRawGradient R P (fun c d => WithLp.toLp 2 (fun i => Z i c d)) a b =
      WithLp.toLp 2 (fun i => turnGradient R P Z i a b) := by
  ext i
  simp only [turnRawGradient, turnVector, turnGradient, conjugateMatrix,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.mulVec, dotProduct, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem turnRawGradient_symmetric (R : Mat) (P : Mat4) (Z : RawGradient)
    (hZ : ∀ a b, Z a b = Z b a) (a b : Fin 3) :
    turnRawGradient R P Z a b = turnRawGradient R P Z b a := by
  unfold turnRawGradient
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [hZ s r, mul_comm]

/-- The Bianchi constraint itself is preserved by a lifted change of
frame. This is a finite contraction of the quaternion intertwining law. -/
theorem turnRawGradient_bianchi (R : Mat) (hR : R * Rᵀ = 1)
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (Z : RawGradient) (hZ : ∀ s, ∑ r, quaternion r (Z r s) = 0) (b : Fin 3) :
    (∑ a, quaternion a (turnRawGradient R P.matrix Z a b)) = 0 := by
  have hq (a : Fin 3) : quaternion a (turnRawGradient R P.matrix Z a b) =
      ∑ r, ∑ s, (R r a * R s b) • quaternion a (turnVector P.matrix (Z r s)) := by
    simp only [turnRawGradient, turnVector_sum, turnVector_smul]
    simp only [quaternion_smul, Fin.sum_univ_three, quaternion_add]
  rw [show (∑ a, quaternion a (turnRawGradient R P.matrix Z a b)) =
      ∑ a, ∑ r, ∑ s, R s b • (R r a • quaternion a (turnVector P.matrix (Z r s))) by
    simp only [hq, smul_smul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [mul_comm]]
  calc
    _ = ∑ r, ∑ s, R s b •
        (∑ a, R r a • quaternion a (turnVector P.matrix (Z r s))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      simp only [Finset.smul_sum]
    _ = ∑ r, ∑ s, R s b • turnVector P.matrix (quaternion r (Z r s)) := by
      simp_rw [P.quaternion_row_contraction hR]
    _ = ∑ s, R s b • turnVector P.matrix (∑ r, quaternion r (Z r s)) := by
      rw [Finset.sum_comm]
      simp only [turnVector_sum, Finset.smul_sum]
    _ = 0 := by simp only [hZ, turnVector_zero, smul_zero, Finset.sum_const_zero]

theorem turnGradient_bianchi (R : Mat) (hR : R * Rᵀ = 1)
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (Z : Angular.Gradient) (hZ : ∀ r i, gradientDivergence Z r i = 0) :
    ∀ r i, gradientDivergence (turnGradient R P.matrix Z) r i = 0 := by
  have hz (s : Fin 3) :
      (∑ r, quaternion r (WithLp.toLp 2 (fun i => Z i r s))) = 0 := by
    ext i
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.zero_apply]
    simpa only [← quaternionMatrix_apply, gradientDivergence] using hZ s i
  intro r i
  have h := congrArg (fun v : Vec => v i)
    (turnRawGradient_bianchi R hR P
      (fun a b => WithLp.toLp 2 (fun j => Z j a b)) hz r)
  simp only [turnRawGradient_field, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.zero_apply] at h
  simpa only [← quaternionMatrix_apply, gradientDivergence] using h

theorem matrixAction_eq_commutator (s : Fin 3) (M : Mat) :
    matrixAction s M = TraceHessian.rotation s * M - M * TraceHessian.rotation s := by
  ext a b
  simp only [matrixAction, Matrix.sub_apply, Matrix.mul_apply,
    Finset.sum_sub_distrib]

theorem QuaternionLift.conjugate_rotation {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (hR : Rᵀ * R = 1) (s : Fin 3) :
    conjugateMatrix R (∑ r, R r s • TraceHessian.rotation r) =
      TraceHessian.rotation s := by
  have h := congrArg (fun N : Mat => Rᵀ * N) (P.rotation_intertwines s)
  simpa only [← Matrix.mul_assoc, hR, Matrix.one_mul, conjugateMatrix] using h.symm

/-- The spin-two matrix action is the conjugation action forced by the
same quaternion lift, rather than an independent representation premise. -/
theorem QuaternionLift.matrixAction_conjugate {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (hR : Rᵀ * R = 1) (s : Fin 3) (M : Mat) :
    matrixAction s (conjugateMatrix R M) =
      conjugateMatrix R (∑ r, R r s • matrixAction r M) := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  rw [matrixAction_eq_commutator, ← P.conjugate_rotation hR s,
    conjugateMatrix_mul R hR', conjugateMatrix_mul R hR', ← conjugateMatrix_sub]
  congr 1
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    matrixAction_eq_commutator, smul_sub, Finset.sum_sub_distrib]

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! Integrated scalar Bochner identity derived from the actual Ricci
commutator and the frame-flow Green formulas. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem traceFree_four_square (H : Mat4) :
    (∑ i, ∑ j, (H i j - if i = j then Matrix.trace H / 4 else 0) ^ 2) =
      (∑ i, ∑ j, H i j ^ 2) - Matrix.trace H ^ 2 / 4 := by
  norm_num [Fin.sum_univ_four, Matrix.trace, Matrix.diag]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ}
  {a : M → ℝ} (s : ScalarCovariantData d a)

include s

theorem ScalarCovariantData.traceFreeHessian_symmetric (e : FrameBundle g) :
    (scalarTraceFreeHessian g a e)ᵀ = scalarTraceFreeHessian g a e := by
  ext i j
  simp only [Matrix.transpose_apply, scalarTraceFreeHessian,
    s.hessianSymmetric e j i, eq_comm]

omit s in
theorem scalarTraceFreeHessian_trace (e : FrameBundle g) :
    Matrix.trace (scalarTraceFreeHessian g a e) = 0 := by
  simp only [Matrix.trace, Matrix.diag, scalarTraceFreeHessian, ite_true,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, scalarLaplacian]
  ring

omit s in
theorem scalarTraceFreeHessian_square (e : FrameBundle g) :
    (∑ i, ∑ j, scalarTraceFreeHessian g a e i j ^ 2) =
      (∑ j, ∑ i, scalarHessian g a e i j ^ 2) - scalarLaplacian g a e ^ 2 / 4 := by
  calc
    _ = (∑ i, ∑ j, scalarHessian g a e i j ^ 2) - scalarLaplacian g a e ^ 2 / 4 := by
      simpa only [scalarTraceFreeHessian, scalarLaplacian, Matrix.trace, Matrix.diag]
        using traceFree_four_square (fun i j => scalarHessian g a e i j)
    _ = _ := by rw [Finset.sum_comm]

variable [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

theorem ScalarCovariantData.integrated_bochner :
    (∫ e, scalarLaplacian g a e ^ 2 ∂μ) =
      4 * (∫ e, ‖scalarGradientVector g a e‖ ^ 2 ∂μ) +
        (4 / 3 : ℝ) * ∫ e, ∑ i, ∑ j, scalarTraceFreeHessian g a e i j ^ 2 ∂μ := by
  have hH := s.hessian_square_green
  have hL := s.laplacian_square_green
  have hpoint (e : FrameBundle g) :
      (∑ j, scalarGradient g a e j * (∑ i, scalarThird g a e i i j)) =
        (∑ j, scalarGradient g a e j * (∑ i, scalarThird g a e j i i)) +
          3 * ‖scalarGradientVector g a e‖ ^ 2 := by
    simp_rw [s.laplacianGradient_commute, mul_add, Finset.sum_add_distrib]
    congr 1
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ j, scalarGradient g a e j * (3 * scalarGradient g a e j)) =
      3 * ∑ j, scalarGradient g a e j ^ 2
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hgrad : Integrable (fun e => ‖scalarGradientVector g a e‖ ^ 2) μ :=
    (s.continuousGradientVector.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hterm : Integrable (fun e =>
      ∑ j, scalarGradient g a e j * (∑ i, scalarThird g a e j i i)) μ :=
    (continuous_finsetSum _ (fun j _ => (s.continuousGradient j).mul
      (continuous_finsetSum _ (fun i _ => s.continuousThird j i i)))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hhess : Integrable (fun e => ∑ j, ∑ i, scalarHessian g a e i j ^ 2) μ :=
    (continuous_finsetSum _ (fun j _ => continuous_finsetSum _
      (fun i _ => (s.continuousHessian i j).pow 2))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hlap : Integrable (fun e => scalarLaplacian g a e ^ 2) μ :=
    (s.continuousLaplacian.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [hpoint] at hH
  rw [integral_add hterm (hgrad.const_mul 3), integral_const_mul] at hH
  have htf : (∫ e, ∑ i, ∑ j, scalarTraceFreeHessian g a e i j ^ 2 ∂μ) =
      (∫ e, ∑ j, ∑ i, scalarHessian g a e i j ^ 2 ∂μ) -
        (∫ e, scalarLaplacian g a e ^ 2 ∂μ) / 4 := by
    simp_rw [scalarTraceFreeHessian_square]
    rw [integral_sub hhess (hlap.div_const 4), integral_div]
  linarith only [hH, hL, htf]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar Hessian curvature integral follows from coefficient
divergence, skew symmetry and the actual covector commutator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian CurvatureContraction MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance scalarCurvatureGreenRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance scalarCurvatureGreenSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance scalarCurvatureGreenAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ} [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
  {a : M → ℝ}

theorem ScalarCovariantData.coefficient_green (s : ScalarCovariantData d a)
    (Q : Fin 3 → Mat4) (hQ : ∀ r i j, Q r j i = -Q r i j)
    (A : C(FrameBundle g, Mat)) (Z : Fin 4 → C(FrameBundle g, Mat))
    (hA : ∀ i t e, HasDerivAt (fun r => A ((d.flow i).map r e))
      (Z i ((d.flow i).map t e)) t)
    (hdiv : ∀ e r i, (∑ t, ∑ j, Q t i j * Z j e t r) = 0) :
    (∫ e, ∑ p : Averages.CurvatureIndex,
      generalCoefficient Q (A e) p.1.1 p.1.2 p.2.1 p.2.2 *
        scalarHessian g a e p.1.1 p.2.1 * scalarHessian g a e p.1.2 p.2.2 ∂μ) =
      (1 / 2 : ℝ) * ∫ e, ∑ p : Averages.CurvatureIndex,
        generalCoefficient Q (A e) p.1.1 p.1.2 p.2.1 p.2.2 *
          (∑ l, frameCurvature g e.base e.frame p.1.1 p.1.2 l p.2.1 * scalarGradient g a e l) *
          scalarGradient g a e p.2.2 ∂μ := by
  let C (p : Averages.CurvatureIndex) : C(FrameBundle g, ℝ) :=
    ⟨fun e => generalCoefficient Q (A e) p.1.1 p.1.2 p.2.1 p.2.2,
      (generalCoefficientMap Q p.1.1 p.1.2 p.2.1 p.2.2).continuous.comp A.continuous⟩
  let D (p : Averages.CurvatureIndex) : C(FrameBundle g, ℝ) :=
    ⟨fun e => generalCoefficient Q (Z p.1.2 e) p.1.1 p.1.2 p.2.1 p.2.2,
      (generalCoefficientMap Q p.1.1 p.1.2 p.2.1 p.2.2).continuous.comp
        (Z p.1.2).continuous⟩
  have hc : ∀ i j l e, (∑ k, D ((i,k),(j,l)) e) = 0 := by
    intro i j l e
    exact generalCoefficient_divergence Q (fun k => Z k e) (hdiv e) i j l
  have hs : ∀ i k j l e, C ((k,i),(j,l)) e = -C ((i,k),(j,l)) e := by
    intro i k j l e
    exact generalCoefficient_skew Q hQ (A e) i k j l
  have hd (p : Averages.CurvatureIndex) (t : ℝ) (e : FrameBundle g) :
      HasDerivAt (fun r => C p ((d.flow p.1.2).map r e))
        (D p ((d.flow p.1.2).map t e)) t :=
    (generalCoefficientMap Q p.1.1 p.1.2 p.2.1 p.2.2).hasFDerivAt.comp_hasDerivAt t
      (hA p.1.2 t e)
  have hg := Averages.weighted_curvature_green μ (fun i => (d.flow i).map)
    (fun i => (d.flow i).continuous) (fun i => (d.flow i).preserves)
    (ContinuousMap.const _ 1) (fun _ => ContinuousMap.const _ 0) C D
    s.gradientField s.hessianField s.thirdField hc hs
    (fun _ t _ => hasDerivAt_const t 1) hd s.derivativeGradient s.derivativeHessian
  have hC (p : Averages.CurvatureIndex) (e : FrameBundle g) :
      C p e = generalCoefficient Q (A e) p.1.1 p.1.2 p.2.1 p.2.2 := rfl
  simpa only [hC, ScalarCovariantData.gradientField, ScalarCovariantData.hessianField,
    ScalarCovariantData.thirdField, ContinuousMap.coe_mk, ContinuousMap.coe_const,
    Function.const_apply, one_mul, zero_mul, add_zero, RCLike.inner_apply, conj_trivial,
    s.commutator, mul_comm, mul_left_comm, mul_assoc] using hg

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact prescribed trace in arbitrary matrix coordinates. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

/-- Subtracting the actual matrix Weyl equation removes the complete
Ricci commutator, including the skew derivative part. -/
theorem general_trace_subtracted_condition (A : Mat) (X : Hessian)
    (hA : symmetric A) (htA : traceFree A)
    (hmatrix : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbianchi : ∀ i r, divergence X i r = 0)
    (hcomm : ∀ i j a b, X i j a b - X j i a b = bundleCurvatureAction A i j A a b) :
    condition (X - traceComponent (weylLaplacian A)) := by
  have hsM := weylLaplacian_symmetric A hA
  have htM := weylLaplacian_traceFree A htA
  have htrace := weyl_trace_eq_of_bianchi_commutator A hA htA X hmatrix hbianchi hcomm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    ext a b
    change X i j a b - traceComponent (weylLaplacian A) i j a b =
      X j i a b - traceComponent (weylLaplacian A) j i a b
    have h := hcomm i j a b
    have hc := traceComponent_weylLaplacian_skew A hA htA i j a b
    linarith
  · intro i j
    constructor
    · intro a b
      change X i j a b - traceComponent (weylLaplacian A) i j a b =
        X i j b a - traceComponent (weylLaplacian A) i j b a
      rw [(hmatrix i j).1 a b, traceComponent_symmetric _ hsM htM i j a b]
    · change (∑ a, (X i j a a - traceComponent (weylLaplacian A) i j a a)) = 0
      rw [Finset.sum_sub_distrib, (hmatrix i j).2,
        traceComponent_traceFree _ hsM htM i j, sub_self]
  · unfold hessianTrace
    change (∑ i, (X i i - traceComponent (weylLaplacian A) i i)) = 0
    rw [Finset.sum_sub_distrib]
    change hessianTrace X - hessianTrace (traceComponent (weylLaplacian A)) = 0
    rw [htrace, trace_traceComponent, sub_self]
  · intro i r
    rw [divergence_sub, hbianchi, traceComponent_divergence _ hsM htM, sub_self]

/-- The operator on a matrix obtained by contracting two infinitesimal
matrix rotations with the full Weyl coefficient. -/
def generalMatrixActionSquare (A M : Mat) : Mat :=
  ∑ r, ∑ s, A r s • matrixAction r (matrixAction s M)

private theorem generalMatrixActionSquare_add (A B M : Mat) :
    generalMatrixActionSquare (A + B) M =
      generalMatrixActionSquare A M + generalMatrixActionSquare B M := by
  simp only [generalMatrixActionSquare, Matrix.add_apply, add_smul,
    Finset.sum_add_distrib]

private theorem generalMatrixActionSquare_smul (c : ℝ) (A M : Mat) :
    generalMatrixActionSquare (c • A) M = c • generalMatrixActionSquare A M := by
  simp only [generalMatrixActionSquare, Matrix.smul_apply, smul_eq_mul,
    mul_smul, Finset.smul_sum]

private theorem matrixSlotAction_coeff_add (A B M : Mat) :
    matrixSlotAction (A + B) M = matrixSlotAction A M + matrixSlotAction B M := by
  ext i j
  simp only [matrixSlotAction, Matrix.add_apply, add_mul, mul_add,
    Finset.sum_add_distrib]
  split_ifs <;> ring

private theorem matrixSlotAction_coeff_smul (c : ℝ) (A M : Mat) :
    matrixSlotAction (c • A) M = c • matrixSlotAction A M := by
  ext i j
  simp only [matrixSlotAction, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  split_ifs <;> ring

private theorem generalMatrixActionSquare_diagonal (t : Fin 3 → ℝ) (M : Mat)
    (ht : ∑ r, t r = 0) (hM : symmetric M) (htM : traceFree M) :
    generalMatrixActionSquare (Matrix.diagonal t) M =
      (24 : ℝ) • matrixSlotAction (Matrix.diagonal t) M := by
  simp only [generalMatrixActionSquare, Matrix.diagonal_apply,
    ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [matrixSlotAction_diagonal]
  exact weighted_matrixAction_square t ht M hM htM

private theorem generalMatrixActionSquare_symmetricUnit (r s : Fin 3) (M : Mat) :
    generalMatrixActionSquare (symmetricUnit r s) M =
      matrixAction r (matrixAction s M) + matrixAction s (matrixAction r M) := by
  fin_cases r <;> fin_cases s <;>
    simp [generalMatrixActionSquare, symmetricUnit, Fin.sum_univ_three, add_smul, add_comm]
  all_goals exact add_comm _ _

private theorem matrixAction_cross_01 (M : Mat)
    (hM : symmetric M) (htM : traceFree M) :
    generalMatrixActionSquare (symmetricUnit 0 1) M =
      (24 : ℝ) • matrixSlotAction (symmetricUnit 0 1) M := by
  rw [generalMatrixActionSquare_symmetricUnit]
  ext i j
  change matrixAction 0 (matrixAction 1 M) i j +
    matrixAction 1 (matrixAction 0 M) i j =
      24 * matrixSlotAction (symmetricUnit 0 1) M i j
  rw [← coordinates_eq M hM htM]
  simp only [matrixAction_coordinates_zero, matrixAction_coordinates_one]
  fin_cases i <;> fin_cases j <;>
    norm_num [symmetricUnit, matrixSlotAction, ofCoordinates, Fin.sum_univ_three]
  all_goals ring

private theorem matrixAction_cross_02 (M : Mat)
    (hM : symmetric M) (htM : traceFree M) :
    generalMatrixActionSquare (symmetricUnit 0 2) M =
      (24 : ℝ) • matrixSlotAction (symmetricUnit 0 2) M := by
  rw [generalMatrixActionSquare_symmetricUnit]
  ext i j
  change matrixAction 0 (matrixAction 2 M) i j +
    matrixAction 2 (matrixAction 0 M) i j =
      24 * matrixSlotAction (symmetricUnit 0 2) M i j
  rw [← coordinates_eq M hM htM]
  simp only [matrixAction_coordinates_zero, matrixAction_coordinates_two]
  fin_cases i <;> fin_cases j <;>
    norm_num [symmetricUnit, matrixSlotAction, ofCoordinates, Fin.sum_univ_three]
  all_goals ring

private theorem matrixAction_cross_12 (M : Mat)
    (hM : symmetric M) (htM : traceFree M) :
    generalMatrixActionSquare (symmetricUnit 1 2) M =
      (24 : ℝ) • matrixSlotAction (symmetricUnit 1 2) M := by
  rw [generalMatrixActionSquare_symmetricUnit]
  ext i j
  change matrixAction 1 (matrixAction 2 M) i j +
    matrixAction 2 (matrixAction 1 M) i j =
      24 * matrixSlotAction (symmetricUnit 1 2) M i j
  rw [← coordinates_eq M hM htM]
  simp only [matrixAction_coordinates_one, matrixAction_coordinates_two]
  fin_cases i <;> fin_cases j <;>
    norm_num [symmetricUnit, matrixSlotAction, ofCoordinates, Fin.sum_univ_three]
  all_goals ring

/-- The diagonal spin-two identity extends to the full symmetric
trace-free coefficient by its three off-diagonal entries. -/
theorem general_matrixAction_square (A M : Mat)
    (hA : symmetric A) (htA : traceFree A) (hM : symmetric M) (htM : traceFree M) :
    generalMatrixActionSquare A M = (24 : ℝ) • matrixSlotAction A M := by
  rw [symmetricMatrix_expansion A hA]
  simp only [generalMatrixActionSquare_add, generalMatrixActionSquare_smul,
    matrixSlotAction_coeff_add, matrixSlotAction_coeff_smul]
  rw [generalMatrixActionSquare_diagonal _ M htA hM htM,
    matrixAction_cross_01 M hM htM, matrixAction_cross_02 M hM htM,
    matrixAction_cross_12 M hM htM]
  module


/-- The polarized arbitrary-matrix curvature operator. -/
def generalCurvaturePairing (A U : Mat) (X Y : Hessian) : ℝ :=
  4 * hessianPairing X Y +
    (∑ r, ∑ s, A r s * hessianPairing (totalPlus r X) (totalPlus s Y)) / 24 +
    (∑ r, ∑ s, U r s * hessianPairing (totalMinus r X) (totalMinus s Y)) / 4

theorem generalCurvaturePairing_self (A U : Mat) (X : Hessian) :
    generalCurvaturePairing A U X X = generalCasimirCurvatureForm A U X := by
  simp only [generalCurvaturePairing, generalCasimirCurvatureForm,
    hessianGram, hessianPairing_self]

private theorem weightedPairing_comm (A : Mat) (hA : symmetric A)
    (F G : Fin 3 → Hessian) :
    (∑ r, ∑ s, A r s * hessianPairing (F r) (G s)) =
      ∑ r, ∑ s, A r s * hessianPairing (G r) (F s) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [hA s r, hessianPairing_comm]

theorem generalCurvaturePairing_comm (A U : Mat) (hA : symmetric A) (hU : symmetric U)
    (X Y : Hessian) :
    generalCurvaturePairing A U X Y = generalCurvaturePairing A U Y X := by
  rw [generalCurvaturePairing, generalCurvaturePairing, hessianPairing_comm X Y,
    weightedPairing_comm A hA, weightedPairing_comm U hU]

theorem generalCurvaturePairing_add_left (A U : Mat) (X Y Z : Hessian) :
    generalCurvaturePairing A U (X + Y) Z =
      generalCurvaturePairing A U X Z + generalCurvaturePairing A U Y Z := by
  simp only [generalCurvaturePairing, totalPlus_add, totalMinus_add,
    hessianPairing_add_left, mul_add, Finset.sum_add_distrib]
  ring

theorem generalCurvaturePairing_smul_left (A U : Mat) (c : ℝ) (X Y : Hessian) :
    generalCurvaturePairing A U (c • X) Y = c * generalCurvaturePairing A U X Y := by
  have h (a b : ℝ) : a * (c * b) = c * (a * b) := by ring
  simp only [generalCurvaturePairing, totalPlus_smul, totalMinus_smul,
    hessianPairing_smul_left, h, ← Finset.mul_sum]
  ring

theorem generalCurvaturePairing_add_right (A U : Mat) (X Y Z : Hessian) :
    generalCurvaturePairing A U X (Y + Z) =
      generalCurvaturePairing A U X Y + generalCurvaturePairing A U X Z := by
  simp only [generalCurvaturePairing, totalPlus_add, totalMinus_add,
    hessianPairing_add_right, mul_add, Finset.sum_add_distrib]
  ring

theorem generalCurvaturePairing_smul_right (A U : Mat) (c : ℝ) (X Y : Hessian) :
    generalCurvaturePairing A U X (c • Y) = c * generalCurvaturePairing A U X Y := by
  have h (a b : ℝ) : a * (c * b) = c * (a * b) := by ring
  simp only [generalCurvaturePairing, totalPlus_smul, totalMinus_smul,
    hessianPairing_smul_right, h, ← Finset.mul_sum]
  ring

private theorem traceLift_pairing_double_sum (A : Mat) (F : Fin 3 → Fin 3 → Mat)
    (Y : Hessian) :
    (∑ r, ∑ s, A r s * hessianPairing (traceLift (F r s)) Y) =
      hessianPairing (traceLift (∑ r, ∑ s, A r s • F r s)) Y := by
  simp only [Fin.sum_univ_three, traceLift_add, traceLift_smul,
    hessianPairing_add_left, hessianPairing_smul_left]

/-- The exact trace-component action is invariant under an arbitrary
symmetric trace-free Weyl coefficient. -/
theorem general_traceLift_curvatureAction (A U M : Mat)
    (hA : symmetric A) (htA : traceFree A) (hM : symmetric M) (htM : traceFree M)
    (Y : Hessian) :
    generalCurvaturePairing A U (traceLift M) Y =
      hessianPairing (traceLift ((4 : ℝ) • M - matrixSlotAction A M)) Y := by
  have hp (r s : Fin 3) :
      hessianPairing (totalPlus r (traceLift M)) (totalPlus s Y) =
        -hessianPairing (traceLift (matrixAction s (matrixAction r M))) Y := by
    rw [totalPlus_traceLift]
    have h := totalPlus_skew s (traceLift (matrixAction r M)) Y
    rw [totalPlus_traceLift] at h
    linarith
  have hw : (∑ r, ∑ s, A r s *
      hessianPairing (traceLift (matrixAction s (matrixAction r M))) Y) =
        24 * hessianPairing (traceLift (matrixSlotAction A M)) Y := by
    have he : (∑ r, ∑ s, A r s *
        hessianPairing (traceLift (matrixAction s (matrixAction r M))) Y) =
        ∑ r, ∑ s, A r s * hessianPairing (traceLift (matrixAction r (matrixAction s M))) Y := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      rw [hA s r]
    rw [he, traceLift_pairing_double_sum]
    change hessianPairing (traceLift (generalMatrixActionSquare A M)) Y = _
    rw [general_matrixAction_square A M hA htA hM htM,
      traceLift_smul, hessianPairing_smul_left]
  have hz (V : Hessian) : hessianPairing (0 : Hessian) V = 0 := by
    simp [hessianPairing]
  rw [traceLift_sub, traceLift_smul]
  simp only [generalCurvaturePairing, hp, totalMinus_traceLift, hz,
    mul_neg, Finset.sum_neg_distrib, mul_zero, Finset.sum_const_zero,
    zero_div, add_zero]
  rw [hw]
  rw [sub_eq_add_neg, ← neg_one_smul ℝ (traceLift (matrixSlotAction A M)),
    hessianPairing_add_left, hessianPairing_smul_left, hessianPairing_smul_left]
  ring

def generalTraceCurvatureBlock (A M : Mat) : Mat :=
  (4 : ℝ) • M - matrixSlotAction A M

theorem general_traceComponent_curvatureAction (A U M : Mat)
    (hA : symmetric A) (htA : traceFree A) (hM : symmetric M) (htM : traceFree M)
    (Y : Hessian) :
    generalCurvaturePairing A U (traceComponent M) Y =
      hessianPairing (traceComponent (generalTraceCurvatureBlock A M)) Y := by
  change generalCurvaturePairing A U ((5 / 12 : ℝ) • traceLift M) Y =
    hessianPairing ((5 / 12 : ℝ) • traceLift (generalTraceCurvatureBlock A M)) Y
  rw [generalCurvaturePairing_smul_left, hessianPairing_smul_left,
    general_traceLift_curvatureAction A U M hA htA hM htM Y]
  rfl


theorem generalTraceCurvatureBlock_symmetric (A M : Mat)
    (hA : symmetric A) (hM : symmetric M) :
    symmetric (generalTraceCurvatureBlock A M) := by
  intro a b
  have hrow (c : Fin 3) :
      A a c * M c b + M a c * A c b = A b c * M c a + M b c * A c a := by
    rw [hA b c, hM c a, hM b c, hA c a]
    ring
  change 4 * M a b - matrixSlotAction A M a b =
    4 * M b a - matrixSlotAction A M b a
  rw [hM a b]
  unfold matrixSlotAction
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  simp_rw [hrow]
  by_cases hab : a = b
  · subst b
    rfl
  · simp only [hab, Ne.symm hab, ite_false]

theorem generalTraceCurvatureBlock_traceFree (A M : Mat) (hM : traceFree M) :
    traceFree (generalTraceCurvatureBlock A M) := by
  have hs : Matrix.trace (matrixSlotAction A M) = 0 := by
    rw [matrixSlotAction_eq, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add,
      Matrix.trace_smul, Matrix.trace_mul_comm M A]
    norm_num
    ring
  change Matrix.trace (generalTraceCurvatureBlock A M) = 0
  rw [generalTraceCurvatureBlock, Matrix.trace_sub, Matrix.trace_smul,
    show Matrix.trace M = 0 from hM, hs]
  ring

/-- The full trace curvature term pairs through the actual tensor trace. -/
theorem general_traceComponent_curvaturePairing (A U M : Mat)
    (hA : symmetric A) (htA : traceFree A) (hM : symmetric M) (htM : traceFree M)
    (X : Hessian) (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hb : ∀ i r, divergence X i r = 0) :
    generalCurvaturePairing A U (traceComponent M) X =
      (5 / 12 : ℝ) * matrixPairing (generalTraceCurvatureBlock A M) (hessianTrace X) := by
  rw [general_traceComponent_curvatureAction A U M hA htA hM htM X]
  exact traceComponent_pairing_hessian _ (generalTraceCurvatureBlock_symmetric A M hA hM)
    (generalTraceCurvatureBlock_traceFree A M htM) X hm hb

theorem general_prescribed_trace_curvaturePairing (A U M : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A)
    (hM : symmetric M) (htM : traceFree M)
    (X : Hessian) (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hb : ∀ i r, divergence X i r = 0) (htrace : hessianTrace X = M) :
    generalCurvaturePairing A U X (traceComponent M) =
      generalCurvaturePairing A U (traceComponent M) (traceComponent M) := by
  rw [generalCurvaturePairing_comm A U hA hU X,
    general_traceComponent_curvaturePairing A U M hA htA hM htM X hm hb,
    general_traceComponent_curvaturePairing A U M hA htA hM htM (traceComponent M)
      (fun i j => ⟨traceComponent_symmetric M hM htM i j,
        traceComponent_traceFree M hM htM i j⟩)
      (traceComponent_divergence M hM htM), htrace, trace_traceComponent]

/-- Exact trace subtraction includes the unsymmetrized weight derivative. -/
theorem general_weighted_trace_subtraction (A U M : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A)
    (hM : symmetric M) (htM : traceFree M)
    (X L : Hessian) (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hb : ∀ i r, divergence X i r = 0) (htrace : hessianTrace X = M) (m : ℝ) :
    m * generalCurvaturePairing A U (X - traceComponent M) (X - traceComponent M) +
        generalCurvaturePairing A U (X - traceComponent M) L =
      m * generalCurvaturePairing A U X X + generalCurvaturePairing A U X L -
        m * generalCurvaturePairing A U (traceComponent M) (traceComponent M) -
          generalCurvaturePairing A U (traceComponent M) L := by
  have hx := general_prescribed_trace_curvaturePairing A U M hA hU htA hM htM
    X hm hb htrace
  have hsub : X - traceComponent M = X + (-1 : ℝ) • traceComponent M := by module
  rw [hsub]
  simp only [generalCurvaturePairing_add_left, generalCurvaturePairing_add_right,
    generalCurvaturePairing_smul_left, generalCurvaturePairing_smul_right]
  rw [generalCurvaturePairing_comm A U hA hU (traceComponent M) X, hx]
  ring


/-- The prescribed trace is exactly the invariant polynomial coefficient
already differentiated in the geometric trace Green identity. -/
theorem generalTraceCurvatureBlock_weylLaplacian (A : Mat)
    (hA : symmetric A) (htA : traceFree A) :
    generalTraceCurvatureBlock A (weylLaplacian A) = (6 : ℝ) • traceCoefficient A :=
  trace_coefficient_eq A hA htA

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! The sharp cubic estimate in an arbitrary frame. The diagonalized
matrix is the contraction of the gradient with its distinguished covector,
not the Weyl matrix and not a moving eigenframe. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem weightedCubicField_tensor (a : Vec) (Z : Angular.Gradient)
    (hZ : ∀ i, symmetric (Z i)) :
    weightedCubicField a Z = weightedCubicTrace a (gradientTensor Z) := by
  have hd (i : Fin 4) : derivativeMatrix (gradientTensor Z) i = Z i := by
    ext r s
    exact congrArg (fun v : Vec => v i) (gradientTensor_matrix Z hZ r s)
  simp only [weightedCubicField, weightedCubicTrace, hd]

theorem weightedCubicField_smul (c : ℝ) (a : Vec) (Z : Angular.Gradient) :
    weightedCubicField (c • a) Z = c * weightedCubicField a Z := by
  simp only [weightedCubicField, Pi.smul_apply, smul_eq_mul, mul_assoc,
    Finset.mul_sum]

private theorem distinguished_matrix_symmetric (a : Vec) (Z : Angular.Gradient)
    (hZ : ∀ i, symmetric (Z i)) : symmetric (∑ i, a i • Z i) := by
  intro r s
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hZ i r s]

private theorem distinguished_matrix_traceFree (a : Vec) (Z : Angular.Gradient)
    (hZ : ∀ i, traceFree (Z i)) : traceFree (∑ i, a i • Z i) := by
  change Matrix.trace (∑ i, a i • Z i) = 0
  rw [Matrix.trace_sum]
  simp only [Matrix.trace_smul, show ∀ i, Matrix.trace (Z i) = 0 from hZ,
    smul_zero, Finset.sum_const_zero]

private theorem distinguished_matrix_turn (R : Mat) (P : Mat4)
    (hP : P * Pᵀ = 1) (a : Vec) (Z : Angular.Gradient) :
    (∑ i, (turnVector P a) i • turnGradient R P Z i) =
      conjugateMatrix R (∑ i, a i • Z i) := by
  simpa only [turnVector, Matrix.mulVec, Matrix.transpose_apply, dotProduct] using
    weighted_sum_turnGradient R P hP a Z

/-- Sharp cubic contraction for arbitrary symmetric trace-free Bianchi
gradients and arbitrary distinguished covectors. -/
theorem weightedCubicField_sharp (a : Vec) (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0) :
    |weightedCubicField a Z| ≤ ‖a‖ *
      ((24 / 5 : ℝ) * Real.sqrt (3 / 5) * weylGradientEnergy Z *
        Real.sqrt (weylGradientEnergy Z)) := by
  have he : 0 ≤ weylGradientEnergy Z := by
    unfold weylGradientEnergy matrixPairing
    apply div_nonneg _ (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro r _
    apply Finset.sum_nonneg
    intro s _
    exact mul_self_nonneg _
  by_cases ha : a = 0
  · simp [ha, weightedCubicField]
  let a₀ : Vec := (‖a‖⁻¹ : ℝ) • a
  have ha₀ : ‖a₀‖ = 1 := norm_smul_inv_norm ha
  have harec : a = ‖a‖ • a₀ := by
    dsimp only [a₀]
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha), one_smul]
  suffices hunit : |weightedCubicField a₀ Z| ≤
      (24 / 5 : ℝ) * Real.sqrt (3 / 5) * weylGradientEnergy Z *
        Real.sqrt (weylGradientEnergy Z) by
    have hhom : weightedCubicField a Z = ‖a‖ * weightedCubicField a₀ Z := by
      conv_lhs => rw [harec]
      exact weightedCubicField_smul ‖a‖ a₀ Z
    rw [hhom, abs_mul, abs_of_nonneg (norm_nonneg a)]
    exact mul_le_mul_of_nonneg_left hunit (norm_nonneg a)
  let M : Mat := ∑ i, a₀ i • Z i
  by_cases hM : M = 0
  · have hc : weightedCubicField a₀ Z = 0 := by
      rw [weightedCubicField_eq]
      change Matrix.trace (M * _) = 0
      rw [hM, Matrix.zero_mul, Matrix.trace_zero]
    rw [hc, abs_zero]
    positivity
  have hMv : 0 < normalizedBlockNorm M :=
    lt_of_le_of_ne (normalizedBlockNorm_nonneg M)
      (Ne.symm (mt (normalizedBlockNorm_eq_zero_iff M).mp hM))
  obtain ⟨R, hR, ⟨P⟩, S, hdiag⟩ := exists_lifted_spectral_shape M
    (distinguished_matrix_symmetric a₀ Z hs) (distinguished_matrix_traceFree a₀ Z ht) hMv
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  let Z' := turnGradient R P.matrix Z
  let a' := turnVector P.matrix a₀
  have hs' : ∀ i, symmetric (Z' i) := turnGradient_symmetric R P.matrix Z hs
  have ht' : ∀ i, traceFree (Z' i) := turnGradient_traceFree R hR' P.matrix Z ht
  have hb' : ∀ r i, gradientDivergence Z' r i = 0 := turnGradient_bianchi R hR' P Z hb
  have ha' : ‖a'‖ = 1 := (turnVector_norm P.matrix P.mul_transpose a₀).trans ha₀
  have hshape (r s : Fin 3) :
      inner ℝ a' ((gradientTensor Z').matrix r s) =
        if r = s then normalizedBlockNorm M * S.s r else 0 := by
    rw [gradientTensor_matrix Z' hs']
    have h := congrArg (fun N : Mat => N r s)
      ((distinguished_matrix_turn R P.matrix P.mul_transpose a₀ Z).trans hdiag)
    simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul,
      mul_comm, a', Z', M, conjugateMatrix] using h
  have hc := cubicContraction_sharp_tensor_diagonal S a' (gradientTensor Z')
    (gradientTensor_traceFree Z' ht') (gradientTensor_bianchi Z' hs' hb') ha'
    (normalizedBlockNorm_nonneg M) hshape
  have he' : (gradientTensor Z').squaredNorm / 6 = weylGradientEnergy Z := by
    rw [gradientTensor_energy Z' hs', weylGradientEnergy_turn R hR' P.matrix P.mul_transpose]
  rw [he'] at hc
  have hcube : weightedCubicField a' Z' = weightedCubicField a₀ Z := by
    change weightedCubicField (fun i => ∑ k, P.matrix k i * a₀ k)
      (turnGradient R P.matrix Z) = weightedCubicField a₀ Z
    exact weightedCubicField_turn R hR' P.matrix P.mul_transpose a₀ Z
  rw [← hcube, weightedCubicField_tensor a' Z' hs', weightedCubicTrace_eq, abs_mul]
  norm_num only [abs_of_pos (show (0 : ℝ) < 6 by norm_num)]
  nlinarith only [hc]

/-- The actual cubic trace with the squared-weight derivative has exactly
the coefficient used in the scalar quartic relaxation. -/
theorem weightedCubicField_squared_weight_bound (M : ℝ) (hM : 0 ≤ M)
    (p q : Vec) (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0) :
    -(5 / 36 : ℝ) * weightedCubicField (((-(3 / 4 : ℝ) * M) • (p - q)) : Vec) Z ≤
      (1 / 2 : ℝ) * Real.sqrt (3 / 5) * (‖p‖ + ‖q‖) * M *
        (weylGradientEnergy Z * Real.sqrt (weylGradientEnergy Z)) := by
  have he : 0 ≤ weylGradientEnergy Z := by
    unfold weylGradientEnergy matrixPairing
    apply div_nonneg _ (by norm_num)
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => mul_self_nonneg (Z i a b)
  have hn : ‖(-(3 / 4 : ℝ) * M) • (p - q)‖ ≤
      (3 / 4 : ℝ) * M * (‖p‖ + ‖q‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hM]
    norm_num
    exact mul_le_mul_of_nonneg_left (norm_sub_le p q) (by positivity)
  have hc := weightedCubicField_sharp ((-(3 / 4 : ℝ) * M) • (p - q)) Z hs ht hb
  have hu := hc.trans (mul_le_mul_of_nonneg_right hn
    (show 0 ≤ (24 / 5 : ℝ) * Real.sqrt (3 / 5) * weylGradientEnergy Z *
      Real.sqrt (weylGradientEnergy Z) by positivity))
  have hlo := (abs_le.mp hu).1
  nlinarith only [hlo]

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! Weighted integration by parts for the trace-free scalar Hessian.
This is the four-dimensional identity used in the nonlinear proof of
the sharp positive-Ricci scalar inequality. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ} {a w : M → ℝ}

namespace ScalarCovariantData

def traceFreeHessianField (s : ScalarCovariantData d a) (i j : Fin 4) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => scalarTraceFreeHessian g a e i j, by
    have hH := s.continuousHessian i j
    have hL := s.continuousLaplacian
    unfold scalarTraceFreeHessian
    split_ifs <;> fun_prop⟩

def traceFreeHessianDerivativeField (s : ScalarCovariantData d a)
    (k i j : Fin 4) : C(FrameBundle g, ℝ) :=
  ⟨fun e => scalarThird g a e k i j -
    if i = j then (∑ l, scalarThird g a e k l l) / 4 else 0, by
    have hT := s.continuousThird k i j
    have hL := continuous_finsetSum Finset.univ (fun l _ => s.continuousThird k l l)
    split_ifs <;> fun_prop⟩

theorem derivativeTraceFreeHessian (s : ScalarCovariantData d a)
    (k i j : Fin 4) (t : ℝ) (e : FrameBundle g) :
    HasDerivAt (fun r => scalarTraceFreeHessian g a ((d.flow k).map r e) i j)
      (s.traceFreeHessianDerivativeField k i j ((d.flow k).map t e)) t := by
  dsimp only [traceFreeHessianDerivativeField, ContinuousMap.coe_mk,
    scalarTraceFreeHessian]
  split_ifs
  · exact (s.derivativeHessian k i j t e).sub
      ((s.derivativeLaplacian k t e).div_const 4)
  · simpa only [sub_zero] using s.derivativeHessian k i j t e

theorem traceFreeHessian_divergence (s : ScalarCovariantData d a)
    (e : FrameBundle g) (j : Fin 4) :
    (∑ i, s.traceFreeHessianDerivativeField i i j e) =
      (3 / 4 : ℝ) * ((∑ i, scalarThird g a e j i i) +
        4 * scalarGradient g a e j) := by
  simp only [traceFreeHessianDerivativeField, ContinuousMap.coe_mk,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [s.laplacianGradient_commute]
  ring

end ScalarCovariantData

theorem scalarTraceFreeHessian_pairing (e : FrameBundle g) :
    (∑ i, ∑ j, scalarTraceFreeHessian g a e i j * scalarHessian g a e i j) =
      ∑ i, ∑ j, scalarTraceFreeHessian g a e i j ^ 2 := by
  have ht := scalarTraceFreeHessian_trace (g := g) (a := a) e
  have hpoint (i j : Fin 4) :
      scalarTraceFreeHessian g a e i j * scalarHessian g a e i j =
        scalarTraceFreeHessian g a e i j ^ 2 +
          if i = j then scalarTraceFreeHessian g a e i i * scalarLaplacian g a e / 4
          else 0 := by
    by_cases h : i = j
    · subst j
      simp only [scalarTraceFreeHessian, ite_true]
      ring
    · simp only [scalarTraceFreeHessian, h, ite_false, sub_zero, add_zero]
      ring
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.sum_div, ← Finset.sum_mul]
  change _ + Matrix.trace (scalarTraceFreeHessian g a e) * scalarLaplacian g a e / 4 = _
  rw [ht, zero_mul, zero_div, add_zero]

variable [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

theorem ScalarCovariantData.weighted_traceFree_green
    (s : ScalarCovariantData d a) (v : ScalarCovariantData d w) :
    (∫ e, w e.base * (∑ i, ∑ j, scalarTraceFreeHessian g a e i j ^ 2) ∂μ) =
      -(∫ e, ∑ j, scalarGradient g a e j *
        ((∑ i, scalarGradient g w e i * scalarTraceFreeHessian g a e i j) +
          (3 / 4 : ℝ) * w e.base *
            ((∑ i, scalarThird g a e j i i) + 4 * scalarGradient g a e j)) ∂μ) := by
  let f (i j : Fin 4) : C(FrameBundle g, ℝ) :=
    v.valueField * s.traceFreeHessianField i j
  let df (i j : Fin 4) : C(FrameBundle g, ℝ) :=
    v.gradientField i * s.traceFreeHessianField i j +
      v.valueField * s.traceFreeHessianDerivativeField i i j
  have hd (i j : Fin 4) (t : ℝ) (e : FrameBundle g) :
      HasDerivAt (fun r => f i j ((d.flow i).map r e))
        (df i j ((d.flow i).map t e)) t :=
    (v.derivativeValue i t e).mul (s.derivativeTraceFreeHessian i i j t e)
  have hg (i j : Fin 4) := scalar_flow_green (d := d) i (f i j) (df i j)
    (s.gradientField j) (s.hessianField i j) (hd i j) (s.derivativeGradient i j)
  have hi (i j : Fin 4) : Integrable
      (fun e => df i j e * scalarGradient g a e j) μ :=
    ((df i j).continuous.mul (s.continuousGradient j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hj (i j : Fin 4) : Integrable
      (fun e => f i j e * scalarHessian g a e i j) μ :=
    ((f i j).continuous.mul (s.continuousHessian i j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he := congrArg (fun z : Fin 4 → Fin 4 → ℝ => ∑ j, ∑ i, z i j)
    (funext fun i => funext fun j => hg i j)
  simp only [ScalarCovariantData.gradientField, ScalarCovariantData.hessianField,
    ContinuousMap.coe_mk, Finset.sum_neg_distrib] at he
  simp_rw [← integral_finsetSum _ (fun i _ => hi i _),
    ← integral_finsetSum _ (fun i _ => hj i _)] at he
  rw [← integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ => hi i j)),
    ← integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ => hj i j))] at he
  have hleft (e : FrameBundle g) :
      (∑ j, ∑ i, df i j e * scalarGradient g a e j) =
        ∑ j, scalarGradient g a e j *
          ((∑ i, scalarGradient g w e i * scalarTraceFreeHessian g a e i j) +
            (3 / 4 : ℝ) * w e.base *
              ((∑ i, scalarThird g a e j i i) + 4 * scalarGradient g a e j)) := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [df, ContinuousMap.coe_add, ContinuousMap.coe_mul, Pi.add_apply,
      Pi.mul_apply, ScalarCovariantData.gradientField, ScalarCovariantData.valueField,
      ScalarCovariantData.traceFreeHessianField, ContinuousMap.coe_mk,
      add_mul, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum,
      s.traceFreeHessian_divergence]
    ring
  have hright (e : FrameBundle g) :
      (∑ j, ∑ i, f i j e * scalarHessian g a e i j) =
        w e.base * (∑ i, ∑ j, scalarTraceFreeHessian g a e i j ^ 2) := by
    simp only [f, ContinuousMap.coe_mul, Pi.mul_apply,
      ScalarCovariantData.valueField, ScalarCovariantData.traceFreeHessianField,
      ContinuousMap.coe_mk, mul_assoc]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_comm, scalarTraceFreeHessian_pairing]
  have hl := integral_congr_ae (μ := μ) (Filter.Eventually.of_forall hleft)
  have hr := integral_congr_ae (μ := μ) (Filter.Eventually.of_forall hright)
  linarith only [he, hl, hr]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The elementary Grassmannian calculation needed for the sectional
criterion. Two arbitrary unit coefficient vectors in the positive and
negative quaternion triples are realized by a genuine two-plane. -/

namespace PositiveEinsteinFour.SectionalPlane

open EinsteinFour Matrix Bianchi TraceHessian QuaternionFrame Angular
open scoped BigOperators

noncomputable section

abbrev Vec4 := EuclideanSpace ℝ (Fin 4)

def act (A : Geometry.Mat4) (v : Vec4) : Vec4 :=
  WithLp.toLp 2 (A *ᵥ (v : Fin 4 → ℝ))

theorem act_add (A B : Geometry.Mat4) (v : Vec4) :
    act (A + B) v = act A v + act B v := by
  ext i
  simp [act, Matrix.add_mulVec]

theorem act_smul (r : ℝ) (A : Geometry.Mat4) (v : Vec4) :
    act (r • A) v = r • act A v := by
  ext i
  simp [act, Matrix.smul_mulVec]

theorem act_sum {ι : Type*} [Fintype ι] (A : ι → Geometry.Mat4) (v : Vec4) :
    act (∑ i, A i) v = ∑ i, act (A i) v := by
  ext i
  simp [act, Matrix.sum_mulVec]

theorem act_mul (A B : Geometry.Mat4) (v : Vec4) :
    act (A * B) v = act A (act B v) := by
  ext i
  simp [act, Matrix.mulVec_mulVec]

theorem act_smul_vector (A : Geometry.Mat4) (r : ℝ) (v : Vec4) :
    act A (r • v) = r • act A v := by
  ext i
  simp [act, Matrix.mulVec_smul]

@[simp] theorem act_zero (v : Vec4) : act (0 : Geometry.Mat4) v = 0 := by
  ext i
  simp [act]

@[simp] theorem act_one (v : Vec4) : act (1 : Geometry.Mat4) v = v := by
  ext i
  simp [act]

theorem act_norm (A : Geometry.Mat4) (hA : Aᵀ * A = 1) (v : Vec4) :
    ‖act A v‖ = ‖v‖ := by
  have hs : ‖act A v‖ ^ 2 = ‖v‖ ^ 2 := by
    simpa only [act, EuclideanSpace.real_norm_sq_eq, Matrix.transpose_transpose,
      Matrix.transpose_apply, Matrix.mulVec, dotProduct] using
      orthogonal_square_sum Aᵀ (by simpa using hA) v
  nlinarith [norm_nonneg (act A v), norm_nonneg v]

theorem act_inner_adjoint (A : Geometry.Mat4) (v w : Vec4) :
    inner ℝ (act A v) w = inner ℝ v (act Aᵀ w) := by
  simp only [act, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem act_skew_self (A : Geometry.Mat4) (hA : Aᵀ = -A) (v : Vec4) :
    inner ℝ (act A v) v = 0 := by
  have hh := act_inner_adjoint A v v
  rw [hA, show -A = (-1 : ℝ) • A by simp, act_smul] at hh
  simp only [inner_smul_right, neg_one_mul] at hh
  rw [real_inner_comm v (act A v)] at hh
  linarith [real_inner_comm (act A v) v]

/-- Every pair of unit imaginary quaternions admits a common vector on
which their actions are opposite. The trace-zero product makes its positive
projection nonzero. -/
theorem exists_common_vector (s t : Fin 3 → ℝ)
    (hs : ∑ i, s i ^ 2 = 1) (ht : ∑ i, t i ^ 2 = 1) :
    ∃ v : Vec4, ‖v‖ = 1 ∧
      act (imaginaryCombination quaternionMatrix s) v =
        -act (imaginaryCombination oppositeMatrix t) v := by
  let L := imaginaryCombination quaternionMatrix s
  let R := imaginaryCombination oppositeMatrix t
  have hL : L * L = -1 := by
    simpa only [L, hs, neg_one_smul] using
      imaginaryCombination_square quaternionMatrix quaternionMatrix_anticommutator s
  have hR : R * R = -1 := by
    simpa only [R, ht, neg_one_smul] using
      imaginaryCombination_square oppositeMatrix oppositeMatrix_anticommutator t
  have hcomm : R * L = L * R := by
    change R * (∑ i, s i • quaternionMatrix i) =
      (∑ i, s i • quaternionMatrix i) * R
    rw [Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mul_smul, Matrix.smul_mul]
    exact congrArg (fun A : Geometry.Mat4 => s i • A)
      (imaginaryRight_commutes_positive t i)
  have htracePair (i j : Fin 3) : Matrix.trace (quaternionMatrix i * oppositeMatrix j) = 0 := by
    have hh := mixingCoefficient_trace i j
    rw [mixingCoefficient, quaternionMatrix_transpose, Matrix.neg_mul,
      Matrix.trace_neg] at hh
    linarith
  have htrace : Matrix.trace (L * R) = 0 := by
    simp only [L, R, imaginaryCombination, Matrix.sum_mul, Matrix.mul_sum,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum,
      Matrix.trace_smul, htracePair, smul_zero, Finset.sum_const_zero]
  let K : Geometry.Mat4 := 1 + L * R
  have hK : K ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.trace hz
    simp only [K, Matrix.trace_add, htrace, add_zero, Matrix.trace_one,
      Fintype.card_fin, Nat.cast_ofNat, Matrix.trace_zero] at hh
    norm_num at hh
  have hker : (L + R) * K = 0 := by
    calc
      _ = L + R + (L * L) * R + (R * L) * R := by dsimp [K]; noncomm_ring
      _ = L + R + (L * L) * R + L * (R * R) := by rw [hcomm]; noncomm_ring
      _ = 0 := by rw [hL, hR]; simp
  have hex : ∃ j : Fin 4, ∃ i : Fin 4, K i j ≠ 0 := by
    by_contra! hh
    apply hK
    ext i j
    exact hh j i
  obtain ⟨j, i, hij⟩ := hex
  let w : Vec4 := act K (WithLp.toLp 2 (Pi.single j 1))
  have hw : w ≠ 0 := by
    intro hz
    have hi := congrArg (fun v : Vec4 => v i) hz
    apply hij
    simpa [w, act] using hi
  let v : Vec4 := (‖w‖⁻¹ : ℝ) • w
  have hv : ‖v‖ = 1 := norm_smul_inv_norm hw
  refine ⟨v, hv, ?_⟩
  have hk : act (L + R) v = 0 := by
    change act (L + R) ((‖w‖⁻¹ : ℝ) • w) = 0
    rw [act_smul_vector]
    change ‖w‖⁻¹ • act (L + R) (act K (WithLp.toLp 2 (Pi.single j 1))) = 0
    rw [← act_mul, hker, act_zero, smul_zero]
  rw [act_add] at hk
  exact eq_neg_of_add_eq_zero_left hk

def coefficient (Q : Geometry.Mat4) (u v : Vec4) : ℝ := inner ℝ (act Q v) u

theorem coefficient_eq_sum (Q : Geometry.Mat4) (u v : Vec4) :
    coefficient Q u v = ∑ a, ∑ b, Q a b * u a * v b := by
  simp only [coefficient, act, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem quaternion_gram (v : Vec4) (i j : Fin 3) :
    inner ℝ (act (quaternionMatrix i) v) (act (quaternionMatrix j) v) =
      if i = j then ‖v‖ ^ 2 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [act, quaternionMatrix, PiLp.inner_apply, RCLike.inner_apply,
      EuclideanSpace.real_norm_sq_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

theorem opposite_gram (v : Vec4) (i j : Fin 3) :
    inner ℝ (act (oppositeMatrix i) v) (act (oppositeMatrix j) v) =
      if i = j then ‖v‖ ^ 2 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [act, oppositeMatrix, Geometry.oppositeQuaternion, quaternionMatrix,
      PiLp.inner_apply, RCLike.inner_apply, EuclideanSpace.real_norm_sq_eq,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

theorem coefficient_combination (Q : Fin 3 → Geometry.Mat4)
    (hQ : ∀ v i j, inner ℝ (act (Q i) v) (act (Q j) v) =
      if i = j then ‖v‖ ^ 2 else 0) (s : Fin 3 → ℝ) (v : Vec4) (i : Fin 3) :
    coefficient (Q i) (act (imaginaryCombination Q s) v) v = s i * ‖v‖ ^ 2 := by
  rw [coefficient, imaginaryCombination, act_sum]
  simp only [act_smul, inner_sum, inner_smul_right, hQ, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem exists_two_plane (s t : Fin 3 → ℝ)
    (hs : ∑ i, s i ^ 2 = 1) (ht : ∑ i, t i ^ 2 = 1) :
    ∃ u v : Vec4, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ inner ℝ u v = 0 ∧
      (∀ i, coefficient (quaternionMatrix i) u v = s i) ∧
      (∀ i, coefficient (oppositeMatrix i) u v = -t i) := by
  obtain ⟨v, hv, hpair⟩ := exists_common_vector s t hs ht
  let L := imaginaryCombination quaternionMatrix s
  let u := act L v
  have hLorth : Lᵀ * L = 1 :=
    imaginaryCombination_orthogonal quaternionMatrix quaternionMatrix_anticommutator
      quaternionMatrix_transpose s hs
  refine ⟨u, v, (act_norm L hLorth v).trans hv, hv, ?_, ?_, ?_⟩
  · exact act_skew_self L (imaginaryCombination_transpose quaternionMatrix
      quaternionMatrix_transpose s) v
  · intro i
    simpa only [u, L, hv, one_pow, mul_one] using
      coefficient_combination quaternionMatrix quaternion_gram s v i
  · intro i
    change coefficient (oppositeMatrix i) (act L v) v = -t i
    rw [hpair]
    simp only [coefficient, inner_neg_right]
    have hh := coefficient_combination oppositeMatrix opposite_gram t v i
    simpa only [coefficient, hv, one_pow, mul_one] using congrArg Neg.neg hh

end
end PositiveEinsteinFour.SectionalPlane
end


section

/-! The arbitrary-frame weighted Hessian square in the original Green form. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

private theorem innerBianchi_add (X Y : Hessian)
    (hmX : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbX : ∀ i r, divergence X i r = 0)
    (hmY : ∀ i j, symmetric (Y i j) ∧ traceFree (Y i j))
    (hbY : ∀ i r, divergence Y i r = 0) :
    (∀ i j, symmetric ((X + Y) i j) ∧ traceFree ((X + Y) i j)) ∧
      (∀ i r, divergence (X + Y) i r = 0) := by
  constructor
  · intro i j
    constructor
    · intro a b
      change X i j a b + Y i j a b = X i j b a + Y i j b a
      rw [(hmX i j).1 a b, (hmY i j).1 a b]
    · change (∑ a, (X i j a a + Y i j a a)) = 0
      rw [Finset.sum_add_distrib, (hmX i j).2, (hmY i j).2, add_zero]
  · intro i r
    rw [divergence_add, hbX i r, hbY i r, add_zero]

/-- Polarization retains the exact full-matrix Green form on arbitrary
inner-Bianchi tensors, including nonsymmetric outer derivative slots. -/
theorem generalOriginal_polarization (A U : Mat) (hA : symmetric A) (hU : symmetric U)
    (htA : traceFree A) (htU : traceFree U) (X Y : Hessian)
    (hmX : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbX : ∀ i r, divergence X i r = 0)
    (hmY : ∀ i j, symmetric (Y i j) ∧ traceFree (Y i j))
    (hbY : ∀ i r, divergence Y i r = 0) :
    (generalOriginalCurvatureForm A U (X + Y) - generalOriginalCurvatureForm A U X -
      generalOriginalCurvatureForm A U Y) / 2 = generalCurvaturePairing A U X Y := by
  have hsum := innerBianchi_add X Y hmX hbX hmY hbY
  rw [generalOriginalCurvatureForm_eq_of_inner_bianchi A U (X + Y) hA hU htA htU
      hsum.1 hsum.2,
    generalOriginalCurvatureForm_eq_of_inner_bianchi A U X hA hU htA htU hmX hbX,
    generalOriginalCurvatureForm_eq_of_inner_bianchi A U Y hA hU htA htU hmY hbY,
    ← generalCurvaturePairing_self, ← generalCurvaturePairing_self,
    ← generalCurvaturePairing_self]
  rw [generalCurvaturePairing_add_left, generalCurvaturePairing_add_right,
    generalCurvaturePairing_add_right, generalCurvaturePairing_comm A U hA hU Y X]
  ring

theorem general_weightedQuadratic_eq (A U : Mat) (hA : symmetric A) (hU : symmetric U)
    (htA : traceFree A) (htU : traceFree U) (m : ℝ) (X Y : Hessian)
    (hmX : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbX : ∀ i r, divergence X i r = 0)
    (hmY : ∀ i j, symmetric (Y i j) ∧ traceFree (Y i j))
    (hbY : ∀ i r, divergence Y i r = 0) :
    weightedQuadratic (generalOriginalCurvatureForm A U) m X Y =
      (m * generalCurvaturePairing A U X X + generalCurvaturePairing A U X Y) / 6 := by
  unfold weightedQuadratic
  rw [generalOriginal_polarization A U hA hU htA htU X Y hmX hbX hmY hbY,
    generalOriginalCurvatureForm_eq_of_inner_bianchi A U X hA hU htA htU hmX hbX,
    ← generalCurvaturePairing_self]


private theorem generalPlus_projection_pairing (r s : Fin 3) (X L : Hessian)
    (hX : condition X) :
    hessianPairing (totalPlus r X) (totalPlus s (highestProjection L)) =
      hessianPairing (totalPlus r X) (totalPlus s L) := by
  have hXX := totalPlus_condition s (totalPlus r X) (totalPlus_condition r X hX)
  have hp := highestProjection_pairing_left (totalPlus s (totalPlus r X)) L hXX
  have h1 := totalPlus_skew s (totalPlus r X) (highestProjection L)
  have h2 := totalPlus_skew s (totalPlus r X) L
  linarith

private theorem generalMinus_projection_pairing (r s : Fin 3) (X L : Hessian)
    (hX : condition X) :
    hessianPairing (totalMinus r X) (totalMinus s (highestProjection L)) =
      hessianPairing (totalMinus r X) (totalMinus s L) := by
  have hXX := totalMinus_condition s (totalMinus r X) (totalMinus_condition r X hX)
  have hp := highestProjection_pairing_left (totalMinus s (totalMinus r X)) L hXX
  have h1 := totalMinus_skew s (totalMinus r X) (highestProjection L)
  have h2 := totalMinus_skew s (totalMinus r X) L
  linarith

theorem generalCurvaturePairing_highestProjection (A U : Mat) (X L : Hessian)
    (hX : condition X) :
    generalCurvaturePairing A U X (highestProjection L) = generalCurvaturePairing A U X L := by
  simp only [generalCurvaturePairing, highestProjection_pairing_left X L hX,
    generalPlus_projection_pairing _ _ X L hX,
    generalMinus_projection_pairing _ _ X L hX]

/-- The local square uses the actual orthogonal projection, with arbitrary
symmetric matrix coefficients and no pointwise eigenframe. -/
theorem general_weighted_highestProjection_square (A U : Mat)
    (hA : symmetric A) (hU : symmetric U) (X L : Hessian) (hX : condition X)
    (x y m : ℝ) (hm : 0 < m)
    (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2) :
    0 ≤ (m / 6) * generalCurvaturePairing A U X X +
      generalCurvaturePairing A U X L / 6 +
      generalCurvaturePairing A U (highestProjection L) (highestProjection L) / (24 * m) := by
  obtain ⟨c, rfl⟩ := exists_highest X hX
  obtain ⟨d, hd⟩ := highestProjection_has_coordinates L
  have hsum : condition (highest c + (1 / (2 * m)) • highestProjection L) := by
    rw [← hd, ← highest_smul, ← highest_add]
    exact highest_condition _
  have hq := generalCasimirCurvatureForm_nonneg A U _ hsum x y hAx hUy hxy
  rw [← generalCurvaturePairing_self] at hq
  have he : (m / 6) * generalCurvaturePairing A U
      (highest c + (1 / (2 * m)) • highestProjection L)
      (highest c + (1 / (2 * m)) • highestProjection L) =
      (m / 6) * generalCurvaturePairing A U (highest c) (highest c) +
        generalCurvaturePairing A U (highest c) L / 6 +
        generalCurvaturePairing A U (highestProjection L) (highestProjection L) / (24 * m) := by
    rw [generalCurvaturePairing_add_left]
    simp only [generalCurvaturePairing_add_right, generalCurvaturePairing_smul_left,
      generalCurvaturePairing_smul_right]
    rw [generalCurvaturePairing_comm A U hA hU (highestProjection L) (highest c),
      generalCurvaturePairing_highestProjection A U (highest c) L (highest_condition c)]
    field_simp [hm.ne']
    ring
  rw [← he]
  exact mul_nonneg (by positivity) hq

def generalTraceCorrection (A U M : Mat) (m : ℝ) (L : Hessian) : ℝ :=
  -(m * generalCurvaturePairing A U (traceComponent M) (traceComponent M) +
    generalCurvaturePairing A U (traceComponent M) L) / 6

/-- The full arbitrary-frame local Hessian inequality, including the exact
prescribed trace and the constructed highest-projection cost. -/
theorem general_local_weighted_original_square (A U M : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (hM : symmetric M) (htM : traceFree M) (X L : Hessian)
    (hmX : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbX : ∀ i r, divergence X i r = 0) (htrace : hessianTrace X = M)
    (hY : condition (X - traceComponent M))
    (hmL : ∀ i j, symmetric (L i j) ∧ traceFree (L i j))
    (hbL : ∀ i r, divergence L i r = 0)
    (x y m : ℝ) (hm : 0 < m)
    (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2) :
    0 ≤ weightedQuadratic (generalOriginalCurvatureForm A U) m X L +
      generalTraceCorrection A U M m L +
      generalCurvaturePairing A U (highestProjection L) (highestProjection L) / (24 * m) := by
  have hsquare := general_weighted_highestProjection_square A U hA hU
    (X - traceComponent M) L hY x y m hm hAx hUy hxy
  have hsub := general_weighted_trace_subtraction A U M hA hU htA hM htM X L
    hmX hbX htrace m
  rw [general_weightedQuadratic_eq A U hA hU htA htU m X L hmX hbX hmL hbL]
  unfold generalTraceCorrection
  linarith

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! The actual Hessian after subtracting its forced trace belongs to the
highest tensor subspace. Its trace and outer symmetry are derived from
the same raw curvature commutator used in the Green identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Membership of the actual trace-free Hessian in the highest subspace
is a theorem, rather than an additional geometric input. -/
theorem MetricGreenData.highestRemainder
    {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (d : MetricGreenData g μ) (e : FrameBundle g) :
    condition (plusWeylHessian g e.base e.frame -
      traceComponent (weylLaplacian (plusWeyl g e.base e.frame))) :=
  general_trace_subtracted_condition _ _ (d.weyl.symmetric e) (d.weyl.traceFree e)
    (d.weyl.hessianMatrix e) (d.weyl.hessianBianchi e) (d.weyl.hessianCommutator e)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The sharp opposite-block cost for an arbitrary symmetric coefficient
matrix.  A concrete orthogonal quaternion expansion of the two derivative
slots replaces a second choice of eigenframe. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

/-- The coefficients in the orthonormal basis `(L_a R_b)/2` of real
four-by-four matrices, with the scalar quaternion in position zero. -/
def rightQuaternionCoefficients (M : Mat4) : Mat4 :=
  ![![(M 0 0 + M 1 1 + M 2 2 + M 3 3) / 2,
      (-M 0 1 + M 1 0 + M 2 3 - M 3 2) / 2,
      (-M 0 2 - M 1 3 + M 2 0 + M 3 1) / 2,
      (-M 0 3 + M 1 2 - M 2 1 + M 3 0) / 2],
    ![(-M 0 1 + M 1 0 - M 2 3 + M 3 2) / 2,
      (-M 0 0 - M 1 1 + M 2 2 + M 3 3) / 2,
      (M 0 3 - M 1 2 - M 2 1 + M 3 0) / 2,
      (-M 0 2 - M 1 3 - M 2 0 - M 3 1) / 2],
    ![(-M 0 2 + M 1 3 + M 2 0 - M 3 1) / 2,
      (-M 0 3 - M 1 2 - M 2 1 - M 3 0) / 2,
      (-M 0 0 + M 1 1 - M 2 2 + M 3 3) / 2,
      (M 0 1 + M 1 0 - M 2 3 - M 3 2) / 2],
    ![(-M 0 3 - M 1 2 + M 2 1 + M 3 0) / 2,
      (M 0 2 - M 1 3 + M 2 0 - M 3 1) / 2,
      (-M 0 1 - M 1 0 - M 2 3 - M 3 2) / 2,
      (-M 0 0 + M 1 1 + M 2 2 - M 3 3) / 2]]

/-- The exact Parseval identity for this real orthogonal expansion. -/
theorem rightQuaternionCoefficients_pairing (M N : Mat4) :
    (∑ a, ∑ b, rightQuaternionCoefficients M a b * rightQuaternionCoefficients N a b) =
      ∑ i, ∑ j, M i j * N i j := by
  norm_num [rightQuaternionCoefficients, Fin.sum_univ_four]
  ring

private def rightMatrixAction (r : Fin 3) (M : Mat4) : Mat4 := fun i j =>
  (∑ k, rightQuaternion r i k * M k j) + ∑ k, rightQuaternion r j k * M i k

private def rightCoefficientAction (r : Fin 3) (C : Mat4) : Mat4 := fun a =>
  ![![0, 0, 2 * C a 3, -2 * C a 2],
    ![0, -2 * C a 3, 0, 2 * C a 1],
    ![0, 2 * C a 2, -2 * C a 1, 0]] r

private theorem rightQuaternionCoefficients_action_zero (M : Mat4) :
    rightQuaternionCoefficients (rightMatrixAction 0 M) =
      rightCoefficientAction 0 (rightQuaternionCoefficients M) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rightQuaternionCoefficients, rightMatrixAction, rightCoefficientAction,
      rightQuaternion, Fin.sum_univ_four] <;> ring

private theorem rightQuaternionCoefficients_action_one (M : Mat4) :
    rightQuaternionCoefficients (rightMatrixAction 1 M) =
      rightCoefficientAction 1 (rightQuaternionCoefficients M) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rightQuaternionCoefficients, rightMatrixAction, rightCoefficientAction,
      rightQuaternion, Fin.sum_univ_four] <;> ring

private theorem rightQuaternionCoefficients_action_two (M : Mat4) :
    rightQuaternionCoefficients (rightMatrixAction 2 M) =
      rightCoefficientAction 2 (rightQuaternionCoefficients M) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rightQuaternionCoefficients, rightMatrixAction, rightCoefficientAction,
      rightQuaternion, Fin.sum_univ_four] <;> ring

private theorem rightQuaternionCoefficients_action (r : Fin 3) (M : Mat4) :
    rightQuaternionCoefficients (rightMatrixAction r M) =
      rightCoefficientAction r (rightQuaternionCoefficients M) := by
  fin_cases r
  · exact rightQuaternionCoefficients_action_zero M
  · exact rightQuaternionCoefficients_action_one M
  · exact rightQuaternionCoefficients_action_two M

private theorem rightCoefficientAction_pairing (r s : Fin 3) (C : Mat4) :
    (∑ a, ∑ b, rightCoefficientAction r C a b * rightCoefficientAction s C a b) =
      4 * ((if r = s then ∑ a, ∑ t : Fin 3, C a t.succ ^ 2 else 0) -
        ∑ a, C a r.succ * C a s.succ) := by
  fin_cases r <;> fin_cases s <;>
    simp [rightCoefficientAction, Fin.sum_univ_four, Fin.sum_univ_three] <;> ring

private theorem rightMatrixAction_pairing (r s : Fin 3) (M : Mat4) :
    (∑ i, ∑ j, rightMatrixAction r M i j * rightMatrixAction s M i j) =
      4 * ((if r = s then
          ∑ a, ∑ t : Fin 3, rightQuaternionCoefficients M a t.succ ^ 2 else 0) -
        ∑ a, rightQuaternionCoefficients M a r.succ *
          rightQuaternionCoefficients M a s.succ) := by
  rw [← rightQuaternionCoefficients_pairing,
    rightQuaternionCoefficients_action, rightQuaternionCoefficients_action]
  exact rightCoefficientAction_pairing r s (rightQuaternionCoefficients M)

/-- Only the three imaginary right-quaternion coefficients enter the
opposite-block action. -/
def rightVectorEnergy (X : Hessian) : ℝ :=
  ∑ a, ∑ b, ∑ t : Fin 4, ∑ r : Fin 3,
    rightQuaternionCoefficients (fun i j => X i j a b) t r.succ ^ 2

/-- Their ordinary three-dimensional coefficient Gram form. -/
def rightVectorGram (U : Mat) (X : Hessian) : ℝ :=
  ∑ a, ∑ b, ∑ t : Fin 4, ∑ r, ∑ s,
    U r s * rightQuaternionCoefficients (fun i j => X i j a b) t r.succ *
      rightQuaternionCoefficients (fun i j => X i j a b) t s.succ

/-- The omitted scalar right-quaternion coefficient has nonnegative energy. -/
theorem rightVectorEnergy_le (X : Hessian) : rightVectorEnergy X ≤ hessianNormSq X := by
  have h (a b : Fin 3) :
      (∑ t : Fin 4, ∑ r : Fin 3,
        rightQuaternionCoefficients (fun i j => X i j a b) t r.succ ^ 2) ≤
        ∑ i, ∑ j, X i j a b ^ 2 := by
    have hp := rightQuaternionCoefficients_pairing
      (fun i j => X i j a b) (fun i j => X i j a b)
    simp only [← pow_two] at hp
    rw [← hp]
    apply Finset.sum_le_sum
    intro t _
    simp only [Fin.sum_univ_four, Fin.sum_univ_three,
      show (0 : Fin 3).succ = (1 : Fin 4) from rfl,
      show (1 : Fin 3).succ = (2 : Fin 4) from rfl,
      show (2 : Fin 3).succ = (3 : Fin 4) from rfl]
    linarith [sq_nonneg (rightQuaternionCoefficients (fun i j => X i j a b) t 0)]
  exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => h a b

private theorem sum_pair_triple (F : Fin 3 → Fin 3 → Fin 4 → Fin 3 → Fin 3 → ℝ) :
    (∑ r, ∑ s, ∑ a, ∑ b, ∑ t, F a b t r s) =
      ∑ a, ∑ b, ∑ t, ∑ r, ∑ s, F a b t r s := by
  have move (G : Fin 3 → Fin 3 → Fin 4 → Fin 3 → ℝ) :
      (∑ r, ∑ a, ∑ b, ∑ t, G a b t r) =
        ∑ a, ∑ b, ∑ t, ∑ r, G a b t r := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_comm]
  calc
    _ = ∑ r, ∑ a, ∑ b, ∑ t, ∑ s, F a b t r s := by
      apply Finset.sum_congr rfl
      intro r _
      exact move (fun a b t s => F a b t r s)
    _ = _ := move (fun a b t r => ∑ s, F a b t r s)

private theorem weighted_complement_gram (U H : Mat) (e : ℝ) :
    (∑ r, ∑ s, U r s * (4 * ((if r = s then e else 0) - H r s))) =
      4 * ((∑ r, U r r) * e - ∑ r, ∑ s, U r s * H r s) := by
  simp only [Fin.sum_univ_three]
  norm_num
  ring

/-- The complete minus Gram matrix is the scalar part minus this positive
three-dimensional Gram form. This identity is valid for every Hessian. -/
theorem hessianGram_totalMinus (U : Mat) (X : Hessian) :
    hessianGram U (fun r => totalMinus r X) =
      4 * ((∑ r, U r r) * rightVectorEnergy X - rightVectorGram U X) := by
  have hp (r s : Fin 3) :
      hessianPairing (totalMinus r X) (totalMinus s X) =
        4 * ((if r = s then rightVectorEnergy X else 0) -
          ∑ a, ∑ b, ∑ t : Fin 4,
            rightQuaternionCoefficients (fun i j => X i j a b) t r.succ *
              rightQuaternionCoefficients (fun i j => X i j a b) t s.succ) := by
    change (∑ a : Fin 3, ∑ b : Fin 3,
      ∑ i : Fin 4, ∑ j : Fin 4,
        rightMatrixAction r (fun i j => X i j a b) i j *
          rightMatrixAction s (fun i j => X i j a b) i j) = _
    have he (a b : Fin 3) := rightMatrixAction_pairing r s
      (show Mat4 from fun i j => X i j a b)
    simp_rw [he]
    by_cases hrs : r = s <;>
      simp [hrs, rightVectorEnergy, Finset.sum_sub_distrib, ← Finset.mul_sum]
  let H : Mat := fun r s => ∑ a : Fin 3, ∑ b : Fin 3, ∑ t : Fin 4,
    rightQuaternionCoefficients (fun i j => X i j a b) t r.succ *
      rightQuaternionCoefficients (fun i j => X i j a b) t s.succ
  have he : hessianGram U (fun r => totalMinus r X) =
      ∑ r : Fin 3, ∑ s : Fin 3,
        U r s * (4 * ((if r = s then rightVectorEnergy X else 0) - H r s)) := by
    unfold hessianGram
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    exact congrArg (fun z : ℝ => U r s * z) (hp r s)
  rw [he, weighted_complement_gram U H (rightVectorEnergy X)]
  congr 2
  dsimp only [H]
  simp only [Finset.mul_sum]
  rw [sum_pair_triple]
  unfold rightVectorGram
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Positive semidefiniteness is used only on the actual coefficient vectors. -/
theorem rightVectorGram_nonneg (U : Mat) (hU : U.PosSemidef) (X : Hessian) :
    0 ≤ rightVectorGram U X := by
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  apply Finset.sum_nonneg
  intro t _
  have h := hU.dotProduct_mulVec_nonneg
    (fun r => rightQuaternionCoefficients (fun i j => X i j a b) t r.succ)
  simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem rightVectorGram_shift (U : Mat) (y : ℝ) (X : Hessian) :
    rightVectorGram (U + y • (1 : Mat)) X =
      rightVectorGram U X + y * rightVectorEnergy X := by
  have h (c : Fin 3 → ℝ) :
      (∑ r, ∑ s, (U + y • (1 : Mat)) r s * c r * c s) =
        (∑ r, ∑ s, U r s * c r * c s) + y * ∑ r, c r ^ 2 := by
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Fin.sum_univ_three]
    norm_num
    ring
  unfold rightVectorGram rightVectorEnergy
  simp_rw [h]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- A shifted positive matrix with zero trace has a nonnegative shift. -/
theorem shift_nonneg_of_traceFree (U : Mat) (hU : traceFree U) (y : ℝ)
    (hUy : (U + y • (1 : Mat)).PosSemidef) : 0 ≤ y := by
  have h := hUy.trace_nonneg
  have ht : Matrix.trace U = 0 := hU
  rw [Matrix.trace_add, Matrix.trace_smul, ht] at h
  norm_num at h
  linarith

/-- Sharp opposite-block upper cost, with no eigenframe and no additional
condition on the two-derivative tensor. -/
theorem general_minus_cost (U : Mat) (hU : traceFree U) (y : ℝ) (hy : 0 ≤ y)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (X : Hessian) :
    hessianGram U (fun r => totalMinus r X) / 4 ≤ y * hessianNormSq X := by
  have h := rightVectorGram_nonneg _ hUy X
  rw [rightVectorGram_shift] at h
  rw [hessianGram_totalMinus, hU]
  have he := mul_le_mul_of_nonneg_left (rightVectorEnergy_le X) hy
  nlinarith only [h, he]

/-- The sign of the shift is already forced by the matrix hypotheses. -/
theorem general_minus_cost_of_shift (U : Mat) (hU : traceFree U) (y : ℝ)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (X : Hessian) :
    hessianGram U (fun r => totalMinus r X) / 4 ≤ y * hessianNormSq X :=
  general_minus_cost U hU y (shift_nonneg_of_traceFree U hU y hUy) hUy X

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! Apply the arbitrary-matrix highest-square inequality to the actual
metric Hessian and its exact trace. No eigenframe is differentiated. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Pointwise shifted-matrix positivity is the elementary sectional
condition consumed by the local tensor estimate. Its geometric derivation
from the curvature decomposition is separate from the weighted estimate. -/
def ShiftedCurvaturePositive (g : SmoothMetric M) : Prop :=
  ∀ e : FrameBundle g, ∃ x y : ℝ,
    (plusWeyl g e.base e.frame + x • (1 : Mat)).PosSemidef ∧
    (minusWeyl g e.base e.frame + y • (1 : Mat)).PosSemidef ∧ x + y ≤ 2

theorem MetricGreenData.localWeightedHessian
    {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (d : MetricGreenData g μ) (o : OppositeWeylData d)
    (hp : ShiftedCurvaturePositive g) (e : FrameBundle g)
    (m : ℝ) (hm : 0 < m) (a : Vec) :
    let A := plusWeyl g e.base e.frame
    let U := minusWeyl g e.base e.frame
    let X := plusWeylHessian g e.base e.frame
    let L := weightTensor a (plusGradientTensor g e.base e.frame)
    0 ≤ weightedQuadratic (generalOriginalCurvatureForm A U) m X L +
      generalTraceCorrection A U (weylLaplacian A) m L +
      generalCurvaturePairing A U (highestProjection L) (highestProjection L) / (24 * m) := by
  dsimp only
  obtain ⟨x, y, hAx, hUy, hxy⟩ := hp e
  have hL := weightTensor_matrix_bianchi a (plusGradientTensor g e.base e.frame)
    (gradientTensor_traceFree _ (d.gradientConstraints e).2)
    (gradientTensor_bianchi _ (d.gradientConstraints e).1 (d.gradientBianchi e))
  exact general_local_weighted_original_square _ _ _ (d.weyl.symmetric e) (o.symmetric e)
    (d.weyl.traceFree e) (o.traceFree e)
    (weylLaplacian_symmetric _ (d.weyl.symmetric e))
    (weylLaplacian_traceFree _ (d.weyl.traceFree e)) _ _
    (d.weyl.hessianMatrix e) (d.weyl.hessianBianchi e)
    (metric_weyl_trace g d.weyl e) (d.highestRemainder e) hL.1 hL.2
    x y m hm hAx hUy hxy

/-- The pointwise square integrates directly on the actual frame bundle. -/
theorem MetricGreenData.integratedWeightedHessian
    {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (d : MetricGreenData g μ) (o : OppositeWeylData d)
    (hp : ShiftedCurvaturePositive g) (m : FrameBundle g → ℝ)
    (hm : ∀ e, 0 < m e) (a : FrameBundle g → Vec) :
    0 ≤ ∫ e,
      weightedQuadratic
        (generalOriginalCurvatureForm (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
        (m e) (plusWeylHessian g e.base e.frame)
        (weightTensor (a e) (plusGradientTensor g e.base e.frame)) +
      generalTraceCorrection (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (weylLaplacian (plusWeyl g e.base e.frame)) (m e)
        (weightTensor (a e) (plusGradientTensor g e.base e.frame)) +
      generalCurvaturePairing (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (highestProjection (weightTensor (a e) (plusGradientTensor g e.base e.frame)))
        (highestProjection (weightTensor (a e) (plusGradientTensor g e.base e.frame))) /
          (24 * m e) ∂μ :=
  integral_nonneg (fun e => d.localWeightedHessian o hp e (m e) (hm e) (a e))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The sharp real-vector projection cost in an arbitrary Weyl frame. -/

namespace PositiveEinsteinFour.Bianchi

open scoped BigOperators
open Matrix TraceHessian HighestHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

private theorem quaternion_combination_pairing (a : Vec) (r t : ℝ)
    (c d : Fin 3 → ℝ) :
    (∑ i : Fin 4, (r * a i + ∑ s, c s * quaternion s a i) *
      (t * a i + ∑ s, d s * quaternion s a i)) =
        ‖a‖ ^ 2 * (r * t + ∑ s, c s * d s) := by
  simp [EuclideanSpace.real_norm_sq_eq, quaternion, Fin.sum_univ_four, Fin.sum_univ_three]
  ring

private theorem rawPairing_entries (Z W : RawGradient) :
    rawPairing Z W = ∑ b, ∑ c, ∑ j : Fin 4, Z b c j * W b c j := by
  rw [rawPairing_vectors]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]

/-- Polarized version of the real outer-quaternion calculation. -/
theorem quaternionCombination_pairing (a : Vec) (Z W : RawGradient)
    (C D : Fin 3 → RawGradient) :
    hessianPairing (quaternionCombination a Z C) (quaternionCombination a W D) =
      ‖a‖ ^ 2 * (rawPairing Z W + ∑ s, rawPairing (C s) (D s)) := by
  have h (b c : Fin 3) (j : Fin 4) :
      (∑ i, quaternionCombination a Z C i j b c * quaternionCombination a W D i j b c) =
        ‖a‖ ^ 2 * (Z b c j * W b c j + ∑ s, C s b c j * D s b c j) := by
    simpa only [quaternionCombination, mul_comm] using
      quaternion_combination_pairing a (Z b c j) (W b c j)
        (fun s => C s b c j) (fun s => D s b c j)
  calc
    _ = ∑ b, ∑ c, ∑ j : Fin 4, ∑ i : Fin 4,
        quaternionCombination a Z C i j b c * quaternionCombination a W D i j b c := by
      unfold hessianPairing
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = ‖a‖ ^ 2 * ((∑ b, ∑ c, ∑ j : Fin 4, Z b c j * W b c j) +
        ∑ b, ∑ c, ∑ j : Fin 4, ∑ s, C s b c j * D s b c j) := by
      simp_rw [h]
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by
      simp only [rawPairing_entries]
      congr 2
      calc
        _ = ∑ b, ∑ c, ∑ s, ∑ j : Fin 4, C s b c j * D s b c j := by
          apply Finset.sum_congr rfl
          intro b _
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.sum_comm]
        _ = ∑ b, ∑ s, ∑ c, ∑ j : Fin 4, C s b c j * D s b c j := by
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.sum_comm]
        _ = _ := Finset.sum_comm

/-- Both generator indices of the real-vector identity are retained. -/
theorem totalPlus_weightPlusPart_pairing (s t : Fin 3) (a : Vec) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    hessianPairing (totalPlus s (weightPlusPart a Z))
      (totalPlus t (weightPlusPart a Z)) =
      ‖a‖ ^ 2 * ((if s = t then (7 / 12 : ℝ) * Z.squaredNorm else 0) +
        (3 / 4 : ℝ) * rawPairing (rawGradientGenerator s Z.matrix)
          (rawGradientGenerator t Z.matrix)) := by
  rw [totalPlus_weightPlusPart, totalPlus_weightPlusPart,
    hessianPairing_smul_left, hessianPairing_smul_right,
    quaternionCombination_pairing, rawPairing_smul_left, rawPairing_smul_right,
    rawCostCoefficient_pairing s t Z hz hb]
  by_cases hst : s = t <;> simp only [hst, ite_true, ite_false] <;> ring

/-- The plus contribution to the sharp cost, with a full symmetric Weyl matrix. -/
theorem totalPlus_weightPlusPart_generalCost (A : Mat)
    (hA : symmetric A) (ht : traceFree A) (a : Vec) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    hessianGram A (fun r => totalPlus r (weightPlusPart a Z)) =
      -30 * ‖a‖ ^ 2 * generalGradientForm A Z := by
  have he := general_generator_energy A hA ht Z hz hb
  change (∑ r, A r r) = 0 at ht
  simp only [hessianGram, totalPlus_weightPlusPart_pairing _ _ a Z hz hb]
  simp only [Fin.sum_univ_three] at he ht ⊢
  norm_num
  linear_combination (3 / 4 : ℝ) * ‖a‖ ^ 2 * he +
    (7 / 12 : ℝ) * ‖a‖ ^ 2 * Z.squaredNorm * ht

end
end PositiveEinsteinFour.Bianchi

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

private theorem hessianNormSq_nonneg (X : Hessian) : 0 ≤ hessianNormSq X := by
  unfold hessianNormSq
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem general_nonneg_of_plus_energy (A U : Mat) (X : Hessian)
    (x y : ℝ) (hy : 0 ≤ y)
    (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2)
    (hp : (∑ r, hessianNormSq (totalPlus r X)) = 48 * hessianNormSq X) :
    0 ≤ generalCasimirCurvatureForm A U X := by
  have ha := hessianGram_nonneg _ hAx (fun r => totalPlus r X)
  have hu := hessianGram_nonneg _ hUy (fun r => totalMinus r X)
  rw [hessianGram_shift, hp] at ha
  rw [hessianGram_shift] at hu
  have hm := mul_le_mul_of_nonneg_left (totalMinus_energy_le X) hy
  have hn := mul_nonneg (show 0 ≤ 4 - 2 * x - 2 * y by linarith)
    (hessianNormSq_nonneg X)
  unfold generalCasimirCurvatureForm
  nlinarith only [ha, hu, hm, hn]

private theorem totalPlus_sub (r : Fin 3) (X Y : Hessian) :
    totalPlus r (X - Y) = totalPlus r X - totalPlus r Y := by
  have h : X - Y = X + (-1 : ℝ) • Y := by module
  rw [h, totalPlus_add, totalPlus_smul]
  module

private theorem projected_plus_pairing (r : Fin 3) (W : Hessian) :
    hessianPairing (totalPlus r W) (totalPlus r (highestProjection W)) =
      hessianNormSq (totalPlus r (highestProjection W)) := by
  have hP := highestProjection_condition W
  have hPP := totalPlus_condition r (totalPlus r (highestProjection W))
    (totalPlus_condition r (highestProjection W) hP)
  have h := highestProjection_pairing_right W
    (totalPlus r (totalPlus r (highestProjection W))) hPP
  have h1 := totalPlus_skew r W (totalPlus r (highestProjection W))
  have h2 := totalPlus_skew r (highestProjection W) (totalPlus r (highestProjection W))
  rw [hessianPairing_self] at h2
  linarith

private theorem projection_difference_plus_energy (W : Hessian)
    (hW : (∑ r, hessianNormSq (totalPlus r W)) = 48 * hessianNormSq W) :
    (∑ r, hessianNormSq (totalPlus r (W - highestProjection W))) =
      48 * hessianNormSq (W - highestProjection W) := by
  have hP := totalPlus_energy_of_condition (highestProjection W) (highestProjection_condition W)
  have hN := highestProjection_norm_split W
  rw [hessianNormSq_sub] at hN
  simp only [totalPlus_sub, hessianNormSq_sub, projected_plus_pairing]
  simp only [Fin.sum_univ_three] at hW hP ⊢
  nlinarith

/-- The projection cost is bounded by the real-vector plus part in any frame. -/
theorem general_highestProjection_curvature_le (A U : Mat) (hA : symmetric A)
    (hU : symmetric U) (x y : ℝ) (hy : 0 ≤ y)
    (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2)
    (W : Hessian) (hp : (∑ r, hessianNormSq (totalPlus r W)) = 48 * hessianNormSq W) :
    generalCurvaturePairing A U (highestProjection W) (highestProjection W) ≤
      generalCurvaturePairing A U W W := by
  have hn := general_nonneg_of_plus_energy A U (W - highestProjection W) x y hy
    hAx hUy hxy (projection_difference_plus_energy W hp)
  rw [← generalCurvaturePairing_self] at hn
  have hsub : W - highestProjection W = W + (-1 : ℝ) • highestProjection W := by module
  rw [hsub, generalCurvaturePairing_add_left] at hn
  simp only [generalCurvaturePairing_add_right, generalCurvaturePairing_smul_left,
    generalCurvaturePairing_smul_right] at hn
  have hc := generalCurvaturePairing_comm A U hA hU W (highestProjection W)
  have hpair := generalCurvaturePairing_highestProjection A U (highestProjection W) W
    (highestProjection_condition W)
  linarith

/-- The original sharp projection bound, with no diagonal frame assumption. -/
theorem general_highestProjection_weight_cost (A U : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (x y : ℝ) (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2)
    (a : Vec) (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    generalCurvaturePairing A U
      (highestProjection (weightTensor a Z)) (highestProjection (weightTensor a Z)) ≤
      ‖a‖ ^ 2 * ((7 / 12 : ℝ) * (4 + y) * Z.squaredNorm -
        (5 / 4 : ℝ) * generalGradientForm A Z) := by
  have hproj : highestProjection (weightPlusPart a Z) =
      highestProjection (weightTensor a Z) := by
    rw [weightPlusPart_eq_plusPolynomial, highestProjection_plusPolynomial]
  have hp := general_highestProjection_curvature_le A U hA hU x y
    (shift_nonneg_of_traceFree U htU y hUy) hAx hUy hxy (weightPlusPart a Z)
    (weightPlusPart_plus_energy a Z hz hb)
  rw [hproj] at hp
  have hm := general_minus_cost_of_shift U htU y hUy (weightPlusPart a Z)
  have hc := totalPlus_weightPlusPart_generalCost A hA htA a Z hz hb
  have hn := weightPlusPart_norm a Z hz hb
  conv_rhs at hp =>
    rw [generalCurvaturePairing_self]
    unfold generalCasimirCurvatureForm
  rw [hc, hn] at hp
  rw [hn] at hm
  nlinarith only [hp, hm]

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! Continuity of the actual weighted-Hessian integrands. The orthogonal
projection is the already constructed projection, not a chosen eigenframe. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance hessianContinuityNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance hessianContinuityNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance hessianContinuityNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

def hessianVectorMap : Hessian →L[ℝ] HessianSpace :=
  ({ toFun := hessianVector
     map_add' := fun X Y => by ext p; rfl
     map_smul' := fun r X => by ext p; rfl } : Hessian →ₗ[ℝ] HessianSpace).toContinuousLinearMap

def vectorHessianMap : HessianSpace →L[ℝ] Hessian :=
  ({ toFun := vectorHessian
     map_add' := fun X Y => by ext i j a b; rfl
     map_smul' := fun r X => by ext i j a b; rfl } : HessianSpace →ₗ[ℝ] Hessian).toContinuousLinearMap

theorem continuous_highestProjection : Continuous highestProjection :=
  vectorHessianMap.continuous.comp
    (highestSubspace.starProjection.continuous.comp hessianVectorMap.continuous)

section Continuous

variable {Ω : Type*} [TopologicalSpace Ω]

theorem continuous_hessianPairing {X Y : Ω → Hessian}
    (hX : Continuous X) (hY : Continuous Y) :
    Continuous (fun x => hessianPairing (X x) (Y x)) := by
  simp only [← hessianVector_inner]
  exact (hessianVectorMap.continuous.comp hX).inner
    (hessianVectorMap.continuous.comp hY)

theorem continuous_derivativePairing {A : Ω → DerivativeCoefficient} {X Y : Ω → Hessian}
    (hA : Continuous A) (hX : Continuous X) (hY : Continuous Y) :
    Continuous (fun x => HighestHessian.derivativePairing (A x) (X x) (Y x)) := by
  simp only [HighestHessian.derivativePairing, matrixPairing]
  fun_prop

theorem continuous_matrixHessianPairing {A : Ω → Mat} {X Y : Ω → Hessian}
    (hA : Continuous A) (hX : Continuous X) (hY : Continuous Y) :
    Continuous (fun x => matrixHessianPairing (A x) (X x) (Y x)) := by
  unfold matrixHessianPairing
  apply continuous_finsetSum
  intro i _
  exact (gradientVectorMap.continuous.comp ((continuous_apply i).comp hX)).inner
    ((matrixSlot.continuous.comp hA).clm_apply
      (gradientVectorMap.continuous.comp ((continuous_apply i).comp hY)))

theorem continuous_weightedQuadratic {q : Ω → Hessian → ℝ}
    (hq : ∀ W : Ω → Hessian, Continuous W → Continuous (fun x => q x (W x)))
    {m : Ω → ℝ} {X L : Ω → Hessian}
    (hm : Continuous m) (hX : Continuous X) (hL : Continuous L) :
    Continuous (fun x => weightedQuadratic (q x) (m x) (X x) (L x)) := by
  exact ((hm.mul (hq X hX)).add
    ((((hq (X + L) (hX.add hL)).sub (hq X hX)).sub (hq L hL)).div_const 2)).div_const 6

theorem continuous_weylGradientEnergy {Z : Ω → Fin 4 → Mat} (hZ : Continuous Z) :
    Continuous (fun x => weylGradientEnergy (Z x)) := by
  simp only [weylGradientEnergy, matrixPairing]
  fun_prop

theorem continuous_matrixSlotAction {A Z : Ω → Mat}
    (hA : Continuous A) (hZ : Continuous Z) :
    Continuous (fun x => matrixSlotAction (A x) (Z x)) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  by_cases hab : a = b
  · simp only [matrixSlotAction, hab, ite_true]
    fun_prop
  · simp only [matrixSlotAction, hab, ite_false]
    fun_prop

theorem continuous_weylMatrixEnergy {A : Ω → Mat} {Z : Ω → Fin 4 → Mat}
    (hA : Continuous A) (hZ : Continuous Z) :
    Continuous (fun x => weylMatrixEnergy (A x) (Z x)) := by
  have h (i : Fin 4) := continuous_matrixSlotAction hA ((continuous_apply i).comp hZ)
  simp only [weylMatrixEnergy, matrixPairing]
  fun_prop

theorem continuous_weylRadialSquare {A : Ω → Mat} {Z : Ω → Fin 4 → Mat}
    (hA : Continuous A) (hZ : Continuous Z) :
    Continuous (fun x => weylRadialSquare (A x) (Z x)) := by
  simp only [weylRadialSquare, Matrix.trace, Matrix.diag, Matrix.mul_apply]
  fun_prop

theorem rawBianchiProjection_coordinates (Z : RawGradient) (p : GradientIndex) :
    rawCoordinates (rawBianchiProjection Z) p = (1 / 10 : ℝ) *
      (6 * rawCoordinates Z p - ∑ q, gradientCouplingKernel p q * rawCoordinates Z q) := by
  change (1 / 10 : ℝ) * (6 * rawCoordinates Z p - rawCoordinates (rawCoupling Z) p) = _
  rw [rawCoupling_coordinates]

theorem continuous_weylCompressionEnergy {A : Ω → Mat} {Z : Ω → Fin 4 → Mat}
    (hA : Continuous A) (hZ : Continuous Z) (hs : ∀ x i, symmetric (Z x i)) :
    Continuous (fun x => weylCompressionEnergy (A x) (Z x)) := by
  have hg (p : GradientIndex) : Continuous (fun x =>
      rawCoordinates (generalMatrixAction (A x) (gradientTensor (Z x)).matrix) p) := by
    change Continuous (fun x => matrixSlotAction (A x)
      (fun a b => (gradientTensor (Z x)).matrix a b p.1) p.2.1 p.2.2)
    simp_rw [gradientTensor_matrix _ (hs _)]
    exact (continuous_apply p.2.2).comp ((continuous_apply p.2.1).comp
      (continuous_matrixSlotAction hA ((continuous_apply p.1).comp hZ)))
  unfold weylCompressionEnergy rawPairing
  simp_rw [rawBianchiProjection_coordinates]
  fun_prop

theorem continuous_generalCurvaturePairing {A U : Ω → Mat} {X Y : Ω → Hessian}
    (hA : Continuous A) (hU : Continuous U) (hX : Continuous X) (hY : Continuous Y) :
    Continuous (fun x => generalCurvaturePairing (A x) (U x) (X x) (Y x)) := by
  have hplus (s : Fin 3) {F : Ω → Hessian} (hF : Continuous F) :
      Continuous (fun x => totalPlus s (F x)) := by
    change Continuous (fun x i j a b =>
      (∑ c, (rotation s a c * F x i j c b - F x i j a c * rotation s c b)) +
        (∑ k, quaternionMatrix s i k * F x k j a b) +
        ∑ k, quaternionMatrix s j k * F x i k a b)
    fun_prop
  have hminus (s : Fin 3) {F : Ω → Hessian} (hF : Continuous F) :
      Continuous (fun x => totalMinus s (F x)) := by
    change Continuous (fun x i j a b =>
      (∑ k, rightQuaternion s i k * F x k j a b) +
        ∑ k, rightQuaternion s j k * F x i k a b)
    fun_prop
  unfold generalCurvaturePairing
  exact ((continuous_const.mul (continuous_hessianPairing hX hY)).add
    ((continuous_finsetSum _ fun r _ => continuous_finsetSum _ fun s _ =>
      ((continuous_apply s).comp ((continuous_apply r).comp hA)).mul
        (continuous_hessianPairing (hplus r hX) (hplus s hY))).div_const 24)).add
    ((continuous_finsetSum _ fun r _ => continuous_finsetSum _ fun s _ =>
      ((continuous_apply s).comp ((continuous_apply r).comp hU)).mul
        (continuous_hessianPairing (hminus r hX) (hminus s hY))).div_const 4)

end Continuous

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem continuousFullHessian (d : MetricGreenData g μ) :
    Continuous (fun e : FrameBundle g => plusWeylHessian g e.base e.frame) :=
  continuous_pi (fun i => continuous_pi (d.continuousHessian i))

theorem continuousWeightTensor (d : MetricGreenData g μ)
    (dm : Fin 4 → C(FrameBundle g, ℝ)) :
    Continuous (fun e => weightTensor (WithLp.toLp 2 (fun i => dm i e))
      (plusGradientTensor g e.base e.frame)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  change Continuous (fun e => dm i e *
    (gradientTensor (plusWeylGradient g e.base e.frame)).matrix a b j)
  simp_rw [gradientTensor_matrix _ (d.gradientConstraints _).1]
  exact (dm i).continuous.mul
    ((continuous_apply b).comp ((continuous_apply a).comp (d.continuousGradient j)))

theorem continuousProjectionCost (d : MetricGreenData g μ) (o : OppositeWeylData d)
    (m : C(FrameBundle g, ℝ)) (hm : ∀ e, 0 < m e)
    (dm : Fin 4 → C(FrameBundle g, ℝ)) :
    Continuous (fun e =>
      generalCurvaturePairing (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (highestProjection (weightTensor (WithLp.toLp 2 (fun i => dm i e))
          (plusGradientTensor g e.base e.frame)))
        (highestProjection (weightTensor (WithLp.toLp 2 (fun i => dm i e))
          (plusGradientTensor g e.base e.frame))) / (24 * m e)) := by
  have hP := continuous_highestProjection.comp (d.continuousWeightTensor dm)
  exact (continuous_generalCurvaturePairing d.continuousWeyl o.continuousWeyl hP hP).div
    (continuous_const.mul m.continuous) (fun e => mul_ne_zero (by norm_num) (ne_of_gt (hm e)))

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identify the complete trace correction in the invariant local square
with the already proved metric trace Green integral. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem matrixPairing_weightTensor_trace (A : Mat) (a : Vec) (Z : Tensor) :
    matrixPairing A (hessianTrace (weightTensor a Z)) =
      ∑ i, a i * matrixPairing A (rawMatrixSlice Z.matrix i) := by
  simp only [matrixPairing, hessianTrace, weightTensor, Matrix.sum_apply,
    Finset.mul_sum, rawMatrixSlice]
  calc
    _ = ∑ b, ∑ i, ∑ c, A b c * (a i * Z.matrix b c i) := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = ∑ i, ∑ b, ∑ c, A b c * (a i * Z.matrix b c i) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      ring

theorem general_traceCorrection_weyl (A U : Mat)
    (hA : symmetric A) (htA : traceFree A) (m : ℝ) (a : Vec) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    generalTraceCorrection A U (weylLaplacian A) m (weightTensor a Z) =
      -(5 / 12 : ℝ) * (m * matrixPairing (traceCoefficient A) (weylLaplacian A) +
        ∑ i, a i * matrixPairing (traceCoefficient A) (rawMatrixSlice Z.matrix i)) := by
  have hs := weylLaplacian_symmetric A hA
  have ht := weylLaplacian_traceFree A htA
  have hL := weightTensor_matrix_bianchi a Z hz hb
  unfold generalTraceCorrection
  rw [general_traceComponent_curvaturePairing A U _ hA htA hs ht _
      (fun i j => ⟨traceComponent_symmetric _ hs ht i j,
        traceComponent_traceFree _ hs ht i j⟩) (traceComponent_divergence _ hs ht),
    general_traceComponent_curvaturePairing A U _ hA htA hs ht _ hL.1 hL.2,
    trace_traceComponent, generalTraceCurvatureBlock_weylLaplacian A hA htA]
  have hp (B : Mat) : matrixPairing ((6 : ℝ) • traceCoefficient A) B =
      6 * matrixPairing (traceCoefficient A) B := by
    simp only [matrixPairing, Matrix.smul_apply, smul_eq_mul,
      mul_assoc, ← Finset.mul_sum]
  rw [hp, hp, matrixPairing_weightTensor_trace]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem traceGreen (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hm : ∀ i t e, HasDerivAt (fun s => m ((d.flow i).map s e))
      (dm i ((d.flow i).map t e)) t) :
    (∫ e, generalTraceCorrection (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (weylLaplacian (plusWeyl g e.base e.frame)) (m e)
      (weightTensor (WithLp.toLp 2 (fun i => dm i e))
        (plusGradientTensor g e.base e.frame)) ∂μ) =
    ∫ e, m e * ((10 + (5 / 2 : ℝ) * normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2) *
        weylGradientEnergy (plusWeylGradient g e.base e.frame) -
      25 * weylMatrixEnergy (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) +
      5 * weylRadialSquare (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame)) ∂μ := by
  have h := weighted_metric_trace_scalar g d.flow m dm d.continuousWeyl
    d.continuousGradient (fun i => d.continuousHessianSlice i i)
    d.weyl.symmetric (fun e => (d.gradientConstraints e).1) hm d.derivativeWeyl
    (fun i t e => hasDerivAt_matrixVector (d.derivativeGradient i i t e))
  rw [← integral_const_mul] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with e
  simp only [plusGradientTensor]
  rw [general_traceCorrection_weyl _ _ (d.weyl.symmetric e) (d.weyl.traceFree e) _ _ _
    (gradientTensor_traceFree _ (d.gradientConstraints e).2)
    (gradientTensor_bianchi _ (d.gradientConstraints e).1 (d.gradientBianchi e)),
    metric_weyl_trace g d.weyl e]
  simp only [rawMatrixSlice_gradientTensor _ (d.gradientConstraints e).1]

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The nine commuting-quaternion products are an actual orthogonal
basis for symmetric trace-free scalar Hessians in four dimensions. -/

namespace PositiveEinsteinFour.ScalarHessian

open scoped BigOperators
open Matrix TraceHessian Angular HighestHessian

noncomputable section

abbrev Matrix4 := Geometry.Mat4

def scalarPairing (S T : Matrix4) : ℝ := ∑ a, ∑ b, S a b * T a b

def scalarNormSq (S : Matrix4) : ℝ := scalarPairing S S

/-- Coefficients of the basis `-I_i J_j`, whose squared norms are four. -/
def coefficients (S : Matrix4) : Mat := fun i j =>
  rightQuaternionCoefficients S i.succ j.succ / 2

def reconstruct (C : Mat) : Matrix4 := ∑ i, ∑ j, C i j • mixingCoefficient i j

private theorem coefficients_pairing_row_zero (S : Matrix4) (j : Fin 3) :
    coefficients S 0 j = scalarPairing (mixingCoefficient 0 j) S / 4 := by
  fin_cases j <;>
    norm_num [coefficients, rightQuaternionCoefficients, scalarPairing,
      mixingCoefficient_eq_table, coefficientTable, Fin.sum_univ_four] <;> ring

private theorem coefficients_pairing_row_one (S : Matrix4) (j : Fin 3) :
    coefficients S 1 j = scalarPairing (mixingCoefficient 1 j) S / 4 := by
  fin_cases j <;>
    norm_num [coefficients, rightQuaternionCoefficients, scalarPairing,
      mixingCoefficient_eq_table, coefficientTable, Fin.sum_univ_four] <;> ring

private theorem coefficients_pairing_row_two (S : Matrix4) (j : Fin 3) :
    coefficients S 2 j = scalarPairing (mixingCoefficient 2 j) S / 4 := by
  fin_cases j <;>
    norm_num [coefficients, rightQuaternionCoefficients, scalarPairing,
      mixingCoefficient_eq_table, coefficientTable, Fin.sum_univ_four] <;> ring

theorem coefficients_pairing (S : Matrix4) (i j : Fin 3) :
    coefficients S i j = scalarPairing (mixingCoefficient i j) S / 4 := by
  fin_cases i
  · exact coefficients_pairing_row_zero S j
  · exact coefficients_pairing_row_one S j
  · exact coefficients_pairing_row_two S j

theorem reconstruct_apply (C : Mat) (a b : Fin 4) :
    reconstruct C a b = ∑ i, ∑ j, C i j * mixingCoefficient i j a b := by
  simp only [reconstruct, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

private theorem reconstruct_entry_zero (S : Matrix4) (b : Fin 4) :
    reconstruct (coefficients S) 0 b =
      (S 0 b + S b 0) / 2 - (if (0 : Fin 4) = b then Matrix.trace S / 4 else 0) := by
  fin_cases b <;>
    norm_num [reconstruct_apply, coefficients, rightQuaternionCoefficients,
      mixingCoefficient_eq_table, coefficientTable, Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag,
      Fin.sum_univ_three, Fin.sum_univ_four] <;> ring

private theorem reconstruct_entry_one (S : Matrix4) (b : Fin 4) :
    reconstruct (coefficients S) 1 b =
      (S 1 b + S b 1) / 2 - (if (1 : Fin 4) = b then Matrix.trace S / 4 else 0) := by
  fin_cases b <;>
    norm_num [reconstruct_apply, coefficients, rightQuaternionCoefficients,
      mixingCoefficient_eq_table, coefficientTable, Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag,
      Fin.sum_univ_three, Fin.sum_univ_four] <;> ring

private theorem reconstruct_entry_two (S : Matrix4) (b : Fin 4) :
    reconstruct (coefficients S) 2 b =
      (S 2 b + S b 2) / 2 - (if (2 : Fin 4) = b then Matrix.trace S / 4 else 0) := by
  fin_cases b <;>
    norm_num [reconstruct_apply, coefficients, rightQuaternionCoefficients,
      mixingCoefficient_eq_table, coefficientTable, Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag,
      Fin.sum_univ_three, Fin.sum_univ_four] <;> ring

private theorem reconstruct_entry_three (S : Matrix4) (b : Fin 4) :
    reconstruct (coefficients S) 3 b =
      (S 3 b + S b 3) / 2 - (if (3 : Fin 4) = b then Matrix.trace S / 4 else 0) := by
  fin_cases b <;>
    norm_num [reconstruct_apply, coefficients, rightQuaternionCoefficients,
      mixingCoefficient_eq_table, coefficientTable, Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag,
      Fin.sum_univ_three, Fin.sum_univ_four] <;> ring

theorem reconstruct_entry (S : Matrix4) (a b : Fin 4) :
    reconstruct (coefficients S) a b =
      (S a b + S b a) / 2 - (if a = b then Matrix.trace S / 4 else 0) := by
  fin_cases a
  · exact reconstruct_entry_zero S b
  · exact reconstruct_entry_one S b
  · exact reconstruct_entry_two S b
  · exact reconstruct_entry_three S b

theorem reconstruct_coefficients (S : Matrix4) (hs : Sᵀ = S) (ht : Matrix.trace S = 0) :
    reconstruct (coefficients S) = S := by
  ext a b
  rw [reconstruct_entry, ht]
  have hab : S b a = S a b := congrArg (fun M : Matrix4 => M a b) hs
  rw [hab]
  split_ifs <;> ring

theorem scalarPairing_comm (S T : Matrix4) : scalarPairing S T = scalarPairing T S := by
  simp only [scalarPairing, mul_comm]

theorem scalarPairing_sum_left {ι : Type*} [Fintype ι] (f : ι → Matrix4) (T : Matrix4) :
    scalarPairing (∑ i, f i) T = ∑ i, scalarPairing (f i) T := by
  simp only [scalarPairing, Matrix.sum_apply, Finset.sum_mul]
  calc
    _ = ∑ a, ∑ i, ∑ b, f i a b * T a b := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

theorem scalarPairing_smul_left (r : ℝ) (S T : Matrix4) :
    scalarPairing (r • S) T = r * scalarPairing S T := by
  simp only [scalarPairing, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem scalarPairing_reconstruct (C : Mat) (S : Matrix4) :
    scalarPairing (reconstruct C) S = 4 * ∑ i, ∑ j, C i j * coefficients S i j := by
  simp only [reconstruct, scalarPairing_sum_left, scalarPairing_smul_left, coefficients_pairing,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Parseval's identity in the nine actual quaternion product directions. -/
theorem scalarPairing_coefficients (S T : Matrix4)
    (hs : Sᵀ = S) (ht : Matrix.trace S = 0) :
    scalarPairing S T = 4 * ∑ i, ∑ j, coefficients S i j * coefficients T i j := by
  conv_lhs => rw [← reconstruct_coefficients S hs ht]
  exact scalarPairing_reconstruct _ _

theorem scalarNormSq_coefficients (S : Matrix4) (hs : Sᵀ = S) (ht : Matrix.trace S = 0) :
    scalarNormSq S = 4 * ∑ i, ∑ j, coefficients S i j ^ 2 := by
  simpa only [scalarNormSq, pow_two] using scalarPairing_coefficients S S hs ht

theorem scalarNormSq_nonneg (S : Matrix4) : 0 ≤ scalarNormSq S := by
  unfold scalarNormSq scalarPairing
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => mul_self_nonneg (S a b)

end
end PositiveEinsteinFour.ScalarHessian
end


section

/-! The scalar norm bounds forced by shifted positive semidefiniteness. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian HighestHessian PositiveEinsteinFour.Geometry

noncomputable section

/-- A trace-free block bounded below by `-x` has normalized norm at most
`x`; the zero block is included. -/
theorem normalizedBlockNorm_le_shift (A : Mat) (hs : symmetric A) (ht : traceFree A)
    (x : ℝ) (hAx : (A + x • (1 : Mat)).PosSemidef) :
    normalizedBlockNorm A ≤ x := by
  by_cases hv : normalizedBlockNorm A = 0
  · rw [hv]
    exact shift_nonneg_of_traceFree A ht x hAx
  have hvp : 0 < normalizedBlockNorm A :=
    lt_of_le_of_ne (normalizedBlockNorm_nonneg A) (Ne.symm hv)
  obtain ⟨R, hR, _, S, hS⟩ := exists_lifted_spectral_shape A hs ht hvp
  obtain ⟨r, hr, _, _, _, hmin⟩ := shape_exists_minimum_parameter S
  have hbound := shape_minimum_parameter_bound A R hR S (normalizedBlockNorm A) x r hS hAx hmin
  have hprod : 0 ≤ normalizedBlockNorm A * (r - 1) :=
    mul_nonneg hvp.le (sub_nonneg.mpr hr)
  nlinarith only [hbound, hprod]

/-- The shifted curvature domain implies the full closed scalar norm
triangle, without excluding zeros of either block. -/
theorem normalizedBlockNorm_sum_le_two (A U : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (x y : ℝ) (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2) :
    normalizedBlockNorm A + normalizedBlockNorm U ≤ 2 := by
  have ha := normalizedBlockNorm_le_shift A hA htA x hAx
  have hu := normalizedBlockNorm_le_shift U hU htU y hUy
  linarith only [ha, hu, hxy]

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! All five Green integrals for the actual Weyl Hessian. The result has
only first derivatives and the constructed orthogonal-projection cost. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian CurvatureContraction MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance hessianAssemblyNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance hessianAssemblyNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance hessianAssemblyNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

def invariantHessianForm (A U : Mat) (Z : Fin 4 → Mat) : ℝ :=
  (-42 - 3 * normalizedBlockNorm U ^ 2 - (10 / 3 : ℝ) * normalizedBlockNorm A ^ 2) *
      weylGradientEnergy Z +
    75 * weylMatrixEnergy A Z + (25 / 3 : ℝ) * weylMatrixEnergy (traceFreeSquare A) Z -
    (100 / 3 : ℝ) * weylCompressionEnergy A Z + 5 * weylRadialSquare A Z

theorem invariant_green_polynomial_identity (m v b e B C E R c k : ℝ) :
    m * ((-42 - 3 * b ^ 2 - (10 / 3 : ℝ) * v ^ 2) * e +
      75 * B + (25 / 3 : ℝ) * C - (100 / 3 : ℝ) * E + 5 * R) -
        (5 / 36 : ℝ) * c + k =
      4 * (m * (-13 * e + 20 * B)) -
        (5 / 6 : ℝ) * (m * (7 * v ^ 2 * e - 4 * B - 4 * C)) -
        (5 / 3 : ℝ) * (m * (-10 * B - 3 * C + 20 * E) + c / 12) -
        m * (3 * b ^ 2 * e) + m * ((10 + (5 / 2 : ℝ) * v ^ 2) * e - 25 * B + 5 * R) + k := by
  ring

theorem general_weightedQuadratic_original (A U : Mat) (m : ℝ) (X L : Hessian) :
    weightedQuadratic (generalOriginalCurvatureForm A U) m X L =
      4 * weightedQuadratic hessianNormSq m X L -
        (5 / 6 : ℝ) * weightedQuadratic
          (fun W => derivativePairing (generalCoefficient quaternionMatrix A) W W) m X L -
        (5 / 3 : ℝ) * weightedQuadratic
          (fun W => matrixHessianPairing A W W) m X L -
        weightedQuadratic
          (fun W => derivativePairing (generalCoefficient Angular.oppositeMatrix U) W W) m X L := by
  unfold weightedQuadratic generalOriginalCurvatureForm
  ring

section Integral

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

local instance : NormedAddCommGroup C(Ω, ℝ) := ContinuousMap.instNormedAddCommGroup
local instance : NormedSpace ℝ C(Ω, ℝ) := ContinuousMap.normedSpace

private def hessianIntegral : C(Ω, ℝ) →L[ℝ] ℝ :=
  (L1.integralCLM (μ := μ)).comp (ContinuousMap.toLp 1 μ ℝ)

private theorem hessianIntegral_apply (f : C(Ω, ℝ)) :
    hessianIntegral μ f = ∫ x, f x ∂μ := by
  change L1.integralCLM (ContinuousMap.toLp 1 μ ℝ f) = _
  rw [← L1.integral_eq, L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 1) μ f)

private theorem hessianIntegral_combination (I T F U D K : C(Ω, ℝ)) :
    (∫ x, 4 * I x - (5 / 6 : ℝ) * T x - (5 / 3 : ℝ) * F x - U x + D x + K x ∂μ) =
      4 * (∫ x, I x ∂μ) - (5 / 6 : ℝ) * (∫ x, T x ∂μ) -
        (5 / 3 : ℝ) * (∫ x, F x ∂μ) - (∫ x, U x ∂μ) +
        (∫ x, D x ∂μ) + (∫ x, K x ∂μ) := by
  change (∫ x, (((4 : ℝ) • I - (5 / 6 : ℝ) • T - (5 / 3 : ℝ) • F - U + D + K) x) ∂μ) = _
  rw [← hessianIntegral_apply]
  simp only [map_add, map_sub, map_smul, smul_eq_mul, hessianIntegral_apply]

end Integral

section Continuous

variable {Ω : Type*} [TopologicalSpace Ω]

theorem continuous_generalCoefficient (Q : Fin 3 → Mat4) {A : Ω → Mat}
    (hA : Continuous A) : Continuous (fun x => generalCoefficient Q (A x)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro k
  apply continuous_pi
  intro j
  apply continuous_pi
  intro l
  exact (generalCoefficientMap Q i k j l).continuous.comp hA

theorem continuous_weylLaplacian : Continuous weylLaplacian := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [weylLaplacian, traceFreeSquare, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.mul_apply, Matrix.trace, Matrix.diag, smul_eq_mul]
  fun_prop

theorem continuous_traceComponent : Continuous traceComponent := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  by_cases hij : i = j
  · simp only [traceComponent, traceLift, matrixAction, Matrix.smul_apply, smul_eq_mul,
      hij, ite_true]
    fun_prop
  · simp only [traceComponent, traceLift, matrixAction, Matrix.smul_apply, smul_eq_mul,
      hij, ite_false]
    fun_prop

theorem continuous_traceFreeSquare : Continuous traceFreeSquare := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [traceFreeSquare, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.smul_apply, Matrix.trace, Matrix.diag, smul_eq_mul]
  fun_prop

end Continuous

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

def plusMatrixMap (d : MetricGreenData g μ) : C(FrameBundle g, Mat) :=
  ⟨fun e => plusWeyl g e.base e.frame, d.continuousWeyl⟩

def minusMatrixMap (d : MetricGreenData g μ) (o : OppositeWeylData d) : C(FrameBundle g, Mat) :=
  ⟨fun e => minusWeyl g e.base e.frame, o.continuousWeyl⟩

def gradientMap (d : MetricGreenData g μ) : C(FrameBundle g, Fin 4 → Mat) :=
  ⟨fun e => plusWeylGradient g e.base e.frame, continuous_pi d.continuousGradient⟩

def hessianMap (d : MetricGreenData g μ) : C(FrameBundle g, Hessian) :=
  ⟨fun e => plusWeylHessian g e.base e.frame, d.continuousFullHessian⟩

def weightTensorMap (d : MetricGreenData g μ) (dm : Fin 4 → C(FrameBundle g, ℝ)) :
    C(FrameBundle g, Hessian) :=
  ⟨fun e => weightTensor (WithLp.toLp 2 (fun i => dm i e)) (plusGradientTensor g e.base e.frame),
    d.continuousWeightTensor dm⟩

def hessianIdentityField (d : MetricGreenData g μ) (m : C(FrameBundle g, ℝ))
    (dm : Fin 4 → C(FrameBundle g, ℝ)) : C(FrameBundle g, ℝ) :=
  ⟨fun e => weightedQuadratic hessianNormSq (m e) (d.hessianMap e) (d.weightTensorMap dm e),
    continuous_weightedQuadratic (fun W hW => by
      simpa only [hessianPairing_self] using continuous_hessianPairing hW hW)
      m.continuous (d.hessianMap.continuous) (d.weightTensorMap dm).continuous⟩

def hessianPlusField (d : MetricGreenData g μ) (m : C(FrameBundle g, ℝ))
    (dm : Fin 4 → C(FrameBundle g, ℝ)) : C(FrameBundle g, ℝ) :=
  ⟨fun e => weightedQuadratic
    (fun W => derivativePairing (generalCoefficient quaternionMatrix (d.plusMatrixMap e)) W W)
    (m e) (d.hessianMap e) (d.weightTensorMap dm e),
    continuous_weightedQuadratic
      (q := fun e W => derivativePairing (generalCoefficient quaternionMatrix (d.plusMatrixMap e)) W W)
      (m := m) (X := d.hessianMap) (L := d.weightTensorMap dm)
      (fun W hW => continuous_derivativePairing (X := W) (Y := W)
        (continuous_generalCoefficient quaternionMatrix d.plusMatrixMap.continuous) hW hW)
      m.continuous d.hessianMap.continuous (d.weightTensorMap dm).continuous⟩

def hessianMatrixField (d : MetricGreenData g μ) (m : C(FrameBundle g, ℝ))
    (dm : Fin 4 → C(FrameBundle g, ℝ)) : C(FrameBundle g, ℝ) :=
  ⟨fun e => weightedQuadratic (fun W => matrixHessianPairing (d.plusMatrixMap e) W W)
    (m e) (d.hessianMap e) (d.weightTensorMap dm e),
    continuous_weightedQuadratic
      (q := fun e W => matrixHessianPairing (d.plusMatrixMap e) W W)
      (m := m) (X := d.hessianMap) (L := d.weightTensorMap dm)
      (fun W hW => continuous_matrixHessianPairing (X := W) (Y := W)
        d.plusMatrixMap.continuous hW hW)
      m.continuous d.hessianMap.continuous (d.weightTensorMap dm).continuous⟩

def hessianMinusField (d : MetricGreenData g μ) (o : OppositeWeylData d)
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ)) : C(FrameBundle g, ℝ) :=
  ⟨fun e => weightedQuadratic
    (fun W => derivativePairing (generalCoefficient Angular.oppositeMatrix (d.minusMatrixMap o e)) W W)
    (m e) (d.hessianMap e) (d.weightTensorMap dm e),
    continuous_weightedQuadratic
      (q := fun e W => derivativePairing (generalCoefficient Angular.oppositeMatrix (d.minusMatrixMap o e)) W W)
      (m := m) (X := d.hessianMap) (L := d.weightTensorMap dm)
      (fun W hW => continuous_derivativePairing (X := W) (Y := W)
        (continuous_generalCoefficient Angular.oppositeMatrix (d.minusMatrixMap o).continuous) hW hW)
      m.continuous d.hessianMap.continuous (d.weightTensorMap dm).continuous⟩

def traceComponentMap (d : MetricGreenData g μ) : C(FrameBundle g, Hessian) :=
  ⟨fun e => traceComponent (weylLaplacian (d.plusMatrixMap e)),
    continuous_traceComponent.comp (continuous_weylLaplacian.comp d.plusMatrixMap.continuous)⟩

def hessianTraceField (d : MetricGreenData g μ) (o : OppositeWeylData d)
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ)) : C(FrameBundle g, ℝ) :=
  ⟨fun e => generalTraceCorrection (d.plusMatrixMap e) (d.minusMatrixMap o e)
    (weylLaplacian (d.plusMatrixMap e)) (m e) (d.weightTensorMap dm e),
    (((m.continuous.mul (continuous_generalCurvaturePairing d.plusMatrixMap.continuous
      (d.minusMatrixMap o).continuous d.traceComponentMap.continuous d.traceComponentMap.continuous)).add
      (continuous_generalCurvaturePairing d.plusMatrixMap.continuous (d.minusMatrixMap o).continuous
        d.traceComponentMap.continuous (d.weightTensorMap dm).continuous)).neg).div_const 6⟩

def hessianCostField (d : MetricGreenData g μ) (o : OppositeWeylData d)
    (m : C(FrameBundle g, ℝ)) (hm : ∀ e, 0 < m e) (dm : Fin 4 → C(FrameBundle g, ℝ)) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => generalCurvaturePairing (d.plusMatrixMap e) (d.minusMatrixMap o e)
      (highestProjection (d.weightTensorMap dm e)) (highestProjection (d.weightTensorMap dm e)) /
        (24 * m e), d.continuousProjectionCost o m hm dm⟩

def gradientEnergyField (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => weylGradientEnergy (d.gradientMap e), continuous_weylGradientEnergy d.gradientMap.continuous⟩

def matrixEnergyField (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => weylMatrixEnergy (d.plusMatrixMap e) (d.gradientMap e),
    continuous_weylMatrixEnergy d.plusMatrixMap.continuous d.gradientMap.continuous⟩

def squareEnergyField (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => weylMatrixEnergy (traceFreeSquare (d.plusMatrixMap e)) (d.gradientMap e),
    continuous_weylMatrixEnergy (continuous_traceFreeSquare.comp d.plusMatrixMap.continuous)
      d.gradientMap.continuous⟩

def compressionEnergyField (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => weylCompressionEnergy (d.plusMatrixMap e) (d.gradientMap e),
    continuous_weylCompressionEnergy d.plusMatrixMap.continuous d.gradientMap.continuous
      (fun e => (d.gradientConstraints e).1)⟩

def radialEnergyField (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => weylRadialSquare (d.plusMatrixMap e) (d.gradientMap e),
    continuous_weylRadialSquare d.plusMatrixMap.continuous d.gradientMap.continuous⟩

def plusNormField (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => normalizedBlockNorm (d.plusMatrixMap e),
    continuous_normalizedBlockNorm.comp d.plusMatrixMap.continuous⟩

def minusNormField (d : MetricGreenData g μ) (o : OppositeWeylData d) : C(FrameBundle g, ℝ) :=
  ⟨fun e => normalizedBlockNorm (d.minusMatrixMap o e),
    continuous_normalizedBlockNorm.comp (d.minusMatrixMap o).continuous⟩

def weightCubicField (d : MetricGreenData g μ) (dm : Fin 4 → C(FrameBundle g, ℝ)) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => ∑ i, dm i e * Matrix.trace (d.gradientMap e i *
    (∑ j, d.gradientMap e j * d.gradientMap e j)), by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.sum_apply]
      fun_prop⟩

/-- The weighted Hessian estimate with every Green contribution evaluated
on the actual metric tensors. The geometric shifted-positivity condition
is kept separate; no new integral estimate is an input. -/
theorem weightedHessianGreen (d : MetricGreenData g μ) (o : OppositeWeylData d)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (m : C(FrameBundle g, ℝ)) (hmpos : ∀ e, 0 < m e)
    (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hm : ∀ i t e, HasDerivAt (fun s => m ((d.flow i).map s e))
      (dm i ((d.flow i).map t e)) t) :
    0 ≤ ∫ e, m e * invariantHessianForm (plusWeyl g e.base e.frame)
        (minusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) -
      (5 / 36 : ℝ) * (∑ i, dm i e * Matrix.trace (plusWeylGradient g e.base e.frame i *
        (∑ j, plusWeylGradient g e.base e.frame j * plusWeylGradient g e.base e.frame j))) +
      generalCurvaturePairing (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (highestProjection (weightTensor (WithLp.toLp 2 (fun i => dm i e))
          (plusGradientTensor g e.base e.frame)))
        (highestProjection (weightTensor (WithLp.toLp 2 (fun i => dm i e))
          (plusGradientTensor g e.base e.frame))) / (24 * m e) ∂μ := by
  let A := fun e : FrameBundle g => plusWeyl g e.base e.frame
  let U := fun e : FrameBundle g => minusWeyl g e.base e.frame
  let Z := fun e : FrameBundle g => plusWeylGradient g e.base e.frame
  let I := d.hessianIdentityField m dm
  let T := d.hessianPlusField m dm
  let F := d.hessianMatrixField m dm
  let V := d.hessianMinusField o m dm
  let D := d.hessianTraceField o m dm
  let K := d.hessianCostField o m hmpos dm
  let E := d.gradientEnergyField
  let B := d.matrixEnergyField
  let C := d.squareEnergyField
  let P := d.compressionEnergyField
  let R := d.radialEnergyField
  let v := d.plusNormField
  let b := d.minusNormField o
  let cubic := d.weightCubicField dm
  let RI : C(FrameBundle g, ℝ) := ⟨fun e => m e * (-13 * E e + 20 * B e), by fun_prop⟩
  let RT : C(FrameBundle g, ℝ) := ⟨fun e => m e * (7 * v e ^ 2 * E e - 4 * B e - 4 * C e), by fun_prop⟩
  let RF : C(FrameBundle g, ℝ) := ⟨fun e => m e * (-10 * B e - 3 * C e + 20 * P e) + cubic e / 12, by fun_prop⟩
  let RV : C(FrameBundle g, ℝ) := ⟨fun e => m e * (3 * b e ^ 2 * E e), by fun_prop⟩
  let RD : C(FrameBundle g, ℝ) := ⟨fun e => m e * ((10 + (5 / 2 : ℝ) * v e ^ 2) * E e -
    25 * B e + 5 * R e), by fun_prop⟩
  have hI : (∫ e, I e ∂μ) = ∫ e, RI e ∂μ := d.identityGreen m dm hm
  have hT : (∫ e, T e ∂μ) = ∫ e, RT e ∂μ := d.plusCurvatureGreen hdecomp m dm hm
  have hF : (∫ e, F e ∂μ) = ∫ e, RF e ∂μ := d.matrixGreen m dm hm
  have hV : (∫ e, V e ∂μ) = ∫ e, RV e ∂μ := d.minusCurvatureGreen o hdecomp m dm hm
  have hD : (∫ e, D e ∂μ) = ∫ e, RD e ∂μ := d.traceGreen m dm hm
  have hn : 0 ≤ ∫ e, 4 * I e - (5 / 6 : ℝ) * T e - (5 / 3 : ℝ) * F e - V e + D e + K e ∂μ := by
    apply integral_nonneg
    intro e
    change (0 : ℝ) ≤ 4 * I e - (5 / 6 : ℝ) * T e - (5 / 3 : ℝ) * F e - V e + D e + K e
    have hh := d.localWeightedHessian o hp e (m e) (hmpos e) (WithLp.toLp 2 (fun i => dm i e))
    simpa only [general_weightedQuadratic_original, I, T, F, V, D, K,
      hessianIdentityField, hessianPlusField, hessianMatrixField, hessianMinusField,
      hessianTraceField, hessianCostField, plusMatrixMap, minusMatrixMap, hessianMap,
      weightTensorMap, ContinuousMap.coe_mk] using hh
  rw [hessianIntegral_combination, hI, hT, hF, hV, hD,
    ← hessianIntegral_combination μ RI RT RF RV RD K] at hn
  convert hn using 1
  apply integral_congr_ae
  filter_upwards [] with e
  change m e * invariantHessianForm (A e) (U e) (Z e) - (5 / 36 : ℝ) * cubic e + K e = _
  exact invariant_green_polynomial_identity (m e) (v e) (b e) (E e) (B e) (C e)
    (P e) (R e) (cubic e) (K e)

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual projection cost is a four-by-four quadratic form in the
weight derivative. This finite expansion is used for its integral limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

def derivativeBasis (i : Fin 4) : Vec := WithLp.toLp 2 (fun j => if j = i then 1 else 0)

def highestProjectionMap : Hessian →L[ℝ] Hessian :=
  vectorHessianMap.comp (highestSubspace.starProjection.comp hessianVectorMap)

theorem highestProjectionMap_apply (X : Hessian) : highestProjectionMap X = highestProjection X := rfl

theorem weightTensor_basis_sum (a : Vec) (Z : Tensor) :
    weightTensor a Z = ∑ i, a i • weightTensor (derivativeBasis i) Z := by
  ext j k b c
  simp [Finset.sum_apply, Matrix.sum_apply, Matrix.smul_apply,
    weightTensor, derivativeBasis]

def projectedWeightKernel (A U : Mat) (Z : Tensor) (i j : Fin 4) : ℝ :=
  generalCurvaturePairing A U
    (highestProjection (weightTensor (derivativeBasis i) Z))
    (highestProjection (weightTensor (derivativeBasis j) Z)) / 24

theorem projection_weight_cost_expansion (A U : Mat) (Z : Tensor) (a : Vec) (m : ℝ) :
    generalCurvaturePairing A U (highestProjection (weightTensor a Z))
      (highestProjection (weightTensor a Z)) / (24 * m) =
        ∑ i, ∑ j, (a i * a j / m) * projectedWeightKernel A U Z i j := by
  have hP : highestProjection (weightTensor a Z) =
      ∑ i, a i • highestProjection (weightTensor (derivativeBasis i) Z) := by
    change highestProjectionMap (weightTensor a Z) = _
    rw [weightTensor_basis_sum, map_sum]
    simp only [map_smul, highestProjectionMap_apply]
  rw [hP]
  simp only [Fin.sum_univ_four, generalCurvaturePairing_add_left,
    generalCurvaturePairing_add_right, generalCurvaturePairing_smul_left,
    generalCurvaturePairing_smul_right, projectedWeightKernel]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem MetricGreenData.continuousProjectedWeightKernel
    {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (d : MetricGreenData g μ) (o : OppositeWeylData d) (i j : Fin 4) :
    Continuous (fun e : FrameBundle g => projectedWeightKernel
      (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (plusGradientTensor g e.base e.frame) i j) := by
  have h (k : Fin 4) : Continuous (fun e : FrameBundle g =>
      highestProjection (weightTensor (derivativeBasis k) (plusGradientTensor g e.base e.frame))) := by
    exact continuous_highestProjection.comp
      (d.continuousWeightTensor (fun l => ContinuousMap.const _ (if l = k then 1 else 0)))
  exact (continuous_generalCurvaturePairing d.continuousWeyl o.continuousWeyl (h i) (h j)).div_const 24

end
end PositiveEinsteinFour.Geometry
end


section

/-! The pointwise sectional curvature criterion.

Gursky--LeBrun, `On Einstein Manifolds of Positive Sectional Curvature`
(1999), Lemma 1 proof, equation (5), pp.4--5, arXiv:math/9807055.
For Einstein curvature the minimum sectional curvature is half of
`s/6 + lambda_plus + lambda_minus`. At Ric=3g, strict positivity says
the negatives of the two minimum eigenvalues have sum less than two.
The positive-semidefinite formulation below is that local specialization.
 -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def RicciThree (g : SmoothMetric M) : Prop :=
  ∀ c : M, chartRicci g c = (3 : ℝ) • chartMetric g c

/-- Equation (5) in the proof of the published Lemma 1, with strict
sectional positivity and scalar curvature twelve. -/
def GurskyLeBrunSectionalInput (g : SmoothMetric M) : Prop :=
  RicciThree g → HasPositiveSectionalCurvature g →
    ∀ e : FrameBundle g, ∃ x y : ℝ,
      (plusWeyl g e.base e.frame + x • (1 : Mat)).PosSemidef ∧
      (minusWeyl g e.base e.frame + y • (1 : Mat)).PosSemidef ∧ x + y < 2

variable {g : SmoothMetric M} {μ : MeasureTheory.Measure (FrameBundle g)}

theorem shiftedCurvaturePositive_of_published
    (h : GurskyLeBrunSectionalInput g) (hRic : RicciThree g)
    (hsec : HasPositiveSectionalCurvature g) : ShiftedCurvaturePositive g := by
  intro e
  obtain ⟨x, y, hx, hy, hxy⟩ := h hRic hsec e
  exact ⟨x, y, hx, hy, hxy.le⟩

theorem strict_norm_pinching_of_published (d : MetricGreenData g μ)
    (o : OppositeWeylData d) (h : GurskyLeBrunSectionalInput g)
    (hRic : RicciThree g) (hsec : HasPositiveSectionalCurvature g) (e : FrameBundle g) :
    normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2 := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h hRic hsec e
  have hp := QuaternionFrame.normalizedBlockNorm_le_shift _ (d.weyl.symmetric e)
    (d.weyl.traceFree e) x hx
  have hm := QuaternionFrame.normalizedBlockNorm_le_shift _ (o.symmetric e)
    (o.traceFree e) y hy
  linarith only [hp, hm, hxy]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual scalar-Hessian Weyl operators, on the nine quaternion-product
coordinates. Only the algebra needed by the weighted variance is used. -/

namespace PositiveEinsteinFour.ScalarHessian

open scoped BigOperators
open Matrix TraceHessian Angular HighestHessian CurvatureContraction

noncomputable section

def blockActionLinear (Q : Fin 3 → Matrix4) (A : Mat) : Matrix4 →ₗ[ℝ] Matrix4 where
  toFun S := -(1 / 2 : ℝ) • ∑ r, ∑ s, A r s • (Q r * S * Q s)
  map_add' S T := by
    simp only [Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib]
  map_smul' c S := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
    calc
      _ = -(1 / 2 : ℝ) • ∑ r, ∑ s, c • (A r s • (Q r * S * Q s)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro s _
        exact smul_comm _ _ _
      _ = _ := by
        simp only [← Finset.smul_sum]
        exact smul_comm _ _ _

def blockAction (Q : Fin 3 → Matrix4) (A : Mat) (S : Matrix4) : Matrix4 :=
  blockActionLinear Q A S

theorem clifford_triple (Q : Fin 3 → Matrix4)
    (hQ : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Matrix4)) (r i s : Fin 3) :
    Q r * Q i * Q s + Q s * Q i * Q r =
      (2 : ℝ) • ((if r = s then Q i else 0) -
        (if r = i then Q s else 0) - (if i = s then Q r else 0)) := by
  calc
    _ = (Q r * Q i + Q i * Q r) * Q s -
        Q i * (Q r * Q s + Q s * Q r) +
        (Q i * Q s + Q s * Q i) * Q r := by noncomm_ring
    _ = _ := by
      rw [hQ, hQ, hQ]
      split_ifs <;>
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
          zero_smul, zero_mul, mul_zero]
      all_goals module

private theorem folded_clifford_triple (Q : Fin 3 → Matrix4) (A : Mat) (i : Fin 3) :
    (∑ r, ∑ s, A r s • ((if r = s then Q i else 0) -
      (if r = i then Q s else 0) - (if i = s then Q r else 0))) =
      Matrix.trace A • Q i - (∑ s, A i s • Q s) - ∑ r, A r i • Q r := by
  fin_cases i <;> ext a b <;>
    simp [Fin.sum_univ_three, Matrix.trace, Matrix.diag, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul] <;> ring

theorem weighted_clifford_sandwich (Q : Fin 3 → Matrix4)
    (hQ : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Matrix4))
    (A : Mat) (hs : symmetric A) (ht : traceFree A) (i : Fin 3) :
    (∑ r, ∑ s, A r s • (Q r * Q i * Q s)) =
      (-2 : ℝ) • ∑ r, A r i • Q r := by
  let G : Matrix4 := ∑ r, ∑ s, A r s • (Q r * Q i * Q s)
  have hrev : G = ∑ r, ∑ s, A r s • (Q s * Q i * Q r) := by
    dsimp only [G]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro r _
    rw [hs s r]
  have hadd : G + G =
      (2 : ℝ) • (Matrix.trace A • Q i - (∑ s, A i s • Q s) - ∑ r, A r i • Q r) := by
    conv_lhs => rhs; rw [hrev]
    dsimp only [G]
    rw [← Finset.sum_add_distrib]
    simp only [← Finset.sum_add_distrib, ← smul_add, clifford_triple Q hQ]
    simp only [smul_comm _ (2 : ℝ), ← Finset.smul_sum]
    rw [folded_clifford_triple]
  have hrow : (∑ s, A i s • Q s) = ∑ r, A r i • Q r := by
    apply Finset.sum_congr rfl
    intro r _
    rw [hs i r]
  have htrace : Matrix.trace A = 0 := ht
  rw [hrow, htrace, zero_smul] at hadd
  change G = _
  apply (smul_right_injective (R := ℝ) (M := Matrix4) (by norm_num : (2 : ℝ) ≠ 0))
  calc
    (2 : ℝ) • G = G + G := by module
    _ = (2 : ℝ) • (0 - (∑ r, A r i • Q r) - ∑ r, A r i • Q r) := hadd
    _ = _ := by module

private theorem blockAction_product (Q P : Fin 3 → Matrix4)
    (hQ : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Matrix4))
    (hcomm : ∀ r s, P r * Q s = Q s * P r)
    (A : Mat) (hs : symmetric A) (ht : traceFree A) (i j : Fin 3) :
    blockAction Q A (-(Q i * P j)) = ∑ r, A r i • (-(Q r * P j)) := by
  have hterm (r s : Fin 3) : Q r * (-(Q i * P j)) * Q s = -(Q r * Q i * Q s) * P j := by
    calc
      _ = -(Q r * Q i * (P j * Q s)) := by noncomm_ring
      _ = _ := by rw [hcomm]; noncomm_ring
  unfold blockAction blockActionLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, hterm]
  have hid : (∑ r, ∑ s, A r s • (-(Q r * Q i * Q s) * P j)) =
      -(∑ r, ∑ s, A r s • (Q r * Q i * Q s)) * P j := by
    simp only [Matrix.sum_mul, Matrix.smul_mul, neg_mul, smul_neg,
      Finset.sum_neg_distrib]
  rw [hid, weighted_clifford_sandwich Q hQ A hs ht i]
  have hscalar : -((-2 : ℝ) • (∑ r, A r i • Q r)) =
      (2 : ℝ) • (∑ r, A r i • Q r) := by module
  rw [hscalar, Matrix.smul_mul, smul_smul]
  norm_num
  simp only [Matrix.sum_mul, Matrix.smul_mul]

theorem plusAction_basis (A : Mat) (hs : symmetric A) (ht : traceFree A) (i j : Fin 3) :
    blockAction quaternionMatrix A (mixingCoefficient i j) =
      ∑ r, A r i • mixingCoefficient r j := by
  simpa only [mixingCoefficient, quaternionMatrix_transpose, Matrix.neg_mul] using
    blockAction_product quaternionMatrix oppositeMatrix quaternionMatrix_anticommutator
      oppositeMatrix_commute A hs ht i j

theorem minusAction_basis (U : Mat) (hs : symmetric U) (ht : traceFree U) (i j : Fin 3) :
    blockAction oppositeMatrix U (mixingCoefficient i j) =
      ∑ s, U s j • mixingCoefficient i s := by
  have hc (r s : Fin 3) : quaternionMatrix r * oppositeMatrix s =
      oppositeMatrix s * quaternionMatrix r := (oppositeMatrix_commute s r).symm
  have h := blockAction_product oppositeMatrix quaternionMatrix oppositeMatrix_anticommutator
    hc U hs ht j i
  simpa only [mixingCoefficient, quaternionMatrix_transpose, Matrix.neg_mul,
    oppositeMatrix_commute] using h

theorem blockAction_reconstruct (Q : Fin 3 → Matrix4) (A C : Mat) :
    blockAction Q A (reconstruct C) =
      ∑ i, ∑ j, C i j • blockAction Q A (mixingCoefficient i j) := by
  simp only [reconstruct, blockAction, map_sum, map_smul]

theorem basis_pairing (S : Matrix4) (i j : Fin 3) :
    scalarPairing (mixingCoefficient i j) S = 4 * coefficients S i j := by
  rw [coefficients_pairing]
  ring

/-- The plus operator is the ordinary coefficient-matrix quadratic form
on the columns of the nine-product expansion. -/
theorem plusAction_pairing (A : Mat) (hA : symmetric A) (htA : traceFree A)
    (S : Matrix4) (hS : Sᵀ = S) (htS : Matrix.trace S = 0) :
    scalarPairing (blockAction quaternionMatrix A S) S =
      4 * ∑ j, ∑ r, ∑ s, A r s * coefficients S r j * coefficients S s j := by
  have haction : blockAction quaternionMatrix A S =
      ∑ i, ∑ j, coefficients S i j • (∑ r, A r i • mixingCoefficient r j) := by
    calc
      _ = blockAction quaternionMatrix A (reconstruct (coefficients S)) := by
        rw [reconstruct_coefficients S hS htS]
      _ = _ := by rw [blockAction_reconstruct]; simp_rw [plusAction_basis A hA htA]
  rw [haction]
  simp only [scalarPairing_sum_left, scalarPairing_smul_left, basis_pairing]
  simp only [Fin.sum_univ_three]
  ring

/-- The minus operator acts on the rows of the same expansion. -/
theorem minusAction_pairing (U : Mat) (hU : symmetric U) (htU : traceFree U)
    (S : Matrix4) (hS : Sᵀ = S) (htS : Matrix.trace S = 0) :
    scalarPairing (blockAction oppositeMatrix U S) S =
      4 * ∑ i, ∑ r, ∑ s, U r s * coefficients S i r * coefficients S i s := by
  have haction : blockAction oppositeMatrix U S =
      ∑ i, ∑ j, coefficients S i j • (∑ s, U s j • mixingCoefficient i s) := by
    calc
      _ = blockAction oppositeMatrix U (reconstruct (coefficients S)) := by
        rw [reconstruct_coefficients S hS htS]
      _ = _ := by rw [blockAction_reconstruct]; simp_rw [minusAction_basis U hU htU]
  rw [haction]
  simp only [scalarPairing_sum_left, scalarPairing_smul_left, basis_pairing]
  simp only [Fin.sum_univ_three]
  ring

end
end PositiveEinsteinFour.ScalarHessian
end


section

/-! The scalar-Hessian curvature contraction in the weighted-variance
argument, with the actual Einstein curvature tensor and arbitrary
symmetric trace-free Weyl matrices. -/

namespace PositiveEinsteinFour.ScalarHessian

open scoped BigOperators
open Matrix TraceHessian Bianchi Angular CurvatureContraction
open PositiveEinsteinFour.Geometry

noncomputable section

def scalarCurvatureContraction (A U : Mat) (p : Vec) : ℝ :=
  ∑ l, ∑ h, ((1 / 2 : ℝ) * (∑ j, ∑ i, ∑ k,
    (generalCoefficient quaternionMatrix A i k j l +
      generalCoefficient oppositeMatrix U i k j l) *
      generalEinsteinCoefficient A U i k j h)) * p h * p l

private theorem sum_five_permute (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ i, ∑ k, ∑ j, ∑ l, ∑ h, f i k j l h) =
      ∑ l, ∑ h, ∑ j, ∑ i, ∑ k, f i k j l h := by
  let e : (((Fin 4 × Fin 4) × (Fin 4 × Fin 4)) × Fin 4) ≃
      ((Fin 4 × Fin 4) × (Fin 4 × (Fin 4 × Fin 4))) :=
    { toFun := fun x => ((x.1.2.2, x.2), (x.1.2.1, (x.1.1.1, x.1.1.2)))
      invFun := fun y => (((y.2.2.1, y.2.2.2), (y.2.1, y.1.1)), y.1.2)
      left_inv := by rintro ⟨⟨⟨i, k⟩, ⟨j, l⟩⟩, h⟩; rfl
      right_inv := by rintro ⟨⟨l, h⟩, ⟨j, ⟨i, k⟩⟩⟩; rfl }
  have he := e.sum_comp (fun y => f y.2.2.1 y.2.2.2 y.2.1 y.1.1 y.1.2)
  change (∑ x : ((Fin 4 × Fin 4) × (Fin 4 × Fin 4)) × Fin 4,
      f x.1.1.1 x.1.1.2 x.1.2.1 x.1.2.2 x.2) =
    ∑ y : (Fin 4 × Fin 4) × (Fin 4 × (Fin 4 × Fin 4)),
      f y.2.2.1 y.2.2.2 y.2.1 y.1.1 y.1.2 at he
  simpa only [Fintype.sum_prod_type] using he

/-- The curvature term in the tuple-indexed Green identity is exactly the
contraction above; this is only reindexing, with no tensor hypothesis. -/
theorem scalarCurvatureContraction_tuple (A U : Mat) (p : Vec) :
    (1 / 2 : ℝ) * ∑ q : (Fin 4 × Fin 4) × (Fin 4 × Fin 4),
      (generalCoefficient quaternionMatrix A q.1.1 q.1.2 q.2.1 q.2.2 +
        generalCoefficient oppositeMatrix U q.1.1 q.1.2 q.2.1 q.2.2) *
        (∑ h, generalEinsteinCoefficient A U q.1.1 q.1.2 q.2.1 h * p h) * p q.2.2 =
      scalarCurvatureContraction A U p := by
  unfold scalarCurvatureContraction
  simp only [Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact sum_five_permute _

theorem scalarCurvatureContraction_eq (A U : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (p : Vec) :
    scalarCurvatureContraction A U p =
      3 * (normalizedBlockNorm A ^ 2 + normalizedBlockNorm U ^ 2) * ‖p‖ ^ 2 := by
  have hpoint (l h : Fin 4) :
      (1 / 2 : ℝ) * (∑ j, ∑ i, ∑ k,
        (generalCoefficient quaternionMatrix A i k j l +
          generalCoefficient oppositeMatrix U i k j l) *
          generalEinsteinCoefficient A U i k j h) =
      ((Matrix.trace (A * A) + Matrix.trace (U * U)) / 2) *
        (if l = h then 1 else 0) := by
    have hp : (1 / 2 : ℝ) * (∑ j, ∑ i, ∑ k,
        generalCoefficient quaternionMatrix A i k j l * generalEinsteinCoefficient A U i k j h) =
      (Matrix.trace (A * A) / 2) * (if l = h then 1 else 0) :=
      plus_generalCoefficient_ricci A U hA htA l h
    have hm : (1 / 2 : ℝ) * (∑ j, ∑ i, ∑ k,
        generalCoefficient oppositeMatrix U i k j l * generalEinsteinCoefficient A U i k j h) =
      (Matrix.trace (U * U) / 2) * (if l = h then 1 else 0) :=
      minus_generalCoefficient_ricci A U hU htU l h
    simp only [add_mul, Finset.sum_add_distrib, mul_add]
    rw [hp, hm]
    ring
  unfold scalarCurvatureContraction
  simp_rw [hpoint]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [mul_assoc, ← pow_two]
  rw [← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
  have hAn := trace_square_eq_six_norm_sq A hA
  have hUn := trace_square_eq_six_norm_sq U hU
  rw [← pow_two] at hAn hUn
  rw [hAn, hUn]
  ring

end
end PositiveEinsteinFour.ScalarHessian
end


section

/-! The Ricci normalization in an orthonormal frame is equivalent to the
actual chart Ricci normalization. This allows the raw frame calculus data
to use the already supplied Ricci contraction for its derived identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

private theorem orthogonal_basis_conjugation_injective (E : Mat4)
    (hE : IsUnit E.det) {A B : Mat4} (h : Eᵀ * A * E = Eᵀ * B * E) : A = B := by
  have hi : E * E⁻¹ = 1 := Matrix.mul_nonsing_inv E hE
  have hit : (Eᵀ)⁻¹ * Eᵀ = 1 := Matrix.nonsing_inv_mul _ (by simpa using hE)
  have hc (X : Mat4) : (Eᵀ)⁻¹ * (Eᵀ * X * E) * E⁻¹ = X := by
    calc
      _ = ((Eᵀ)⁻¹ * Eᵀ) * X * (E * E⁻¹) := by noncomm_ring
      _ = X := by rw [hi, hit, one_mul, mul_one]
  have he := congrArg (fun X : Mat4 => (Eᵀ)⁻¹ * X * E⁻¹) h
  simpa only [hc] using he

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem chartRicci_three_of_frame (e : OrthonormalFrame g c)
    (h : ∀ j k, (∑ i, frameCurvature g c e i j k i) = if j = k then 3 else 0) :
    chartRicci g c = (3 : ℝ) • chartMetric g c := by
  have hf : e.ricci = (3 : ℝ) • (1 : Mat4) := by
    ext j k
    rw [← frameCurvature_ricci e j k, h j k]
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, mul_ite,
      mul_one, mul_zero]
  apply orthogonal_basis_conjugation_injective e.matrix
    (isUnit_iff_ne_zero.mpr e.det_ne_zero)
  change e.ricci = e.matrixᵀ * ((3 : ℝ) • chartMetric g c) * e.matrix
  rw [mul_smul_comm, smul_mul_assoc, e.orthonormal]
  exact hf

theorem ricciThree_of_frame_contraction
    (h : ∀ (e : FrameBundle g) j k,
      (∑ i, frameCurvature g e.base e.frame i j k i) = if j = k then 3 else 0) :
    RicciThree g := by
  intro c
  exact chartRicci_three_of_frame (canonicalFrame g c) (h (frameAt g c))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial first derivative and its exact contribution to the
invariant Hessian expression. Division by a zero Weyl norm is harmless. -/

namespace PositiveEinsteinFour.Geometry

open TraceHessian HighestHessian
open scoped BigOperators

noncomputable section

def blockRadialGradient (A : Mat) (Z : Fin 4 → Mat) : Bianchi.Vec :=
  WithLp.toLp 2 (fun i => regularizedRadialDerivative 0 A (Z i))

theorem trace_eq_norm_mul_radial (A Z : Mat) :
    Matrix.trace (A * Z) = 6 * normalizedBlockNorm A * regularizedRadialDerivative 0 A Z := by
  by_cases hv : normalizedBlockNorm A = 0
  · have hA := (normalizedBlockNorm_eq_zero_iff A).mp hv
    simp [hA, regularizedRadialDerivative]
  · unfold regularizedRadialDerivative
    rw [regularizedBlockNorm_zero]
    field_simp [hv]

theorem weylRadialSquare_eq (A : Mat) (Z : Fin 4 → Mat) :
    weylRadialSquare A Z = normalizedBlockNorm A ^ 2 * ‖blockRadialGradient A Z‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold weylRadialSquare blockRadialGradient
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [trace_eq_norm_mul_radial A (Z i)]
  ring

theorem invariantHessianForm_eq_collected (A U : Mat) (Z : Fin 4 → Mat) :
    invariantHessianForm A U Z = collectedHessianForm
      (normalizedBlockNorm A) (normalizedBlockNorm U) (weylGradientEnergy Z)
      (weylMatrixEnergy A Z) (weylMatrixEnergy (traceFreeSquare A) Z)
      (weylCompressionEnergy A Z) (‖blockRadialGradient A Z‖ ^ 2) := by
  unfold invariantHessianForm collectedHessianForm
  rw [weylRadialSquare_eq]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual projection term in the metric Hessian estimate converges
under norm regularization, including at zeros of either Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory Filter
open scoped BigOperators Topology Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def regularizedProjectionCost (g : SmoothMetric M) (ε : ℝ) (e : FrameBundle g) : ℝ :=
  let A := plusWeyl g e.base e.frame
  let U := minusWeyl g e.base e.frame
  let Z := plusWeylGradient g e.base e.frame
  let V := minusWeylGradient g e.base e.frame
  let a : Vec := WithLp.toLp 2 (fun i => regularizedWeylWeightDerivative ε A U (Z i) (V i))
  let L := weightTensor a (gradientTensor Z)
  generalCurvaturePairing A U (highestProjection L) (highestProjection L) /
    (24 * regularizedWeylWeight ε A U)

theorem regularizedProjectionCost_eq_matrixWeight (g : SmoothMetric M) (ε : ℝ)
    (e : FrameBundle g) :
    regularizedProjectionCost g ε e =
      regularizedMatrixWeight ε (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) (minusWeylGradient g e.base e.frame)
        (projectedWeightKernel (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
          (plusGradientTensor g e.base e.frame)) :=
  projection_weight_cost_expansion _ _ _ _ _

theorem MetricGreenData.integral_regularizedProjectionCost_tendsto
    {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (d : MetricGreenData g μ) (o : OppositeWeylData d)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (he : ∀ n, ε n ≤ 1 / 3)
    (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ e, regularizedProjectionCost g (ε n) e ∂μ) atTop
      (𝓝 (∫ e, regularizedProjectionCost g 0 e ∂μ)) := by
  simp_rw [regularizedProjectionCost_eq_matrixWeight]
  exact integral_regularizedMatrixWeight_tendsto μ _ _ _ _ _
    d.continuousWeyl o.continuousWeyl d.continuousGradient o.continuousGradient
    (d.continuousProjectedWeightKernel o)
    (fun i e => (d.gradientConstraints e).1 i)
    (fun i e => (o.gradientConstraints e).1 i) hpinch ε hε he hlim

end
end PositiveEinsteinFour.Geometry
end


section

/-! The genuine smooth norm weights in the actual metric Hessian estimate. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def regularizedHessianIntegrand (g : SmoothMetric M) (ε : ℝ) (e : FrameBundle g) : ℝ :=
  let A := plusWeyl g e.base e.frame
  let U := minusWeyl g e.base e.frame
  let Z := plusWeylGradient g e.base e.frame
  let V := minusWeylGradient g e.base e.frame
  let m := regularizedWeylWeight ε A U
  let a : Vec := WithLp.toLp 2 (fun i => regularizedWeylWeightDerivative ε A U (Z i) (V i))
  let L := weightTensor a (gradientTensor Z)
  m * invariantHessianForm A U Z -
    (5 / 36 : ℝ) * (∑ i, a i * Matrix.trace (Z i * (∑ j, Z j * Z j))) +
    generalCurvaturePairing A U (highestProjection L) (highestProjection L) / (24 * m)

theorem MetricGreenData.regularizedHessianGreen
    {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (d : MetricGreenData g μ) (o : OppositeWeylData d)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2)
    (ε : ℝ) (hε : 0 < ε) (he : ε ≤ 1 / 3) :
    0 ≤ ∫ e, regularizedHessianIntegrand g ε e ∂μ := by
  exact d.weightedHessianGreen o hp hdecomp
    (frameRegularizedWeight g ε d.continuousWeyl o.continuousWeyl)
    (frameRegularizedWeight_pos g ε hε.le he d.continuousWeyl o.continuousWeyl hpinch)
    (frameRegularizedWeightDerivative g ε hε d.continuousWeyl o.continuousWeyl
      d.continuousGradient o.continuousGradient)
    (frameRegularizedWeight_hasDerivAt g d.flow ε hε d.continuousWeyl o.continuousWeyl
      d.continuousGradient o.continuousGradient d.weyl.symmetric o.symmetric
      d.derivativeWeyl o.derivativeWeyl)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Covariance of the actual Bianchi projection. The two generator
transformations are derived from the same quaternion frame change and
contract against its orthogonal three-dimensional matrix. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

def rawField (Z : RawGradient) : Angular.Gradient := fun i a b => Z a b i
def fieldRaw (Z : Angular.Gradient) : RawGradient :=
  fun a b => WithLp.toLp 2 (fun i => Z i a b)

@[simp] theorem rawField_fieldRaw (Z : Angular.Gradient) : rawField (fieldRaw Z) = Z := rfl
@[simp] theorem fieldRaw_rawField (Z : RawGradient) : fieldRaw (rawField Z) = Z := rfl

theorem turnRawGradient_fieldRaw (R : Mat) (P : Mat4) (Z : Angular.Gradient) :
    turnRawGradient R P (fieldRaw Z) = fieldRaw (turnGradient R P Z) := by
  funext a b
  exact turnRawGradient_field R P Z a b

theorem turnRawGradient_add (R : Mat) (P : Mat4) (Z W : RawGradient) :
    turnRawGradient R P (Z + W) = turnRawGradient R P Z + turnRawGradient R P W := by
  funext a b
  simp only [turnRawGradient, Pi.add_apply, smul_add, Finset.sum_add_distrib,
    turnVector_add]

theorem turnRawGradient_sub (R : Mat) (P : Mat4) (Z W : RawGradient) :
    turnRawGradient R P (Z - W) = turnRawGradient R P Z - turnRawGradient R P W := by
  funext a b
  have ht : turnVector P (-∑ r, ∑ s, (R r a * R s b) • W r s) =
      -turnVector P (∑ r, ∑ s, (R r a * R s b) • W r s) := by
    simpa only [neg_one_smul] using turnVector_smul P (-1)
      (∑ r, ∑ s, (R r a * R s b) • W r s)
  simp only [turnRawGradient, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]
  rw [sub_eq_add_neg, turnVector_add, ht]
  rfl

theorem turnRawGradient_smul (R : Mat) (P : Mat4) (c : ℝ) (Z : RawGradient) :
    turnRawGradient R P (c • Z) = c • turnRawGradient R P Z := by
  funext a b
  simp only [turnRawGradient, Pi.smul_apply, smul_comm _ c, ← Finset.smul_sum,
    turnVector_smul]

theorem turnRawGradient_sum {ι : Type*} [Fintype ι]
    (R : Mat) (P : Mat4) (Z : ι → RawGradient) :
    turnRawGradient R P (∑ i, Z i) = ∑ i, turnRawGradient R P (Z i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      funext a b
      simp [turnRawGradient, turnVector_zero]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, turnRawGradient_add, ih]

theorem rawMatrixRotation_field (s : Fin 3) (Z : Angular.Gradient) :
    rawMatrixRotation s (fieldRaw Z) = fieldRaw (fun i => matrixAction s (Z i)) := by
  funext a b
  ext i
  simp only [rawMatrixRotation, fieldRaw, PiLp.sub_apply, WithLp.ofLp_sum,
    Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, matrixAction,
    Finset.sum_sub_distrib, mul_comm]

theorem matrixAction_sum_smul {ι : Type*} [Fintype ι] (s : Fin 3)
    (c : ι → ℝ) (A : ι → Mat) :
    matrixAction s (∑ i, c i • A i) = ∑ i, c i • matrixAction s (A i) := by
  simp only [matrixAction_eq_commutator, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_sub, Finset.sum_sub_distrib]

theorem QuaternionLift.rawMatrixRotation_turn {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (hR : Rᵀ * R = 1) (s : Fin 3) (Z : RawGradient) :
    rawMatrixRotation s (turnRawGradient R P.matrix Z) =
      turnRawGradient R P.matrix (∑ r, R r s • rawMatrixRotation r Z) := by
  rw [← fieldRaw_rawField Z]
  rw [turnRawGradient_fieldRaw, rawMatrixRotation_field]
  rw [turnRawGradient_sum]
  simp_rw [turnRawGradient_smul, rawMatrixRotation_field, turnRawGradient_fieldRaw]
  funext a b
  ext i
  change matrixAction s (turnGradient R P.matrix (rawField Z) i) a b = _
  rw [turnGradient, matrixAction_sum_smul]
  simp_rw [P.matrixAction_conjugate hR, conjugateMatrix_sum, conjugateMatrix_smul]
  simp only [fieldRaw, WithLp.ofLp_sum, Finset.sum_apply, Pi.smul_apply, PiLp.smul_apply,
    turnGradient, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro j _
  ring

def rawQuaternion (s : Fin 3) (Z : RawGradient) : RawGradient :=
  fun a b => quaternion s (Z a b)

private theorem quaternion_sum {ι : Type*} [Fintype ι] (s : Fin 3) (v : ι → Vec) :
    quaternion s (∑ i, v i) = ∑ i, quaternion s (v i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, quaternion_zero]
  | @insert i t hi ih => simp only [Finset.sum_insert hi, quaternion_add, ih]

theorem rawQuaternion_sum_smul {ι : Type*} [Fintype ι] (s : Fin 3)
    (c : ι → ℝ) (Z : ι → RawGradient) :
    rawQuaternion s (∑ i, c i • Z i) = ∑ i, c i • rawQuaternion s (Z i) := by
  funext a b
  simp only [rawQuaternion, Finset.sum_apply, Pi.smul_apply,
    quaternion_sum, quaternion_smul]

theorem QuaternionLift.rawQuaternion_turn {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (s : Fin 3) (Z : RawGradient) :
    rawQuaternion s (turnRawGradient R P.matrix Z) =
      turnRawGradient R P.matrix (∑ r, R r s • rawQuaternion r Z) := by
  funext a b
  simp only [rawQuaternion, turnRawGradient, P.quaternion_turnVector]
  congr 1
  simp only [quaternion_sum, quaternion_smul, Finset.sum_apply, Pi.smul_apply,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  ring

theorem rawCoupling_eq (Z : RawGradient) :
    rawCoupling Z = ∑ s, rawQuaternion s (rawMatrixRotation s Z) := by
  funext a b
  rfl

/-- The actual Casimir coupling is unchanged by the passive frame
transformation, because both of its generator indices rotate together. -/
theorem QuaternionLift.rawCoupling_turn {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (hR : Rᵀ * R = 1) (Z : RawGradient) :
    rawCoupling (turnRawGradient R P.matrix Z) =
      turnRawGradient R P.matrix (rawCoupling Z) := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  have hr (r t : Fin 3) : (∑ s, R r s * R t s) = if r = t then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      congrArg (fun A : Mat => A r t) hR'
  rw [rawCoupling_eq]
  simp_rw [P.rawMatrixRotation_turn hR, P.rawQuaternion_turn,
    rawQuaternion_sum_smul]
  rw [← turnRawGradient_sum]
  congr 1
  calc
    _ = ∑ r, ∑ t, (∑ s, R r s * R t s) •
        rawQuaternion r (rawMatrixRotation t Z) := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      simp only [Finset.sum_smul]
    _ = rawCoupling Z := by
      simp only [hr, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
      exact (rawCoupling_eq Z).symm

theorem QuaternionLift.rawBianchiProjection_turn {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (hR : Rᵀ * R = 1) (Z : RawGradient) :
    rawBianchiProjection (turnRawGradient R P.matrix Z) =
      turnRawGradient R P.matrix (rawBianchiProjection Z) := by
  simp only [rawBianchiProjection, turnRawGradient_smul, turnRawGradient_sub,
    P.rawCoupling_turn hR]

theorem rawPairing_turn (R : Mat) (hR : R * Rᵀ = 1)
    (P : Mat4) (hP : P * Pᵀ = 1) (Z W : RawGradient) :
    rawPairing (turnRawGradient R P Z) (turnRawGradient R P W) = rawPairing Z W := by
  rw [← fieldRaw_rawField Z, ← fieldRaw_rawField W]
  simp only [turnRawGradient_fieldRaw]
  simp only [rawPairing, rawCoordinates, Fintype.sum_prod_type, fieldRaw]
  exact turnGradient_pairing R hR P hP _ _

theorem generalMatrixAction_field (A : Mat) (Z : Angular.Gradient) :
    generalMatrixAction A (fieldRaw Z) =
      fieldRaw (fun i => matrixSlotAction A (Z i)) := rfl

theorem generalMatrixAction_turn (R : Mat) (hR : Rᵀ * R = 1) (P : Mat4)
    (A : Mat) (Z : RawGradient) :
    generalMatrixAction (conjugateMatrix R A) (turnRawGradient R P Z) =
      turnRawGradient R P (generalMatrixAction A Z) := by
  rw [← fieldRaw_rawField Z]
  simp only [turnRawGradient_fieldRaw, generalMatrixAction_field]
  rw [turnGradient_slot R hR]

theorem gradientTensor_matrix_eq_fieldRaw (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) : (gradientTensor Z).matrix = fieldRaw Z := by
  funext a b
  exact gradientTensor_matrix Z hs a b

/-- The genuine squared norm of the projected matrix action is invariant
under the locally constructed frame change. -/
theorem QuaternionLift.weylCompressionEnergy_turn {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (hR : Rᵀ * R = 1) (A : Mat) (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) :
    weylCompressionEnergy (conjugateMatrix R A) (turnGradient R P.matrix Z) =
      weylCompressionEnergy A Z := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  have hs' := turnGradient_symmetric R P.matrix Z hs
  unfold weylCompressionEnergy
  rw [gradientTensor_matrix_eq_fieldRaw _ hs', gradientTensor_matrix_eq_fieldRaw Z hs,
    ← turnRawGradient_fieldRaw, generalMatrixAction_turn R hR,
    P.rawBianchiProjection_turn hR, rawPairing_turn R hR' P.matrix P.mul_transpose]

theorem QuaternionLift.invariantHessianForm_turn {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (hR : Rᵀ * R = 1) (A U : Mat) (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) :
    invariantHessianForm (conjugateMatrix R A) U (turnGradient R P.matrix Z) =
      invariantHessianForm A U Z := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  unfold invariantHessianForm
  rw [conjugateMatrix_norm R hR' A,
    weylGradientEnergy_turn R hR' P.matrix P.mul_transpose,
    weylMatrixEnergy_turn R hR P.matrix P.mul_transpose,
    weylMatrixSquareEnergy_turn R hR P.matrix P.mul_transpose,
    P.weylCompressionEnergy_turn hR A Z hs,
    weylRadialSquare_turn R hR' P.matrix P.mul_transpose]

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! Shifted positive Weyl coefficients give an upper bound on the scalar trace-free Hessian, using its actual nine real coefficients. -/

namespace PositiveEinsteinFour.ScalarHessian

open scoped BigOperators
open Matrix TraceHessian Angular HighestHessian

noncomputable section

def coefficientQuadratic (A : Mat) (c : Fin 3 → ℝ) : ℝ :=
  ∑ r, ∑ s, A r s * c r * c s

def crossVector (t : Fin 3) (c : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![![0, -c 2, c 1], ![c 2, 0, -c 0], ![-c 1, c 0, 0]] t

theorem coefficientQuadratic_nonneg (A : Mat) (hA : A.PosSemidef) (c : Fin 3 → ℝ) :
    0 ≤ coefficientQuadratic A c := by
  have h := hA.dotProduct_mulVec_nonneg c
  simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum] at h
  convert h using 1
  unfold coefficientQuadratic
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem coefficientQuadratic_cross_identity (A : Mat) (hA : symmetric A)
    (ht : traceFree A) (x : ℝ) (c : Fin 3 → ℝ) :
    (∑ t, coefficientQuadratic (A + x • (1 : Mat)) (crossVector t c)) =
      2 * x * (∑ r, c r ^ 2) - coefficientQuadratic A c := by
  have htrace : A 0 0 + A 1 1 + A 2 2 = 0 := by
    simpa only [traceFree, Matrix.trace, Matrix.diag, Fin.sum_univ_three] using ht
  norm_num [coefficientQuadratic, crossVector, Fin.sum_univ_three,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    hA 1 0, hA 2 0, hA 2 1]
  linear_combination (c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2) * htrace

/-- The upper eigenvalue bound follows directly from shifted positivity,
with no spectral frame. -/
theorem coefficientQuadratic_le_two_shift (A : Mat) (hA : symmetric A)
    (ht : traceFree A) (x : ℝ) (hx : (A + x • (1 : Mat)).PosSemidef)
    (c : Fin 3 → ℝ) :
    coefficientQuadratic A c ≤ 2 * x * ∑ r, c r ^ 2 := by
  have hn : 0 ≤ ∑ t, coefficientQuadratic (A + x • (1 : Mat)) (crossVector t c) :=
    Finset.sum_nonneg fun t _ => coefficientQuadratic_nonneg _ hx _
  rw [coefficientQuadratic_cross_identity A hA ht x c] at hn
  linarith only [hn]

def columnGram (A C : Mat) : ℝ := ∑ j, coefficientQuadratic A (fun i => C i j)

def rowGram (A C : Mat) : ℝ := ∑ i, coefficientQuadratic A (fun j => C i j)

theorem columnGram_le_two_shift (A C : Mat) (hA : symmetric A) (ht : traceFree A)
    (x : ℝ) (hx : (A + x • (1 : Mat)).PosSemidef) :
    columnGram A C ≤ 2 * x * ∑ i, ∑ j, C i j ^ 2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun j _ =>
    coefficientQuadratic_le_two_shift A hA ht x hx (fun i => C i j)
  change columnGram A C ≤ _ at h
  rw [← Finset.mul_sum, Finset.sum_comm] at h
  exact h

theorem rowGram_le_two_shift (A C : Mat) (hA : symmetric A) (ht : traceFree A)
    (x : ℝ) (hx : (A + x • (1 : Mat)).PosSemidef) :
    rowGram A C ≤ 2 * x * ∑ i, ∑ j, C i j ^ 2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    coefficientQuadratic_le_two_shift A hA ht x hx (fun j => C i j)
  change rowGram A C ≤ _ at h
  rwa [← Finset.mul_sum] at h

/-- The sharp scalar-Hessian operator bound for arbitrary
symmetric Weyl matrices and their actual shifted positive forms. -/
theorem scalarHessian_operator_bound (A U : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (x y : ℝ) (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2)
    (S : Matrix4) (hS : Sᵀ = S) (htS : Matrix.trace S = 0) :
    scalarPairing (blockAction quaternionMatrix A S) S +
      scalarPairing (blockAction oppositeMatrix U S) S ≤ 4 * scalarNormSq S := by
  have hp := columnGram_le_two_shift A (coefficients S) hA htA x hAx
  have hm := rowGram_le_two_shift U (coefficients S) hU htU y hUy
  have hN : 0 ≤ ∑ i, ∑ j, coefficients S i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [plusAction_pairing A hA htA S hS htS, minusAction_pairing U hU htU S hS htS,
    scalarNormSq_coefficients S hS htS]
  change 4 * columnGram A (coefficients S) + 4 * rowGram U (coefficients S) ≤ _
  have hsum : 2 * (x + y) * (∑ i, ∑ j, coefficients S i j ^ 2) ≤
      4 * (∑ i, ∑ j, coefficients S i j ^ 2) := by
    exact mul_le_mul_of_nonneg_right (by linarith only [hxy]) hN
  nlinarith only [hp, hm, hsum]

end
end PositiveEinsteinFour.ScalarHessian
end


section

/-! The sectional criterion from actual two-planes. The quaternionic
Grassmann calculation and the minimum-eigenvalue argument connect sectional
positivity with the Riemann curvature decomposition and symmetry identities. -/

namespace PositiveEinsteinFour.SectionalPlane

open EinsteinFour Matrix Bianchi TraceHessian QuaternionFrame Angular
open scoped BigOperators Manifold ContDiff

noncomputable section

def quadratic (A : Geometry.Mat3) (v : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ i, ∑ j, A i j * v i * v j

theorem quadratic_smul (A : Geometry.Mat3) (r : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    quadratic A (r • v) = r ^ 2 * quadratic A v := by
  simp only [quadratic, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadratic_add_scalar (A : Geometry.Mat3) (r : ℝ)
    (v : EuclideanSpace ℝ (Fin 3)) :
    quadratic (A + r • (1 : Geometry.Mat3)) v = quadratic A v + r * ‖v‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [quadratic, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, add_mul, Finset.sum_add_distrib, ite_mul, mul_ite,
    one_mul, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    pow_two, Finset.mul_sum, mul_assoc]

/-- An attained minimum on the unit sphere supplies the exact PSD shift. -/
theorem exists_minimum_shift (A : Geometry.Mat3) (hA : symmetric A) :
    ∃ s : EuclideanSpace ℝ (Fin 3), ‖s‖ = 1 ∧
      (A + (-quadratic A s) • (1 : Geometry.Mat3)).PosSemidef := by
  have hcont : Continuous (quadratic A) := by unfold quadratic; fun_prop
  obtain ⟨s, hs, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr (show (0 : ℝ) ≤ 1 by norm_num)) hcont.continuousOn
  have hsnorm : ‖s‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hs
  refine ⟨s, hsnorm, ?_⟩
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · have ha : A.IsHermitian := by ext i j; exact hA j i
    exact ha.add (Matrix.isHermitian_one.smul (show IsSelfAdjoint (-quadratic A s) by rfl))
  · intro z
    let v : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 z
    have hv : 0 ≤ quadratic (A + (-quadratic A s) • (1 : Geometry.Mat3)) v := by
      by_cases hz : v = 0
      · simp [hz, quadratic]
      have hn : 0 < ‖v‖ := norm_pos_iff.mpr hz
      have hunit : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := norm_smul_inv_norm hz
      have hl := hmin (show (‖v‖⁻¹ : ℝ) • v ∈ Metric.sphere 0 1 by
        simpa only [Metric.mem_sphere, dist_zero_right] using hunit)
      change quadratic A s ≤ quadratic A ((‖v‖⁻¹ : ℝ) • v) at hl
      rw [quadratic_smul] at hl
      have hscale : ‖v‖ ^ 2 * (‖v‖⁻¹) ^ 2 = 1 := by field_simp [ne_of_gt hn]
      have hm := mul_le_mul_of_nonneg_left hl (sq_nonneg ‖v‖)
      rw [← mul_assoc, hscale, one_mul] at hm
      rw [quadratic_add_scalar]
      nlinarith only [hm]
    simpa only [quadratic, v, Matrix.mulVec, dotProduct, Pi.star_apply,
      star_trivial, PiLp.toLp_apply, Finset.mul_sum, mul_assoc, mul_comm,
      mul_left_comm] using hv

def sectionalValue (R : CurvatureArray) (u v : Vec4) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * u a * v b * v c * u d

theorem sectionalValue_add (R S : CurvatureArray) (u v : Vec4) :
    sectionalValue (R + S) u v = sectionalValue R u v + sectionalValue S u v := by
  simp [sectionalValue, add_mul, Finset.sum_add_distrib]

theorem sectionalValue_smul (r : ℝ) (R : CurvatureArray) (u v : Vec4) :
    sectionalValue (r • R) u v = r * sectionalValue R u v := by
  simp [sectionalValue, Finset.mul_sum, mul_assoc]

theorem sectionalValue_sum {ι : Type*} [Fintype ι] (R : ι → CurvatureArray)
    (u v : Vec4) : sectionalValue (∑ i, R i) u v = ∑ i, sectionalValue (R i) u v := by
  let F : CurvatureArray →ₗ[ℝ] ℝ :=
    { toFun := fun S => sectionalValue S u v
      map_add' := fun S T => sectionalValue_add S T u v
      map_smul' := fun r S => by
        simpa only [smul_eq_mul, RingHom.id_apply] using sectionalValue_smul r S u v }
  change F (∑ i, R i) = ∑ i, F (R i)
  exact map_sum F R Finset.univ

theorem sectionalValue_twoFormProduct (P Q : Geometry.Mat4) (u v : Vec4) :
    sectionalValue (twoFormProduct P Q) u v = coefficient P u v * coefficient Q u v := by
  simp only [sectionalValue, twoFormProduct, coefficient_eq_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem sectionalValue_blockTensor (A : Geometry.Mat3) (Q : Fin 3 → Geometry.Mat4)
    (u v : Vec4) : sectionalValue (blockTensor A Q) u v =
      (1 / 2 : ℝ) * ∑ i, ∑ j, A i j * coefficient (Q i) u v * coefficient (Q j) u v := by
  simp only [blockTensor, sectionalValue_smul, sectionalValue_sum,
    sectionalValue_twoFormProduct, mul_assoc]

theorem plane_independent {u v : Vec4} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (horth : inner ℝ u v = 0) : LinearIndependent ℝ ![u, v] := by
  apply linearIndependent_of_ne_zero_of_inner_eq_zero
  · intro i
    fin_cases i
    · change u ≠ 0
      exact norm_ne_zero_iff.mp (by rw [hu]; norm_num)
    · change v ≠ 0
      exact norm_ne_zero_iff.mp (by rw [hv]; norm_num)
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · change inner ℝ u v = 0
      exact horth
    · change inner ℝ v u = 0
      simpa only [real_inner_comm] using horth
    · exact False.elim (hij rfl)

/-- Positivity on actual two-planes bounds every pair of unit block
Rayleigh quotients; both blocks can be minimized independently. -/
theorem rayleigh_sum_pos (A B : Geometry.Mat3)
    (hp : ∀ u v : Vec4, LinearIndependent ℝ ![u, v] →
      0 < sectionalValue (einsteinCurvatureTensor A B) u v)
    (s t : EuclideanSpace ℝ (Fin 3)) (hs : ‖s‖ = 1) (ht : ‖t‖ = 1) :
    0 < 2 + quadratic A s + quadratic B t := by
  have hs2 : ∑ i, s i ^ 2 = 1 := by
    simpa only [hs, one_pow] using (EuclideanSpace.real_norm_sq_eq s).symm
  have ht2 : ∑ i, t i ^ 2 = 1 := by
    simpa only [ht, one_pow] using (EuclideanSpace.real_norm_sq_eq t).symm
  obtain ⟨u, v, hu, hv, huv, hplus, hminus⟩ := exists_two_plane s t hs2 ht2
  have hpos := hp u v (plane_independent hu hv huv)
  have hform : sectionalValue (einsteinCurvatureTensor A B) u v =
      (2 + quadratic A s + quadratic B t) / 2 := by
    rw [einsteinCurvatureTensor, sectionalValue_add, sectionalValue_blockTensor,
      sectionalValue_blockTensor]
    simp_rw [hplus, hminus]
    have hnA : quadratic (1 + A) s = quadratic A s + 1 := by
      rw [add_comm (1 : Geometry.Mat3) A]
      simpa only [one_smul, hs, one_pow, mul_one] using quadratic_add_scalar A 1 s
    have hnB : quadratic (1 + B) t = quadratic B t + 1 := by
      rw [add_comm (1 : Geometry.Mat3) B]
      simpa only [one_smul, ht, one_pow, mul_one] using quadratic_add_scalar B 1 t
    dsimp [quadratic] at hnA hnB ⊢
    simp only [mul_neg, neg_mul, neg_neg]
    linarith
  rw [hform] at hpos
  linarith

/-- The published sectional criterion follows from the proved plane
realization and elementary extrema on two unit spheres. -/
theorem shifts_of_positive_planes (A B : Geometry.Mat3)
    (hA : symmetric A) (hB : symmetric B)
    (hp : ∀ u v : Vec4, LinearIndependent ℝ ![u, v] →
      0 < sectionalValue (einsteinCurvatureTensor A B) u v) :
    ∃ x y : ℝ, (A + x • (1 : Geometry.Mat3)).PosSemidef ∧
      (B + y • (1 : Geometry.Mat3)).PosSemidef ∧ x + y < 2 := by
  obtain ⟨s, hs, hAs⟩ := exists_minimum_shift A hA
  obtain ⟨t, ht, hBt⟩ := exists_minimum_shift B hB
  have hpos := rayleigh_sum_pos A B hp s t hs ht
  exact ⟨-quadratic A s, -quadratic B t, hAs, hBt, by linarith⟩

end
end PositiveEinsteinFour.SectionalPlane
namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix SectionalPlane
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem OrthonormalFrame.map_eq_combination {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) (u : FourSpace) :
    e.map u = ∑ i, u i • e.vector i := by
  ext j
  simp only [OrthonormalFrame.map_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    OrthonormalFrame.vector_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sectionalValue_frame (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (u v : FourSpace) :
    sectionalValue (frameCurvature g c e) u v =
      sectionalNumerator g c (chartAt FourSpace c c) (e.map u) (e.map v) := by
  let C : Mat4 := fun i j => if j = 0 then u i else v i
  have heq : (fun s : Fin 4 => ∑ a, C a (![0, 1, 1, 0] s) • e.vector a) =
      ![e.map u, e.map v, e.map v, e.map u] := by
    funext s
    fin_cases s
    · change (∑ a, u a • e.vector a) = e.map u
      exact (e.map_eq_combination u).symm
    · change (∑ a, v a • e.vector a) = e.map v
      exact (e.map_eq_combination v).symm
    · change (∑ a, v a • e.vector a) = e.map v
      exact (e.map_eq_combination v).symm
    · change (∑ a, u a • e.vector a) = e.map u
      exact (e.map_eq_combination u).symm
  have hh := multilinear_combinations (curvatureForm g c) C e.vector ![0, 1, 1, 0]
  rw [heq] at hh
  change sectionalNumerator g c (chartAt FourSpace c c) (e.map u) (e.map v) = _ at hh
  rw [hh]
  change (∑ a, ∑ b, ∑ p, ∑ r,
      frameCurvature g c e a b p r * u a * v b * v p * u r) =
    ∑ a, ∑ b, ∑ p, ∑ r,
      (u a * v b * v p * u r) * frameCurvature g c e a b p r
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- The pointwise sectional threshold follows from
ordinary curvature-block symmetry/decomposition and actual positive
sectional curvature. No eigenvalue/sectional estimate is a premise. -/
theorem sectionalInput_of_curvature_decomposition (g : SmoothMetric M)
    (hdecomp : RicciThree g → ∀ c (e : OrthonormalFrame g c), frameCurvature g c e =
      Angular.einsteinCurvatureTensor (plusWeyl g c e) (minusWeyl g c e))
    (hplus : ∀ e : FrameBundle g, TraceHessian.symmetric (plusWeyl g e.base e.frame))
    (hminus : ∀ e : FrameBundle g, TraceHessian.symmetric (minusWeyl g e.base e.frame)) :
    GurskyLeBrunSectionalInput g := by
  intro hRic hsec e
  apply shifts_of_positive_planes _ _ (hplus e) (hminus e)
  intro u v huv
  rw [← hdecomp hRic e.base e.frame, sectionalValue_frame]
  exact e.frame.sectional_pos hsec u v huv

end
end PositiveEinsteinFour.Geometry
end


section

/-! The six canonical two-form coordinates of an algebraic curvature
array. All reconstruction statements here are finite-dimensional algebra;
the actual metric curvature symmetries are supplied separately. -/

namespace PositiveEinsteinFour.AlgebraicCurvature

open Matrix TraceHessian Angular
open PositiveEinsteinFour.Geometry (curvatureBlock curvatureBlock_symmetric)
open scoped BigOperators

noncomputable section

def pair (i : Fin 6) : Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] i

def pairIndex (i j : Fin 4) : Fin 6 :=
  match i.val, j.val with
  | 0, 1 => 0 | 1, 0 => 0
  | 0, 2 => 1 | 2, 0 => 1
  | 0, 3 => 2 | 3, 0 => 2
  | 1, 2 => 3 | 2, 1 => 3
  | 1, 3 => 4 | 3, 1 => 4
  | 2, 3 => 5 | 3, 2 => 5
  | _, _ => 0

def pairSign (i j : Fin 4) : ℝ :=
  if i < j then 1 else if i = j then 0 else -1

def matrixOf (R : CurvatureArray) : Matrix (Fin 6) (Fin 6) ℝ := fun a b =>
  R (pair a).1 (pair a).2 (pair b).1 (pair b).2

def tensorOf (K : Matrix (Fin 6) (Fin 6) ℝ) : CurvatureArray := fun i j k l =>
  pairSign i j * pairSign k l * K (pairIndex i j) (pairIndex k l)

def FirstSkew (R : CurvatureArray) : Prop := ∀ i j k l, R j i k l = -R i j k l

def LastSkew (R : CurvatureArray) : Prop := ∀ i j k l, R i j l k = -R i j k l

def PairSymmetric (R : CurvatureArray) : Prop := ∀ i j k l, R k l i j = R i j k l

def FirstBianchi (R : CurvatureArray) : Prop :=
  ∀ i j k l, R i j k l + R j k i l + R k i j l = 0

theorem pairSymmetric_of_bianchi {R : CurvatureArray}
    (hf : FirstSkew R) (hl : LastSkew R) (hb : FirstBianchi R) : PairSymmetric R := by
  intro a b c d
  have h1 := hb a b c d
  have h2 := hb a b d c
  have h3 := hb c d a b
  have h4 := hb b d c a
  rw [hf a c b d] at h1
  rw [hl a b c d] at h2
  rw [hl d a b c, hl a c b d] at h3
  rw [hl b d a c, hf c d b a, hl c d a b,
    hf b c d a, hl b c a d] at h4
  linarith

def ricci (R : CurvatureArray) (j k : Fin 4) : ℝ := ∑ i, R i j k i

theorem first_diagonal_zero {R : CurvatureArray} (h : FirstSkew R) (i k l : Fin 4) :
    R i i k l = 0 := by have hh := h i i k l; linarith

theorem last_diagonal_zero {R : CurvatureArray} (h : LastSkew R) (i j k : Fin 4) :
    R i j k k = 0 := by have hh := h i j k k; linarith

private theorem tensorOf_matrixOf_row0 {R : CurvatureArray}
    (hf : FirstSkew R) (hl : LastSkew R) (j k l : Fin 4) :
    tensorOf (matrixOf R) 0 j k l = R 0 j k l := by
  have f10 (k l) := hf 0 1 k l
  have f20 (k l) := hf 0 2 k l
  have f30 (k l) := hf 0 3 k l
  have f21 (k l) := hf 1 2 k l
  have f31 (k l) := hf 1 3 k l
  have f32 (k l) := hf 2 3 k l
  have l10 (i j) := hl i j 0 1
  have l20 (i j) := hl i j 0 2
  have l30 (i j) := hl i j 0 3
  have l21 (i j) := hl i j 1 2
  have l31 (i j) := hl i j 1 3
  have l32 (i j) := hl i j 2 3
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [tensorOf, matrixOf, pair, pairIndex, pairSign,
      first_diagonal_zero hf, last_diagonal_zero hl,
      f10, f20, f30, f21, f31, f32, l10, l20, l30, l21, l31, l32]

private theorem tensorOf_matrixOf_row1 {R : CurvatureArray}
    (hf : FirstSkew R) (hl : LastSkew R) (j k l : Fin 4) :
    tensorOf (matrixOf R) 1 j k l = R 1 j k l := by
  have f10 (k l) := hf 0 1 k l
  have f20 (k l) := hf 0 2 k l
  have f30 (k l) := hf 0 3 k l
  have f21 (k l) := hf 1 2 k l
  have f31 (k l) := hf 1 3 k l
  have f32 (k l) := hf 2 3 k l
  have l10 (i j) := hl i j 0 1
  have l20 (i j) := hl i j 0 2
  have l30 (i j) := hl i j 0 3
  have l21 (i j) := hl i j 1 2
  have l31 (i j) := hl i j 1 3
  have l32 (i j) := hl i j 2 3
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [tensorOf, matrixOf, pair, pairIndex, pairSign,
      first_diagonal_zero hf, last_diagonal_zero hl,
      f10, f20, f30, f21, f31, f32, l10, l20, l30, l21, l31, l32]

private theorem tensorOf_matrixOf_row2 {R : CurvatureArray}
    (hf : FirstSkew R) (hl : LastSkew R) (j k l : Fin 4) :
    tensorOf (matrixOf R) 2 j k l = R 2 j k l := by
  have f10 (k l) := hf 0 1 k l
  have f20 (k l) := hf 0 2 k l
  have f30 (k l) := hf 0 3 k l
  have f21 (k l) := hf 1 2 k l
  have f31 (k l) := hf 1 3 k l
  have f32 (k l) := hf 2 3 k l
  have l10 (i j) := hl i j 0 1
  have l20 (i j) := hl i j 0 2
  have l30 (i j) := hl i j 0 3
  have l21 (i j) := hl i j 1 2
  have l31 (i j) := hl i j 1 3
  have l32 (i j) := hl i j 2 3
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [tensorOf, matrixOf, pair, pairIndex, pairSign,
      first_diagonal_zero hf, last_diagonal_zero hl,
      f10, f20, f30, f21, f31, f32, l10, l20, l30, l21, l31, l32]

private theorem tensorOf_matrixOf_row3 {R : CurvatureArray}
    (hf : FirstSkew R) (hl : LastSkew R) (j k l : Fin 4) :
    tensorOf (matrixOf R) 3 j k l = R 3 j k l := by
  have f10 (k l) := hf 0 1 k l
  have f20 (k l) := hf 0 2 k l
  have f30 (k l) := hf 0 3 k l
  have f21 (k l) := hf 1 2 k l
  have f31 (k l) := hf 1 3 k l
  have f32 (k l) := hf 2 3 k l
  have l10 (i j) := hl i j 0 1
  have l20 (i j) := hl i j 0 2
  have l30 (i j) := hl i j 0 3
  have l21 (i j) := hl i j 1 2
  have l31 (i j) := hl i j 1 3
  have l32 (i j) := hl i j 2 3
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [tensorOf, matrixOf, pair, pairIndex, pairSign,
      first_diagonal_zero hf, last_diagonal_zero hl,
      f10, f20, f30, f21, f31, f32, l10, l20, l30, l21, l31, l32]

/-- First and last skew symmetry reconstruct the whole four-tensor from
its 36 canonical two-form matrix entries. -/
theorem tensorOf_matrixOf {R : CurvatureArray} (hf : FirstSkew R) (hl : LastSkew R) :
    tensorOf (matrixOf R) = R := by
  funext i j k l
  fin_cases i
  · exact tensorOf_matrixOf_row0 hf hl j k l
  · exact tensorOf_matrixOf_row1 hf hl j k l
  · exact tensorOf_matrixOf_row2 hf hl j k l
  · exact tensorOf_matrixOf_row3 hf hl j k l

theorem matrixOf_symmetric {R : CurvatureArray} (h : PairSymmetric R) :
    (matrixOf R)ᵀ = matrixOf R := by
  ext i j
  exact h _ _ _ _

theorem tensor_eq_of_matrixOf_eq {R S : CurvatureArray}
    (hRf : FirstSkew R) (hRl : LastSkew R)
    (hSf : FirstSkew S) (hSl : LastSkew S) (h : matrixOf R = matrixOf S) : R = S := by
  rw [← tensorOf_matrixOf hRf hRl, h, tensorOf_matrixOf hSf hSl]

theorem pairIndex_reverse (i j : Fin 4) : pairIndex j i = pairIndex i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem pairSign_reverse (i j : Fin 4) : pairSign j i = -pairSign i j := by
  fin_cases i <;> fin_cases j <;> norm_num [pairSign]

theorem tensorOf_firstSkew (K : Matrix (Fin 6) (Fin 6) ℝ) : FirstSkew (tensorOf K) := by
  intro i j k l
  simp only [tensorOf, pairIndex_reverse i j, pairSign_reverse i j]
  ring

theorem tensorOf_lastSkew (K : Matrix (Fin 6) (Fin 6) ℝ) : LastSkew (tensorOf K) := by
  intro i j k l
  simp only [tensorOf, pairIndex_reverse k l, pairSign_reverse k l]
  ring

/-- Compression of an antisymmetric coordinate sum to the six increasing
index pairs. The factor two records the two orders of each pair. -/
theorem pair_sum (Q : Mat4) (hQ : Qᵀ = -Q) (f : Fin 6 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4, pairSign i j * Q i j * f (pairIndex i j)) =
      2 * ∑ a : Fin 6, Q (pair a).1 (pair a).2 * f a := by
  have hs (i j : Fin 4) : Q j i = -Q i j := by
    have h := congrArg (fun A : Mat4 => A i j) hQ
    exact h
  have hd (i : Fin 4) : Q i i = 0 := by have h := hs i i; linarith
  norm_num [Fin.sum_univ_succ, pairSign, pairIndex, pair, hd,
    hs 0 1, hs 0 2, hs 0 3, hs 1 2, hs 1 3, hs 2 3]
  ring

def canonicalBlock (K : Matrix (Fin 6) (Fin 6) ℝ) (Q P : Fin 3 → Mat4) : Mat3 :=
  fun s t => -(1 / 2 : ℝ) * ∑ a, ∑ b,
    K a b * Q s (pair a).1 (pair a).2 * P t (pair b).1 (pair b).2


theorem pair_bilinear_sum (K : Matrix (Fin 6) (Fin 6) ℝ) (Q P : Mat4)
    (hQ : Qᵀ = -Q) (hP : Pᵀ = -P) :
    (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
      pairSign i j * pairSign k l * K (pairIndex i j) (pairIndex k l) * Q i j * P k l) =
      4 * ∑ a : Fin 6, ∑ b : Fin 6,
        K a b * Q (pair a).1 (pair a).2 * P (pair b).1 (pair b).2 := by
  let F : Fin 6 → ℝ := fun a => ∑ b, P (pair b).1 (pair b).2 * K a b
  have hi (i j : Fin 4) := pair_sum P hP (fun b => K (pairIndex i j) b)
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin 4, pairSign i j * Q i j *
        (∑ k : Fin 4, ∑ l : Fin 4, pairSign k l * P k l * K (pairIndex i j) (pairIndex k l)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = ∑ i : Fin 4, ∑ j : Fin 4, pairSign i j * Q i j * (2 * F (pairIndex i j)) := by
      simp_rw [hi]
      rfl
    _ = 2 * (∑ i : Fin 4, ∑ j : Fin 4, pairSign i j * Q i j * F (pairIndex i j)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 4 * (∑ a : Fin 6, Q (pair a).1 (pair a).2 * F a) := by
      rw [pair_sum Q hQ F]
      ring
    _ = _ := by
      simp only [F, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

def mixedBlock (R : CurvatureArray) (Q P : Fin 3 → Mat4) : Mat3 := fun s t =>
  (1 / 8 : ℝ) * ∑ p : Fin 4 × Fin 4, ∑ q : Fin 4 × Fin 4,
    R p.1 p.2 q.2 q.1 * Q s p.1 p.2 * P t q.1 q.2

theorem mixedBlock_tensorOf (K : Matrix (Fin 6) (Fin 6) ℝ)
    (Q P : Fin 3 → Mat4) (hQ : ∀ i, (Q i)ᵀ = -Q i) (hP : ∀ i, (P i)ᵀ = -P i) :
    mixedBlock (tensorOf K) Q P = canonicalBlock K Q P := by
  have ht (i j k l : Fin 4) : tensorOf K i j l k =
      -(pairSign i j * pairSign k l * K (pairIndex i j) (pairIndex k l)) := by
    rw [tensorOf, pairSign_reverse k l, pairIndex_reverse k l]
    ring
  ext s t
  simp only [mixedBlock, Fintype.sum_prod_type, ht, neg_mul,
    Finset.sum_neg_distrib]
  rw [pair_bilinear_sum K (Q s) (P t) (hQ s) (hP t)]
  simp only [canonicalBlock]
  ring

theorem curvatureBlock_tensorOf (K : Matrix (Fin 6) (Fin 6) ℝ)
    (Q : Fin 3 → Mat4) (hQ : ∀ i, (Q i)ᵀ = -Q i) :
    curvatureBlock (fun p q => tensorOf K p.1 p.2 q.2 q.1) Q = canonicalBlock K Q Q :=
  mixedBlock_tensorOf K Q Q hQ hQ


def plusFormula (K : Matrix (Fin 6) (Fin 6) ℝ) : Mat3 :=
  ![![-(K 0 0 + K 0 5 + K 5 0 + K 5 5) / 2, -(K 0 1 - K 0 4 + K 5 1 - K 5 4) / 2, -(K 0 2 + K 0 3 + K 5 2 + K 5 3) / 2],
    ![-(K 1 0 + K 1 5 - K 4 0 - K 4 5) / 2, -(K 1 1 - K 1 4 - K 4 1 + K 4 4) / 2, -(K 1 2 + K 1 3 - K 4 2 - K 4 3) / 2],
    ![-(K 2 0 + K 2 5 + K 3 0 + K 3 5) / 2, -(K 2 1 - K 2 4 + K 3 1 - K 3 4) / 2, -(K 2 2 + K 2 3 + K 3 2 + K 3 3) / 2]]

private theorem plusFormula_row0 (K : Matrix (Fin 6) (Fin 6) ℝ) (j : Fin 3) :
    canonicalBlock K quaternionMatrix quaternionMatrix 0 j = plusFormula K 0 j := by
  fin_cases j <;>
    norm_num [canonicalBlock, plusFormula, pair, quaternionMatrix, oppositeMatrix,
      Geometry.oppositeQuaternion, Fin.sum_univ_succ] <;> ring

private theorem plusFormula_row1 (K : Matrix (Fin 6) (Fin 6) ℝ) (j : Fin 3) :
    canonicalBlock K quaternionMatrix quaternionMatrix 1 j = plusFormula K 1 j := by
  fin_cases j <;>
    norm_num [canonicalBlock, plusFormula, pair, quaternionMatrix, oppositeMatrix,
      Geometry.oppositeQuaternion, Fin.sum_univ_succ] <;> ring

private theorem plusFormula_row2 (K : Matrix (Fin 6) (Fin 6) ℝ) (j : Fin 3) :
    canonicalBlock K quaternionMatrix quaternionMatrix 2 j = plusFormula K 2 j := by
  fin_cases j <;>
    norm_num [canonicalBlock, plusFormula, pair, quaternionMatrix, oppositeMatrix,
      Geometry.oppositeQuaternion, Fin.sum_univ_succ] <;> ring

theorem plusFormula_eq (K : Matrix (Fin 6) (Fin 6) ℝ) :
    canonicalBlock K quaternionMatrix quaternionMatrix = plusFormula K := by
  ext i j
  fin_cases i
  · exact plusFormula_row0 K j
  · exact plusFormula_row1 K j
  · exact plusFormula_row2 K j

def minusFormula (K : Matrix (Fin 6) (Fin 6) ℝ) : Mat3 :=
  ![![-(K 0 0 - K 0 5 - K 5 0 + K 5 5) / 2, -(K 0 1 + K 0 4 - K 5 1 - K 5 4) / 2, -(K 0 2 - K 0 3 - K 5 2 + K 5 3) / 2],
    ![-(K 1 0 - K 1 5 + K 4 0 - K 4 5) / 2, -(K 1 1 + K 1 4 + K 4 1 + K 4 4) / 2, -(K 1 2 - K 1 3 + K 4 2 - K 4 3) / 2],
    ![-(K 2 0 - K 2 5 - K 3 0 + K 3 5) / 2, -(K 2 1 + K 2 4 - K 3 1 - K 3 4) / 2, -(K 2 2 - K 2 3 - K 3 2 + K 3 3) / 2]]

private theorem minusFormula_row0 (K : Matrix (Fin 6) (Fin 6) ℝ) (j : Fin 3) :
    canonicalBlock K oppositeMatrix oppositeMatrix 0 j = minusFormula K 0 j := by
  fin_cases j <;>
    norm_num [canonicalBlock, minusFormula, pair, quaternionMatrix, oppositeMatrix,
      Geometry.oppositeQuaternion, Fin.sum_univ_succ] <;> ring

private theorem minusFormula_row1 (K : Matrix (Fin 6) (Fin 6) ℝ) (j : Fin 3) :
    canonicalBlock K oppositeMatrix oppositeMatrix 1 j = minusFormula K 1 j := by
  fin_cases j <;>
    norm_num [canonicalBlock, minusFormula, pair, quaternionMatrix, oppositeMatrix,
      Geometry.oppositeQuaternion, Fin.sum_univ_succ] <;> ring

private theorem minusFormula_row2 (K : Matrix (Fin 6) (Fin 6) ℝ) (j : Fin 3) :
    canonicalBlock K oppositeMatrix oppositeMatrix 2 j = minusFormula K 2 j := by
  fin_cases j <;>
    norm_num [canonicalBlock, minusFormula, pair, quaternionMatrix, oppositeMatrix,
      Geometry.oppositeQuaternion, Fin.sum_univ_succ] <;> ring

theorem minusFormula_eq (K : Matrix (Fin 6) (Fin 6) ℝ) :
    canonicalBlock K oppositeMatrix oppositeMatrix = minusFormula K := by
  ext i j
  fin_cases i
  · exact minusFormula_row0 K j
  · exact minusFormula_row1 K j
  · exact minusFormula_row2 K j

structure EinsteinRelations (K : Matrix (Fin 6) (Fin 6) ℝ) : Prop where
  symmetric : Kᵀ = K
  d0 : K 5 5 = K 0 0
  d1 : K 4 4 = K 1 1
  d2 : K 3 3 = K 2 2
  a01 : K 4 5 = -K 0 1
  a02 : K 3 5 = K 0 2
  a03 : K 2 5 = K 0 3
  a04 : K 1 5 = -K 0 4
  a12 : K 3 4 = -K 1 2
  a13 : K 2 4 = -K 1 3

theorem einsteinRelations_of_ricci (K : Matrix (Fin 6) (Fin 6) ℝ) (hs : Kᵀ = K)
    (hr : ∀ j k, ricci (tensorOf K) j k = if j = k then 3 else 0) :
    EinsteinRelations K := by
  have hs10 : K 1 0 = K 0 1 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 1) hs
  have hs20 : K 2 0 = K 0 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 2) hs
  have hs21 : K 2 1 = K 1 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 2) hs
  have hs30 : K 3 0 = K 0 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 3) hs
  have hs31 : K 3 1 = K 1 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 3) hs
  have hs32 : K 3 2 = K 2 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 3) hs
  have hs40 : K 4 0 = K 0 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 4) hs
  have hs41 : K 4 1 = K 1 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 4) hs
  have hs42 : K 4 2 = K 2 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 4) hs
  have hs43 : K 4 3 = K 3 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 4) hs
  have hs50 : K 5 0 = K 0 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 5) hs
  have hs51 : K 5 1 = K 1 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 5) hs
  have hs52 : K 5 2 = K 2 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 5) hs
  have hs53 : K 5 3 = K 3 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 5) hs
  have hs54 : K 5 4 = K 4 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 4 5) hs
  have hr00 := hr 0 0
  have hr01 := hr 0 1
  have hr02 := hr 0 2
  have hr03 := hr 0 3
  have hr11 := hr 1 1
  have hr12 := hr 1 2
  have hr13 := hr 1 3
  have hr22 := hr 2 2
  have hr23 := hr 2 3
  have hr33 := hr 3 3
  norm_num [ricci, tensorOf, pairIndex, pairSign, Fin.sum_univ_succ,
    hs10, hs20, hs21, hs30, hs31, hs32, hs40, hs41, hs42, hs43, hs50, hs51, hs52, hs53, hs54] at hr00 hr01 hr02 hr03 hr11 hr12 hr13 hr22 hr23 hr33
  refine ⟨hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]

theorem blockTensor_apply (A : Mat3) (Q : Fin 3 → Mat4) (i j k l : Fin 4) :
    blockTensor A Q i j k l = (1 / 2 : ℝ) * ∑ s, ∑ t, A s t * Q s i j * Q t l k := by
  simp only [blockTensor, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, twoFormProduct, mul_assoc]

def blocksTensor (K : Matrix (Fin 6) (Fin 6) ℝ) : CurvatureArray :=
  blockTensor (plusFormula K) quaternionMatrix + blockTensor (minusFormula K) oppositeMatrix

private theorem blocksTensor_row0 (K : Matrix (Fin 6) (Fin 6) ℝ) (h : EinsteinRelations K)
    (j : Fin 6) : matrixOf (blocksTensor K) 0 j = K 0 j := by
  have hs10 : K 1 0 = K 0 1 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 1) h.symmetric
  have hs20 : K 2 0 = K 0 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 2) h.symmetric
  have hs21 : K 2 1 = K 1 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 2) h.symmetric
  have hs30 : K 3 0 = K 0 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 3) h.symmetric
  have hs31 : K 3 1 = K 1 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 3) h.symmetric
  have hs32 : K 3 2 = K 2 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 3) h.symmetric
  have hs40 : K 4 0 = K 0 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 4) h.symmetric
  have hs41 : K 4 1 = K 1 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 4) h.symmetric
  have hs42 : K 4 2 = K 2 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 4) h.symmetric
  have hs43 : K 4 3 = K 3 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 4) h.symmetric
  have hs50 : K 5 0 = K 0 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 5) h.symmetric
  have hs51 : K 5 1 = K 1 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 5) h.symmetric
  have hs52 : K 5 2 = K 2 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 5) h.symmetric
  have hs53 : K 5 3 = K 3 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 5) h.symmetric
  have hs54 : K 5 4 = K 4 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 4 5) h.symmetric
  change blockTensor (plusFormula K) quaternionMatrix (pair 0).1 (pair 0).2
      (pair j).1 (pair j).2 +
    blockTensor (minusFormula K) oppositeMatrix (pair 0).1 (pair 0).2
      (pair j).1 (pair j).2 = K 0 j
  simp only [blockTensor_apply]
  fin_cases j <;>
    norm_num [pair,
      plusFormula, minusFormula, quaternionMatrix, oppositeMatrix, Geometry.oppositeQuaternion,
      Fin.sum_univ_succ, hs10, hs20, hs21, hs30, hs31, hs32, hs40, hs41, hs42, hs43, hs50, hs51, hs52, hs53, hs54,
      h.d0, h.d1, h.d2, h.a01, h.a02, h.a03, h.a04, h.a12, h.a13] <;> ring

private theorem blocksTensor_row1 (K : Matrix (Fin 6) (Fin 6) ℝ) (h : EinsteinRelations K)
    (j : Fin 6) : matrixOf (blocksTensor K) 1 j = K 1 j := by
  have hs10 : K 1 0 = K 0 1 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 1) h.symmetric
  have hs20 : K 2 0 = K 0 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 2) h.symmetric
  have hs21 : K 2 1 = K 1 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 2) h.symmetric
  have hs30 : K 3 0 = K 0 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 3) h.symmetric
  have hs31 : K 3 1 = K 1 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 3) h.symmetric
  have hs32 : K 3 2 = K 2 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 3) h.symmetric
  have hs40 : K 4 0 = K 0 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 4) h.symmetric
  have hs41 : K 4 1 = K 1 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 4) h.symmetric
  have hs42 : K 4 2 = K 2 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 4) h.symmetric
  have hs43 : K 4 3 = K 3 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 4) h.symmetric
  have hs50 : K 5 0 = K 0 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 5) h.symmetric
  have hs51 : K 5 1 = K 1 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 5) h.symmetric
  have hs52 : K 5 2 = K 2 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 5) h.symmetric
  have hs53 : K 5 3 = K 3 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 5) h.symmetric
  have hs54 : K 5 4 = K 4 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 4 5) h.symmetric
  change blockTensor (plusFormula K) quaternionMatrix (pair 1).1 (pair 1).2
      (pair j).1 (pair j).2 +
    blockTensor (minusFormula K) oppositeMatrix (pair 1).1 (pair 1).2
      (pair j).1 (pair j).2 = K 1 j
  simp only [blockTensor_apply]
  fin_cases j <;>
    norm_num [pair,
      plusFormula, minusFormula, quaternionMatrix, oppositeMatrix, Geometry.oppositeQuaternion,
      Fin.sum_univ_succ, hs10, hs20, hs21, hs30, hs31, hs32, hs40, hs41, hs42, hs43, hs50, hs51, hs52, hs53, hs54,
      h.d0, h.d1, h.d2, h.a01, h.a02, h.a03, h.a04, h.a12, h.a13] <;> ring

private theorem blocksTensor_row2 (K : Matrix (Fin 6) (Fin 6) ℝ) (h : EinsteinRelations K)
    (j : Fin 6) : matrixOf (blocksTensor K) 2 j = K 2 j := by
  have hs10 : K 1 0 = K 0 1 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 1) h.symmetric
  have hs20 : K 2 0 = K 0 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 2) h.symmetric
  have hs21 : K 2 1 = K 1 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 2) h.symmetric
  have hs30 : K 3 0 = K 0 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 3) h.symmetric
  have hs31 : K 3 1 = K 1 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 3) h.symmetric
  have hs32 : K 3 2 = K 2 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 3) h.symmetric
  have hs40 : K 4 0 = K 0 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 4) h.symmetric
  have hs41 : K 4 1 = K 1 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 4) h.symmetric
  have hs42 : K 4 2 = K 2 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 4) h.symmetric
  have hs43 : K 4 3 = K 3 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 4) h.symmetric
  have hs50 : K 5 0 = K 0 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 5) h.symmetric
  have hs51 : K 5 1 = K 1 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 5) h.symmetric
  have hs52 : K 5 2 = K 2 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 5) h.symmetric
  have hs53 : K 5 3 = K 3 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 5) h.symmetric
  have hs54 : K 5 4 = K 4 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 4 5) h.symmetric
  change blockTensor (plusFormula K) quaternionMatrix (pair 2).1 (pair 2).2
      (pair j).1 (pair j).2 +
    blockTensor (minusFormula K) oppositeMatrix (pair 2).1 (pair 2).2
      (pair j).1 (pair j).2 = K 2 j
  simp only [blockTensor_apply]
  fin_cases j <;>
    norm_num [pair,
      plusFormula, minusFormula, quaternionMatrix, oppositeMatrix, Geometry.oppositeQuaternion,
      Fin.sum_univ_succ, hs10, hs20, hs21, hs30, hs31, hs32, hs40, hs41, hs42, hs43, hs50, hs51, hs52, hs53, hs54,
      h.d0, h.d1, h.d2, h.a01, h.a02, h.a03, h.a04, h.a12, h.a13] <;> ring

private theorem blocksTensor_row3 (K : Matrix (Fin 6) (Fin 6) ℝ) (h : EinsteinRelations K)
    (j : Fin 6) : matrixOf (blocksTensor K) 3 j = K 3 j := by
  have hs10 : K 1 0 = K 0 1 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 1) h.symmetric
  have hs20 : K 2 0 = K 0 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 2) h.symmetric
  have hs21 : K 2 1 = K 1 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 2) h.symmetric
  have hs30 : K 3 0 = K 0 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 3) h.symmetric
  have hs31 : K 3 1 = K 1 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 3) h.symmetric
  have hs32 : K 3 2 = K 2 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 3) h.symmetric
  have hs40 : K 4 0 = K 0 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 4) h.symmetric
  have hs41 : K 4 1 = K 1 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 4) h.symmetric
  have hs42 : K 4 2 = K 2 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 4) h.symmetric
  have hs43 : K 4 3 = K 3 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 4) h.symmetric
  have hs50 : K 5 0 = K 0 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 5) h.symmetric
  have hs51 : K 5 1 = K 1 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 5) h.symmetric
  have hs52 : K 5 2 = K 2 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 5) h.symmetric
  have hs53 : K 5 3 = K 3 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 5) h.symmetric
  have hs54 : K 5 4 = K 4 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 4 5) h.symmetric
  change blockTensor (plusFormula K) quaternionMatrix (pair 3).1 (pair 3).2
      (pair j).1 (pair j).2 +
    blockTensor (minusFormula K) oppositeMatrix (pair 3).1 (pair 3).2
      (pair j).1 (pair j).2 = K 3 j
  simp only [blockTensor_apply]
  fin_cases j <;>
    norm_num [pair,
      plusFormula, minusFormula, quaternionMatrix, oppositeMatrix, Geometry.oppositeQuaternion,
      Fin.sum_univ_succ, hs10, hs20, hs21, hs30, hs31, hs32, hs40, hs41, hs42, hs43, hs50, hs51, hs52, hs53, hs54,
      h.d0, h.d1, h.d2, h.a01, h.a02, h.a03, h.a04, h.a12, h.a13] <;> ring

private theorem blocksTensor_row4 (K : Matrix (Fin 6) (Fin 6) ℝ) (h : EinsteinRelations K)
    (j : Fin 6) : matrixOf (blocksTensor K) 4 j = K 4 j := by
  have hs10 : K 1 0 = K 0 1 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 1) h.symmetric
  have hs20 : K 2 0 = K 0 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 2) h.symmetric
  have hs21 : K 2 1 = K 1 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 2) h.symmetric
  have hs30 : K 3 0 = K 0 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 3) h.symmetric
  have hs31 : K 3 1 = K 1 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 3) h.symmetric
  have hs32 : K 3 2 = K 2 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 3) h.symmetric
  have hs40 : K 4 0 = K 0 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 4) h.symmetric
  have hs41 : K 4 1 = K 1 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 4) h.symmetric
  have hs42 : K 4 2 = K 2 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 4) h.symmetric
  have hs43 : K 4 3 = K 3 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 4) h.symmetric
  have hs50 : K 5 0 = K 0 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 5) h.symmetric
  have hs51 : K 5 1 = K 1 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 5) h.symmetric
  have hs52 : K 5 2 = K 2 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 5) h.symmetric
  have hs53 : K 5 3 = K 3 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 5) h.symmetric
  have hs54 : K 5 4 = K 4 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 4 5) h.symmetric
  change blockTensor (plusFormula K) quaternionMatrix (pair 4).1 (pair 4).2
      (pair j).1 (pair j).2 +
    blockTensor (minusFormula K) oppositeMatrix (pair 4).1 (pair 4).2
      (pair j).1 (pair j).2 = K 4 j
  simp only [blockTensor_apply]
  fin_cases j <;>
    norm_num [pair,
      plusFormula, minusFormula, quaternionMatrix, oppositeMatrix, Geometry.oppositeQuaternion,
      Fin.sum_univ_succ, hs10, hs20, hs21, hs30, hs31, hs32, hs40, hs41, hs42, hs43, hs50, hs51, hs52, hs53, hs54,
      h.d0, h.d1, h.d2, h.a01, h.a02, h.a03, h.a04, h.a12, h.a13] <;> ring

private theorem blocksTensor_row5 (K : Matrix (Fin 6) (Fin 6) ℝ) (h : EinsteinRelations K)
    (j : Fin 6) : matrixOf (blocksTensor K) 5 j = K 5 j := by
  have hs10 : K 1 0 = K 0 1 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 1) h.symmetric
  have hs20 : K 2 0 = K 0 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 2) h.symmetric
  have hs21 : K 2 1 = K 1 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 2) h.symmetric
  have hs30 : K 3 0 = K 0 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 3) h.symmetric
  have hs31 : K 3 1 = K 1 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 3) h.symmetric
  have hs32 : K 3 2 = K 2 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 3) h.symmetric
  have hs40 : K 4 0 = K 0 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 4) h.symmetric
  have hs41 : K 4 1 = K 1 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 4) h.symmetric
  have hs42 : K 4 2 = K 2 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 4) h.symmetric
  have hs43 : K 4 3 = K 3 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 4) h.symmetric
  have hs50 : K 5 0 = K 0 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 5) h.symmetric
  have hs51 : K 5 1 = K 1 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 5) h.symmetric
  have hs52 : K 5 2 = K 2 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 5) h.symmetric
  have hs53 : K 5 3 = K 3 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 5) h.symmetric
  have hs54 : K 5 4 = K 4 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 4 5) h.symmetric
  change blockTensor (plusFormula K) quaternionMatrix (pair 5).1 (pair 5).2
      (pair j).1 (pair j).2 +
    blockTensor (minusFormula K) oppositeMatrix (pair 5).1 (pair 5).2
      (pair j).1 (pair j).2 = K 5 j
  simp only [blockTensor_apply]
  fin_cases j <;>
    norm_num [pair,
      plusFormula, minusFormula, quaternionMatrix, oppositeMatrix, Geometry.oppositeQuaternion,
      Fin.sum_univ_succ, hs10, hs20, hs21, hs30, hs31, hs32, hs40, hs41, hs42, hs43, hs50, hs51, hs52, hs53, hs54,
      h.d0, h.d1, h.d2, h.a01, h.a02, h.a03, h.a04, h.a12, h.a13] <;> ring

theorem matrixOf_blocksTensor (K : Matrix (Fin 6) (Fin 6) ℝ) (h : EinsteinRelations K) :
    matrixOf (blocksTensor K) = K := by
  ext i j
  fin_cases i
  · exact blocksTensor_row0 K h j
  · exact blocksTensor_row1 K h j
  · exact blocksTensor_row2 K h j
  · exact blocksTensor_row3 K h j
  · exact blocksTensor_row4 K h j
  · exact blocksTensor_row5 K h j


theorem matrixOf_tensorOf (K : Matrix (Fin 6) (Fin 6) ℝ) : matrixOf (tensorOf K) = K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixOf, tensorOf, pair, pairSign, pairIndex]

theorem blockTensor_firstSkew (A : Mat3) (Q : Fin 3 → Mat4)
    (hQ : ∀ s, (Q s)ᵀ = -Q s) : FirstSkew (blockTensor A Q) := by
  intro i j k l
  have he (s : Fin 3) : Q s j i = -Q s i j :=
    congrArg (fun M : Mat4 => M i j) (hQ s)
  simp only [blockTensor_apply, he, mul_neg, neg_mul, Finset.sum_neg_distrib]

theorem blockTensor_lastSkew (A : Mat3) (Q : Fin 3 → Mat4)
    (hQ : ∀ s, (Q s)ᵀ = -Q s) : LastSkew (blockTensor A Q) := by
  intro i j k l
  have he (s : Fin 3) : Q s k l = -Q s l k :=
    congrArg (fun M : Mat4 => M l k) (hQ s)
  simp only [blockTensor_apply, he, mul_neg, Finset.sum_neg_distrib]

theorem blocksTensor_firstSkew (K : Matrix (Fin 6) (Fin 6) ℝ) : FirstSkew (blocksTensor K) := by
  intro i j k l
  change blockTensor (plusFormula K) quaternionMatrix j i k l +
      blockTensor (minusFormula K) oppositeMatrix j i k l = _
  rw [blockTensor_firstSkew _ _ quaternionMatrix_transpose,
    blockTensor_firstSkew _ _ QuaternionFrame.oppositeMatrix_transpose]
  simp only [blocksTensor, Pi.add_apply]
  ring

theorem blocksTensor_lastSkew (K : Matrix (Fin 6) (Fin 6) ℝ) : LastSkew (blocksTensor K) := by
  intro i j k l
  change blockTensor (plusFormula K) quaternionMatrix i j l k +
      blockTensor (minusFormula K) oppositeMatrix i j l k = _
  rw [blockTensor_lastSkew _ _ quaternionMatrix_transpose,
    blockTensor_lastSkew _ _ QuaternionFrame.oppositeMatrix_transpose]
  simp only [blocksTensor, Pi.add_apply]
  ring

theorem tensorOf_eq_blocksTensor (K : Matrix (Fin 6) (Fin 6) ℝ) (h : EinsteinRelations K) :
    tensorOf K = blocksTensor K := by
  apply tensor_eq_of_matrixOf_eq (tensorOf_firstSkew K) (tensorOf_lastSkew K)
    (blocksTensor_firstSkew K) (blocksTensor_lastSkew K)
  rw [matrixOf_tensorOf, matrixOf_blocksTensor K h]

/-- The Einstein block decomposition follows from ordinary algebraic
curvature symmetries and Ricci normalization, using the actual quaternion
contractions. No decomposition or sectional threshold is assumed. -/
theorem einstein_decomposition (R : CurvatureArray) (hf : FirstSkew R)
    (hl : LastSkew R) (hp : PairSymmetric R)
    (hr : ∀ j k, ricci R j k = if j = k then 3 else 0) :
    R = einsteinCurvatureTensor
      (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) quaternionMatrix - 1)
      (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) oppositeMatrix - 1) := by
  let K := matrixOf R
  have hn : tensorOf K = R := tensorOf_matrixOf hf hl
  have hk : EinsteinRelations K := einsteinRelations_of_ricci K (matrixOf_symmetric hp)
    (by intro j k; rw [hn]; exact hr j k)
  have hcplus : curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) quaternionMatrix =
      plusFormula K := by
    have hh := curvatureBlock_tensorOf K quaternionMatrix quaternionMatrix_transpose
    rw [plusFormula_eq] at hh
    simpa only [hn] using hh
  have hcminus : curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) oppositeMatrix =
      minusFormula K := by
    have hh := curvatureBlock_tensorOf K oppositeMatrix QuaternionFrame.oppositeMatrix_transpose
    rw [minusFormula_eq] at hh
    simpa only [hn] using hh
  calc
    R = tensorOf K := hn.symm
    _ = blocksTensor K := tensorOf_eq_blocksTensor K hk
    _ = _ := by
      rw [hcplus, hcminus]
      unfold blocksTensor einsteinCurvatureTensor
      have ha : (1 : Mat3) + (plusFormula K - 1) = plusFormula K := by abel
      have hb : (1 : Mat3) + (minusFormula K - 1) = minusFormula K := by abel
      rw [ha, hb]

theorem einstein_decomposition_of_bianchi (R : CurvatureArray) (hf : FirstSkew R)
    (hl : LastSkew R) (hb : FirstBianchi R)
    (hr : ∀ j k, ricci R j k = if j = k then 3 else 0) :
    R = einsteinCurvatureTensor
      (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) quaternionMatrix - 1)
      (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) oppositeMatrix - 1) :=
  einstein_decomposition R hf hl (pairSymmetric_of_bianchi hf hl hb) hr

theorem curvaturePairing_symmetric (R : CurvatureArray) (hf : FirstSkew R)
    (hl : LastSkew R) (hp : PairSymmetric R) (p q : Fin 4 × Fin 4) :
    R p.1 p.2 q.2 q.1 = R q.1 q.2 p.2 p.1 := by
  calc
    _ = R q.2 q.1 p.1 p.2 := (hp _ _ _ _).symm
    _ = -R q.1 q.2 p.1 p.2 := hf _ _ _ _
    _ = _ := by rw [hl]; simp

theorem curvatureBlock_sub_one_symmetric (R : CurvatureArray) (hf : FirstSkew R)
    (hl : LastSkew R) (hp : PairSymmetric R) (Q : Fin 3 → Mat4) :
    symmetric (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) Q - 1) := by
  have hh := curvatureBlock_symmetric (curvaturePairing_symmetric R hf hl hp) Q
  have ht : (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) Q - 1)ᵀ =
      curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) Q - 1 := by
    rw [Matrix.transpose_sub, hh, Matrix.transpose_one]
  intro i j
  exact congrArg (fun A : Mat3 => A j i) ht

end
end PositiveEinsteinFour.AlgebraicCurvature
end


section

/-! The refined Kato bound in an arbitrary orthonormal frame, including
the zero Weyl block. The pointwise spectral frame is constructed, and the
Bianchi condition is transported by its actual quaternion lift. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem blockRadialGradient_turn (R : Mat) (hR : R * Rᵀ = 1) (P : Mat4)
    (A : Mat) (Z : Angular.Gradient) :
    blockRadialGradient (conjugateMatrix R A) (turnGradient R P Z) =
      turnVector P (blockRadialGradient A Z) := by
  ext i
  simp only [blockRadialGradient, regularizedRadialDerivative, regularizedBlockNorm_zero,
    conjugateMatrix_norm R hR, trace_turnGradient R hR, turnVector,
    Matrix.mulVec, Matrix.transpose_apply, dotProduct, Finset.sum_div, mul_div_assoc]

theorem blockRadialGradient_diagonal (S : Shape) (v : ℝ)
    (Z : Angular.Gradient) :
    blockRadialGradient (Matrix.diagonal (fun a => v * S.s a)) Z =
      (v / normalizedBlockNorm (Matrix.diagonal (fun a => v * S.s a))) •
        radialCoordinate S (gradientTensor Z) := by
  ext i
  simp only [blockRadialGradient, regularizedRadialDerivative, regularizedBlockNorm_zero,
    Matrix.trace, Matrix.diagonal_mul, Matrix.diag_apply, radialCoordinate,
    gradientTensor, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  ring

/-- Refined Kato for the actual radial derivative of a symmetric
trace-free block. No nonvanishing or eigenframe premise is required. -/
theorem blockRadialGradient_refined_kato (A : Mat) (Z : Angular.Gradient)
    (hA : symmetric A) (htA : traceFree A)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0) :
    (5 / 3 : ℝ) * ‖blockRadialGradient A Z‖ ^ 2 ≤ weylGradientEnergy Z := by
  by_cases hv : normalizedBlockNorm A = 0
  · have hp : blockRadialGradient A Z = 0 := by
      ext i
      simp [blockRadialGradient, regularizedRadialDerivative,
        regularizedBlockNorm_zero, hv]
    rw [hp, norm_zero, zero_pow (by decide), mul_zero]
    unfold weylGradientEnergy matrixPairing
    apply div_nonneg _ (by norm_num)
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => mul_self_nonneg (Z i a b)
  have hvp : 0 < normalizedBlockNorm A :=
    lt_of_le_of_ne (normalizedBlockNorm_nonneg A) (Ne.symm hv)
  obtain ⟨R, hR, ⟨P⟩, S, hS⟩ := exists_lifted_spectral_shape A hA htA hvp
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  let W := turnGradient R P.matrix Z
  have hsW : ∀ i, symmetric (W i) := turnGradient_symmetric R P.matrix Z hs
  have htW : ∀ i, traceFree (W i) := turnGradient_traceFree R hR' P.matrix Z ht
  have hbW : ∀ r i, gradientDivergence W r i = 0 := turnGradient_bianchi R hR' P Z hb
  have hnorm : normalizedBlockNorm (Matrix.diagonal (fun i => normalizedBlockNorm A * S.s i)) =
      normalizedBlockNorm A := by
    rw [← hS]
    exact conjugateMatrix_norm R hR' A
  have hp : blockRadialGradient (conjugateMatrix R A) W =
      radialCoordinate S (gradientTensor W) := by
    rw [show conjugateMatrix R A = _ from hS,
      blockRadialGradient_diagonal S (normalizedBlockNorm A) W,
      hnorm, div_self hv, one_smul]
  have hk := refined_kato S (gradientTensor W)
    (gradientTensor_traceFree W htW) (gradientTensor_bianchi W hsW hbW)
  rw [gradientTensor_energy W hsW, ← hp] at hk
  have hnormeq : ‖blockRadialGradient (conjugateMatrix R A) W‖ ^ 2 =
      ‖blockRadialGradient A Z‖ ^ 2 := by
    rw [blockRadialGradient_turn R hR' P.matrix A Z,
      turnVector_norm P.matrix P.mul_transpose]
  rw [hnormeq, weylGradientEnergy_turn R hR' P.matrix P.mul_transpose] at hk
  exact hk

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The actual global Hessian inequality for the nonsmooth norm weight.
The limit is proved on the original Weyl tensors, including their zeros. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory Filter
open scoped BigOperators Topology Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem regularizedHessianIntegrand_eq_weight (g : SmoothMetric M) (ε : ℝ)
    (e : FrameBundle g) :
    regularizedHessianIntegrand g ε e =
      regularizedHessianWeight ε (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) (minusWeylGradient g e.base e.frame)
        (invariantHessianForm (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame))
        (fun i => -(5 / 36 : ℝ) * Matrix.trace (plusWeylGradient g e.base e.frame i *
          (∑ j, plusWeylGradient g e.base e.frame j * plusWeylGradient g e.base e.frame j)))
        (projectedWeightKernel (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
          (plusGradientTensor g e.base e.frame)) := by
  have hc := regularizedProjectionCost_eq_matrixWeight g ε e
  change regularizedWeylWeight ε _ _ * _ - (5 / 36 : ℝ) * _ +
    regularizedProjectionCost g ε e = _
  rw [hc]
  unfold regularizedHessianWeight
  congr 1
  rw [Finset.mul_sum]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

def invariantHessianField (d : MetricGreenData g μ) (o : OppositeWeylData d) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => invariantHessianForm (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
    (plusWeylGradient g e.base e.frame), by
      change Continuous (fun e =>
        (-42 - 3 * d.minusNormField o e ^ 2 - (10 / 3 : ℝ) * d.plusNormField e ^ 2) *
          d.gradientEnergyField e + 75 * d.matrixEnergyField e +
          (25 / 3 : ℝ) * d.squareEnergyField e -
          (100 / 3 : ℝ) * d.compressionEnergyField e + 5 * d.radialEnergyField e)
      fun_prop⟩

def cubicEntryField (d : MetricGreenData g μ) (i : Fin 4) : C(FrameBundle g, ℝ) :=
  ⟨fun e => -(5 / 36 : ℝ) * Matrix.trace (d.gradientMap e i *
    (∑ j, d.gradientMap e j * d.gradientMap e j)), by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.sum_apply]
      fun_prop⟩

theorem integral_regularizedHessian_tendsto (d : MetricGreenData g μ) (o : OppositeWeylData d)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (he : ∀ n, ε n ≤ 1 / 3)
    (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ e, regularizedHessianIntegrand g (ε n) e ∂μ) atTop
      (𝓝 (∫ e, regularizedHessianIntegrand g 0 e ∂μ)) := by
  simp_rw [regularizedHessianIntegrand_eq_weight]
  exact integral_regularizedHessianWeight_tendsto μ _ _ _ _ _ _ _
    d.continuousWeyl o.continuousWeyl d.continuousGradient o.continuousGradient
    (d.invariantHessianField o).continuous (fun i => (d.cubicEntryField i).continuous)
    (d.continuousProjectedWeightKernel o)
    (fun i e => (d.gradientConstraints e).1 i)
    (fun i e => (o.gradientConstraints e).1 i) hpinch ε hε he hlim

/-- The nonsmooth norm weight satisfies the actual integrated Hessian
inequality. No positivity of either Weyl norm is required. -/
theorem unregularizedHessianGreen (d : MetricGreenData g μ) (o : OppositeWeylData d)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    0 ≤ ∫ e, regularizedHessianIntegrand g 0 e ∂μ := by
  let ε : ℕ → ℝ := fun n => (1 / 3 : ℝ) * (1 / ((n : ℝ) + 1))
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  have he (n) : ε n ≤ 1 / 3 := by
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    have hi : 1 / ((n : ℝ) + 1) ≤ (1 : ℝ) := by
      exact (div_le_one (by positivity)).mpr hn
    dsimp [ε]
    nlinarith
  have hlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 3 : ℝ)
  exact ge_of_tendsto' (d.integral_regularizedHessian_tendsto o hpinch ε hε he hlim)
    (fun n => d.regularizedHessianGreen o hp hdecomp hpinch (ε n) (hε n) (he n))

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Almost-everywhere support of the norm gradient on the actual frame
bundle. A fixed positive regularization allows the level-set argument
to use ordinary smooth derivatives at every point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff

noncomputable section

local instance radialLevelNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance radialLevelNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance radialLevelNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

private theorem regularizedRadial_zero_implies (A Z : Mat)
    (h : regularizedRadialDerivative 1 A Z = 0) :
    regularizedRadialDerivative 0 A Z = 0 := by
  have hn : 6 * regularizedBlockNorm 1 A ≠ 0 := by
    unfold regularizedBlockNorm
    positivity
  have ht : Matrix.trace (A * Z) = 0 := by
    unfold regularizedRadialDerivative at h
    exact (div_eq_zero_iff.mp h).resolve_right hn
  simp only [regularizedRadialDerivative, ht, zero_div]

private theorem radial_zero_ae_on_level
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    (μ : Measure Ω) [SFinite μ]
    (φ : Fin 4 → ℝ → Ω ≃ᵐ Ω)
    (hφ : ∀ i, Continuous (fun p : ℝ × Ω => φ i p.1 p.2))
    (hpres : ∀ i t, MeasurePreserving (φ i t) μ μ)
    (A : Ω → Mat) (Z : Fin 4 → Ω → Mat)
    (hA : Continuous A) (hZ : ∀ i, Continuous (Z i))
    (hs : ∀ x, TraceHessian.symmetric (A x))
    (hd : ∀ i t x, HasDerivAt (fun s => A (φ i s x)) (Z i (φ i t x)) t)
    (c : ℝ) :
    ∀ᵐ x ∂μ, normalizedBlockNorm (A x) = c →
      blockRadialGradient (A x) (fun i => Z i x) = 0 := by
  have hi (i : Fin 4) := ae_flow_derivative_zero_on_level μ (φ i) (hφ i) (hpres i)
    (fun x => regularizedBlockNorm 1 (A x))
    (fun x => regularizedRadialDerivative 1 (A x) (Z i x))
    ((continuous_regularizedBlockNorm 1).comp hA)
    (continuous_regularizedRadialDerivative 1 (by norm_num) A (Z i) hA (hZ i))
    (fun t x => hasDerivAt_regularizedBlockNorm (hd i t x)
      (fun s => hs (φ i s x)) (by norm_num))
    (Real.sqrt (c ^ 2 + 1))
  have hall := ae_all_iff.mpr hi
  filter_upwards [hall] with x hx
  intro hc
  ext i
  change regularizedRadialDerivative 0 (A x) (Z i x) = 0
  apply regularizedRadial_zero_implies
  apply hx i
  simp only [regularizedBlockNorm, hc, one_pow]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)} [SFinite μ]

theorem MetricGreenData.radial_zero_ae_on_level (d : MetricGreenData g μ) (c : ℝ) :
    ∀ᵐ e ∂μ, normalizedBlockNorm (plusWeyl g e.base e.frame) = c →
      blockRadialGradient (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) = 0 :=
  PositiveEinsteinFour.Geometry.radial_zero_ae_on_level μ (fun i => (d.flow i).map)
    (fun i => (d.flow i).continuous) (fun i => (d.flow i).preserves)
    _ _ d.continuousWeyl d.continuousGradient d.weyl.symmetric d.derivativeWeyl c

theorem OppositeWeylData.radial_zero_ae_on_level {d : MetricGreenData g μ}
    (o : OppositeWeylData d) (c : ℝ) :
    ∀ᵐ e ∂μ, normalizedBlockNorm (minusWeyl g e.base e.frame) = c →
      blockRadialGradient (minusWeyl g e.base e.frame)
        (minusWeylGradient g e.base e.frame) = 0 :=
  PositiveEinsteinFour.Geometry.radial_zero_ae_on_level μ (fun i => (d.flow i).map)
    (fun i => (d.flow i).continuous) (fun i => (d.flow i).preserves)
    _ _ o.continuousWeyl o.continuousGradient o.symmetric o.derivativeWeyl c

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identify the scalar-Hessian matrix operator with the actual
four-index curvature coefficient used in integration by parts. -/

namespace PositiveEinsteinFour.ScalarHessian

open scoped BigOperators
open Matrix TraceHessian Angular CurvatureContraction

noncomputable section

private theorem sum_four_swap {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  have h := (Equiv.prodComm (α × β) (γ × δ)).sum_comp
    (fun p : (γ × δ) × (α × β) => f p.2.1 p.2.2 p.1.1 p.1.2)
  simpa only [Fintype.sum_prod_type, Equiv.prodComm_apply, Prod.swap_prod_mk] using h

theorem blockAction_entry (Q : Fin 3 → Matrix4)
    (hQ : ∀ r, (Q r)ᵀ = -Q r) (A : Mat) (S : Matrix4) (i j : Fin 4) :
    blockAction Q A S i j =
      ∑ k, ∑ l, generalCoefficient Q A i k j l * S k l := by
  have hskew (r : Fin 3) (a b : Fin 4) : Q r a b = -Q r b a := by
    have h := congrArg (fun M : Matrix4 => M b a) (hQ r)
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using h
  have hmul (r s : Fin 3) : (Q r * S * Q s) i j =
      -(∑ k, ∑ l, Q r i k * Q s j l * S k l) := by
    calc
      _ = ∑ k, ∑ l, Q r i k * S k l * Q s l j := by
        simp only [Matrix.mul_apply, Finset.sum_mul]
        exact Finset.sum_comm
      _ = ∑ k, ∑ l, -(Q r i k * Q s j l * S k l) := by
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        rw [hskew s l j]
        ring
      _ = _ := by simp only [Finset.sum_neg_distrib]
  change (-(1 / 2 : ℝ) • ∑ r, ∑ s, A r s • (Q r * S * Q s)) i j = _
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, hmul,
    mul_neg, Finset.sum_neg_distrib, neg_mul, neg_neg]
  calc
    _ = (1 / 2 : ℝ) * ∑ r, ∑ s, ∑ k, ∑ l, A r s * Q r i k * Q s j l * S k l := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = (1 / 2 : ℝ) * ∑ k, ∑ l, ∑ r, ∑ s, A r s * Q r i k * Q s j l * S k l := by
      rw [sum_four_swap]
    _ = _ := by
      simp only [generalCoefficient, Finset.mul_sum, Finset.sum_mul, mul_assoc]

/-- The row of the four-index operator is `(i,j)` and the column `(k,l)`. -/
def blockQuadratic (Q : Fin 3 → Matrix4) (A : Mat) (S : Matrix4) : ℝ :=
  ∑ i, ∑ k, ∑ j, ∑ l, generalCoefficient Q A i k j l * S i j * S k l

theorem blockQuadratic_eq_pairing (Q : Fin 3 → Matrix4)
    (hQ : ∀ r, (Q r)ᵀ = -Q r) (A : Mat) (S : Matrix4) :
    blockQuadratic Q A S = scalarPairing (blockAction Q A S) S := by
  symm
  unfold scalarPairing
  simp_rw [blockAction_entry Q hQ, Finset.sum_mul]
  calc
    _ = ∑ i, ∑ k, ∑ j, ∑ l, (generalCoefficient Q A i k j l * S k l) * S i j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      unfold blockQuadratic
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      ring

theorem scalarHessian_coefficient_bound (A U : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (x y : ℝ) (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2)
    (S : Matrix4) (hS : Sᵀ = S) (htS : Matrix.trace S = 0) :
    blockQuadratic quaternionMatrix A S + blockQuadratic oppositeMatrix U S ≤
      4 * scalarNormSq S := by
  rw [blockQuadratic_eq_pairing quaternionMatrix quaternionMatrix_transpose,
    blockQuadratic_eq_pairing oppositeMatrix QuaternionFrame.oppositeMatrix_transpose]
  exact scalarHessian_operator_bound A U hA hU htA htU x y hAx hUy hxy S hS htS

end
end PositiveEinsteinFour.ScalarHessian
end


section

/-! The scalar trace of each quaternion curvature block is fixed by the
Einstein contraction and the first Bianchi identity. -/

namespace PositiveEinsteinFour.AlgebraicCurvature

open Matrix TraceHessian Angular
open PositiveEinsteinFour.Geometry (curvatureBlock curvatureBlock_symmetric)
open scoped BigOperators

noncomputable section

theorem weyl_blocks_traceFree (R : CurvatureArray) (hf : FirstSkew R)
    (hl : LastSkew R) (hb : FirstBianchi R)
    (hr : ∀ j k, ricci R j k = if j = k then 3 else 0) :
    traceFree (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) quaternionMatrix - 1) ∧
      traceFree (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) oppositeMatrix - 1) := by
  let K := matrixOf R
  have hn : tensorOf K = R := tensorOf_matrixOf hf hl
  have hs : Kᵀ = K := matrixOf_symmetric (pairSymmetric_of_bianchi hf hl hb)
  have hK : EinsteinRelations K := einsteinRelations_of_ricci K hs
    (by intro j k; rw [hn]; exact hr j k)
  have hs50 : K 5 0 = K 0 5 := congrArg (fun A => A 0 5) hs
  have hs41 : K 4 1 = K 1 4 := congrArg (fun A => A 1 4) hs
  have hs32 : K 3 2 = K 2 3 := congrArg (fun A => A 2 3) hs
  have hzero := hr 0 0
  have hcycle := hb 0 1 2 3
  rw [← hn] at hzero hcycle
  norm_num [ricci, tensorOf, pairIndex, pairSign, Fin.sum_univ_succ] at hzero
  norm_num [tensorOf, pairIndex, pairSign, hs32] at hcycle
  have hcplus : curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) quaternionMatrix =
      plusFormula K := by
    have hh := curvatureBlock_tensorOf K quaternionMatrix quaternionMatrix_transpose
    rw [plusFormula_eq] at hh
    simpa only [hn] using hh
  have hcminus : curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) oppositeMatrix =
      minusFormula K := by
    have hh := curvatureBlock_tensorOf K oppositeMatrix QuaternionFrame.oppositeMatrix_transpose
    rw [minusFormula_eq] at hh
    simpa only [hn] using hh
  rw [hcplus, hcminus]
  constructor
  · change (∑ i : Fin 3, (plusFormula K i i - (1 : Mat3) i i)) = 0
    norm_num [Matrix.one_apply, Fin.sum_univ_three,
      plusFormula, hK.d0, hK.d1, hK.d2, hs50, hs41, hs32]
    linarith only [hzero, hcycle]
  · change (∑ i : Fin 3, (minusFormula K i i - (1 : Mat3) i i)) = 0
    norm_num [Matrix.one_apply, Fin.sum_univ_three,
      minusFormula, hK.d0, hK.d1, hK.d2, hs50, hs41, hs32]
    linarith only [hzero, hcycle]

end
end PositiveEinsteinFour.AlgebraicCurvature
end


section

/-! Contracting the differential Bianchi identity, with the same index
convention as the actual frame Ricci tensor. -/

namespace PositiveEinsteinFour.AlgebraicCurvature

open Angular
open scoped BigOperators

noncomputable section

def DifferentialBianchi (D : Fin 4 → CurvatureArray) : Prop :=
  ∀ a i j k l, D a i j k l + D i j a k l + D j a i k l = 0

theorem divergence_eq_ricci_derivatives (D : Fin 4 → CurvatureArray)
    (hp : ∀ a, PairSymmetric (D a)) (hl : ∀ a, LastSkew (D a))
    (hb : DifferentialBianchi D) (j k l : Fin 4) :
    (∑ i, D i i j k l) = -(∑ i, D k i j l i) + ∑ i, D l i k j i := by
  have he (i : Fin 4) : D i i j k l = -D k i j l i + D l i k j i := by
    have h := hb i k l i j
    rw [hp i i j k l, hp k i j l i, hl l i k j i] at h
    linarith only [h]
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem divergence_zero_of_ricci_parallel (D : Fin 4 → CurvatureArray)
    (hp : ∀ a, PairSymmetric (D a)) (hl : ∀ a, LastSkew (D a))
    (hb : DifferentialBianchi D)
    (hRic : ∀ a j k, ∑ i, D a i j k i = 0) (j k l : Fin 4) :
    (∑ i, D i i j k l) = 0 := by
  rw [divergence_eq_ricci_derivatives D hp hl hb, hRic k j l, hRic l k j]
  simp

end
end PositiveEinsteinFour.AlgebraicCurvature

namespace PositiveEinsteinFour.Geometry

open Matrix
open scoped BigOperators

noncomputable section

def curvatureDerivativeArray (T : CovariantCoordinates 5) :
    Fin 4 → Angular.CurvatureArray := fun a i j k l => T ![a, i, j, k, l]

private def bianchiCycle : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 0, 3, 4]
  invFun := ![2, 0, 1, 3, 4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private theorem frameTensor_precompose_five (A : Mat4) (T : CovariantCoordinates 5)
    (σ : Equiv.Perm (Fin 5)) (a : Fin 5 → Fin 4) :
    frameTensor A T (a ∘ σ) = frameTensor A (fun b => T (b ∘ σ)) a := by
  let e : (Fin 5 → Fin 4) ≃ (Fin 5 → Fin 4) :=
    Equiv.arrowCongr σ.symm (Equiv.refl (Fin 4))
  unfold frameTensor
  calc
    _ = ∑ b : Fin 5 → Fin 4,
        (∏ i, A (e b i) ((a ∘ σ) i)) * T (e b) :=
      (e.sum_comp (fun b => (∏ i, A (b i) ((a ∘ σ) i)) * T b)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      change (∏ i, A (b (σ i)) (a (σ i))) * T (b ∘ σ) = _
      rw [Equiv.prod_comp σ (fun i => A (b i) (a i))]

/-- The cyclic differential identity is preserved by the actual tensor
pullback; no orthogonality or frame-flow premise is required. -/
theorem frameTensor_differentialBianchi (A : Mat4) (T : CovariantCoordinates 5)
    (h : AlgebraicCurvature.DifferentialBianchi (curvatureDerivativeArray T)) :
    AlgebraicCurvature.DifferentialBianchi (curvatureDerivativeArray (frameTensor A T)) := by
  have hc (b : Fin 5 → Fin 4) :
      T b + T (b ∘ bianchiCycle) + T (b ∘ (bianchiCycle.trans bianchiCycle)) = 0 := by
    have hb : b = ![b 0, b 1, b 2, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    have h1 : b ∘ bianchiCycle = ![b 1, b 2, b 0, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    have h2 : b ∘ (bianchiCycle.trans bianchiCycle) =
        ![b 2, b 0, b 1, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    rw [h1, h2, hb]
    exact h _ _ _ _ _
  intro a i j k l
  let v : Fin 5 → Fin 4 := ![a, i, j, k, l]
  have h1 : v ∘ bianchiCycle = ![i, j, a, k, l] := by
    funext s
    fin_cases s <;> rfl
  have h2 : v ∘ (bianchiCycle.trans bianchiCycle) = ![j, a, i, k, l] := by
    funext s
    fin_cases s <;> rfl
  have hh : frameTensor A T v + frameTensor A T (v ∘ bianchiCycle) +
      frameTensor A T (v ∘ (bianchiCycle.trans bianchiCycle)) = 0 := by
    rw [frameTensor_precompose_five A T bianchiCycle v,
      frameTensor_precompose_five A T (bianchiCycle.trans bianchiCycle) v]
    unfold frameTensor
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro b _
    linear_combination (∏ s, A (b s) (v s)) * hc b
  rw [h1, h2] at hh
  exact hh

end
end PositiveEinsteinFour.Geometry
end


section

/-! The opposite Bianchi triple becomes the positive triple after
reflecting only the derivative index. This gives the same invariant Kato
bound for the actual opposite Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

def orientationSign (i : Fin 4) : ℝ := if i = 0 then -1 else 1

theorem orientationSign_sq (i : Fin 4) : orientationSign i ^ 2 = 1 := by
  unfold orientationSign
  split_ifs <;> norm_num

def reflectedGradient (Z : Angular.Gradient) : Angular.Gradient :=
  fun i => orientationSign i • Z i

theorem reflectedGradient_divergence (Z : Angular.Gradient) (r : Fin 3) (i : Fin 4) :
    gradientDivergence (reflectedGradient Z) r i = orientationSign i *
      ∑ s, ∑ j, Angular.oppositeMatrix s i j * Z j s r := by
  simp only [gradientDivergence, reflectedGradient, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro j _
  unfold Angular.oppositeMatrix oppositeQuaternion orientationSign
  split_ifs <;> ring

theorem reflectedGradient_energy (Z : Angular.Gradient) :
    weylGradientEnergy (reflectedGradient Z) = weylGradientEnergy Z := by
  unfold weylGradientEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  unfold matrixPairing
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [reflectedGradient, Matrix.smul_apply, smul_eq_mul]
  calc
    _ = orientationSign i ^ 2 * (Z i a b * Z i a b) := by ring
    _ = _ := by rw [orientationSign_sq, one_mul]

theorem reflectedGradient_radial_norm (A : Mat) (Z : Angular.Gradient) :
    ‖blockRadialGradient A (reflectedGradient Z)‖ ^ 2 = ‖blockRadialGradient A Z‖ ^ 2 := by
  have hp (i : Fin 4) : regularizedRadialDerivative 0 A (reflectedGradient Z i) =
      orientationSign i * regularizedRadialDerivative 0 A (Z i) := by
    simp only [reflectedGradient, regularizedRadialDerivative, Matrix.mul_smul,
      Matrix.trace_smul, smul_eq_mul]
    ring
  simp only [EuclideanSpace.real_norm_sq_eq]
  change (∑ i, regularizedRadialDerivative 0 A (reflectedGradient Z i) ^ 2) =
    ∑ i, regularizedRadialDerivative 0 A (Z i) ^ 2
  apply Finset.sum_congr rfl
  intro i _
  rw [hp, mul_pow, orientationSign_sq, one_mul]

theorem opposite_refinedKato (A : Mat) (Z : Angular.Gradient)
    (hA : symmetric A) (htA : traceFree A)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, (∑ s, ∑ j, Angular.oppositeMatrix s i j * Z j s r) = 0) :
    (5 / 3 : ℝ) * ‖blockRadialGradient A Z‖ ^ 2 ≤ weylGradientEnergy Z := by
  have hs' (i) : symmetric (reflectedGradient Z i) := by
    intro a b
    simp only [reflectedGradient, Matrix.smul_apply, smul_eq_mul, hs i a b]
  have ht' (i) : traceFree (reflectedGradient Z i) := by
    change (∑ a, orientationSign i * Z i a a) = 0
    rw [← Finset.mul_sum, ht, mul_zero]
  have hb' (r i) : gradientDivergence (reflectedGradient Z) r i = 0 := by
    rw [reflectedGradient_divergence, hb, mul_zero]
  have h := QuaternionFrame.blockRadialGradient_refined_kato A (reflectedGradient Z)
    hA htA hs' ht' hb'
  rwa [reflectedGradient_energy, reflectedGradient_radial_norm] at h

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem OppositeWeylData.refinedKato {d : MetricGreenData g μ} (o : OppositeWeylData d)
    (e : FrameBundle g) :
    (5 / 3 : ℝ) * ‖blockRadialGradient (minusWeyl g e.base e.frame)
      (minusWeylGradient g e.base e.frame)‖ ^ 2 ≤
        weylGradientEnergy (minusWeylGradient g e.base e.frame) :=
  opposite_refinedKato _ _ (o.symmetric e) (o.traceFree e)
    (o.gradientConstraints e).1 (o.gradientConstraints e).2 (o.gradientBianchi e)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The refined Kato contraction estimate without division by the
norm of the symmetric trace-free matrix. -/

namespace PositiveEinsteinFour.Geometry

open TraceHessian QuaternionFrame
open scoped BigOperators

noncomputable section

/-- The invariant radial Kato estimate gives a polynomial contraction
bound, including at the zero matrix. -/
theorem refined_kato_matrixPairing (A : Mat) (Z : Fin 4 → Mat)
    (hA : symmetric A) (htA : traceFree A)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0) :
    (∑ i, matrixPairing A (Z i) ^ 2) ≤
      (3 / 5 : ℝ) * matrixPairing A A * ∑ i, matrixPairing (Z i) (Z i) := by
  have htrace (i : Fin 4) : matrixPairing A (Z i) = Matrix.trace (A * Z i) := by
    have htranspose : Matrix.transpose (Z i) = Z i := by
      ext a b
      exact hs i b a
    rw [matrixPairing_eq_trace, htranspose]
  have hrad : (∑ i, matrixPairing A (Z i) ^ 2) / 36 =
      normalizedBlockNorm A ^ 2 * ‖blockRadialGradient A Z‖ ^ 2 := by
    simpa only [weylRadialSquare, htrace] using weylRadialSquare_eq A Z
  have hk := mul_le_mul_of_nonneg_left
    (blockRadialGradient_refined_kato A Z hA htA hs ht hb)
    (sq_nonneg (normalizedBlockNorm A))
  have henergy : (∑ i, matrixPairing (Z i) (Z i)) = 6 * weylGradientEnergy Z := by
    unfold weylGradientEnergy
    ring
  rw [matrixPairing_self_norm, henergy]
  nlinarith only [hrad, hk]

/-- Coordinate form of the refined Kato contraction estimate. The
off-diagonal entries have their full Frobenius multiplicity. -/
theorem refined_kato_contraction (A : Mat) (Z : Fin 4 → Mat)
    (hA : symmetric A) (htA : traceFree A)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0) :
    (∑ i, (∑ a, ∑ b, A a b * Z i a b) ^ 2) ≤
      (3 / 5 : ℝ) * (∑ a, ∑ b, A a b ^ 2) *
        ∑ i, ∑ a, ∑ b, Z i a b ^ 2 := by
  simpa only [matrixPairing, ← pow_two] using
    refined_kato_matrixPairing A Z hA htA hs ht hb

end
end PositiveEinsteinFour.Geometry
end


section

/-! The regularized scalar Weyl equation follows from ordinary derivatives
of the actual block and its proved matrix Laplacian. Test functions are
arbitrary smooth flow weights, ready for the polynomial coupling test. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance normEquationNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance normEquationNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance normEquationNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

def regularizedRadialSecond (ε : ℝ) (A Z X : Mat) : ℝ :=
  (Matrix.trace (Z * Z + A * X) / 6 - regularizedRadialDerivative ε A Z ^ 2) /
    regularizedBlockNorm ε A

theorem hasDerivAt_regularizedRadialDerivative
    {A Z : ℝ → Mat} {X : Mat} {t ε : ℝ}
    (hA : HasDerivAt A (Z t) t) (hZ : HasDerivAt Z X t)
    (hs : ∀ s, TraceHessian.symmetric (A s)) (hε : 0 < ε) :
    HasDerivAt (fun s => regularizedRadialDerivative ε (A s) (Z s))
      (regularizedRadialSecond ε (A t) (Z t) X) t := by
  have hn := regularizedBlockNorm_pos ε hε (A t)
  have hd := ((hasDerivAt_matrixTrace (hA.mul hZ)).div_const 6).div
    (hasDerivAt_regularizedBlockNorm hA hs hε) (ne_of_gt hn)
  convert! hd using 1
  · funext s
    change regularizedRadialDerivative ε (A s) (Z s) =
      Matrix.trace (A s * Z s) / 6 / regularizedBlockNorm ε (A s)
    unfold regularizedRadialDerivative
    ring
  · unfold regularizedRadialSecond regularizedRadialDerivative
    change _ = (Matrix.trace (Z t * Z t + A t * X) / 6 * regularizedBlockNorm ε (A t) -
      Matrix.trace (A t * Z t) / 6 *
        (Matrix.trace (A t * Z t) / (6 * regularizedBlockNorm ε (A t)))) /
      regularizedBlockNorm ε (A t) ^ 2
    field_simp [ne_of_gt hn]

theorem continuous_regularizedRadialSecond {Ω : Type*} [TopologicalSpace Ω]
    (ε : ℝ) (hε : 0 < ε) (A Z X : Ω → Mat)
    (hA : Continuous A) (hZ : Continuous Z) (hX : Continuous X) :
    Continuous (fun x => regularizedRadialSecond ε (A x) (Z x) (X x)) := by
  exact (((matrixTraceMap.continuous.comp ((hZ.mul hZ).add (hA.mul hX))).div_const 6).sub
    ((continuous_regularizedRadialDerivative ε hε A Z hA hZ).pow 2)).div
      ((continuous_regularizedBlockNorm ε).comp hA)
      (fun x => ne_of_gt (regularizedBlockNorm_pos ε hε (A x)))

theorem regularizedRadialSecond_sum (ε : ℝ) (A : Mat) (Z : Fin 4 → Mat) (X : Hessian)
    (hZ : ∀ i, TraceHessian.symmetric (Z i)) (hX : hessianTrace X = weylLaplacian A) :
    (∑ i, regularizedRadialSecond ε A (Z i) (X i i)) =
      (weylGradientEnergy Z + Matrix.trace (A * weylLaplacian A) / 6 -
        (∑ i, regularizedRadialDerivative ε A (Z i) ^ 2)) / regularizedBlockNorm ε A := by
  have hs (i : Fin 4) : Matrix.trace (Z i * Z i) = matrixPairing (Z i) (Z i) := by
    rw [matrixPairing_eq_trace]
    congr 2
    ext a b
    exact hZ i a b
  have hx : (∑ i, Matrix.trace (A * X i i)) = Matrix.trace (A * weylLaplacian A) := by
    rw [← Matrix.trace_sum, ← Matrix.mul_sum]
    exact congrArg (fun Q => Matrix.trace (A * Q)) hX
  unfold regularizedRadialSecond
  rw [← Finset.sum_div]
  congr 1
  simp only [Matrix.trace_add, add_div, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.sum_div, hs, hx, weylGradientEnergy]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

def regularizedNormField (d : MetricGreenData g μ) (ε : ℝ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => regularizedBlockNorm ε (plusWeyl g e.base e.frame),
    (continuous_regularizedBlockNorm ε).comp d.continuousWeyl⟩

def regularizedRadialField (d : MetricGreenData g μ) (ε : ℝ) (hε : 0 < ε) (i : Fin 4) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => regularizedRadialDerivative ε (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i),
    continuous_regularizedRadialDerivative ε hε _ _ d.continuousWeyl (d.continuousGradient i)⟩

def regularizedSecondField (d : MetricGreenData g μ) (ε : ℝ) (hε : 0 < ε) (i : Fin 4) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => regularizedRadialSecond ε (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i) (plusWeylHessian g e.base e.frame i i),
    continuous_regularizedRadialSecond ε hε _ _ _ d.continuousWeyl
      (d.continuousGradient i) (d.continuousHessian i i)⟩

theorem regularizedRadialField_derivative (d : MetricGreenData g μ)
    (ε : ℝ) (hε : 0 < ε) (i : Fin 4) (t : ℝ) (e : FrameBundle g) :
    HasDerivAt (fun s => d.regularizedRadialField ε hε i ((d.flow i).map s e))
      (d.regularizedSecondField ε hε i ((d.flow i).map t e)) t :=
  hasDerivAt_regularizedRadialDerivative (d.derivativeWeyl i t e)
    (d.derivativeGradient i i t e) (fun s => d.weyl.symmetric ((d.flow i).map s e)) hε

/-- The weak scalar norm equation at positive regularization. Its matrix
Laplacian term is fixed by the proved Bianchi commutator equation. -/
theorem testedRegularizedNormEquation (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (ε : ℝ) (hε : 0 < ε) (k : C(FrameBundle g, ℝ))
    (dk : Fin 4 → C(FrameBundle g, ℝ))
    (hk : ∀ i t e, HasDerivAt (fun s => k ((d.flow i).map s e))
      (dk i ((d.flow i).map t e)) t) :
    (∫ e, k e * ((weylGradientEnergy (plusWeylGradient g e.base e.frame) +
        Matrix.trace (plusWeyl g e.base e.frame * weylLaplacian (plusWeyl g e.base e.frame)) / 6 -
        ∑ i, (d.regularizedRadialField ε hε i e) ^ 2) / d.regularizedNormField ε e) +
      ∑ i, dk i e * d.regularizedRadialField ε hε i e ∂μ) = 0 := by
  let P := d.regularizedRadialField ε hε
  let Q := d.regularizedSecondField ε hε
  let F : Fin 4 → C(FrameBundle g, ℝ) := fun i => k * P i
  let D : Fin 4 → C(FrameBundle g, ℝ) := fun i => dk i * P i + k * Q i
  have hd (i) : (∫ e, D i e ∂μ) = 0 := by
    apply Averages.integral_flow_derivative_zero μ (d.flow i).map
      (d.flow i).continuous (d.flow i).preserves (F i) (D i)
    intro t e
    exact (hk i t e).mul (d.regularizedRadialField_derivative ε hε i t e)
  have hi (i : Fin 4) : Integrable (fun e => D i e) μ :=
    (D i).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsum : (∫ e, ∑ i, D i e ∂μ) = 0 := by
    rw [integral_finsetSum _ (fun i _ => hi i)]
    simp only [hd, Finset.sum_const_zero]
  convert hsum using 1
  apply integral_congr_ae
  filter_upwards [] with e
  have heq := regularizedRadialSecond_sum ε (plusWeyl g e.base e.frame)
    (plusWeylGradient g e.base e.frame) (plusWeylHessian g e.base e.frame)
    (d.gradientConstraints e).1 (metric_weyl_trace g d.weyl e)
  change k e * _ + (∑ i, dk i e * P i e) =
    ∑ i, (dk i e * P i e + k e * Q i e)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  change (∑ i, Q i e) = _ at heq
  rw [heq]
  dsimp only [regularizedNormField, regularizedRadialField, ContinuousMap.coe_mk]
  ring

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The integrated scalar-Hessian curvature identity. The only
differential inputs are the raw scalar and Weyl parallel-frame derivatives
and Ricci commutator. Coefficient divergence and the exact contraction are
proved from the Bianchi equation and the finite-dimensional calculations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Bianchi CurvatureContraction ScalarHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance scalarIdentityRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance scalarIdentitySpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance scalarIdentityAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

theorem scalar_block_quadratic_tuple (A U : Mat) (H : Mat4) :
    (∑ p : Averages.CurvatureIndex,
      (generalCoefficient quaternionMatrix A p.1.1 p.1.2 p.2.1 p.2.2 +
        generalCoefficient Angular.oppositeMatrix U p.1.1 p.1.2 p.2.1 p.2.2) *
          (H p.1.2 p.2.2 * H p.1.1 p.2.1)) =
      blockQuadratic quaternionMatrix A H + blockQuadratic Angular.oppositeMatrix U H := by
  simp only [blockQuadratic, Fintype.sum_prod_type, mul_add, Finset.sum_add_distrib,
    mul_assoc, mul_comm, mul_left_comm]

theorem scalar_curvature_contraction_commuted (A U : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (p : Bianchi.Vec) :
    (1 / 2 : ℝ) * (∑ q : Averages.CurvatureIndex,
      (generalCoefficient quaternionMatrix A q.1.1 q.1.2 q.2.1 q.2.2 +
        generalCoefficient Angular.oppositeMatrix U q.1.1 q.1.2 q.2.1 q.2.2) *
          (p q.2.2 * ∑ l, generalEinsteinCoefficient A U q.1.1 q.1.2 q.2.1 l * p l)) =
      3 * (normalizedBlockNorm A ^ 2 + normalizedBlockNorm U ^ 2) * ‖p‖ ^ 2 := by
  have h := scalarCurvatureContraction_tuple A U p
  rw [scalarCurvatureContraction_eq A U hA hU htA htU p] at h
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ} [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
  {a : M → ℝ}

omit [CompactSpace (FrameBundle g)] in
theorem scalarGradientVector_apply (e : FrameBundle g) (i : Fin 4) :
    scalarGradientVector g a e i = scalarGradient g a e i := rfl

def scalarWeylHessianForm (g : SmoothMetric M) (a : M → ℝ) (e : FrameBundle g) : ℝ :=
  blockQuadratic quaternionMatrix (plusWeyl g e.base e.frame) (scalarHessian g a e) +
    blockQuadratic Angular.oppositeMatrix (minusWeyl g e.base e.frame) (scalarHessian g a e)

theorem ScalarCovariantData.curvature_identity (s : ScalarCovariantData d a)
    (o : OppositeWeylData d)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)) :
    (∫ e, scalarWeylHessianForm g a e ∂μ) =
      3 * ∫ e, (normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 +
        normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2) *
          ‖scalarGradientVector g a e‖ ^ 2 ∂μ := by
  let C (p : Averages.CurvatureIndex) : C(FrameBundle g, ℝ) :=
    ⟨fun e => generalCoefficient quaternionMatrix (plusWeyl g e.base e.frame)
        p.1.1 p.1.2 p.2.1 p.2.2 +
      generalCoefficient Angular.oppositeMatrix (minusWeyl g e.base e.frame)
        p.1.1 p.1.2 p.2.1 p.2.2,
      ((generalCoefficientMap quaternionMatrix p.1.1 p.1.2 p.2.1 p.2.2).continuous.comp
        d.continuousWeyl).add
        ((generalCoefficientMap Angular.oppositeMatrix p.1.1 p.1.2 p.2.1 p.2.2).continuous.comp
          o.continuousWeyl)⟩
  let D (p : Averages.CurvatureIndex) : C(FrameBundle g, ℝ) :=
    ⟨fun e => generalCoefficient quaternionMatrix (plusWeylGradient g e.base e.frame p.1.2)
        p.1.1 p.1.2 p.2.1 p.2.2 +
      generalCoefficient Angular.oppositeMatrix (minusWeylGradient g e.base e.frame p.1.2)
        p.1.1 p.1.2 p.2.1 p.2.2,
      ((generalCoefficientMap quaternionMatrix p.1.1 p.1.2 p.2.1 p.2.2).continuous.comp
        (d.continuousGradient p.1.2)).add
        ((generalCoefficientMap Angular.oppositeMatrix p.1.1 p.1.2 p.2.1 p.2.2).continuous.comp
          (o.continuousGradient p.1.2))⟩
  have hC (p : Averages.CurvatureIndex) (e : FrameBundle g) :
      C p e = generalCoefficient quaternionMatrix (plusWeyl g e.base e.frame)
        p.1.1 p.1.2 p.2.1 p.2.2 +
      generalCoefficient Angular.oppositeMatrix (minusWeyl g e.base e.frame)
        p.1.1 p.1.2 p.2.1 p.2.2 := rfl
  have hD (p : Averages.CurvatureIndex) (e : FrameBundle g) :
      D p e = generalCoefficient quaternionMatrix (plusWeylGradient g e.base e.frame p.1.2)
        p.1.1 p.1.2 p.2.1 p.2.2 +
      generalCoefficient Angular.oppositeMatrix (minusWeylGradient g e.base e.frame p.1.2)
        p.1.1 p.1.2 p.2.1 p.2.2 := rfl
  have hc : ∀ i j l e, (∑ k, D ((i,k),(j,l)) e) = 0 := by
    intro i j l e
    simp only [hD, Finset.sum_add_distrib]
    rw [generalCoefficient_divergence quaternionMatrix _ (d.gradientBianchi e),
      generalCoefficient_divergence Angular.oppositeMatrix _ (o.gradientBianchi e)]
    exact add_zero 0
  have hminus (r : Fin 3) (i j : Fin 4) :
      Angular.oppositeMatrix r j i = -Angular.oppositeMatrix r i j := by
    exact congrArg (fun A : Mat4 => A i j) (QuaternionFrame.oppositeMatrix_transpose r)
  have hs : ∀ i k j l e, C ((k,i),(j,l)) e = -C ((i,k),(j,l)) e := by
    intro i k j l e
    simp only [hC]
    rw [generalCoefficient_skew quaternionMatrix (fun r i j => quaternionMatrix_skew r j i),
      generalCoefficient_skew Angular.oppositeMatrix hminus]
    ring
  have hd (p : Averages.CurvatureIndex) (t : ℝ) (e : FrameBundle g) :
      HasDerivAt (fun r => C p ((d.flow p.1.2).map r e))
        (D p ((d.flow p.1.2).map t e)) t :=
    ((generalCoefficientMap quaternionMatrix p.1.1 p.1.2 p.2.1 p.2.2).hasFDerivAt.comp_hasDerivAt t
      (d.derivativeWeyl p.1.2 t e)).add
      ((generalCoefficientMap Angular.oppositeMatrix p.1.1 p.1.2 p.2.1 p.2.2).hasFDerivAt.comp_hasDerivAt t
        (o.derivativeWeyl p.1.2 t e))
  have hg := Averages.weighted_curvature_green μ (fun i => (d.flow i).map)
    (fun i => (d.flow i).continuous) (fun i => (d.flow i).preserves)
    (ContinuousMap.const _ 1) (fun _ => ContinuousMap.const _ 0) C D
    s.gradientField s.hessianField s.thirdField hc hs
    (fun _ t _ => hasDerivAt_const t 1) hd s.derivativeGradient s.derivativeHessian
  have hR (e : FrameBundle g) (i k j l : Fin 4) :
      frameCurvature g e.base e.frame i k l j =
        generalEinsteinCoefficient (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) i k j l := by
    rw [generalEinsteinCoefficient_eq_tensor, hdecomp e]
  simp only [ScalarCovariantData.gradientField, ScalarCovariantData.hessianField,
    ScalarCovariantData.thirdField, ContinuousMap.coe_mk, ContinuousMap.coe_const,
    Function.const_apply, one_mul, zero_mul, add_zero, RCLike.inner_apply,
    conj_trivial, s.commutator, hR] at hg
  rw [← integral_const_mul] at hg
  have hleft (e : FrameBundle g) :
      (∑ p : Averages.CurvatureIndex,
        C p e * (scalarHessian g a e p.1.2 p.2.2 * scalarHessian g a e p.1.1 p.2.1)) =
      scalarWeylHessianForm g a e := by
    simpa only [scalarWeylHessianForm, hC] using
      scalar_block_quadratic_tuple (plusWeyl g e.base e.frame)
        (minusWeyl g e.base e.frame) (scalarHessian g a e)
  simp_rw [hleft] at hg
  rw [hg, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with e
  have hpoint := scalar_curvature_contraction_commuted
    (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
    (d.weyl.symmetric e) (o.symmetric e) (d.weyl.traceFree e) (o.traceFree e)
    (scalarGradientVector g a e)
  simpa only [hC, scalarGradientVector_apply, mul_assoc] using hpoint

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar Weyl operators annihilate the metric trace.  This identifies
actual Hessian contractions with their trace-free parts. -/

namespace PositiveEinsteinFour.ScalarHessian

open scoped BigOperators
open Matrix TraceHessian Angular CurvatureContraction

noncomputable section

theorem weighted_clifford_product_zero (Q : Fin 3 → Matrix4)
    (hQ : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Matrix4))
    (A : Mat) (hs : symmetric A) (ht : traceFree A) :
    (∑ r, ∑ s, A r s • (Q r * Q s)) = 0 := by
  let W : Matrix4 := ∑ r, ∑ s, A r s • (Q r * Q s)
  have hrev : W = ∑ r, ∑ s, A r s • (Q s * Q r) := by
    dsimp only [W]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro r _
    rw [hs s r]
  have hadd : W + W = (-2 * Matrix.trace A) • (1 : Matrix4) := by
    conv_lhs => rhs; rw [hrev]
    dsimp only [W]
    rw [← Finset.sum_add_distrib]
    simp only [← Finset.sum_add_distrib, ← smul_add, hQ]
    norm_num [Fin.sum_univ_three, Matrix.trace, Matrix.diag, smul_smul]
    module
  rw [show Matrix.trace A = 0 from ht, mul_zero, zero_smul] at hadd
  have htwo : (2 : ℝ) • W = 0 := by simpa only [two_smul] using hadd
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem blockAction_one (Q : Fin 3 → Matrix4)
    (hQ : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Matrix4))
    (A : Mat) (hs : symmetric A) (ht : traceFree A) :
    blockAction Q A (1 : Matrix4) = 0 := by
  change -(1 / 2 : ℝ) • (∑ r, ∑ s, A r s • (Q r * 1 * Q s)) = 0
  simp only [Matrix.mul_one, weighted_clifford_product_zero Q hQ A hs ht, smul_zero]

theorem blockAction_trace (Q : Fin 3 → Matrix4)
    (hQ : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Matrix4))
    (A : Mat) (hs : symmetric A) (ht : traceFree A) (S : Matrix4) :
    Matrix.trace (blockAction Q A S) = 0 := by
  have hrev : (∑ r, ∑ s, A r s • (Q s * Q r)) = 0 := by
    calc
      _ = ∑ s, ∑ r, A r s • (Q s * Q r) := Finset.sum_comm
      _ = ∑ s, ∑ r, A s r • (Q s * Q r) := by
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro r _
        rw [hs r s]
      _ = 0 := weighted_clifford_product_zero Q hQ A hs ht
  have hid : Matrix.trace (blockAction Q A S) =
      -(1 / 2 : ℝ) * Matrix.trace ((∑ r, ∑ s, A r s • (Q s * Q r)) * S) := by
    change Matrix.trace (-(1 / 2 : ℝ) • (∑ r, ∑ s, A r s • (Q r * S * Q s))) = _
    simp only [Matrix.trace_smul, Matrix.trace_sum, Matrix.sum_mul,
      Matrix.smul_mul, smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [Matrix.trace_mul_cycle]
  rw [hid, hrev, zero_mul, Matrix.trace_zero, mul_zero]

def traceFreePart (S : Matrix4) : Matrix4 := S - (Matrix.trace S / 4) • (1 : Matrix4)

theorem traceFreePart_symmetric (S : Matrix4) (hS : Sᵀ = S) :
    (traceFreePart S)ᵀ = traceFreePart S := by
  simp only [traceFreePart, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, hS]

theorem traceFreePart_trace (S : Matrix4) : Matrix.trace (traceFreePart S) = 0 := by
  simp only [traceFreePart, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul]
  ring

theorem traceFreePart_norm (S : Matrix4) :
    scalarNormSq (traceFreePart S) = scalarNormSq S - (Matrix.trace S) ^ 2 / 4 := by
  norm_num [traceFreePart, scalarNormSq, scalarPairing, Matrix.trace, Matrix.diag,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_four]
  ring

theorem scalarPairing_one_right (S : Matrix4) : scalarPairing S 1 = Matrix.trace S := by
  simp [scalarPairing, Matrix.one_apply, Matrix.trace, Matrix.diag]

theorem scalarPairing_sub_right (R S T : Matrix4) :
    scalarPairing R (S - T) = scalarPairing R S - scalarPairing R T := by
  simp only [scalarPairing, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem scalarPairing_smul_right (r : ℝ) (R S : Matrix4) :
    scalarPairing R (r • S) = r * scalarPairing R S := by
  rw [scalarPairing_comm, scalarPairing_smul_left, scalarPairing_comm S R]

theorem blockQuadratic_traceFreePart (Q : Fin 3 → Matrix4)
    (hskew : ∀ r, (Q r)ᵀ = -Q r)
    (hQ : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Matrix4))
    (A : Mat) (hs : symmetric A) (ht : traceFree A) (S : Matrix4) :
    blockQuadratic Q A (traceFreePart S) = blockQuadratic Q A S := by
  rw [blockQuadratic_eq_pairing Q hskew, blockQuadratic_eq_pairing Q hskew]
  have hact : blockAction Q A (traceFreePart S) = blockAction Q A S := by
    change blockActionLinear Q A (S - (Matrix.trace S / 4) • (1 : Matrix4)) = _
    rw [map_sub, map_smul]
    change blockAction Q A S - (Matrix.trace S / 4) • blockAction Q A 1 = _
    rw [blockAction_one Q hQ A hs ht, smul_zero, sub_zero]
  rw [hact, traceFreePart, scalarPairing_sub_right, scalarPairing_smul_right,
    scalarPairing_one_right, blockAction_trace Q hQ A hs ht, mul_zero, sub_zero]

/-- The actual scalar Hessian may retain its trace; the Weyl contraction
only sees the trace-free part. -/
theorem scalarHessian_coefficient_bound_full (A U : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (x y : ℝ) (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2)
    (S : Matrix4) (hS : Sᵀ = S) :
    blockQuadratic quaternionMatrix A S + blockQuadratic oppositeMatrix U S ≤
      4 * scalarNormSq (traceFreePart S) := by
  rw [← blockQuadratic_traceFreePart quaternionMatrix quaternionMatrix_transpose
      quaternionMatrix_anticommutator A hA htA S,
    ← blockQuadratic_traceFreePart oppositeMatrix QuaternionFrame.oppositeMatrix_transpose
      oppositeMatrix_anticommutator U hU htU S]
  exact scalarHessian_coefficient_bound A U hA hU htA htU x y hAx hUy hxy
    (traceFreePart S) (traceFreePart_symmetric S hS) (traceFreePart_trace S)

end
end PositiveEinsteinFour.ScalarHessian
end


section

/-! The actual invariant Hessian form is bounded by its concrete spectral
parameter form. Only the negative compression-energy term is relaxed. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian HighestHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem rawPairing_self_nonneg (Z : RawGradient) : 0 ≤ rawPairing Z Z := by
  exact Finset.sum_nonneg fun p _ => mul_self_nonneg (rawCoordinates Z p)

theorem rawPairing_sub_right (Z W V : RawGradient) :
    rawPairing Z (W - V) = rawPairing Z W - rawPairing Z V := by
  rw [rawPairing_comm, rawPairing_sub_left, rawPairing_comm W, rawPairing_comm V]

/-- The explicit Bianchi curvature action is an orthogonal test of the
true projected action. Its squared norm is therefore a lower bound. -/
theorem projected_diagonal_energy_lower (S : Shape) (v : ℝ) (p k l : Vec) :
    (curvatureAction S v p k l).squaredNorm ≤
      rawPairing
        (rawBianchiProjection (generalMatrixAction
          (Matrix.diagonal (fun a => v * S.s a)) (parameters S p k l).matrix))
        (rawBianchiProjection (generalMatrixAction
          (Matrix.diagonal (fun a => v * S.s a)) (parameters S p k l).matrix)) := by
  let X := rawBianchiProjection (generalMatrixAction
    (Matrix.diagonal (fun a => v * S.s a)) (parameters S p k l).matrix)
  let Y := curvatureAction S v p k l
  have hcross : rawPairing X Y.matrix = Y.squaredNorm := by
    rw [rawBianchiProjection_pairing _ Y (parameters_bianchi S _ _ _),
      generalMatrixAction_diagonal, rawMatrixCurvature_shape, tensor_pairing_eq_raw,
      curvatureAction_compressed_energy]
    ring
  have hy : rawPairing Y.matrix Y.matrix = Y.squaredNorm := by
    rw [rawPairing_vectors]
    simp only [Tensor.squaredNorm, real_inner_self_eq_norm_sq]
  have hn := rawPairing_self_nonneg (X - Y.matrix)
  rw [rawPairing_sub_left, rawPairing_sub_right, rawPairing_sub_right,
    rawPairing_comm Y.matrix X, hcross, hy] at hn
  linarith only [hn]

theorem weylMatrixEnergy_diagonal (t : Fin 3 → ℝ) (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i)) :
    weylMatrixEnergy (Matrix.diagonal t) Z =
      (∑ a, t a * ∑ b, ‖(gradientTensor Z).matrix a b‖ ^ 2) / 6 := by
  have h := generalMatrixAction_gradient_pairing (Matrix.diagonal t) Z hs
  rw [generalMatrixAction_diagonal, rawMatrixCurvature_pairing _ _ _
    (gradientTensor_traceFree Z ht)] at h
  simp only [diagonalGradientPairing, real_inner_self_eq_norm_sq] at h
  linarith only [h]

theorem weighted_row_norms (w : Fin 3 → ℝ) (hw : ∑ a, w a = 0) (T : Tensor) :
    (∑ a, w a * ∑ b, ‖T.matrix a b‖ ^ 2) =
      (∑ a, w a * ‖T.diagonal a‖ ^ 2) - ∑ a, w a * ‖T.off a‖ ^ 2 := by
  simp only [Fin.sum_univ_three] at hw
  simp [Tensor.matrix, Fin.sum_univ_three]
  linear_combination (‖T.off 0‖ ^ 2 + ‖T.off 1‖ ^ 2 + ‖T.off 2‖ ^ 2) * hw

theorem weylMatrixEnergy_shape (S : Shape) (v : ℝ) (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i)) :
    weylMatrixEnergy (Matrix.diagonal (fun a => v * S.s a)) Z =
      curvatureContraction S v (gradientTensor Z) := by
  rw [weylMatrixEnergy_diagonal _ Z hs ht]
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [weighted_row_norms S.s S.trace]
  unfold curvatureContraction
  ring

theorem shape_traceFreeSquare (S : Shape) (v : ℝ) :
    traceFreeSquare (Matrix.diagonal (fun a => v * S.s a)) =
      Matrix.diagonal (fun a => v ^ 2 * S.squareWeight a) := by
  have hsum : (∑ a, (v * S.s a) ^ 2) = 6 * v ^ 2 := by
    simp only [mul_pow, ← Finset.mul_sum, S.square]
    ring
  unfold traceFreeSquare
  rw [Matrix.diagonal_mul_diagonal]
  have htrace : Matrix.trace (Matrix.diagonal
      (fun a => (v * S.s a) * (v * S.s a))) = 6 * v ^ 2 := by
    simpa only [Matrix.trace_diagonal, ← pow_two] using hsum
  rw [htrace]
  ext a b
  by_cases hab : a = b
  · subst b
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      Matrix.diagonal_apply_eq, smul_eq_mul, mul_one, Shape.squareWeight]
    ring
  · simp [Matrix.sub_apply, Matrix.smul_apply, hab]

theorem weylMatrixEnergy_squareShape (S : Shape) (v : ℝ) (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i)) :
    weylMatrixEnergy (traceFreeSquare (Matrix.diagonal (fun a => v * S.s a))) Z =
      squareCurvatureContraction S v (gradientTensor Z) := by
  have hw : ∑ a, S.squareWeight a = 0 := by
    simp only [Shape.squareWeight, Finset.sum_sub_distrib, S.square,
      Finset.sum_const, Finset.card_fin]
    norm_num
  rw [shape_traceFreeSquare, weylMatrixEnergy_diagonal _ Z hs ht]
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [weighted_row_norms S.squareWeight hw]
  unfold squareCurvatureContraction
  ring

/-- All scalar contractions needed by the source Hessian form can be
evaluated in the single pointwise spectral frame. No smooth eigenframe
or second-block diagonalization is involved. -/
theorem invariantHessianForm_spectral_upper_of_frame (A U : Mat) (Z : Angular.Gradient)
    (R : Mat) (hR : Rᵀ * R = 1)
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (S : Shape)
    (hS : conjugateMatrix R A = Matrix.diagonal (fun i => normalizedBlockNorm A * S.s i))
    (hv : 0 < normalizedBlockNorm A)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0) :
    ∃ (p k l : Vec),
      (parameters S p k l).squaredNorm / 6 = weylGradientEnergy Z ∧
      ‖p‖ ^ 2 = ‖blockRadialGradient A Z‖ ^ 2 ∧
      weylMatrixEnergy A Z =
        curvatureContraction S (normalizedBlockNorm A) (parameters S p k l) ∧
      invariantHessianForm A U Z ≤
        hessianTensorForm S (normalizedBlockNorm A) (normalizedBlockNorm U) p k l := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  let W := turnGradient R P.matrix Z
  let T := gradientTensor W
  let p := radialCoordinate S T
  let k := secondCoordinate S T
  let l := thirdCoordinate S T
  have hsW := turnGradient_symmetric R P.matrix Z hs
  have htW := turnGradient_traceFree R hR' P.matrix Z ht
  have hbW := turnGradient_bianchi R hR' P Z hb
  have hT : parameters S p k l = T :=
    parameters_reconstruction S T (gradientTensor_traceFree W htW)
      (gradientTensor_bianchi W hsW hbW)
  have he : T.squaredNorm / 6 = weylGradientEnergy Z := by
    rw [gradientTensor_energy W hsW, weylGradientEnergy_turn R hR' P.matrix P.mul_transpose]
  have hrad : ‖p‖ ^ 2 = ‖blockRadialGradient A Z‖ ^ 2 := by
    have hnorm : normalizedBlockNorm (Matrix.diagonal (fun i => normalizedBlockNorm A * S.s i)) =
        normalizedBlockNorm A := by rw [← hS]; exact conjugateMatrix_norm R hR' A
    have hp : blockRadialGradient (conjugateMatrix R A) W = p := by
      rw [show conjugateMatrix R A = _ from hS,
        blockRadialGradient_diagonal S (normalizedBlockNorm A) W, hnorm,
        div_self (ne_of_gt hv), one_smul]
    have hr := blockRadialGradient_turn R hR' P.matrix A Z
    rw [hp] at hr
    rw [hr, turnVector_norm P.matrix P.mul_transpose]
  have hB : weylMatrixEnergy A Z = curvatureContraction S (normalizedBlockNorm A) T := by
    rw [← weylMatrixEnergy_turn R hR P.matrix P.mul_transpose, show conjugateMatrix R A = _ from hS]
    exact weylMatrixEnergy_shape S _ W hsW htW
  have hC : weylMatrixEnergy (traceFreeSquare A) Z =
      squareCurvatureContraction S (normalizedBlockNorm A) T := by
    rw [← weylMatrixSquareEnergy_turn R hR P.matrix P.mul_transpose,
      show conjugateMatrix R A = _ from hS]
    exact weylMatrixEnergy_squareShape S _ W hsW htW
  have hE : (curvatureAction S (normalizedBlockNorm A) p k l).squaredNorm / 6 ≤
      weylCompressionEnergy A Z := by
    rw [← P.weylCompressionEnergy_turn hR A Z hs,
      show conjugateMatrix R A = _ from hS]
    unfold weylCompressionEnergy
    change (curvatureAction S (normalizedBlockNorm A) p k l).squaredNorm / 6 ≤
      rawPairing
        (rawBianchiProjection (generalMatrixAction
          (Matrix.diagonal (fun i => normalizedBlockNorm A * S.s i)) T.matrix))
        (rawBianchiProjection (generalMatrixAction
          (Matrix.diagonal (fun i => normalizedBlockNorm A * S.s i)) T.matrix)) / 6
    rw [← hT]
    exact div_le_div_of_nonneg_right (projected_diagonal_energy_lower S _ p k l)
      (by norm_num)
  refine ⟨p, k, l, ?_, hrad, ?_, ?_⟩
  · rw [hT]
    exact he
  · rw [hT]
    exact hB
  · rw [invariantHessianForm_eq_collected]
    unfold collectedHessianForm hessianTensorForm
    rw [hB, hC, ← he, ← hT, ← hrad]
    linarith only [hE]

/-- The pointwise spectral frame is constructed from the actual block. -/
theorem invariantHessianForm_spectral_upper (A U : Mat) (Z : Angular.Gradient)
    (hA : symmetric A) (htA : traceFree A) (hv : 0 < normalizedBlockNorm A)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0) :
    ∃ (S : Shape) (p k l : Vec),
      (parameters S p k l).squaredNorm / 6 = weylGradientEnergy Z ∧
      ‖p‖ ^ 2 = ‖blockRadialGradient A Z‖ ^ 2 ∧
      invariantHessianForm A U Z ≤
        hessianTensorForm S (normalizedBlockNorm A) (normalizedBlockNorm U) p k l := by
  obtain ⟨R, hR, ⟨P⟩, S, hS⟩ := exists_lifted_spectral_shape A hA htA hv
  obtain ⟨p, k, l, he, hp, _, hh⟩ :=
    invariantHessianForm_spectral_upper_of_frame A U Z R hR P S hS hv hs ht hb
  exact ⟨S, p, k, l, he, hp, hh⟩

/-- The same spectral shape supplies both the Hessian estimate and the
minimum-eigenvalue parameter constrained by positive shifted curvature. -/
theorem invariantHessianForm_shifted_spectral_upper (A U : Mat) (Z : Angular.Gradient)
    (hA : symmetric A) (htA : traceFree A) (hv : 0 < normalizedBlockNorm A)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0)
    (x : ℝ) (hAx : (A + x • (1 : Mat)).PosSemidef) :
    ∃ (S : Shape) (r : ℝ) (p k l : Vec),
      1 ≤ r ∧ r ≤ 2 ∧ S.sigma = (3 * r - r ^ 3) / 2 ∧
      normalizedBlockNorm A * r ≤ x ∧
      Matrix.trace (A * (A * A)) = 6 * normalizedBlockNorm A ^ 3 * S.sigma ∧
      (parameters S p k l).squaredNorm / 6 = weylGradientEnergy Z ∧
      ‖p‖ ^ 2 = ‖blockRadialGradient A Z‖ ^ 2 ∧
      weylMatrixEnergy A Z =
        curvatureContraction S (normalizedBlockNorm A) (parameters S p k l) ∧
      invariantHessianForm A U Z ≤
        hessianTensorForm S (normalizedBlockNorm A) (normalizedBlockNorm U) p k l := by
  obtain ⟨R, hR, ⟨P⟩, S, hS⟩ := exists_lifted_spectral_shape A hA htA hv
  obtain ⟨r, hr, hr2, hσ, _, hmin⟩ := shape_exists_minimum_parameter S
  obtain ⟨p, k, l, he, hp, hB, hh⟩ :=
    invariantHessianForm_spectral_upper_of_frame A U Z R hR P S hS hv hs ht hb
  exact ⟨S, r, p, k, l, hr, hr2, hσ,
    shape_minimum_parameter_bound A R hR S _ x r hS hAx hmin,
    shape_traceCube A R hR S _ hS, he, hp, hB, hh⟩

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The zero-Ricci specialization for a derivative slice of curvature. -/

namespace PositiveEinsteinFour.AlgebraicCurvature

open Matrix TraceHessian Angular
open PositiveEinsteinFour.Geometry (curvatureBlock)
open scoped BigOperators

noncomputable section

theorem ricci_zero_blocks_traceFree (R : CurvatureArray) (hf : FirstSkew R)
    (hl : LastSkew R) (hb : FirstBianchi R)
    (hr : ∀ j, ricci R j j = 0) :
    traceFree (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) quaternionMatrix) ∧
      traceFree (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) oppositeMatrix) := by
  let K := matrixOf R
  have hn : tensorOf K = R := tensorOf_matrixOf hf hl
  have hs : Kᵀ = K := matrixOf_symmetric (pairSymmetric_of_bianchi hf hl hb)
  have hs50 : K 5 0 = K 0 5 := congrArg (fun A => A 0 5) hs
  have hs41 : K 4 1 = K 1 4 := congrArg (fun A => A 1 4) hs
  have hs32 : K 3 2 = K 2 3 := congrArg (fun A => A 2 3) hs
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  have h3 := hr 3
  have hcycle := hb 0 1 2 3
  rw [← hn] at h0 h1 h2 h3 hcycle
  norm_num [ricci, tensorOf, pairIndex, pairSign, Fin.sum_univ_succ] at h0 h1 h2 h3
  norm_num [tensorOf, pairIndex, pairSign, hs32] at hcycle
  have hcplus : curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) quaternionMatrix =
      plusFormula K := by
    have hh := curvatureBlock_tensorOf K quaternionMatrix quaternionMatrix_transpose
    rw [plusFormula_eq] at hh
    simpa only [hn] using hh
  have hcminus : curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) oppositeMatrix =
      minusFormula K := by
    have hh := curvatureBlock_tensorOf K oppositeMatrix QuaternionFrame.oppositeMatrix_transpose
    rw [minusFormula_eq] at hh
    simpa only [hn] using hh
  rw [hcplus, hcminus]
  constructor
  · change (∑ i : Fin 3, plusFormula K i i) = 0
    norm_num [Fin.sum_univ_three, plusFormula, hs50, hs41, hs32]
    linarith only [h0, h1, h2, h3, hcycle]
  · change (∑ i : Fin 3, minusFormula K i i) = 0
    norm_num [Fin.sum_univ_three, minusFormula, hs50, hs41, hs32]
    linarith only [h0, h1, h2, h3, hcycle]

end
end PositiveEinsteinFour.AlgebraicCurvature
end


section

/-! The quaternionic contraction of a closed, alternating three-tensor.
This is the finite differential-Bianchi calculation used by Weyl blocks. -/

namespace PositiveEinsteinFour.Geometry

open Matrix
open scoped BigOperators

noncomputable section

private theorem quaternion_cyclic_0 (B : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hs : ∀ a b c, B a b c + B a c b = 0)
    (hc : ∀ a b c, B a b c + B b c a + B c a b = 0) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      TraceHessian.quaternionMatrix s 0 j *
        TraceHessian.quaternionMatrix s a b * B j a b) =
      -2 * ∑ j : Fin 4, B j j 0 := by
  norm_num [TraceHessian.quaternionMatrix, Fin.sum_univ_succ]
  linear_combination hs 0 0 0 + hs 1 1 0 + hs 2 2 0 + hs 3 3 0
    + (2 * hc 1 2 3 - hs 1 2 3 - hs 2 1 3 - hs 3 1 2)

private theorem quaternion_cyclic_1 (B : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hs : ∀ a b c, B a b c + B a c b = 0)
    (hc : ∀ a b c, B a b c + B b c a + B c a b = 0) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      TraceHessian.quaternionMatrix s 1 j *
        TraceHessian.quaternionMatrix s a b * B j a b) =
      -2 * ∑ j : Fin 4, B j j 1 := by
  norm_num [TraceHessian.quaternionMatrix, Fin.sum_univ_succ]
  linear_combination hs 0 0 1 + hs 1 1 1 + hs 2 2 1 + hs 3 3 1
    - (2 * hc 0 2 3 - hs 0 2 3 - hs 2 0 3 - hs 3 0 2)

private theorem quaternion_cyclic_2 (B : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hs : ∀ a b c, B a b c + B a c b = 0)
    (hc : ∀ a b c, B a b c + B b c a + B c a b = 0) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      TraceHessian.quaternionMatrix s 2 j *
        TraceHessian.quaternionMatrix s a b * B j a b) =
      -2 * ∑ j : Fin 4, B j j 2 := by
  norm_num [TraceHessian.quaternionMatrix, Fin.sum_univ_succ]
  linear_combination hs 0 0 2 + hs 1 1 2 + hs 2 2 2 + hs 3 3 2
    + (2 * hc 0 1 3 - hs 0 1 3 - hs 1 0 3 - hs 3 0 1)

private theorem quaternion_cyclic_3 (B : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hs : ∀ a b c, B a b c + B a c b = 0)
    (hc : ∀ a b c, B a b c + B b c a + B c a b = 0) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      TraceHessian.quaternionMatrix s 3 j *
        TraceHessian.quaternionMatrix s a b * B j a b) =
      -2 * ∑ j : Fin 4, B j j 3 := by
  norm_num [TraceHessian.quaternionMatrix, Fin.sum_univ_succ]
  linear_combination hs 0 0 3 + hs 1 1 3 + hs 2 2 3 + hs 3 3 3
    - (2 * hc 0 1 2 - hs 0 1 2 - hs 1 0 2 - hs 2 0 1)

theorem quaternion_cyclic_contraction (B : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hs : ∀ a b c, B a b c + B a c b = 0)
    (hc : ∀ a b c, B a b c + B b c a + B c a b = 0) (i : Fin 4) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      TraceHessian.quaternionMatrix s i j *
        TraceHessian.quaternionMatrix s a b * B j a b) =
      -2 * ∑ j : Fin 4, B j j i := by
  fin_cases i
  · exact quaternion_cyclic_0 B hs hc
  · exact quaternion_cyclic_1 B hs hc
  · exact quaternion_cyclic_2 B hs hc
  · exact quaternion_cyclic_3 B hs hc

private theorem opposite_quaternion_cyclic_0 (B : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hs : ∀ a b c, B a b c + B a c b = 0)
    (hc : ∀ a b c, B a b c + B b c a + B c a b = 0) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      Angular.oppositeMatrix s 0 j *
        Angular.oppositeMatrix s a b * B j a b) =
      -2 * ∑ j : Fin 4, B j j 0 := by
  norm_num [Angular.oppositeMatrix, oppositeQuaternion, TraceHessian.quaternionMatrix,
    Fin.sum_univ_succ]
  linear_combination hs 0 0 0 + hs 1 1 0 + hs 2 2 0 + hs 3 3 0
    - (2 * hc 1 2 3 - hs 1 2 3 - hs 2 1 3 - hs 3 1 2)

private theorem opposite_quaternion_cyclic_1 (B : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hs : ∀ a b c, B a b c + B a c b = 0)
    (hc : ∀ a b c, B a b c + B b c a + B c a b = 0) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      Angular.oppositeMatrix s 1 j *
        Angular.oppositeMatrix s a b * B j a b) =
      -2 * ∑ j : Fin 4, B j j 1 := by
  norm_num [Angular.oppositeMatrix, oppositeQuaternion, TraceHessian.quaternionMatrix,
    Fin.sum_univ_succ]
  linear_combination hs 0 0 1 + hs 1 1 1 + hs 2 2 1 + hs 3 3 1
    + (2 * hc 0 2 3 - hs 0 2 3 - hs 2 0 3 - hs 3 0 2)

private theorem opposite_quaternion_cyclic_2 (B : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hs : ∀ a b c, B a b c + B a c b = 0)
    (hc : ∀ a b c, B a b c + B b c a + B c a b = 0) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      Angular.oppositeMatrix s 2 j *
        Angular.oppositeMatrix s a b * B j a b) =
      -2 * ∑ j : Fin 4, B j j 2 := by
  norm_num [Angular.oppositeMatrix, oppositeQuaternion, TraceHessian.quaternionMatrix,
    Fin.sum_univ_succ]
  linear_combination hs 0 0 2 + hs 1 1 2 + hs 2 2 2 + hs 3 3 2
    - (2 * hc 0 1 3 - hs 0 1 3 - hs 1 0 3 - hs 3 0 1)

private theorem opposite_quaternion_cyclic_3 (B : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hs : ∀ a b c, B a b c + B a c b = 0)
    (hc : ∀ a b c, B a b c + B b c a + B c a b = 0) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      Angular.oppositeMatrix s 3 j *
        Angular.oppositeMatrix s a b * B j a b) =
      -2 * ∑ j : Fin 4, B j j 3 := by
  norm_num [Angular.oppositeMatrix, oppositeQuaternion, TraceHessian.quaternionMatrix,
    Fin.sum_univ_succ]
  linear_combination hs 0 0 3 + hs 1 1 3 + hs 2 2 3 + hs 3 3 3
    + (2 * hc 0 1 2 - hs 0 1 2 - hs 1 0 2 - hs 2 0 1)

theorem opposite_quaternion_cyclic_contraction (B : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hs : ∀ a b c, B a b c + B a c b = 0)
    (hc : ∀ a b c, B a b c + B b c a + B c a b = 0) (i : Fin 4) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      Angular.oppositeMatrix s i j *
        Angular.oppositeMatrix s a b * B j a b) =
      -2 * ∑ j : Fin 4, B j j i := by
  fin_cases i
  · exact opposite_quaternion_cyclic_0 B hs hc
  · exact opposite_quaternion_cyclic_1 B hs hc
  · exact opposite_quaternion_cyclic_2 B hs hc
  · exact opposite_quaternion_cyclic_3 B hs hc

/-- Differential Bianchi removes the Hodge-star part of the quaternionic
contraction; its remaining part is the ordinary divergence. -/
theorem curvature_quaternion_contraction (D : Fin 4 → Angular.CurvatureArray)
    (hs : ∀ a, AlgebraicCurvature.FirstSkew (D a))
    (hc : AlgebraicCurvature.DifferentialBianchi D) (i k l : Fin 4) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      TraceHessian.quaternionMatrix s i j *
        TraceHessian.quaternionMatrix s a b * D j a b k l) =
      -2 * ∑ j : Fin 4, D j j i k l := by
  apply quaternion_cyclic_contraction (fun j a b => D j a b k l)
  · intro a b c
    have h := hs a b c k l
    linarith only [h]
  · intro a b c
    exact hc a b c k l


theorem opposite_curvature_quaternion_contraction (D : Fin 4 → Angular.CurvatureArray)
    (hs : ∀ a, AlgebraicCurvature.FirstSkew (D a))
    (hc : AlgebraicCurvature.DifferentialBianchi D) (i k l : Fin 4) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      Angular.oppositeMatrix s i j *
        Angular.oppositeMatrix s a b * D j a b k l) =
      -2 * ∑ j : Fin 4, D j j i k l := by
  apply opposite_quaternion_cyclic_contraction (fun j a b => D j a b k l)
  · intro a b c
    have h := hs a b c k l
    linarith only [h]
  · intro a b c
    exact hc a b c k l


private theorem sum_six_last_pair
    (f : Fin 3 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ s, ∑ j, ∑ a, ∑ b, ∑ c, ∑ d, f s j a b c d) =
      ∑ c, ∑ d, ∑ s, ∑ j, ∑ a, ∑ b, f s j a b c d := by
  let e : ((Fin 4 × Fin 4) × ((Fin 3 × Fin 4) × (Fin 4 × Fin 4))) ≃
      ((Fin 3 × Fin 4) × ((Fin 4 × Fin 4) × (Fin 4 × Fin 4))) := {
    toFun := fun p => (p.2.1, (p.2.2, p.1))
    invFun := fun p => (p.2.2, (p.1, p.2.1))
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  simpa only [e, Equiv.coe_fn_mk, Fintype.sum_prod_type] using (e.sum_comp
    (fun p => f p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2)).symm

/-- The block divergence is the quaternionic contraction of the complete
five-tensor, with the unused two-form pair kept intact. -/
theorem gradientBlock_divergence_eq_kernel (Q : Fin 3 → Mat4)
    (T : CovariantCoordinates 5) (r : Fin 3) (i : Fin 4) :
    (∑ s, ∑ j, Q s i j * gradientBlock T Q j s r) =
      (1 / 8 : ℝ) * ∑ c, ∑ d, Q r c d *
        (∑ s, ∑ j, ∑ a, ∑ b, Q s i j * Q s a b * T ![j, a, b, d, c]) := by
  unfold gradientBlock blockCoordinates curvatureBlock
  simp only [Fintype.sum_prod_type]
  change (∑ s, ∑ j, Q s i j * ((1 / 8 : ℝ) *
    ∑ a, ∑ b, ∑ c, ∑ d, T ![j, a, b, d, c] * Q s a b * Q r c d)) = _
  simp only [Finset.mul_sum]
  rw [sum_six_last_pair]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- A divergence-free curvature derivative satisfying differential Bianchi
has a divergence-free self-dual block. -/
theorem gradientBlock_divergence_zero (T : CovariantCoordinates 5)
    (hs : ∀ a, AlgebraicCurvature.FirstSkew (curvatureDerivativeArray T a))
    (hc : AlgebraicCurvature.DifferentialBianchi (curvatureDerivativeArray T))
    (hd : ∀ i k l, ∑ j, T ![j, j, i, k, l] = 0)
    (r : Fin 3) (i : Fin 4) :
    gradientDivergence (fun j => gradientBlock T TraceHessian.quaternionMatrix j) r i = 0 := by
  change (∑ s, ∑ j, TraceHessian.quaternionMatrix s i j *
    gradientBlock T TraceHessian.quaternionMatrix j s r) = 0
  rw [gradientBlock_divergence_eq_kernel]
  have he (c d : Fin 4) :
      (∑ s, ∑ j, ∑ a, ∑ b,
        TraceHessian.quaternionMatrix s i j * TraceHessian.quaternionMatrix s a b *
          T ![j, a, b, d, c]) = 0 := by
    have h := curvature_quaternion_contraction (curvatureDerivativeArray T) hs hc i d c
    change (∑ s, ∑ j, ∑ a, ∑ b,
      TraceHessian.quaternionMatrix s i j * TraceHessian.quaternionMatrix s a b *
        T ![j, a, b, d, c]) = -2 * ∑ j, T ![j, j, i, d, c] at h
    rw [h, hd i d c, mul_zero]
  simp only [he, mul_zero, Finset.sum_const_zero]

/-- The contracted Ricci identity supplies the remaining divergence
condition; all the block-Bianchi algebra is then automatic. -/
theorem gradientBlock_divergence_of_ricci_parallel (T : CovariantCoordinates 5)
    (hs : ∀ a, AlgebraicCurvature.FirstSkew (curvatureDerivativeArray T a))
    (hl : ∀ a, AlgebraicCurvature.LastSkew (curvatureDerivativeArray T a))
    (hp : ∀ a, AlgebraicCurvature.PairSymmetric (curvatureDerivativeArray T a))
    (hc : AlgebraicCurvature.DifferentialBianchi (curvatureDerivativeArray T))
    (hr : ∀ a j k, ∑ i, T ![a, i, j, k, i] = 0)
    (r : Fin 3) (i : Fin 4) :
    gradientDivergence (fun j => gradientBlock T TraceHessian.quaternionMatrix j) r i = 0 := by
  apply gradientBlock_divergence_zero T hs hc
  intro i k l
  exact AlgebraicCurvature.divergence_zero_of_ricci_parallel
    (curvatureDerivativeArray T) hp hl hc hr i k l


/-- The opposite quaternion block satisfies its own Bianchi contraction. -/
theorem opposite_gradientBlock_divergence_zero (T : CovariantCoordinates 5)
    (hs : ∀ a, AlgebraicCurvature.FirstSkew (curvatureDerivativeArray T a))
    (hc : AlgebraicCurvature.DifferentialBianchi (curvatureDerivativeArray T))
    (hd : ∀ i k l, ∑ j, T ![j, j, i, k, l] = 0)
    (r : Fin 3) (i : Fin 4) :
    (∑ s, ∑ j, Angular.oppositeMatrix s i j *
      gradientBlock T Angular.oppositeMatrix j s r) = 0 := by
  rw [gradientBlock_divergence_eq_kernel]
  have he (c d : Fin 4) :
      (∑ s, ∑ j, ∑ a, ∑ b,
        Angular.oppositeMatrix s i j * Angular.oppositeMatrix s a b *
          T ![j, a, b, d, c]) = 0 := by
    have h := opposite_curvature_quaternion_contraction
      (curvatureDerivativeArray T) hs hc i d c
    change (∑ s, ∑ j, ∑ a, ∑ b,
      Angular.oppositeMatrix s i j * Angular.oppositeMatrix s a b *
        T ![j, a, b, d, c]) = -2 * ∑ j, T ![j, j, i, d, c] at h
    rw [h, hd i d c, mul_zero]
  simp only [he, mul_zero, Finset.sum_const_zero]

theorem opposite_gradientBlock_divergence_of_ricci_parallel (T : CovariantCoordinates 5)
    (hs : ∀ a, AlgebraicCurvature.FirstSkew (curvatureDerivativeArray T a))
    (hl : ∀ a, AlgebraicCurvature.LastSkew (curvatureDerivativeArray T a))
    (hp : ∀ a, AlgebraicCurvature.PairSymmetric (curvatureDerivativeArray T a))
    (hc : AlgebraicCurvature.DifferentialBianchi (curvatureDerivativeArray T))
    (hr : ∀ a j k, ∑ i, T ![a, i, j, k, i] = 0)
    (r : Fin 3) (i : Fin 4) :
    (∑ s, ∑ j, Angular.oppositeMatrix s i j *
      gradientBlock T Angular.oppositeMatrix j s r) = 0 := by
  apply opposite_gradientBlock_divergence_zero T hs hc
  intro i k l
  exact AlgebraicCurvature.divergence_zero_of_ricci_parallel
    (curvatureDerivativeArray T) hp hl hc hr i k l

end
end PositiveEinsteinFour.Geometry
end


section

/-! Reflection of one axis in the actual orthonormal frame. It exchanges
the two Weyl blocks, with one sign for each covariant derivative slot. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Matrix Bundle
open scoped BigOperators Manifold ContDiff

noncomputable section

def frameReflectionMatrix : Mat4 := Matrix.diagonal orientationSign

theorem frameReflectionMatrix_transpose : frameReflectionMatrixᵀ = frameReflectionMatrix := by
  simp [frameReflectionMatrix]

theorem frameReflectionMatrix_sq : frameReflectionMatrix * frameReflectionMatrix = 1 := by
  rw [frameReflectionMatrix, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    exact (pow_two (orientationSign i)).symm.trans (orientationSign_sq i)
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def OrthonormalFrame.reflect {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) : OrthonormalFrame g c where
  matrix := e.matrix * frameReflectionMatrix
  orthonormal := by
    calc
      (e.matrix * frameReflectionMatrix)ᵀ * chartMetric g c *
          (e.matrix * frameReflectionMatrix) =
        frameReflectionMatrixᵀ * (e.matrixᵀ * chartMetric g c * e.matrix) *
          frameReflectionMatrix := by rw [Matrix.transpose_mul]; noncomm_ring
      _ = 1 := by rw [e.orthonormal, mul_one, frameReflectionMatrix_transpose,
        frameReflectionMatrix_sq]

theorem OrthonormalFrame.reflect_matrix {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) (a i : Fin 4) :
    e.reflect.matrix a i = orientationSign i * e.matrix a i := by
  simp only [OrthonormalFrame.reflect, frameReflectionMatrix, Matrix.mul_diagonal]
  ring

theorem OrthonormalFrame.reflect_vector {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) (i : Fin 4) :
    e.reflect.vector i = orientationSign i • e.vector i := by
  ext a
  exact e.reflect_matrix a i

theorem OrthonormalFrame.reflect_reflect {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) : e.reflect.reflect = e := by
  have hm : e.reflect.reflect.matrix = e.matrix := by
    change e.matrix * frameReflectionMatrix * frameReflectionMatrix = e.matrix
    rw [mul_assoc, frameReflectionMatrix_sq, mul_one]
  generalize hf : e.reflect.reflect = f at hm ⊢
  cases e with
  | mk A hA =>
    cases f with
    | mk B hB =>
      dsimp at hm
      subst B
      rfl

def frameReflection {g : SmoothMetric M} (e : FrameBundle g) : FrameBundle g :=
  ⟨e.base, e.frame.reflect⟩

theorem frameReflection_involutive (g : SmoothMetric M) :
    Function.Involutive (frameReflection : FrameBundle g → FrameBundle g) := by
  rintro ⟨c, e⟩
  change (⟨c, e.reflect.reflect⟩ : FrameBundle g) = ⟨c, e⟩
  rw [e.reflect_reflect]

theorem frameCurvature_reflect (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (i j k l : Fin 4) :
    frameCurvature g c e.reflect i j k l =
      orientationSign i * orientationSign j * orientationSign k * orientationSign l *
        frameCurvature g c e i j k l := by
  simp only [frameCurvature, OrthonormalFrame.reflect_matrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem curvatureBlock_reflect (R : (Fin 4 × Fin 4) → (Fin 4 × Fin 4) → ℝ) :
    curvatureBlock (fun p q => orientationSign p.1 * orientationSign p.2 *
      orientationSign q.2 * orientationSign q.1 * R p q) TraceHessian.quaternionMatrix =
      curvatureBlock R oppositeQuaternion := by
  ext s t
  change (1 / 8 : ℝ) * (∑ p, ∑ q, (orientationSign p.1 * orientationSign p.2 *
      orientationSign q.2 * orientationSign q.1 * R p q) *
      TraceHessian.quaternionMatrix s p.1 p.2 * TraceHessian.quaternionMatrix t q.1 q.2) =
    (1 / 8 : ℝ) * (∑ p, ∑ q, R p q *
      oppositeQuaternion s p.1 p.2 * oppositeQuaternion t q.1 q.2)
  apply congrArg (fun z : ℝ => (1 / 8 : ℝ) * z)
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  change _ = R p q *
    (orientationSign p.1 * orientationSign p.2 * TraceHessian.quaternionMatrix s p.1 p.2) *
    (orientationSign q.1 * orientationSign q.2 * TraceHessian.quaternionMatrix t q.1 q.2)
  ring

theorem curvaturePairing_reflect (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) :
    curvaturePairing g c e.reflect = fun p q => orientationSign p.1 * orientationSign p.2 *
      orientationSign q.2 * orientationSign q.1 * curvaturePairing g c e p q := by
  funext p q
  exact frameCurvature_reflect g c e p.1 p.2 q.2 q.1

theorem plusWeyl_reflect (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c) :
    plusWeyl g c e.reflect = minusWeyl g c e := by
  unfold plusWeyl
  rw [curvaturePairing_reflect, curvatureBlock_reflect]
  rfl

theorem minusWeyl_reflect (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c) :
    minusWeyl g c e.reflect = plusWeyl g c e := by
  rw [← plusWeyl_reflect, e.reflect_reflect]

theorem frameTensor_reflect {g : SmoothMetric M} {c : M} (e : OrthonormalFrame g c)
    {n : ℕ} (T : CovariantCoordinates n) (a : Fin n → Fin 4) :
    frameTensor e.reflect.matrix T a =
      (∏ i, orientationSign (a i)) * frameTensor e.matrix T a := by
  simp only [frameTensor, OrthonormalFrame.reflect_matrix, Finset.prod_mul_distrib,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem gradientBlock_frame_reflect {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) (T : CovariantCoordinates 5) (i : Fin 4) :
    gradientBlock (frameTensor e.reflect.matrix T) quaternionMatrix i =
      orientationSign i • gradientBlock (frameTensor e.matrix T) oppositeQuaternion i := by
  ext s t
  simp only [gradientBlock, blockCoordinates, curvatureBlock, frameTensor_reflect,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.prod_univ_zero,
    mul_one]
  change _ = orientationSign i * ((1 / 8 : ℝ) * (_ *
    (orientationSign p.1 * orientationSign p.2 * TraceHessian.quaternionMatrix s p.1 p.2) *
    (orientationSign q.1 * orientationSign q.2 * TraceHessian.quaternionMatrix t q.1 q.2)))
  ring

theorem hessianBlock_frame_reflect {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) (T : CovariantCoordinates 6) (i j : Fin 4) :
    hessianBlock (frameTensor e.reflect.matrix T) quaternionMatrix i j =
      (orientationSign i * orientationSign j) •
        hessianBlock (frameTensor e.matrix T) oppositeQuaternion i j := by
  ext s t
  simp only [hessianBlock, blockCoordinates, curvatureBlock, frameTensor_reflect,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.prod_univ_zero,
    mul_one]
  change _ = orientationSign i * orientationSign j * ((1 / 8 : ℝ) * (_ *
    (orientationSign p.1 * orientationSign p.2 * TraceHessian.quaternionMatrix s p.1 p.2) *
    (orientationSign q.1 * orientationSign q.2 * TraceHessian.quaternionMatrix t q.1 q.2)))
  ring

theorem plusWeylGradient_reflect (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (i : Fin 4) :
    plusWeylGradient g c e.reflect i = orientationSign i • minusWeylGradient g c e i :=
  gradientBlock_frame_reflect e _ i

theorem plusWeylHessian_reflect (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (i j : Fin 4) :
    plusWeylHessian g c e.reflect i j =
      (orientationSign i * orientationSign j) • minusWeylHessian g c e i j :=
  hessianBlock_frame_reflect e _ i j

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual highest-Hessian projection cost in invariant energy units,
then in the same spectral parameters as the Hessian estimate. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian HighestHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

/-- Normalize the arbitrary-frame real-vector cost without rotating the
opposite block or the weight covector. -/
theorem invariant_projection_cost (A U : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (x y : ℝ) (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2)
    (a : Vec) (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0) :
    generalCurvaturePairing A U
        (highestProjection (weightTensor a (gradientTensor Z)))
        (highestProjection (weightTensor a (gradientTensor Z))) / 6 ≤
      ‖a‖ ^ 2 * ((7 / 12 : ℝ) * (4 + y) * weylGradientEnergy Z -
        (5 / 4 : ℝ) * weylMatrixEnergy A Z) := by
  have hc := general_highestProjection_weight_cost A U hA hU htA htU x y hAx hUy hxy
    a (gradientTensor Z) (gradientTensor_traceFree Z ht) (gradientTensor_bianchi Z hs hb)
  have hg : generalGradientForm A (gradientTensor Z) = 6 * weylMatrixEnergy A Z :=
    generalMatrixAction_gradient_pairing A Z hs
  have he : (gradientTensor Z).squaredNorm = 6 * weylGradientEnergy Z := by
    have he' := gradientTensor_energy Z hs
    linarith only [he']
  have hd := div_le_div_of_nonneg_right hc (show (0 : ℝ) ≤ 6 by norm_num)
  rw [hg, he] at hd
  convert hd using 1
  ring

/-- The normalized invariant cost is bounded by the source's exact two
spectral coefficients, retaining the actual total derivative energy. -/
theorem invariant_projection_parameter_cost (A U : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (x y : ℝ) (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2)
    (a : Vec) (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0)
    (S : Shape) (p k l : Vec)
    (he : (parameters S p k l).squaredNorm / 6 = weylGradientEnergy Z)
    (hB : weylMatrixEnergy A Z =
      curvatureContraction S (normalizedBlockNorm A) (parameters S p k l)) :
    generalCurvaturePairing A U
        (highestProjection (weightTensor a (gradientTensor Z)))
        (highestProjection (weightTensor a (gradientTensor Z))) / 6 ≤
      ‖a‖ ^ 2 *
        (QuarticEnergy.projectionCoefficient (normalizedBlockNorm A) y S.sigma S.rho *
          ((5 / 3) * ‖p‖ ^ 2) + Energy.defectCoefficient (normalizedBlockNorm A) y *
          (weylGradientEnergy Z - (5 / 3) * ‖p‖ ^ 2)) := by
  have hc := invariant_projection_cost A U hA hU htA htU x y hAx hUy hxy a Z hs ht hb
  have hp := projection_cost_coefficients S (normalizedBlockNorm_nonneg A) y p k l
  rw [he, ← hB] at hp
  exact hc.trans (mul_le_mul_of_nonneg_left hp (sq_nonneg ‖a‖))

/-- The exact squared weight changes the denominator to the `9/64` coefficient; all remaining quantities are actual invariant energies. -/
theorem invariant_squared_weight_parameter_cost (A U : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (x y : ℝ) (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2)
    (M : ℝ) (hM : M ≠ 0) (p q : Vec) (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0)
    (S : Shape) (p' k l : Vec)
    (he : (parameters S p' k l).squaredNorm / 6 = weylGradientEnergy Z)
    (hp : ‖p'‖ ^ 2 = ‖p‖ ^ 2)
    (hB : weylMatrixEnergy A Z =
      curvatureContraction S (normalizedBlockNorm A) (parameters S p' k l)) :
    generalCurvaturePairing A U
        (highestProjection (weightTensor ((-(3 / 4 : ℝ) * M) • (p - q)) (gradientTensor Z)))
        (highestProjection (weightTensor ((-(3 / 4 : ℝ) * M) • (p - q)) (gradientTensor Z))) /
          (24 * M ^ 2) ≤
      (9 / 64 : ℝ) * ‖p - q‖ ^ 2 *
        (QuarticEnergy.projectionCoefficient (normalizedBlockNorm A) y S.sigma S.rho *
          ((5 / 3) * ‖p‖ ^ 2) + Energy.defectCoefficient (normalizedBlockNorm A) y *
          (weylGradientEnergy Z - (5 / 3) * ‖p‖ ^ 2)) := by
  have hc := invariant_projection_parameter_cost A U hA hU htA htU x y hAx hUy hxy
    ((-(3 / 4 : ℝ) * M) • (p - q)) Z hs ht hb S p' k l he hB
  rw [hp] at hc
  have hd := div_le_div_of_nonneg_right hc (show 0 ≤ 4 * M ^ 2 by positivity)
  have hn : ‖(-(3 / 4 : ℝ) * M) • (p - q)‖ ^ 2 =
      (9 / 16 : ℝ) * M ^ 2 * ‖p - q‖ ^ 2 := by
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [hn] at hd
  convert hd using 1 <;> field_simp [hM] <;> ring

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! Lowering the actual curvature derivative and transporting the second
Bianchi identity to the coordinate/frame tensor used by the Weyl gradient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem covariantDerivative_four_apply (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates 4) (z : FourSpace) (i j k l m : Fin 4) :
    covariantDerivative g c T z ![i, j, k, l, m] =
      partialDeriv (fun w => T w ![j, k, l, m]) i z -
      ((∑ p, christoffel g c z p i j * T z ![p, k, l, m]) +
       (∑ p, christoffel g c z p i k * T z ![j, p, l, m]) +
       (∑ p, christoffel g c z p i l * T z ![j, k, p, m]) +
       (∑ p, christoffel g c z p i m * T z ![j, k, l, p])) := by
  have h0 (p : Fin 4) : Function.update ![j, k, l, m] 0 p = ![p, k, l, m] := by
    funext a
    fin_cases a <;> rfl
  have h1 (p : Fin 4) : Function.update ![j, k, l, m] 1 p = ![j, p, l, m] := by
    funext a
    fin_cases a <;> rfl
  have h2 (p : Fin 4) : Function.update ![j, k, l, m] 2 p = ![j, k, p, m] := by
    funext a
    fin_cases a <;> rfl
  have h3 (p : Fin 4) : Function.update ![j, k, l, m] 3 p = ![j, k, l, p] := by
    funext a
    fin_cases a <;> rfl
  change partialDeriv (fun w => T w ![j, k, l, m]) i z -
    (∑ s : Fin 4, ∑ p, christoffel g c z p i (![j, k, l, m] s) *
      T z (Function.update ![j, k, l, m] s p)) = _
  rw [Fin.sum_univ_four]
  simp only [h0, h1, h2, h3]
  rfl

theorem loweredCurvatureMatrix_apply (g : SmoothMetric M) (c : M)
    (z : FourSpace) (j k l m : Fin 4) :
    (metricInChart g c z * coordinateCurvatureMatrix g c j k z) m l =
      curvatureCoordinates g c z ![j, k, l, m] := by
  simp only [Matrix.mul_apply, coordinateCurvatureMatrix_apply]
  change (∑ a, metricInChart g c z m a * curvatureComponent g c z a j k l) =
    ∑ a, metricInChart g c z a m * curvatureComponent g c z a j k l
  apply Finset.sum_congr rfl
  intro a _
  rw [metricInChart_comm g c z m a]

private theorem lowered_derivative_matrix (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j k : Fin 4) :
    matrixPartial (fun w => metricInChart g c w * coordinateCurvatureMatrix g c j k w) i z -
      (connectionMatrix g c i z)ᵀ *
        (metricInChart g c z * coordinateCurvatureMatrix g c j k z) -
      (metricInChart g c z * coordinateCurvatureMatrix g c j k z) * connectionMatrix g c i z -
      (∑ p, (connectionMatrix g c i z p j •
          (metricInChart g c z * coordinateCurvatureMatrix g c p k z) +
        connectionMatrix g c i z p k •
          (metricInChart g c z * coordinateCurvatureMatrix g c j p z))) =
      metricInChart g c z * coordinateCovariantCurvatureDerivative g c z i j k := by
  have hG (a b : Fin 4) : DifferentiableAt ℝ (fun w => metricInChart g c w a b) z :=
    (metricInChart_contDiffAt g c z hz a b).differentiableAt (by simp)
  have hR (a b : Fin 4) :
      DifferentiableAt ℝ (fun w => coordinateCurvatureMatrix g c j k w a b) z :=
    (coordinateCurvatureMatrix_contDiffAt g c z hz hdet j k a b).differentiableAt (by simp)
  rw [matrixPartial_mul _ _ z hG hR i,
    matrixPartial_metric g c z (isUnit_iff_ne_zero.mpr hdet)]
  have hsum : metricInChart g c z *
      (∑ p, (connectionMatrix g c i z p j • coordinateCurvatureMatrix g c p k z +
        connectionMatrix g c i z p k • coordinateCurvatureMatrix g c j p z)) =
      ∑ p, (connectionMatrix g c i z p j •
          (metricInChart g c z * coordinateCurvatureMatrix g c p k z) +
        connectionMatrix g c i z p k •
          (metricInChart g c z * coordinateCurvatureMatrix g c j p z)) := by
    simp only [Finset.mul_sum, mul_add, mul_smul_comm]
  unfold coordinateCovariantCurvatureDerivative
  rw [mul_sub, hsum]
  noncomm_ring

theorem covariantDerivative_curvature_lowering (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j k l m : Fin 4) :
    covariantDerivative g c (curvatureCoordinates g c) z ![i, j, k, l, m] =
      (metricInChart g c z * coordinateCovariantCurvatureDerivative g c z i j k) m l := by
  rw [← lowered_derivative_matrix g c z hz hdet i j k]
  rw [covariantDerivative_four_apply]
  have heq (r s t u : Fin 4) :
      (fun w => curvatureCoordinates g c w ![r, s, t, u]) =
      (fun w => (metricInChart g c w * coordinateCurvatureMatrix g c r s w) u t) :=
    funext fun w => (loweredCurvatureMatrix_apply g c w r s t u).symm
  rw [heq]
  simp only [matrixPartial, Matrix.sub_apply, Matrix.sum_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply,
    connectionMatrix, ← loweredCurvatureMatrix_apply, Finset.sum_add_distrib]
  simp only [mul_comm]
  ring

/-- Differential Bianchi for the actual fully covariant curvature tensor. -/
theorem curvatureCoordinates_second_bianchi (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) :
    AlgebraicCurvature.DifferentialBianchi
      (curvatureDerivativeArray (covariantDerivative g c (curvatureCoordinates g c) z)) := by
  intro i j k l m
  change covariantDerivative g c (curvatureCoordinates g c) z ![i, j, k, l, m] +
    covariantDerivative g c (curvatureCoordinates g c) z ![j, k, i, l, m] +
    covariantDerivative g c (curvatureCoordinates g c) z ![k, i, j, l, m] = 0
  simp only [covariantDerivative_curvature_lowering g c z hz hdet]
  have h := congrArg (fun A : Mat4 => (metricInChart g c z * A) m l)
    (coordinate_second_bianchi g c z hz hdet i j k)
  simpa only [mul_add, Matrix.add_apply, mul_zero, Matrix.zero_apply] using h

theorem frame_curvature_second_bianchi (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) :
    AlgebraicCurvature.DifferentialBianchi
      (curvatureDerivativeArray (frameTensor e.matrix
        (covariantDerivative g c (curvatureCoordinates g c) (chartAt FourSpace c c)))) := by
  apply frameTensor_differentialBianchi
  apply curvatureCoordinates_second_bianchi
  · exact (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  · exact (chartMetric_posDef g c).det_pos.ne'

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite curvature reconstruction for the orthonormal-frame tensor, using
metric skew-adjointness of the curvature operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem frame_algebraic_firstSkew (e : OrthonormalFrame g c) :
    AlgebraicCurvature.FirstSkew (frameCurvature g c e) := by
  intro i j k l
  exact frameCurvature_first_skew e j i k l

theorem frame_algebraic_firstBianchi (e : OrthonormalFrame g c) :
    AlgebraicCurvature.FirstBianchi (frameCurvature g c e) :=
  frameCurvature_first_bianchi e

theorem frame_algebraic_pairSymmetric (e : OrthonormalFrame g c)
    (hl : AlgebraicCurvature.LastSkew (frameCurvature g c e)) :
    AlgebraicCurvature.PairSymmetric (frameCurvature g c e) :=
  AlgebraicCurvature.pairSymmetric_of_bianchi (frame_algebraic_firstSkew e) hl
    (frame_algebraic_firstBianchi e)

theorem frame_algebraic_ricciThree (e : OrthonormalFrame g c) (hRic : RicciThree g)
    (j k : Fin 4) :
    AlgebraicCurvature.ricci (frameCurvature g c e) j k = if j = k then 3 else 0 := by
  unfold AlgebraicCurvature.ricci
  rw [frameCurvature_ricci]
  have h := congrArg (fun A : Mat4 => A j k) (e.ricci_eq_three_one (hRic c))
  simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, mul_ite,
    mul_one, mul_zero] using h

theorem frame_einstein_decomposition_of_lastSkew (e : OrthonormalFrame g c)
    (hl : AlgebraicCurvature.LastSkew (frameCurvature g c e)) (hRic : RicciThree g) :
    frameCurvature g c e = Angular.einsteinCurvatureTensor
      (plusWeyl g c e) (minusWeyl g c e) :=
  AlgebraicCurvature.einstein_decomposition_of_bianchi (frameCurvature g c e)
    (frame_algebraic_firstSkew e) hl (frame_algebraic_firstBianchi e)
    (frame_algebraic_ricciThree e hRic)

theorem frame_weyl_symmetric_of_lastSkew (e : OrthonormalFrame g c)
    (hl : AlgebraicCurvature.LastSkew (frameCurvature g c e)) :
    TraceHessian.symmetric (plusWeyl g c e) ∧
      TraceHessian.symmetric (minusWeyl g c e) := by
  have hp := frame_algebraic_pairSymmetric e hl
  exact ⟨AlgebraicCurvature.curvatureBlock_sub_one_symmetric _
    (frame_algebraic_firstSkew e) hl hp _,
    AlgebraicCurvature.curvatureBlock_sub_one_symmetric _
    (frame_algebraic_firstSkew e) hl hp _⟩

theorem frame_weyl_traceFree_of_lastSkew (e : OrthonormalFrame g c)
    (hl : AlgebraicCurvature.LastSkew (frameCurvature g c e)) (hRic : RicciThree g) :
    TraceHessian.traceFree (plusWeyl g c e) ∧
      TraceHessian.traceFree (minusWeyl g c e) :=
  AlgebraicCurvature.weyl_blocks_traceFree (frameCurvature g c e)
    (frame_algebraic_firstSkew e) hl (frame_algebraic_firstBianchi e)
    (frame_algebraic_ricciThree e hRic)

theorem sectionalInput_of_lastSkew
    (hl : ∀ c (e : OrthonormalFrame g c),
      AlgebraicCurvature.LastSkew (frameCurvature g c e)) :
    GurskyLeBrunSectionalInput g := by
  apply sectionalInput_of_curvature_decomposition g
  · intro hRic c e
    exact frame_einstein_decomposition_of_lastSkew e (hl c e) hRic
  · intro e
    exact (frame_weyl_symmetric_of_lastSkew e.frame (hl e.base e.frame)).1
  · intro e
    exact (frame_weyl_symmetric_of_lastSkew e.frame (hl e.base e.frame)).2

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrability at a zero Weyl norm is obtained from uniformly bounded
regularized energies and Fatou's lemma. No integrability of the singular
quotient is assumed in the limiting argument. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter TraceHessian
open scoped BigOperators Topology

noncomputable section

theorem integrable_of_ae_limit_norm_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : ℕ → Ω → ℝ) (f : Ω → ℝ) (C : ℝ)
    (hF : ∀ n, Integrable (F n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hbound : ∀ n, (∫ x, ‖F n x‖ ∂μ) ≤ C) : Integrable f μ := by
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (hF n).aestronglyMeasurable) hlim, ?_⟩
  have hf : (∫⁻ x, ‖f x‖ₑ ∂μ) ≤
      liminf (fun n => ∫⁻ x, ‖F n x‖ₑ ∂μ) atTop := by
    calc
      _ = ∫⁻ x, liminf (fun n => ‖F n x‖ₑ) atTop ∂μ :=
        lintegral_congr_ae (hlim.mono (fun x hx => hx.enorm.liminf_eq.symm))
      _ ≤ _ := lintegral_liminf_le' (fun n => (hF n).aestronglyMeasurable.aemeasurable.enorm)
  have hb : liminf (fun n => ∫⁻ x, ‖F n x‖ₑ ∂μ) atTop ≤ ENNReal.ofReal C := by
    rw [Filter.liminf_eq_iSup_iInf_of_nat]
    apply iSup_le
    intro n
    refine (iInf₂_le n le_rfl).trans ?_
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hF n)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  exact lt_of_le_of_lt (hf.trans hb) ENNReal.ofReal_lt_top

theorem regularizedRadialDerivative_factor (ε : ℝ) (A Z : Mat) :
    regularizedRadialDerivative ε A Z =
      (normalizedBlockNorm A / regularizedBlockNorm ε A) * regularizedRadialDerivative 0 A Z := by
  change Matrix.trace (A * Z) / (6 * regularizedBlockNorm ε A) = _
  rw [trace_eq_norm_mul_radial A Z]
  ring

theorem regularized_radial_energy_le (ε : ℝ) (hε : 0 < ε)
    (A : Mat) (Z : Fin 4 → Mat) :
    (∑ i, regularizedRadialDerivative ε A (Z i) ^ 2) ≤ ‖blockRadialGradient A Z‖ ^ 2 := by
  let r := normalizedBlockNorm A / regularizedBlockNorm ε A
  have hr0 : 0 ≤ r := div_nonneg (normalizedBlockNorm_nonneg A)
    (regularizedBlockNorm_pos ε hε A).le
  have hr1 : r ≤ 1 := (div_le_one (regularizedBlockNorm_pos ε hε A)).mpr
    (norm_le_regularizedBlockNorm ε A)
  have hrsq : r ^ 2 ≤ 1 := by nlinarith
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i, regularizedRadialDerivative ε A (Z i) ^ 2) ≤
    ∑ i, regularizedRadialDerivative 0 A (Z i) ^ 2
  apply Finset.sum_le_sum
  intro i _
  rw [regularizedRadialDerivative_factor ε A (Z i), mul_pow]
  exact (mul_le_mul_of_nonneg_right hrsq (sq_nonneg _)).trans_eq (one_mul _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The strengthened scalar Bochner inequality is derived from the actual
metric Green identities and the proved finite-dimensional Hessian estimate. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian ScalarHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance scalarWeightedBochnerRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance scalarWeightedBochnerSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance scalarWeightedBochnerAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ}
  {a : M → ℝ}

theorem scalarTraceFreeHessian_eq_part (e : FrameBundle g) :
    scalarTraceFreeHessian g a e = traceFreePart (scalarHessian g a e) := by
  ext i j
  change scalarHessian g a e i j - (if i = j then scalarLaplacian g a e / 4 else 0) =
    scalarHessian g a e i j - (Matrix.trace (scalarHessian g a e) / 4) *
      (if i = j then 1 else 0)
  change _ = scalarHessian g a e i j - (scalarLaplacian g a e / 4) *
    (if i = j then 1 else 0)
  split_ifs <;> ring

theorem ScalarCovariantData.continuousTraceFreeSquare (s : ScalarCovariantData d a) :
    Continuous (fun e => ∑ i, ∑ j, scalarTraceFreeHessian g a e i j ^ 2) := by
  unfold scalarTraceFreeHessian
  have hL := s.continuousLaplacian
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  have hHij := s.continuousHessian i j
  split_ifs <;> fun_prop

theorem ScalarCovariantData.continuousWeylHessianForm (s : ScalarCovariantData d a)
    (o : OppositeWeylData d) : Continuous (scalarWeylHessianForm g a) := by
  have hp := continuous_generalCoefficient quaternionMatrix d.continuousWeyl
  have hm := continuous_generalCoefficient Angular.oppositeMatrix o.continuousWeyl
  have hH := s.continuousHessian
  unfold scalarWeylHessianForm blockQuadratic
  fun_prop

variable [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

theorem ScalarCovariantData.weighted_bochner (s : ScalarCovariantData d a)
    (o : OppositeWeylData d) (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)) :
    (∫ e, (4 + normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 +
      normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2) *
        ‖scalarGradientVector g a e‖ ^ 2 ∂μ) ≤ ∫ e, scalarLaplacian g a e ^ 2 ∂μ := by
  have hpcont := s.continuousGradientVector.norm.pow 2
  have hvcont := continuous_normalizedBlockNorm.comp d.continuousWeyl
  have hbcont := continuous_normalizedBlockNorm.comp o.continuousWeyl
  have intg {f : FrameBundle g → ℝ} (h : Continuous f) : Integrable f μ :=
    h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hoperator (e : FrameBundle g) :
      scalarWeylHessianForm g a e ≤ 4 * ∑ i, ∑ j, scalarTraceFreeHessian g a e i j ^ 2 := by
    obtain ⟨x, y, hx, hy, hxy⟩ := hp e
    have hS : (scalarHessian g a e)ᵀ = scalarHessian g a e := by
      ext i j
      exact s.hessianSymmetric e j i
    have h := scalarHessian_coefficient_bound_full
      (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (d.weyl.symmetric e) (o.symmetric e) (d.weyl.traceFree e) (o.traceFree e)
      x y hx hy hxy (scalarHessian g a e) hS
    rw [← scalarTraceFreeHessian_eq_part] at h
    simpa only [scalarWeylHessianForm, scalarNormSq, scalarPairing, pow_two] using h
  exact Variance.bochner_weighted_energy
    (intg hpcont) (intg s.continuousTraceFreeSquare)
    (intg (s.continuousWeylHessianForm o))
    (intg (((hvcont.pow 2).add (hbcont.pow 2)).mul hpcont))
    s.integrated_bochner (s.curvature_identity o hdecomp)
    (Filter.Eventually.of_forall hoperator)

end
end PositiveEinsteinFour.Geometry
end

end OAI
