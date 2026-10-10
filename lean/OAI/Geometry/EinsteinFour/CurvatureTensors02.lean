import OAI.Geometry.EinsteinFour.AngularClifford
import OAI.Geometry.EinsteinFour.AngularCurvature
import OAI.Geometry.EinsteinFour.BianchiCurvature
import OAI.Geometry.EinsteinFour.ChartCurvatureTransition
import OAI.Geometry.EinsteinFour.ChartMetricNondegeneracy
import OAI.Geometry.EinsteinFour.ChartMetricSmoothness
import OAI.Geometry.EinsteinFour.CoordinateChangeCalculus
import OAI.Geometry.EinsteinFour.CurvatureContraction
import OAI.Geometry.EinsteinFour.CurvatureCoordinateSmoothness
import OAI.Geometry.EinsteinFour.CurvatureMetricSkew
import OAI.Geometry.EinsteinFour.CurvatureTensors00
import OAI.Geometry.EinsteinFour.FrameAverages
import OAI.Geometry.EinsteinFour.FrameCurvatureMetricSkew
import OAI.Geometry.EinsteinFour.FrameOrientation
import OAI.Geometry.EinsteinFour.HighestCoordinates
import OAI.Geometry.EinsteinFour.MatrixSlotCubic
import OAI.Geometry.EinsteinFour.MetricContractionCalculus
import OAI.Geometry.EinsteinFour.MetricHessian
import OAI.Geometry.EinsteinFour.MetricTensorCompatibility
import OAI.Geometry.EinsteinFour.NormVarianceApproximation
import OAI.Geometry.EinsteinFour.QuaternionGenerators
import OAI.Geometry.EinsteinFour.RicciMatrixChange
import OAI.Geometry.EinsteinFour.VarianceCorrection
import OAI.Geometry.EinsteinFour.WeylEstimates00
import OAI.Geometry.EinsteinFour.WeylEstimates01
import OAI.Geometry.EinsteinFour.WeylMatrixEquation
import OAI.Geometry.EinsteinFour.WeylNormal
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace OAI


section

/-! The actual smooth metric supplies the algebraic curvature identities.
No curvature decomposition or sectional criterion is a premise here. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem frameCurvature_last_skew (e : OrthonormalFrame g c) (i j k l : Fin 4) :
    frameCurvature g c e i j k l = -frameCurvature g c e i j l k :=
  frameCurvature_last_skew_of_lowered e
    (fun p q r b => lowered_curvature_last_skew_at_center g c p q b r) i j k l

theorem frame_algebraic_lastSkew (e : OrthonormalFrame g c) :
    AlgebraicCurvature.LastSkew (frameCurvature g c e) :=
  fun i j k l => frameCurvature_last_skew e i j l k

theorem actual_einstein_decomposition (e : OrthonormalFrame g c) (hRic : RicciThree g) :
    frameCurvature g c e = Angular.einsteinCurvatureTensor
      (plusWeyl g c e) (minusWeyl g c e) :=
  frame_einstein_decomposition_of_lastSkew e (frame_algebraic_lastSkew e) hRic

theorem actual_weyl_symmetric (e : OrthonormalFrame g c) :
    TraceHessian.symmetric (plusWeyl g c e) ∧
      TraceHessian.symmetric (minusWeyl g c e) :=
  frame_weyl_symmetric_of_lastSkew e (frame_algebraic_lastSkew e)

theorem actual_weyl_traceFree (e : OrthonormalFrame g c) (hRic : RicciThree g) :
    TraceHessian.traceFree (plusWeyl g c e) ∧
      TraceHessian.traceFree (minusWeyl g c e) :=
  frame_weyl_traceFree_of_lastSkew e (frame_algebraic_lastSkew e) hRic

theorem actual_sectionalInput (g : SmoothMetric M) : GurskyLeBrunSectionalInput g :=
  sectionalInput_of_lastSkew (fun _ e => frame_algebraic_lastSkew e)

/-- Strict pointwise pinching of the normalized Weyl norms follows from
positive sectional curvature and the actual algebraic curvature identities. -/
theorem actual_norm_pinching (hRic : RicciThree g)
    (hsec : HasPositiveSectionalCurvature g) (e : FrameBundle g) :
    normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2 := by
  obtain ⟨x, y, hx, hy, hxy⟩ := actual_sectionalInput g hRic hsec e
  have hs := actual_weyl_symmetric e.frame
  have ht := actual_weyl_traceFree e.frame hRic
  have hp := QuaternionFrame.normalizedBlockNorm_le_shift _ hs.1 ht.1 x hx
  have hm := QuaternionFrame.normalizedBlockNorm_le_shift _ hs.2 ht.2 y hy
  linarith only [hp, hm, hxy]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The zero-Ricci block reconstruction needed for the actual curvature derivative. -/

namespace PositiveEinsteinFour.AlgebraicCurvature

open Matrix TraceHessian Angular
open PositiveEinsteinFour.Geometry (curvatureBlock)
open scoped BigOperators

noncomputable section

theorem relations_of_ricci_zero (K : Matrix (Fin 6) (Fin 6) ℝ) (hs : Kᵀ = K)
    (hr : ∀ j k, ricci (tensorOf K) j k = 0) :
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


theorem ricci_zero_decomposition (R : CurvatureArray) (hf : FirstSkew R)
    (hl : LastSkew R) (hp : PairSymmetric R) (hr : ∀ j k, ricci R j k = 0) :
    R = blockTensor (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) quaternionMatrix)
        quaternionMatrix +
      blockTensor (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) oppositeMatrix)
        oppositeMatrix := by
  let K := matrixOf R
  have hn : tensorOf K = R := tensorOf_matrixOf hf hl
  have hk : EinsteinRelations K := relations_of_ricci_zero K (matrixOf_symmetric hp)
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
  rw [hcplus, hcminus]
  exact hn.symm.trans (tensorOf_eq_blocksTensor K hk)

end
end PositiveEinsteinFour.AlgebraicCurvature
end


section

/-! Tracing the actual curvature derivative commutes with covariant
 differentiation.  The connection terms in the contracted input/output
 slots cancel; no Einstein equation is differentiated here. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

private theorem curvature_trace_connection (C : Mat4)
    (R D : Fin 4 → Fin 4 → Mat4) (j k : Fin 4) :
    (∑ r, (D r j + C * R r j - R r j * C -
      ∑ p, (C p r • R p j + C p j • R r p)) r k) =
      (∑ r, D r j r k) -
      ((∑ p, C p j * ∑ r, R r p r k) +
        ∑ p, C p k * ∑ r, R r j r p) := by
  have hc : (∑ r, ∑ p, C r p * R r j p k) =
      ∑ r, ∑ p, C p r * R p j r k := Finset.sum_comm
  have hj : (∑ r, ∑ p, C p j * R r p r k) =
      ∑ p, C p j * ∑ r, R r p r k := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  have hk : (∑ r, ∑ p, R r j r p * C p k) =
      ∑ p, C p k * ∑ r, R r j r p := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro r _
    ring
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hc, hj, hk]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The Ricci field in one fixed chart, retaining both covariant slots. -/
def ricciTensorCoordinates (g : SmoothMetric M) (c : M) (z : FourSpace) :
    CovariantCoordinates 2 := fun a => ricciInChart g c z (a 0) (a 1)

theorem covariantDerivative_two_apply (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates 2) (z : FourSpace) (i j k : Fin 4) :
    covariantDerivative g c T z ![i, j, k] =
      partialDeriv (fun w => T w ![j, k]) i z -
        ((∑ p, christoffel g c z p i j * T z ![p, k]) +
          ∑ p, christoffel g c z p i k * T z ![j, p]) := by
  have h0 (p : Fin 4) : Function.update ![j, k] 0 p = ![p, k] := by
    funext a
    fin_cases a <;> rfl
  have h1 (p : Fin 4) : Function.update ![j, k] 1 p = ![j, p] := by
    funext a
    fin_cases a <;> rfl
  change partialDeriv (fun w => T w ![j, k]) i z -
    (∑ s : Fin 2, ∑ p, christoffel g c z p i (![j, k] s) *
      T z (Function.update ![j, k] s p)) = _
  rw [Fin.sum_univ_two]
  simp only [h0, h1]
  rfl

theorem ricciInChart_eq_curvatureMatrix_trace (g : SmoothMetric M) (c : M)
    (z : FourSpace) (j k : Fin 4) :
    ricciInChart g c z j k = ∑ r, coordinateCurvatureMatrix g c r j z r k := by
  simp only [coordinateCurvatureMatrix_apply, ricciInChart]

theorem partialDeriv_ricciInChart (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j k : Fin 4) :
    partialDeriv (fun w => ricciInChart g c w j k) i z =
      ∑ r, matrixPartial (coordinateCurvatureMatrix g c r j) i z r k := by
  have he : (fun w => ricciInChart g c w j k) =
      fun w => ∑ r, coordinateCurvatureMatrix g c r j w r k := by
    funext w
    exact ricciInChart_eq_curvatureMatrix_trace g c w j k
  rw [he]
  unfold partialDeriv
  have hd := fderiv_fun_sum (u := Finset.univ)
    (A := fun r w => coordinateCurvatureMatrix g c r j w r k)
    (fun r _ => (coordinateCurvatureMatrix_contDiffAt g c z hz hdet r j r k).differentiableAt
      (by simp))
  rw [hd, _root_.sum_apply]
  rfl

/-- The contracted connection terms cancel in the same fixed chart. -/
theorem covariantDerivative_ricci_eq_curvature_trace (g : SmoothMetric M)
    (c : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j k : Fin 4) :
    covariantDerivative g c (ricciTensorCoordinates g c) z ![i, j, k] =
      ∑ r, coordinateCovariantCurvatureDerivative g c z i r j r k := by
  rw [covariantDerivative_two_apply]
  change partialDeriv (fun w => ricciInChart g c w j k) i z -
    ((∑ p, christoffel g c z p i j * ricciInChart g c z p k) +
      ∑ p, christoffel g c z p i k * ricciInChart g c z j p) = _
  rw [partialDeriv_ricciInChart g c z hz hdet]
  simp only [ricciInChart_eq_curvatureMatrix_trace]
  exact (curvature_trace_connection (connectionMatrix g c i z)
    (fun r s => coordinateCurvatureMatrix g c r s z)
    (fun r s => matrixPartial (coordinateCurvatureMatrix g c r s) i z) j k).symm

/-- Lowering and contracting the actual curvature derivative gives the
actual derivative of Ricci.  Invertibility is used only at the evaluation
point; no derivative of the inverse metric is required. -/
theorem lowered_curvature_derivative_contraction (g : SmoothMetric M)
    (c : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j k : Fin 4) :
    (∑ r, ∑ s, (metricInChart g c z)⁻¹ r s *
      covariantDerivative g c (curvatureCoordinates g c) z ![i, r, j, k, s]) =
      covariantDerivative g c (ricciTensorCoordinates g c) z ![i, j, k] := by
  rw [covariantDerivative_ricci_eq_curvature_trace g c z hz hdet]
  apply Finset.sum_congr rfl
  intro r _
  simp only [covariantDerivative_curvature_lowering g c z hz hdet]
  change ((metricInChart g c z)⁻¹ *
    (metricInChart g c z * coordinateCovariantCurvatureDerivative g c z i r j)) r k = _
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.mpr hdet)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The fixed reflection is continuous in the actual tangent-bundle
topology, and hence defines a measurable involution of the frame bundle. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem continuous_tangent_fiber_smul (a : ℝ) :
    Continuous (fun v : TangentBundle I4 M =>
      (⟨v.proj, a • v.2⟩ : TangentBundle I4 M)) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  rw [FiberBundle.continuousAt_totalSpace FourSpace]
  refine ⟨(FiberBundle.continuous_proj FourSpace (TangentSpace I4)).continuousAt, ?_⟩
  let e := trivializationAt FourSpace (TangentSpace I4 : M → Type _) v.proj
  have hv : v ∈ e.source := e.mem_source.mpr
    (mem_baseSet_trivializationAt FourSpace (TangentSpace I4) v.proj)
  have hc : ContinuousAt (fun w : TangentBundle I4 M => (e w).2) v :=
    continuous_snd.continuousAt.comp (e.toOpenPartialHomeomorph.continuousAt hv)
  apply ((continuousAt_const (y := a)).smul hc).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hv] with w hw
  have hb : w.proj ∈ e.baseSet := e.mem_source.mp hw
  change (e (⟨w.proj, a • w.2⟩ : TangentBundle I4 M)).2 = a • (e w).2
  rw [e.apply_eq_prod_continuousLinearEquivAt ℝ w.proj hb]
  change e.continuousLinearEquivAt ℝ w.proj hb (a • w.2) =
    a • (e (⟨w.proj, w.2⟩ : TangentBundle I4 M)).2
  rw [e.apply_eq_prod_continuousLinearEquivAt ℝ w.proj hb]
  exact map_smul _ _ _

theorem continuous_frameReflection (g : SmoothMetric M) :
    Continuous (frameReflection : FrameBundle g → FrameBundle g) := by
  apply continuous_induced_rng.mpr
  have hv (i : Fin 4) : Continuous (fun e : FrameBundle g =>
      (⟨e.base, orientationSign i • e.frame.vector i⟩ : TangentBundle I4 M)) :=
    (continuous_tangent_fiber_smul (orientationSign i)).comp
      ((continuous_apply i).comp (continuous_snd.comp (continuous_frameRealization g)))
  convert! (continuous_frameBase g).prodMk (continuous_pi hv) using 1
  funext e
  change (e.base, fun i => (⟨e.base, e.frame.reflect.vector i⟩ : TangentBundle I4 M)) =
    (e.base, fun i => (⟨e.base, orientationSign i • e.frame.vector i⟩ : TangentBundle I4 M))
  apply Prod.ext
  · rfl
  · funext i
    exact congrArg (fun v => (⟨e.base, v⟩ : TangentBundle I4 M)) (e.frame.reflect_vector i)

def frameReflectionEquiv (g : SmoothMetric M) : FrameBundle g ≃ᵐ FrameBundle g where
  toFun := frameReflection
  invFun := frameReflection
  left_inv := frameReflection_involutive g
  right_inv := frameReflection_involutive g
  measurable_toFun := (continuous_frameReflection g).measurable
  measurable_invFun := (continuous_frameReflection g).measurable

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrability of the actual nonsmooth Hessian integrand, obtained from
its smooth approximants and their existing common domination. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter TraceHessian
open scoped BigOperators Topology Manifold ContDiff

noncomputable section

local instance hessianIntegrabilityRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance hessianIntegrabilitySpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance hessianIntegrabilityAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

theorem tendsto_regularizedHessianWeight_zero
    (A B : Mat) (Z V : Fin 4 → Mat) (F : ℝ) (G : Fin 4 → ℝ)
    (K : Fin 4 → Fin 4 → ℝ)
    (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2)
    (ε : ℕ → ℝ) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => regularizedHessianWeight (ε n) A B Z V F G K) atTop
      (𝓝 (regularizedHessianWeight 0 A B Z V F G K)) := by
  have hd (i : Fin 4) : Tendsto
      (fun n => regularizedWeylWeightDerivative (ε n) A B (Z i) (V i)) atTop
      (𝓝 (regularizedWeylWeightDerivative 0 A B (Z i) (V i))) := by
    simpa only [Function.comp_def, regularizedWeylWeightDerivative,
      regularizedRadialDerivative, regularizedBlockNorm_zero] using
      (tendsto_regularizedWeylWeightDerivative A B (Z i) (V i)).comp hlim
  have hw : Tendsto (fun n => regularizedWeylWeight (ε n) A B) atTop
      (𝓝 (regularizedWeylWeight 0 A B)) := by
    simpa only [Function.comp_def, regularizedWeylWeight, regularizedBlockNorm_zero] using
      (tendsto_regularizedWeylWeight A B).comp hlim
  have hl := tendsto_finsetSum Finset.univ (fun i _ => (hd i).mul
    (tendsto_const_nhds (x := G i)))
  have hk : Tendsto (fun n => regularizedMatrixWeight (ε n) A B Z V K) atTop
      (𝓝 (regularizedMatrixWeight 0 A B Z V K)) := by
    unfold regularizedMatrixWeight
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact (((hd i).mul (hd j)).div hw (ne_of_gt
      (regularizedWeylWeight_pos 0 (by norm_num) (by norm_num) A B hpinch))).mul
        tendsto_const_nhds
  exact ((hw.mul tendsto_const_nhds).add hl).add hk

section Integral

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

theorem integrable_regularizedHessianWeight_zero
    (A B : Ω → Mat) (Z V : Fin 4 → Ω → Mat) (F : Ω → ℝ)
    (G : Fin 4 → Ω → ℝ) (K : Fin 4 → Fin 4 → Ω → ℝ)
    (hA : Continuous A) (hB : Continuous B) (hZ : ∀ i, Continuous (Z i))
    (hV : ∀ i, Continuous (V i)) (hF : Continuous F)
    (hG : ∀ i, Continuous (G i)) (hK : ∀ i j, Continuous (K i j))
    (hsZ : ∀ i x, symmetric (Z i x)) (hsV : ∀ i x, symmetric (V i x))
    (hpinch : ∀ x, normalizedBlockNorm (A x) + normalizedBlockNorm (B x) < 2) :
    Integrable (fun x => regularizedHessianWeight 0 (A x) (B x)
      (fun i => Z i x) (fun i => V i x) (F x) (fun i => G i x)
        (fun i j => K i j x)) μ := by
  let ε : ℕ → ℝ := fun n => (1 / 3 : ℝ) * (1 / ((n : ℝ) + 1))
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  have he (n) : ε n ≤ 1 / 3 := by
    have hi : 1 / ((n : ℝ) + 1) ≤ (1 : ℝ) :=
      (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    dsimp [ε]
    linarith
  have hlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 3 : ℝ)
  let N : Fin 4 → Ω → ℝ := fun i x => normalizedBlockNorm (Z i x) + normalizedBlockNorm (V i x)
  let bound : Ω → ℝ := fun x => 4 * |F x| +
    (∑ i, (3 / 2 : ℝ) * N i x * |G i x|) +
    ∑ i, ∑ j, 144 * N i x * N j x * |K i j x|
  have hN (i) : Continuous (N i) :=
    (continuous_normalizedBlockNorm.comp (hZ i)).add
      (continuous_normalizedBlockNorm.comp (hV i))
  have hb : Integrable bound μ := by
    have hc : Continuous bound :=
      ((continuous_const.mul hF.abs).add (continuous_finsetSum _ (fun i _ =>
        (continuous_const.mul (hN i)).mul (hG i).abs))).add
        (continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
          ((continuous_const.mul (hN i)).mul (hN j)).mul (hK i j).abs)))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let f : ℕ → Ω → ℝ := fun n x => regularizedHessianWeight (ε n) (A x) (B x)
    (fun i => Z i x) (fun i => V i x) (F x) (fun i => G i x) (fun i j => K i j x)
  have hf (n) : Integrable (f n) μ := by
    have hd (i : Fin 4) := continuous_regularizedWeylWeightDerivative (ε n) (hε n)
      A B (Z i) (V i) hA hB (hZ i) (hV i)
    have hw := continuous_regularizedWeylWeight (ε n) A B hA hB
    have hp x := ne_of_gt (regularizedWeylWeight_pos (ε n) (hε n).le (he n) _ _ (hpinch x))
    have hc : Continuous (f n) := by
      unfold f regularizedHessianWeight regularizedMatrixWeight
      exact ((hw.mul hF).add (continuous_finsetSum _ (fun i _ => (hd i).mul (hG i)))).add
        (continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
          (((hd i).mul (hd j)).div hw hp).mul (hK i j))))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply integrable_of_ae_limit_norm_bound μ f _ (∫ x, bound x ∂μ) hf
  · filter_upwards [] with x
    exact tendsto_regularizedHessianWeight_zero _ _ _ _ _ _ _ (hpinch x) ε hlim
  · intro n
    apply integral_mono_ae (hf n).norm hb
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    exact regularizedHessianWeight_bound (ε n) (hε n) (he n) _ _ _ _ _ _ _
      (fun i => hsZ i x) (fun i => hsV i x) (hpinch x)

end Integral

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem MetricGreenData.hessianIntegrand_integrable (d : MetricGreenData g μ)
    (o : OppositeWeylData d) [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    Integrable (regularizedHessianIntegrand g 0) μ := by
  change Integrable (fun e => regularizedHessianIntegrand g 0 e) μ
  simp_rw [regularizedHessianIntegrand_eq_weight]
  exact integrable_regularizedHessianWeight_zero μ _ _ _ _ _ _ _
    d.continuousWeyl o.continuousWeyl d.continuousGradient o.continuousGradient
    (d.invariantHessianField o).continuous (fun i => (d.cubicEntryField i).continuous)
    (d.continuousProjectedWeightKernel o)
    (fun i e => (d.gradientConstraints e).1 i)
    (fun i e => (o.gradientConstraints e).1 i) hpinch

end
end PositiveEinsteinFour.Geometry
end


section

/-! The singular Weyl energy quotient is integrable. The refined Kato
inequality is kept as a local intermediate input, to be supplied by the
pointwise Bianchi parametrization; no weak norm equation is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators Topology Manifold ContDiff

noncomputable section

local instance normIntegrabilityNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance normIntegrabilityNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance normIntegrabilityNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

theorem regularized_norm_laplacian_split (ε : ℝ) (A : Mat) (e p : ℝ) :
    (e + Matrix.trace (A * weylLaplacian A) / 6 - p) / regularizedBlockNorm ε A =
      (e - p) / regularizedBlockNorm ε A +
        regularizedRadialDerivative ε A (weylLaplacian A) := by
  unfold regularizedRadialDerivative
  ring

theorem weylGradientEnergy_nonneg (Z : Fin 4 → Mat) : 0 ≤ weylGradientEnergy Z := by
  unfold weylGradientEnergy matrixPairing
  exact div_nonneg (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun a _ =>
    Finset.sum_nonneg (fun b _ => mul_self_nonneg _)))) (by norm_num)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

def laplacianNormField (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => normalizedBlockNorm (weylLaplacian (plusWeyl g e.base e.frame)),
    continuous_normalizedBlockNorm.comp (continuous_weylLaplacian.comp d.continuousWeyl)⟩

theorem regularizedEnergyQuotient_bound (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hkato : ∀ e : FrameBundle g, (5 / 3 : ℝ) *
      ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2 ≤
        weylGradientEnergy (plusWeylGradient g e.base e.frame))
    (ε : ℝ) (hε : 0 < ε) :
    (∫ e, weylGradientEnergy (plusWeylGradient g e.base e.frame) /
      regularizedBlockNorm ε (plusWeyl g e.base e.frame) ∂μ) ≤
      (5 / 2 : ℝ) * ∫ e, normalizedBlockNorm (weylLaplacian (plusWeyl g e.base e.frame)) ∂μ := by
  let E := d.gradientEnergyField
  let N := d.regularizedNormField ε
  let P : C(FrameBundle g, ℝ) := ⟨fun e => ∑ i, (d.regularizedRadialField ε hε i e) ^ 2,
    by fun_prop⟩
  let T : C(FrameBundle g, ℝ) :=
    ⟨fun e => regularizedRadialDerivative ε (plusWeyl g e.base e.frame)
      (weylLaplacian (plusWeyl g e.base e.frame)),
      continuous_regularizedRadialDerivative ε hε _ _ d.continuousWeyl
        (continuous_weylLaplacian.comp d.continuousWeyl)⟩
  let L := d.laplacianNormField
  have hN e : 0 < N e := regularizedBlockNorm_pos ε hε _
  let F : C(FrameBundle g, ℝ) := ⟨fun e => E e / N e,
    E.continuous.div N.continuous (fun e => (hN e).ne')⟩
  let Q : C(FrameBundle g, ℝ) := ⟨fun e => (E e - P e) / N e + T e,
    ((E.continuous.sub P.continuous).div N.continuous (fun e => (hN e).ne')).add T.continuous⟩
  have hQ : (∫ e, Q e ∂μ) = 0 := by
    have h := d.testedRegularizedNormEquation ε hε (ContinuousMap.const _ 1)
      (fun _ => ContinuousMap.const _ 0) (by intro i t e; exact hasDerivAt_const t 1)
    simpa only [Q, E, N, P, T, ContinuousMap.coe_const, Function.const_apply, one_mul, zero_mul,
      Finset.sum_const_zero, add_zero, regularizedNormField, regularizedRadialField,
      gradientEnergyField, gradientMap, ContinuousMap.coe_mk, regularized_norm_laplacian_split] using h
  have hpoint (e : FrameBundle g) : F e ≤ (5 / 2 : ℝ) * (Q e + L e) := by
    have hP := regularized_radial_energy_le ε hε (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame)
    have hK := hkato e
    change P e ≤ _ at hP
    change _ ≤ E e at hK
    have he : E e ≤ (5 / 2 : ℝ) * (E e - P e) := by linarith
    have hd := div_le_div_of_nonneg_right he (hN e).le
    have ht := (abs_le.mp (abs_regularizedRadialDerivative_le ε hε
      (plusWeyl g e.base e.frame) (weylLaplacian (plusWeyl g e.base e.frame))
      (weylLaplacian_symmetric _ (d.weyl.symmetric e)))).1
    change -L e ≤ T e at ht
    rw [mul_div_assoc] at hd
    change E e / N e ≤ (5 / 2 : ℝ) * ((E e - P e) / N e + T e + L e)
    nlinarith only [hd, ht]
  have hFi : Integrable F μ := F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hQi : Integrable Q μ := Q.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hLi : Integrable L μ := L.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ e, F e ∂μ) ≤ (5 / 2 : ℝ) * ∫ e, L e ∂μ
  calc
    _ ≤ ∫ e, (5 / 2 : ℝ) * (Q e + L e) ∂μ :=
      integral_mono hFi ((hQi.add hLi).const_mul _) hpoint
    _ = (5 / 2 : ℝ) * ∫ e, L e ∂μ := by
      rw [integral_const_mul, integral_add hQi hLi, hQ, zero_add]

theorem integrableEnergyQuotient (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hkato : ∀ e : FrameBundle g, (5 / 3 : ℝ) *
      ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2 ≤
        weylGradientEnergy (plusWeylGradient g e.base e.frame)) :
    Integrable (fun e => weylGradientEnergy (plusWeylGradient g e.base e.frame) /
      normalizedBlockNorm (plusWeyl g e.base e.frame)) μ := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let F : ℕ → FrameBundle g → ℝ := fun n e =>
    weylGradientEnergy (plusWeylGradient g e.base e.frame) /
      regularizedBlockNorm (ε n) (plusWeyl g e.base e.frame)
  apply integrable_of_ae_limit_norm_bound μ F _
    ((5 / 2 : ℝ) * ∫ e, d.laplacianNormField e ∂μ)
  · intro n
    exact (d.gradientEnergyField.continuous.div (d.regularizedNormField (ε n)).continuous
      (fun e => (regularizedBlockNorm_pos (ε n) (hε n) _).ne')).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · filter_upwards [d.gradient_zero_ae_on_zero] with e he
    by_cases hv : normalizedBlockNorm (plusWeyl g e.base e.frame) = 0
    · have hA := (normalizedBlockNorm_eq_zero_iff _).mp hv
      have hZ := he hA
      have hz : weylGradientEnergy (plusWeylGradient g e.base e.frame) = 0 := by
        simp only [weylGradientEnergy, hZ, matrixPairing, Matrix.zero_apply, mul_zero,
          Finset.sum_const_zero, zero_div]
      simp only [F, hz, zero_div]
      exact tendsto_const_nhds
    · exact tendsto_const_nhds.div ((tendsto_regularizedBlockNorm _).comp hεlim) hv
  · intro n
    have heq : (fun e => ‖F n e‖) = F n := by
      funext e
      apply Real.norm_of_nonneg
      exact div_nonneg (weylGradientEnergy_nonneg _) (regularizedBlockNorm_pos (ε n) (hε n) _).le
    rw [heq]
    exact d.regularizedEnergyQuotient_bound hkato (ε n) (hε n)

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The weighted scalar variance inequality for smooth functions, derived
from the weighted Bochner estimate and degree-zero Poisson solvability. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ} [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]

theorem smooth_weighted_variance
    (o : OppositeWeylData d) (hcalc : PetersenScalarCalculusInput d)
    (hpoisson : PetersenPoissonInput g μ) (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (a : M → ℝ) (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) :
    (∫ e, (a e.base - ∫ f, a f.base ∂μ) ^ 2 ∂μ) ≤
      ∫ e, ‖scalarGradientVector g a e‖ ^ 2 /
        (4 + normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 +
          normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2) ∂μ := by
  obtain ⟨s⟩ := hcalc a ha
  obtain ⟨φ, hφ, hΔ⟩ := hpoisson a ha
  obtain ⟨t⟩ := hcalc φ hφ
  let K : FrameBundle g → ℝ := fun e =>
    4 + normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 +
      normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2
  have hK (e : FrameBundle g) : 0 < K e := by dsimp [K]; positivity
  have hKc : Continuous K := by
    exact (continuous_const.add ((continuous_normalizedBlockNorm.comp d.continuousWeyl).pow 2)).add
      ((continuous_normalizedBlockNorm.comp o.continuousWeyl).pow 2)
  have intg {f : FrameBundle g → ℝ} (h : Continuous f) : Integrable f μ :=
    h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hf := intg ((s.continuousGradientVector.norm.pow 2).div hKc (fun e => (hK e).ne'))
  have hg := intg (hKc.mul (t.continuousGradientVector.norm.pow 2))
  have hc := intg ((s.continuousGradientVector.inner t.continuousGradientVector).neg)
  have hcpoint (e : FrameBundle g) :
      -inner ℝ (scalarGradientVector g a e) (scalarGradientVector g φ e) =
        -(∑ i, scalarGradient g a e i * scalarGradient g φ e i) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      scalarGradientVector, mul_comm]
  have hpair : (∫ e, -inner ℝ (scalarGradientVector g a e) (scalarGradientVector g φ e) ∂μ) =
      ∫ e, (a e.base - ∫ f, a f.base ∂μ) ^ 2 ∂μ := by
    calc
      _ = -(∫ e, ∑ i, scalarGradient g a e i * scalarGradient g φ e i ∂μ) := by
        simp_rw [hcpoint]
        exact integral_neg _
      _ = ∫ e, a e.base * scalarLaplacian g φ e ∂μ := by
        rw [s.scalar_pairing_green t, neg_neg]
      _ = ∫ e, a e.base * (a e.base - ∫ f, a f.base ∂μ) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun e => congrArg (fun z => a e.base * z) (hΔ e))
      _ = _ := Variance.centered_product_integral s.valueField
  have hbound : (∫ e, K e * ‖scalarGradientVector g φ e‖ ^ 2 ∂μ) ≤
      ∫ e, (a e.base - ∫ f, a f.base ∂μ) ^ 2 ∂μ := by
    have h := t.weighted_bochner o hp hdecomp
    simpa only [hΔ] using h
  exact Variance.variance_le_of_poisson_pairing hf hg hc
    (Filter.Eventually.of_forall (fun e => div_nonneg (sq_nonneg _) (hK e).le))
    (Filter.Eventually.of_forall (fun e => mul_nonneg (hK e).le (sq_nonneg _)))
    (Filter.Eventually.of_forall (fun e => Variance.weighted_inner_sq_le
      (scalarGradientVector g a e) (scalarGradientVector g φ e) (hK e)))
    (integral_nonneg (fun e => sq_nonneg _)) hpair hbound

end
end PositiveEinsteinFour.Geometry
end


section

/-! The constant sectional-curvature tensor is parallel for the actual
metric connection. Thus subtracting it preserves differential Bianchi. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

private theorem partial_product {f h : FourSpace → ℝ} {z : FourSpace}
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) (i : Fin 4) :
    partialDeriv (fun w => f w * h w) i z =
      partialDeriv f i z * h z + f z * partialDeriv h i z := by
  simp only [partialDeriv, fderiv_fun_mul hf hh, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

private theorem partial_difference {f h : FourSpace → ℝ} {z : FourSpace}
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) (i : Fin 4) :
    partialDeriv (fun w => f w - h w) i z = partialDeriv f i z - partialDeriv h i z := by
  simp only [partialDeriv, fderiv_fun_sub hf hh, _root_.sub_apply]

theorem covariantDerivative_unitCurvature (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) :
    covariantDerivative g c (unitCurvatureCoordinates g c) z = 0 := by
  funext a
  let G := metricInChart g c
  let C := christoffel g c z
  let d := a 0
  let i := a 1
  let j := a 2
  let k := a 3
  let l := a 4
  have hd (r s : Fin 4) : DifferentiableAt ℝ (fun w => G w r s) z :=
    (metricInChart_contDiffAt g c z hz r s).differentiableAt (by simp)
  have hpartial (r s : Fin 4) : partialDeriv (fun w => G w r s) d z =
      ∑ p, (G z p s * C p d r + G z r p * C p d s) := by
    rw [← christoffel_metric_compatibility g c z (isUnit_iff_ne_zero.mpr hdet)]
    apply Finset.sum_congr rfl
    intro p _
    change G z s p * C p d r + G z r p * C p d s = _
    rw [show G z s p = G z p s from g.symm _ _ _]
  have ha : a = ![d, i, j, k, l] := by
    funext s
    fin_cases s <;> rfl
  change covariantDerivative g c (unitCurvatureCoordinates g c) z a = 0
  rw [ha, covariantDerivative_four_apply]
  simp only [unitCurvatureCoordinates, Matrix.cons_val_zero]
  change partialDeriv (fun w => G w j k * G w i l - G w i k * G w j l) d z -
    ((∑ p, C p d i * (G z j k * G z p l - G z p k * G z j l)) +
      (∑ p, C p d j * (G z p k * G z i l - G z i k * G z p l)) +
      (∑ p, C p d k * (G z j p * G z i l - G z i p * G z j l)) +
      (∑ p, C p d l * (G z j k * G z i p - G z i k * G z j p))) = 0
  rw [partial_difference (f := fun w => G w j k * G w i l)
      (h := fun w => G w i k * G w j l)
      ((hd j k).mul (hd i l)) ((hd i k).mul (hd j l)) d,
    partial_product (hd j k) (hd i l) d, partial_product (hd i k) (hd j l) d]
  simp only [hpartial, mul_add, mul_sub, add_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro p _
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive sectional curvature makes the actual normal Jacobi curvature
matrix positive semidefinite. No separate matrix-positivity input is needed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix SectionalPlane
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem frameJacobiMatrix_apply (e : FrameBundle g) (i j : Fin 3) :
    (1 + frameCurvatureField g e) i j =
      frameCurvature g e.base e.frame i.succ 0 0 j.succ := by
  rw [Matrix.add_apply, Matrix.one_apply, frameCurvatureField_apply]
  ring

theorem frameJacobiMatrix_symmetric (e : FrameBundle g) :
    (1 + frameCurvatureField g e)ᵀ = 1 + frameCurvatureField g e := by
  ext i j
  simp only [Matrix.transpose_apply, frameJacobiMatrix_apply]
  have hp := frame_algebraic_pairSymmetric e.frame (frame_algebraic_lastSkew e.frame)
  rw [← hp j.succ 0 0 i.succ,
    frameCurvature_first_skew e.frame 0 i.succ j.succ 0,
    frameCurvature_last_skew e.frame i.succ 0 j.succ 0, neg_neg]

def normalCoordinates (v : Fin 3 → ℝ) : FourSpace :=
  WithLp.toLp 2 (Fin.cons 0 v)

theorem normalCoordinates_ne_zero {v : Fin 3 → ℝ} (hv : v ≠ 0) :
    normalCoordinates v ≠ 0 := by
  intro he
  apply hv
  funext i
  exact congrArg (fun w : FourSpace => w i.succ) he

theorem normalCoordinates_orthogonal (v : Fin 3 → ℝ) :
    inner ℝ (normalCoordinates v) (coordinateVector 0) = 0 := by
  simp [normalCoordinates, coordinateVector, PiLp.inner_apply, RCLike.inner_apply]

theorem frameJacobiMatrix_quadratic (e : FrameBundle g) (v : Fin 3 → ℝ) :
    star v ⬝ᵥ ((1 + frameCurvatureField g e) *ᵥ v) =
      sectionalValue (frameCurvature g e.base e.frame)
        (normalCoordinates v) (coordinateVector 0) := by
  have hs : sectionalValue (frameCurvature g e.base e.frame)
      (normalCoordinates v) (coordinateVector 0) =
      ∑ i, ∑ j, frameCurvature g e.base e.frame i.succ 0 0 j.succ * v i * v j := by
    simp [sectionalValue, normalCoordinates, coordinateVector,
      Fin.sum_univ_four, Fin.sum_univ_three]
    rfl
  rw [hs]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
    Finset.mul_sum, frameJacobiMatrix_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Positivity of sectional curvatures implies the actual radial matrix
is positive semidefinite, including its zero-vector quadratic value. -/
theorem actual_jacobi_posSemidef (hsec : HasPositiveSectionalCurvature g)
    (e : FrameBundle g) : (1 + frameCurvatureField g e).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.isHermitian_iff_isSymm.mpr (frameJacobiMatrix_symmetric e)
  · intro v
    rw [frameJacobiMatrix_quadratic]
    by_cases hv : v = 0
    · have hn : normalCoordinates v = 0 := by
        subst v
        ext i
        fin_cases i <;> rfl
      simp [hn, sectionalValue]
    · have hu : normalCoordinates v ≠ 0 := normalCoordinates_ne_zero hv
      have hz : coordinateVector (0 : Fin 4) ≠ 0 := by
        intro he
        have h := congrArg (fun w : FourSpace => w 0) he
        norm_num [coordinateVector] at h
      have hlin : LinearIndependent ℝ ![normalCoordinates v, coordinateVector 0] := by
        apply linearIndependent_of_ne_zero_of_inner_eq_zero
        · intro i
          fin_cases i
          · exact hu
          · exact hz
        · intro i j hij
          fin_cases i <;> fin_cases j
          · exact False.elim (hij rfl)
          · exact normalCoordinates_orthogonal v
          · change inner ℝ (coordinateVector 0) (normalCoordinates v) = 0
            rw [real_inner_comm]
            exact normalCoordinates_orthogonal v
          · exact False.elim (hij rfl)
      rw [sectionalValue_frame]
      exact (e.frame.sectional_pos hsec _ _ hlin).le

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite frame transport for the differentiated Ricci contraction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

private def tensorConsEquiv (n : ℕ) :
    (Fin 4 × (Fin n → Fin 4)) ≃ (Fin (n + 1) → Fin 4) where
  toFun p := Fin.cons p.1 p.2
  invFun a := (a 0, fun i => a i.succ)
  left_inv p := by cases p; rfl
  right_inv a := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private theorem sum_tensor_cons {n : ℕ} (f : (Fin (n + 1) → Fin 4) → ℝ) :
    (∑ w, f w) = ∑ b, ∑ v : Fin n → Fin 4, f (Fin.cons b v) := by
  have h := (tensorConsEquiv n).sum_comp f
  have hp : (∑ p : Fin 4 × (Fin n → Fin 4), f (tensorConsEquiv n p)) =
      ∑ b, ∑ v : Fin n → Fin 4, f (Fin.cons b v) := by
    rw [Fintype.sum_prod_type]
    rfl
  exact h.symm.trans hp

theorem frameTensor_cons {n : ℕ} (E : Mat4) (T : CovariantCoordinates (n + 1))
    (a : Fin 4) (v : Fin n → Fin 4) :
    frameTensor E T (Fin.cons a v) =
      ∑ b, E b a * frameTensor E (fun w => T (Fin.cons b w)) v := by
  let f : (Fin (n + 1) → Fin 4) → ℝ :=
    fun w => (∏ i, E (w i) ((Fin.cons a v : Fin (n + 1) → Fin 4) i)) * T w
  change (∑ w, f w) = _
  rw [sum_tensor_cons f]
  dsimp only [f]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    frameTensor, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem frameTensor_zero (E : Mat4) (T : CovariantCoordinates 0)
    (a : Fin 0 → Fin 4) : frameTensor E T a = T a := by
  unfold frameTensor
  rw [Fintype.sum_subsingleton _ a]
  simp

theorem frameTensor_three (E : Mat4) (T : CovariantCoordinates 3)
    (i j k : Fin 4) :
    frameTensor E T ![i, j, k] =
      ∑ a, ∑ b, ∑ c, E a i * E b j * E c k * T ![a, b, c] := by
  change frameTensor E T (Fin.cons i (Fin.cons j (Fin.cons k ![]))) = _
  simp only [frameTensor_cons, frameTensor_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  change E a i * (E b j * (E c k * T ![a, b, c])) = _
  ring

theorem frameTensor_four (E : Mat4) (T : CovariantCoordinates 4)
    (i j k l : Fin 4) :
    frameTensor E T ![i, j, k, l] =
      ∑ a, ∑ b, ∑ c, ∑ d, E a i * E b j * E c k * E d l * T ![a, b, c, d] := by
  change frameTensor E T (Fin.cons i (Fin.cons j (Fin.cons k (Fin.cons l ![])))) = _
  simp only [frameTensor_cons, frameTensor_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  change E a i * (E b j * (E c k * (E d l * T ![a, b, c, d]))) = _
  ring

private theorem frameTensor_trace_gram (E : Mat4) (T : CovariantCoordinates 4)
    (j k : Fin 4) :
    (∑ i, frameTensor E T ![i, j, k, i]) =
      ∑ b, ∑ c, E b j * E c k *
        (∑ a, ∑ d, (E * Eᵀ) a d * T ![a, b, c, d]) := by
  simp only [frameTensor_four]
  calc
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ i,
        E a i * E b j * E c k * E d i * T ![a, b, c, d] := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, ∑ c, ∑ d,
        E b j * E c k * ((E * Eᵀ) a d * T ![a, b, c, d]) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ b, ∑ c, ∑ a, ∑ d,
        E b j * E c k * ((E * Eᵀ) a d * T ![a, b, c, d]) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = _ := by simp only [Finset.mul_sum]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem OrthonormalFrame.matrix_mul_transpose (e : OrthonormalFrame g c) :
    e.matrix * e.matrixᵀ = (chartMetric g c)⁻¹ := by
  have hi : e.matrix * (e.matrixᵀ * chartMetric g c) = 1 :=
    mul_eq_one_comm.mp e.orthonormal
  have hG : IsUnit (chartMetric g c).det :=
    isUnit_iff_ne_zero.mpr (chartMetric_posDef g c).det_pos.ne'
  calc
    _ = e.matrix * e.matrixᵀ * (chartMetric g c * (chartMetric g c)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ hG, mul_one]
    _ = (e.matrix * (e.matrixᵀ * chartMetric g c)) * (chartMetric g c)⁻¹ := by
      noncomm_ring
    _ = _ := by rw [hi, one_mul]

/-- Contracting in an orthonormal frame equals contraction by the inverse
chart metric before framing the uncontracted indices. -/
theorem frameTensor_trace_inverse (e : OrthonormalFrame g c)
    (T : CovariantCoordinates 4) (j k : Fin 4) :
    (∑ i, frameTensor e.matrix T ![i, j, k, i]) =
      ∑ b, ∑ d, e.matrix b j * e.matrix d k *
        (∑ a, ∑ f, (chartMetric g c)⁻¹ a f * T ![a, b, d, f]) := by
  rw [frameTensor_trace_gram, e.matrix_mul_transpose]

/-- All three derivative/Ricci slots transform by the same frame. -/
theorem frame_curvature_derivative_trace (e : OrthonormalFrame g c)
    (a j k : Fin 4) :
    (∑ i, frameTensor e.matrix
      (covariantDerivative g c (curvatureCoordinates g c) (chartAt FourSpace c c))
      ![a, i, j, k, i]) =
      frameTensor e.matrix
        (covariantDerivative g c (ricciTensorCoordinates g c) (chartAt FourSpace c c))
        ![a, j, k] := by
  have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  have hdet := (chartMetric_posDef g c).det_pos.ne'
  change (∑ i, frameTensor e.matrix
    (covariantDerivative g c (curvatureCoordinates g c) (chartAt FourSpace c c))
    (Fin.cons a ![i, j, k, i])) = _
  simp only [frameTensor_cons (n := 4)]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, frameTensor_trace_inverse, frameTensor_three]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro d _
  have h := lowered_curvature_derivative_contraction g c (chartAt FourSpace c c)
    hz hdet t b d
  simp only [← Finset.mul_sum]
  change e.matrix t a * (e.matrix b j * e.matrix d k *
    (∑ r, ∑ s, (chartMetric g c)⁻¹ r s *
      covariantDerivative g c (curvatureCoordinates g c) (chartAt FourSpace c c)
        ![t, r, b, d, s])) = _
  calc
    _ = e.matrix t a * (e.matrix b j * e.matrix d k *
        covariantDerivative g c (ricciTensorCoordinates g c) (chartAt FourSpace c c)
          ![t, b, d]) :=
      congrArg (fun x : ℝ => e.matrix t a * (e.matrix b j * e.matrix d k * x)) h
    _ = _ := by ring

theorem frame_curvature_derivative_trace_zero (e : OrthonormalFrame g c)
    (hRic : covariantDerivative g c (ricciTensorCoordinates g c)
      (chartAt FourSpace c c) = 0) (a j k : Fin 4) :
    (∑ i, frameTensor e.matrix
      (covariantDerivative g c (curvatureCoordinates g c) (chartAt FourSpace c c))
      ![a, i, j, k, i]) = 0 := by
  rw [frame_curvature_derivative_trace, hRic]
  simp [frameTensor]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar Weyl equation at zero regularization. Its singular energy
term is controlled by the proved integrable energy quotient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators Topology Manifold ContDiff

noncomputable section

def scalarNormExpression (ε : ℝ) (A : Mat) (Z : Fin 4 → Mat) : ℝ :=
  (weylGradientEnergy Z - ∑ i, regularizedRadialDerivative ε A (Z i) ^ 2) /
    regularizedBlockNorm ε A + regularizedRadialDerivative ε A (weylLaplacian A)

theorem abs_scalarNormExpression_le (ε : ℝ) (hε : 0 < ε)
    (A : Mat) (Z : Fin 4 → Mat) (hA : symmetric A)
    (hz : normalizedBlockNorm A = 0 → Z = 0)
    (hk : ‖blockRadialGradient A Z‖ ^ 2 ≤ weylGradientEnergy Z) :
    |scalarNormExpression ε A Z| ≤ weylGradientEnergy Z / normalizedBlockNorm A +
      normalizedBlockNorm (weylLaplacian A) := by
  have he := weylGradientEnergy_nonneg Z
  have hn := regularizedBlockNorm_pos ε hε A
  have hp := regularized_radial_energy_le ε hε A Z
  have hpn : 0 ≤ ∑ i, regularizedRadialDerivative ε A (Z i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hq : 0 ≤ (weylGradientEnergy Z -
      ∑ i, regularizedRadialDerivative ε A (Z i) ^ 2) / regularizedBlockNorm ε A :=
    div_nonneg (by linarith) hn.le
  have hb : (weylGradientEnergy Z -
      ∑ i, regularizedRadialDerivative ε A (Z i) ^ 2) / regularizedBlockNorm ε A ≤
      weylGradientEnergy Z / normalizedBlockNorm A := by
    by_cases hv : normalizedBlockNorm A = 0
    · have hZ := hz hv
      subst Z
      simp [weylGradientEnergy, matrixPairing, regularizedRadialDerivative]
    · exact (div_le_div_of_nonneg_right (sub_le_self _ hpn) hn.le).trans
        (div_le_div_of_nonneg_left he
          (lt_of_le_of_ne (normalizedBlockNorm_nonneg A) (Ne.symm hv))
          (norm_le_regularizedBlockNorm ε A))
  exact (abs_add_le _ _).trans (add_le_add
    (by rwa [abs_of_nonneg hq])
    (abs_regularizedRadialDerivative_le ε hε A (weylLaplacian A)
      (weylLaplacian_symmetric A hA)))

theorem tendsto_scalarNormExpression (A : Mat) (Z : Fin 4 → Mat)
    (hz : normalizedBlockNorm A = 0 → Z = 0) :
    Tendsto (fun ε => scalarNormExpression ε A Z) (𝓝 0)
      (𝓝 (scalarNormExpression 0 A Z)) := by
  have ht := tendsto_regularizedRadialDerivative A (weylLaplacian A)
  have hp (i : Fin 4) : Tendsto (fun ε => regularizedRadialDerivative ε A (Z i))
      (𝓝 0) (𝓝 (regularizedRadialDerivative 0 A (Z i))) := by
    simpa [regularizedRadialDerivative, regularizedBlockNorm_zero] using
      tendsto_regularizedRadialDerivative A (Z i)
  have ht' : Tendsto (fun ε => regularizedRadialDerivative ε A (weylLaplacian A))
      (𝓝 0) (𝓝 (regularizedRadialDerivative 0 A (weylLaplacian A))) := by
    simpa [regularizedRadialDerivative, regularizedBlockNorm_zero] using ht
  by_cases hv : normalizedBlockNorm A = 0
  · have hZ := hz hv
    subst Z
    simpa [scalarNormExpression, weylGradientEnergy, matrixPairing,
      regularizedRadialDerivative] using ht'
  · exact ((tendsto_const_nhds.sub (tendsto_finsetSum _ (fun i _ => (hp i).pow 2))).div
      (by simpa only [regularizedBlockNorm_zero] using tendsto_regularizedBlockNorm A)
      (by simpa only [regularizedBlockNorm_zero] using hv)).add ht'

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem integral_scalarNormExpression_tendsto (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hkato : ∀ e : FrameBundle g, (5 / 3 : ℝ) *
      ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2 ≤
        weylGradientEnergy (plusWeylGradient g e.base e.frame))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ e, scalarNormExpression (ε n) (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame) ∂μ) atTop
      (𝓝 (∫ e, scalarNormExpression 0 (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun e =>
    weylGradientEnergy (plusWeylGradient g e.base e.frame) /
      normalizedBlockNorm (plusWeyl g e.base e.frame) + d.laplacianNormField e)
  · intro n
    have hN := (d.regularizedNormField (ε n)).continuous
    have hP : Continuous (fun e => ∑ i, (d.regularizedRadialField (ε n) (hε n) i e) ^ 2) := by
      fun_prop
    exact ((((d.gradientEnergyField.continuous.sub hP).div hN
      (fun e => (regularizedBlockNorm_pos (ε n) (hε n) _).ne')).add
        (continuous_regularizedRadialDerivative (ε n) (hε n) _ _ d.continuousWeyl
          (continuous_weylLaplacian.comp d.continuousWeyl)))).aestronglyMeasurable
  · exact (d.integrableEnergyQuotient hkato).add
      (d.laplacianNormField.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  · intro n
    filter_upwards [d.gradient_zero_ae_on_zero] with e he
    rw [Real.norm_eq_abs]
    apply abs_scalarNormExpression_le (ε n) (hε n) _ _ (d.weyl.symmetric e)
    · intro hv
      exact funext (he ((normalizedBlockNorm_eq_zero_iff _).mp hv))
    · have hk := hkato e
      nlinarith [sq_nonneg ‖blockRadialGradient (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame)‖]
  · filter_upwards [d.gradient_zero_ae_on_zero] with e he
    exact (tendsto_scalarNormExpression _ _ (fun hv =>
      funext (he ((normalizedBlockNorm_eq_zero_iff _).mp hv)))).comp hlim

theorem scalarNormEquation (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hkato : ∀ e : FrameBundle g, (5 / 3 : ℝ) *
      ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2 ≤
        weylGradientEnergy (plusWeylGradient g e.base e.frame)) :
    (∫ e, scalarNormExpression 0 (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame) ∂μ) = 0 := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hz (n) : (∫ e, scalarNormExpression (ε n) (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame) ∂μ) = 0 := by
    have h := d.testedRegularizedNormEquation (ε n) (hε n) (ContinuousMap.const _ 1)
      (fun _ => ContinuousMap.const _ 0) (by intro i t e; exact hasDerivAt_const t 1)
    simpa only [ContinuousMap.coe_const, Function.const_apply, one_mul, zero_mul,
      Finset.sum_const_zero, add_zero, regularizedNormField, regularizedRadialField,
      ContinuousMap.coe_mk, regularized_norm_laplacian_split, scalarNormExpression] using h
  have h := d.integral_scalarNormExpression_tendsto hkato ε hε hlim
  simp only [hz] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Apply the proved scalar variance theorem to smooth regularizations of
actual oriented Weyl norms. All equalities with frame derivatives are
proved from the raw parallel calculus. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ}

def scalarVarianceWeight (g : SmoothMetric M) (e : FrameBundle g) : ℝ :=
  4 + normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 +
    normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2

theorem PetersenOrientedNormInput.plus_regularized_vector
    {orientation : FrameOrientation g} (h : PetersenOrientedNormInput orientation)
    (hflow : OrientationPreservingFlow d orientation) {ε : ℝ} (hε : 0 < ε)
    (s : ScalarCovariantData d (orientedNormRegularization (plusNorm orientation) ε))
    (e : FrameBundle g) (he : e ∈ orientation.positive) :
    scalarGradientVector g (orientedNormRegularization (plusNorm orientation) ε) e =
      Variance.regularizedRadialVector (normalizedBlockNorm (plusWeyl g e.base e.frame)) ε
        (blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)) := by
  ext i
  change scalarGradient g _ e i =
    (normalizedBlockNorm (plusWeyl g e.base e.frame) /
      regularizedBlockNorm ε (plusWeyl g e.base e.frame)) *
        regularizedRadialDerivative 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame i)
  rw [h.plus_regularized_gradient hflow hε s e he i, regularizedRadialDerivative_scale]

theorem PetersenOrientedNormInput.minus_regularized_vector
    {orientation : FrameOrientation g} (h : PetersenOrientedNormInput orientation)
    (o : OppositeWeylData d) (hflow : OrientationPreservingFlow d orientation)
    {ε : ℝ} (hε : 0 < ε)
    (s : ScalarCovariantData d (orientedNormRegularization (minusNorm orientation) ε))
    (e : FrameBundle g) (he : e ∈ orientation.positive) :
    scalarGradientVector g (orientedNormRegularization (minusNorm orientation) ε) e =
      Variance.regularizedRadialVector (normalizedBlockNorm (minusWeyl g e.base e.frame)) ε
        (blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)) := by
  ext i
  change scalarGradient g _ e i =
    (normalizedBlockNorm (minusWeyl g e.base e.frame) /
      regularizedBlockNorm ε (minusWeyl g e.base e.frame)) *
        regularizedRadialDerivative 0 (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame i)
  rw [h.minus_regularized_gradient o hflow hε s e he i, regularizedRadialDerivative_scale]

variable [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]

theorem smooth_weighted_variance_ae
    (o : OppositeWeylData d) (hcalc : PetersenScalarCalculusInput d)
    (hpoisson : PetersenPoissonInput g μ) (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (a : M → ℝ) (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a)
    (f : FrameBundle g → ℝ) (p : FrameBundle g → Bianchi.Vec)
    (hf : (fun e => a e.base) =ᵐ[μ] f)
    (hpgrad : scalarGradientVector g a =ᵐ[μ] p) :
    (∫ e, f e ^ 2 ∂μ) - (∫ e, f e ∂μ) ^ 2 ≤
      ∫ e, ‖p e‖ ^ 2 / scalarVarianceWeight g e ∂μ := by
  obtain ⟨s⟩ := hcalc a ha
  have hi : Integrable (fun e => a e.base) μ := s.continuousValue.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun e => a e.base ^ 2) μ := (s.continuousValue.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hv := smooth_weighted_variance o hcalc hpoisson hp hdecomp a ha
  rw [Variance.integral_centered_square hi hi2, Variance.variance_congr_ae hf] at hv
  apply hv.trans_eq
  apply integral_congr_ae
  filter_upwards [hpgrad] with e he
  rw [he]
  rfl

theorem regularized_difference_variance
    (o : OppositeWeylData d) (orientation : FrameOrientation g)
    (h : PetersenOrientedNormInput orientation)
    (hflow : OrientationPreservingFlow d orientation)
    (hae : ∀ᵐ e ∂μ, e ∈ orientation.positive)
    (hcalc : PetersenScalarCalculusInput d) (hpoisson : PetersenPoissonInput g μ)
    (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    {ε : ℝ} (hε : 0 < ε) :
    (∫ e, Variance.regularizedDifferenceValue
      (normalizedBlockNorm (plusWeyl g e.base e.frame))
      (normalizedBlockNorm (minusWeyl g e.base e.frame)) ε ^ 2 ∂μ) -
    (∫ e, Variance.regularizedDifferenceValue
      (normalizedBlockNorm (plusWeyl g e.base e.frame))
      (normalizedBlockNorm (minusWeyl g e.base e.frame)) ε ∂μ) ^ 2 ≤
    ∫ e, Variance.regularizedDifferenceEnergy
      (normalizedBlockNorm (plusWeyl g e.base e.frame))
      (normalizedBlockNorm (minusWeyl g e.base e.frame)) ε (scalarVarianceWeight g e)
      (blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame))
      (blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)) ∂μ := by
  let av := orientedNormRegularization (plusNorm orientation) ε
  let ab := orientedNormRegularization (minusNorm orientation) ε
  have hav := orientedNormRegularization_smooth h.plusSquareSmooth hε
  have hab := orientedNormRegularization_smooth h.minusSquareSmooth hε
  obtain ⟨sv⟩ := hcalc av hav
  obtain ⟨sb⟩ := hcalc ab hab
  obtain ⟨s⟩ := hcalc (fun c => av c - ab c) (hav.sub hab)
  apply smooth_weighted_variance_ae o hcalc hpoisson hp hdecomp
    (fun c => av c - ab c) (hav.sub hab)
  · filter_upwards [hae] with e he
    change Real.sqrt (plusNorm orientation e.base ^ 2 + ε ^ 2) -
      Real.sqrt (minusNorm orientation e.base ^ 2 + ε ^ 2) = _
    rw [h.plusFrame e he, h.minusFrame e he]
    rfl
  · filter_upwards [hae] with e he
    have hv := h.plus_regularized_vector hflow hε sv e he
    have hb := h.minus_regularized_vector o hflow hε sb e he
    have hd : scalarGradientVector g (fun c => av c - ab c) e =
        scalarGradientVector g av e - scalarGradientVector g ab e := by
      ext i
      exact scalarGradient_sub_of_data sv sb s e i
    exact hd.trans (congrArg₂ (fun x y : Bianchi.Vec => x - y) hv hb)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A chartwise Einstein identity may be differentiated because it holds
on an open set. The center-only `RicciThree` identity is deliberately not
used here; curvature naturality supplies this stronger local identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem covariantDerivative_const_smul (g : SmoothMetric M) (c : M)
    {n : ℕ} (r : ℝ) (T : FourSpace → CovariantCoordinates n) (z : FourSpace) :
    covariantDerivative g c (fun w => r • T w) z = r • covariantDerivative g c T z := by
  funext a
  have hd : partialDeriv (fun w => r * T w (fun i => a i.succ)) (a 0) z =
      r * partialDeriv (fun w => T w (fun i => a i.succ)) (a 0) z := by
    change fderiv ℝ (r • fun w => T w (fun i => a i.succ)) z (coordinateVector (a 0)) = _
    rw [fderiv_const_smul_field]
    rfl
  simp only [covariantDerivative, Pi.smul_apply, smul_eq_mul, hd, mul_sub,
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem ricci_parallel_of_chart_equation (g : SmoothMetric M) (c : M)
    (hRic : ∀ w ∈ (chartAt FourSpace c).target, ∀ i j,
      ricciInChart g c w i j = 3 * metricInChart g c w i j)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    covariantDerivative g c (ricciTensorCoordinates g c) z = 0 := by
  have he : ricciTensorCoordinates g c =ᶠ[𝓝 z]
      (fun w => (3 : ℝ) • metricTensorCoordinates g c w) := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
    funext a
    exact hRic w hw (a 0) (a 1)
  rw [covariantDerivative_congr g c he, covariantDerivative_const_smul,
    covariantDerivative_metricTensor g c z
      (isUnit_iff_ne_zero.mpr (metricInChart_posDef g c z hz).det_pos.ne'), smul_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Subtracting the parallel unit-curvature tensor preserves the actual
differential Bianchi identity. No Einstein or divergence assertion is
needed for this cyclic identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem covariantDerivative_normalizedWeyl (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) :
    covariantDerivative g c (normalizedWeylCoordinates g c) z =
      covariantDerivative g c (curvatureCoordinates g c) z := by
  unfold normalizedWeylCoordinates
  rw [covariantDerivative_sub]
  · rw [covariantDerivative_unitCurvature g c z hz hdet, sub_zero]
  · intro a
    exact (curvatureCoordinates_contDiffAt g c z hz hdet a).differentiableAt (by simp)
  · intro a
    exact (unitCurvatureCoordinates_contDiffAt g c z hz a).differentiableAt (by simp)

theorem normalizedWeylCoordinates_second_bianchi (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) :
    AlgebraicCurvature.DifferentialBianchi
      (curvatureDerivativeArray
        (covariantDerivative g c (normalizedWeylCoordinates g c) z)) := by
  rw [covariantDerivative_normalizedWeyl g c z hz hdet]
  exact curvatureCoordinates_second_bianchi g c z hz hdet

theorem frame_normalizedWeyl_second_bianchi (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) :
    AlgebraicCurvature.DifferentialBianchi
      (curvatureDerivativeArray (frameTensor e.matrix
        (covariantDerivative g c (normalizedWeylCoordinates g c)
          (chartAt FourSpace c c)))) := by
  apply frameTensor_differentialBianchi
  apply normalizedWeylCoordinates_second_bianchi
  · exact (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  · exact (chartMetric_posDef g c).det_pos.ne'

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar shape in the integrated Weyl equation is determined by
the actual determinant and norm, including at a zero Weyl block. Its
upper bound follows from the three-dimensional spectral identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bianchi TraceHessian QuaternionFrame
open scoped BigOperators Manifold ContDiff

noncomputable section

def normalizedDeterminantShape (A : Mat3) : ℝ :=
  A.det / (2 * normalizedBlockNorm A ^ 3)

private theorem shape_product (S : Shape) : (∏ i, S.s i) = 2 * S.sigma := by
  simp only [Fin.prod_univ_three, Shape.sigma, Fin.sum_univ_three]
  rw [S.trace_coordinates]
  ring

private theorem orthogonal_conjugate_det (A R : Mat3) (hR : Rᵀ * R = 1) :
    (Rᵀ * A * R).det = A.det := by
  calc
    _ = A.det * (Rᵀ * R).det := by simp only [Matrix.det_mul]; ring
    _ = _ := by rw [hR, Matrix.det_one, mul_one]

private theorem determinant_shape (A R : Mat3) (hR : Rᵀ * R = 1)
    (S : Shape)
    (hd : Rᵀ * A * R = Matrix.diagonal (fun i => normalizedBlockNorm A * S.s i)) :
    A.det = 2 * normalizedBlockNorm A ^ 3 * S.sigma := by
  rw [← orthogonal_conjugate_det A R hR, hd, Matrix.det_diagonal]
  calc
    _ = normalizedBlockNorm A ^ 3 * ∏ i, S.s i := by
      simp only [Fin.prod_univ_three]
      ring
    _ = _ := by rw [shape_product]; ring

theorem normalizedDeterminantShape_mul (A : Mat3) :
    A.det = 2 * normalizedDeterminantShape A * normalizedBlockNorm A ^ 3 := by
  by_cases h : normalizedBlockNorm A = 0
  · have hA := (normalizedBlockNorm_eq_zero_iff A).mp h
    simp [hA, normalizedDeterminantShape]
  · unfold normalizedDeterminantShape
    field_simp [h]

theorem normalizedDeterminantShape_le_one (A : Mat3)
    (hs : symmetric A) (ht : traceFree A) : normalizedDeterminantShape A ≤ 1 := by
  by_cases h : normalizedBlockNorm A = 0
  · simp [normalizedDeterminantShape, h]
  · have hp : 0 < normalizedBlockNorm A :=
      lt_of_le_of_ne (normalizedBlockNorm_nonneg A) (Ne.symm h)
    obtain ⟨R, hR, _, S, hS⟩ := exists_lifted_spectral_shape A hs ht hp
    have hd := determinant_shape A R hR S hS
    have he : normalizedDeterminantShape A = S.sigma := by
      unfold normalizedDeterminantShape
      rw [hd]
      field_simp [h]
    rw [he]
    nlinarith only [S.sigma_rho_circle, sq_nonneg S.rho]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def plusDeterminantShape (o : FrameOrientation g) (c : M) : ℝ :=
  normalizedDeterminantShape (plusWeyl g c (o.frame c))

def minusDeterminantShape (o : FrameOrientation g) (c : M) : ℝ :=
  normalizedDeterminantShape (minusWeyl g c (o.frame c))

theorem plusDeterminantShape_mul (o : FrameOrientation g) (c : M) :
    (plusWeyl g c (o.frame c)).det =
      2 * plusDeterminantShape o c * plusNorm o c ^ 3 :=
  normalizedDeterminantShape_mul _

theorem minusDeterminantShape_mul (o : FrameOrientation g) (c : M) :
    (minusWeyl g c (o.frame c)).det =
      2 * minusDeterminantShape o c * minusNorm o c ^ 3 :=
  normalizedDeterminantShape_mul _

theorem plusDeterminantShape_le_one (o : FrameOrientation g) (hRic : RicciThree g)
    (c : M) : plusDeterminantShape o c ≤ 1 :=
  normalizedDeterminantShape_le_one _ (actual_weyl_symmetric (o.frame c)).1
    (actual_weyl_traceFree (o.frame c) hRic).1

theorem minusDeterminantShape_le_one (o : FrameOrientation g) (hRic : RicciThree g)
    (c : M) : minusDeterminantShape o c ≤ 1 :=
  normalizedDeterminantShape_le_one _ (actual_weyl_symmetric (o.frame c)).2
    (actual_weyl_traceFree (o.frame c) hRic).2

end
end PositiveEinsteinFour.Geometry
end


section

/-! The center-wise Einstein hypothesis holds in every fixed metric chart
by Ricci naturality. It can therefore be differentiated on that chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem ricciInChart_transition (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    ricciInChart g c z = (chartTransitionMatrix c d z)ᵀ *
      ((show Mat4 from ricciInChart g d (chartTransition c d z)) * chartTransitionMatrix c d z) := by
  have htrace (q : M) (w : FourSpace) :
      ricciMatrix (fun i j => coordinateCurvatureMatrix g q i j w) =
        (show Mat4 from ricciInChart g q w) := by
    ext i j
    exact (ricciInChart_eq_curvatureMatrix_trace g q w i j).symm
  have h := ricciMatrix_pullback (chartTransitionMatrix c d z)
      (fun i j => coordinateCurvatureMatrix g d i j (chartTransition c d z))
      (fun i j => coordinateCurvatureMatrix g c i j z)
      (isUnit_iff_ne_zero.mpr (chartTransitionMatrix_det_ne_zero g c d z hz hx))
      (coordinateCurvatureMatrix_transition g c d z hz hx)
  rw [htrace c z, htrace d (chartTransition c d z)] at h
  exact h

theorem ricciThree_in_chart (g : SmoothMetric M) (hRic : RicciThree g)
    (c : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    ricciInChart g c z = (3 : ℝ) • metricInChart g c z := by
  change (show Mat4 from ricciInChart g c z) = (3 : ℝ) • metricInChart g c z
  let d := (chartAt FourSpace c).symm z
  have hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source :=
    mem_chart_source FourSpace d
  have hd : ricciInChart g d (chartAt FourSpace d d) =
      (3 : ℝ) • metricInChart g d (chartAt FourSpace d d) := by
    ext i j
    exact congrFun (congrFun (hRic d) i) j
  rw [ricciInChart_transition g c d z hz hx]
  change (chartTransitionMatrix c d z)ᵀ *
    ((show Mat4 from ricciInChart g d (chartAt FourSpace d d)) *
      chartTransitionMatrix c d z) = (3 : ℝ) • metricInChart g c z
  rw [hd, smul_mul_assoc, mul_smul_comm]
  change (3 : ℝ) • ((chartTransitionMatrix c d z)ᵀ *
    (metricInChart g d (chartTransition c d z) * chartTransitionMatrix c d z)) = _
  exact congrArg (fun A : Mat4 => (3 : ℝ) • A)
    (metricInChart_transition g c d z hz hx).symm

theorem actual_ricci_parallel (g : SmoothMetric M) (hRic : RicciThree g)
    (c : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    covariantDerivative g c (ricciTensorCoordinates g c) z = 0 := by
  apply ricci_parallel_of_chart_equation g c _ z hz
  intro w hw i j
  exact congrFun (congrFun (ricciThree_in_chart g hRic c w hw) i) j

theorem actual_ricci_parallel_at_center (g : SmoothMetric M) (hRic : RicciThree g)
    (c : M) :
    covariantDerivative g c (ricciTensorCoordinates g c) (chartAt FourSpace c c) = 0 :=
  actual_ricci_parallel g hRic c _ ((chartAt FourSpace c).map_source
    (mem_chart_source FourSpace c))

theorem actual_ricci_hessian (g : SmoothMetric M) (hRic : RicciThree g)
    (c : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    covariantDerivative g c (covariantDerivative g c (ricciTensorCoordinates g c)) z = 0 := by
  have he : covariantDerivative g c (ricciTensorCoordinates g c) =ᶠ[𝓝 z]
      (fun _ => 0) := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
    exact actual_ricci_parallel g hRic c w hw
  rw [covariantDerivative_congr g c he]
  simpa only [zero_smul] using
    covariantDerivative_const_smul g c (n := 3) 0 (fun _ => 0) z

end
end PositiveEinsteinFour.Geometry
end


section

/-! Covariant differentiation preserves the algebraic slot symmetries.
The statements here apply to the actual coordinate curvature and its
actual orthonormal-frame pullback. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem covariantDerivative_permute {n : ℕ} (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates n) (σ : Equiv.Perm (Fin n))
    (z : FourSpace) (d : Fin 4) (a : Fin n → Fin 4) :
    covariantDerivative g c (fun w b => T w (b ∘ σ)) z (Fin.cons d a) =
      covariantDerivative g c T z (Fin.cons d (a ∘ σ)) := by
  change partialDeriv (fun w => T w (a ∘ σ)) d z -
    (∑ i, ∑ b, christoffel g c z b d (a i) * T z ((Function.update a i b) ∘ σ)) =
    partialDeriv (fun w => T w (a ∘ σ)) d z -
    (∑ i, ∑ b, christoffel g c z b d (a (σ i)) *
      T z (Function.update (a ∘ σ) i b))
  congr 1
  rw [← Equiv.sum_comp σ (fun i => ∑ b,
    christoffel g c z b d (a i) * T z ((Function.update a i b) ∘ σ))]
  simp only [Function.update_comp_eq_of_injective a σ.injective]

theorem covariantDerivative_neg {n : ℕ} (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates n) (z : FourSpace) :
    covariantDerivative g c (fun w => -T w) z = -covariantDerivative g c T z := by
  have hp (a : Fin n → Fin 4) (d : Fin 4) :
      partialDeriv (fun w => -T w a) d z = -partialDeriv (fun w => T w a) d z := by
    change (fderiv ℝ (-(fun w => T w a)) z) (coordinateVector d) = _
    rw [fderiv_neg]
    rfl
  funext a
  change partialDeriv (fun w => -T w (fun i => a i.succ)) (a 0) z -
    (∑ i, ∑ b, christoffel g c z b (a 0) (a i.succ) *
      (-T z (Function.update (fun i => a i.succ) i b))) = _
  simp only [hp, mul_neg, Finset.sum_neg_distrib]
  simp only [Pi.neg_apply, covariantDerivative]
  ring

theorem covariantDerivative_permute_eq {n : ℕ} (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates n) (σ : Equiv.Perm (Fin n))
    (z : FourSpace)
    (h : (fun w b => T w (b ∘ σ)) =ᶠ[nhds z] T)
    (d : Fin 4) (a : Fin n → Fin 4) :
    covariantDerivative g c T z (Fin.cons d (a ∘ σ)) =
      covariantDerivative g c T z (Fin.cons d a) := by
  rw [← covariantDerivative_permute]
  exact congrFun (covariantDerivative_congr g c h) (Fin.cons d a)

theorem covariantDerivative_permute_neg {n : ℕ} (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates n) (σ : Equiv.Perm (Fin n))
    (z : FourSpace)
    (h : (fun w b => T w (b ∘ σ)) =ᶠ[nhds z] fun w => -T w)
    (d : Fin 4) (a : Fin n → Fin 4) :
    covariantDerivative g c T z (Fin.cons d (a ∘ σ)) =
      -covariantDerivative g c T z (Fin.cons d a) := by
  rw [← covariantDerivative_permute]
  have hc := congrFun (covariantDerivative_congr g c h) (Fin.cons d a)
  simpa only [covariantDerivative_neg, Pi.neg_apply] using hc

private theorem sum_tensor_permute {n : ℕ}
    (f : (Fin n → Fin 4) → ℝ) (σ : Equiv.Perm (Fin n)) :
    (∑ b, f b) = ∑ b, f (b ∘ σ) := by
  let e : (Fin n → Fin 4) ≃ (Fin n → Fin 4) :=
    Equiv.arrowCongr σ.symm (Equiv.refl (Fin 4))
  exact (e.sum_comp f).symm

theorem frameTensor_permute {n : ℕ} (E : Mat4) (T : CovariantCoordinates n)
    (σ : Equiv.Perm (Fin n)) (a : Fin n → Fin 4) :
    frameTensor E T (a ∘ σ) = frameTensor E (fun b => T (b ∘ σ)) a := by
  let f : (Fin n → Fin 4) → ℝ :=
    fun b => (∏ i, E (b i) (a (σ i))) * T b
  change (∑ b, f b) = _
  rw [sum_tensor_permute f σ]
  change (∑ b, (∏ i, E (b (σ i)) (a (σ i))) * T (b ∘ σ)) = _
  apply Finset.sum_congr rfl
  intro b _
  rw [Equiv.prod_comp σ (fun i => E (b i) (a i))]

theorem frameTensor_neg {n : ℕ} (E : Mat4) (T : CovariantCoordinates n)
    (a : Fin n → Fin 4) : frameTensor E (-T) a = -frameTensor E T a := by
  simp only [frameTensor, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The single-norm and square-root-polynomial smooth tests used in the
final variance and balanced-moment arguments. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ} [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]

theorem regularized_plus_variance
    (o : OppositeWeylData d) (orientation : FrameOrientation g)
    (h : PetersenOrientedNormInput orientation)
    (hflow : OrientationPreservingFlow d orientation)
    (hae : ∀ᵐ e ∂μ, e ∈ orientation.positive)
    (hcalc : PetersenScalarCalculusInput d) (hpoisson : PetersenPoissonInput g μ)
    (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    {ε : ℝ} (hε : 0 < ε) :
    (∫ e, Variance.hRegularizedArgument (normalizedBlockNorm (plusWeyl g e.base e.frame)) ε ^ 2 ∂μ) -
      (∫ e, Variance.hRegularizedArgument (normalizedBlockNorm (plusWeyl g e.base e.frame)) ε ∂μ) ^ 2 ≤
      ∫ e, Variance.regularizedNormEnergy (normalizedBlockNorm (plusWeyl g e.base e.frame)) ε (scalarVarianceWeight g e)
        (blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)) ∂μ := by
  let a := orientedNormRegularization (plusNorm orientation) ε
  have ha := orientedNormRegularization_smooth h.plusSquareSmooth hε
  obtain ⟨s⟩ := hcalc a ha
  apply smooth_weighted_variance_ae o hcalc hpoisson hp hdecomp a ha
  · filter_upwards [hae] with e he
    change Real.sqrt (plusNorm orientation e.base ^ 2 + ε ^ 2) = _
    rw [h.plusFrame e he]
    rfl
  · filter_upwards [hae] with e he
    exact h.plus_regularized_vector hflow hε s e he

theorem regularized_H_plus_variance
    (o : OppositeWeylData d) (orientation : FrameOrientation g)
    (h : PetersenOrientedNormInput orientation)
    (hflow : OrientationPreservingFlow d orientation)
    (hae : ∀ᵐ e ∂μ, e ∈ orientation.positive)
    (hcalc : PetersenScalarCalculusInput d) (hpoisson : PetersenPoissonInput g μ)
    (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    {ε : ℝ} (hε : 0 < ε) :
    (∫ e, Variance.hRegularizedValue (normalizedBlockNorm (plusWeyl g e.base e.frame)) ε ^ 2 ∂μ) -
      (∫ e, Variance.hRegularizedValue (normalizedBlockNorm (plusWeyl g e.base e.frame)) ε ∂μ) ^ 2 ≤
      ∫ e, Variance.hRegularizedEnergy (normalizedBlockNorm (plusWeyl g e.base e.frame)) ε
        (‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2) (scalarVarianceWeight g e) ∂μ := by
  let a := orientedNormRegularization (plusNorm orientation) ε
  have ha := orientedNormRegularization_smooth h.plusSquareSmooth hε
  have hap (c : M) : 0 < a c := Variance.hRegularizedArgument_pos _ _ hε
  have hH := contMDiff_H_of_pos ha hap
  obtain ⟨sa⟩ := hcalc a ha
  obtain ⟨sH⟩ := hcalc (fun c => MomentObstruction.H (a c)) hH
  have hv := smooth_weighted_variance_ae o hcalc hpoisson hp hdecomp
    (fun c => MomentObstruction.H (a c)) hH
    (fun e => Variance.hRegularizedValue (normalizedBlockNorm (plusWeyl g e.base e.frame)) ε)
    (fun e => Variance.hRegularizedDerivative (normalizedBlockNorm (plusWeyl g e.base e.frame)) ε • (blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)))
    (by
      filter_upwards [hae] with e he
      change MomentObstruction.H (Real.sqrt (plusNorm orientation e.base ^ 2 + ε ^ 2)) = _
      rw [h.plusFrame e he]
      rfl)
    (by
      filter_upwards [hae] with e he
      have hgrad := h.plus_regularized_vector hflow hε sa e he
      have hc : scalarGradientVector g (fun c => MomentObstruction.H (a c)) e =
          (Variance.derivativeRatio (a e.base) / (2 * Real.sqrt (a e.base))) •
            scalarGradientVector g a e := by
        ext i
        exact scalarGradient_H_of_data sa sH e (hap e.base) i
      rw [hc, hgrad, Variance.regularizedRadialVector, smul_smul]
      dsimp only [a, orientedNormRegularization]
      rw [h.plusFrame e he]
      rfl)
  have henergy (e : FrameBundle g) := Variance.hRegularizedGradient_energy
    (normalizedBlockNorm (plusWeyl g e.base e.frame)) ε (scalarVarianceWeight g e) (blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)) hε
  simpa only [henergy] using hv

theorem regularized_minus_variance
    (o : OppositeWeylData d) (orientation : FrameOrientation g)
    (h : PetersenOrientedNormInput orientation)
    (hflow : OrientationPreservingFlow d orientation)
    (hae : ∀ᵐ e ∂μ, e ∈ orientation.positive)
    (hcalc : PetersenScalarCalculusInput d) (hpoisson : PetersenPoissonInput g μ)
    (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    {ε : ℝ} (hε : 0 < ε) :
    (∫ e, Variance.hRegularizedArgument (normalizedBlockNorm (minusWeyl g e.base e.frame)) ε ^ 2 ∂μ) -
      (∫ e, Variance.hRegularizedArgument (normalizedBlockNorm (minusWeyl g e.base e.frame)) ε ∂μ) ^ 2 ≤
      ∫ e, Variance.regularizedNormEnergy (normalizedBlockNorm (minusWeyl g e.base e.frame)) ε (scalarVarianceWeight g e)
        (blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)) ∂μ := by
  let a := orientedNormRegularization (minusNorm orientation) ε
  have ha := orientedNormRegularization_smooth h.minusSquareSmooth hε
  obtain ⟨s⟩ := hcalc a ha
  apply smooth_weighted_variance_ae o hcalc hpoisson hp hdecomp a ha
  · filter_upwards [hae] with e he
    change Real.sqrt (minusNorm orientation e.base ^ 2 + ε ^ 2) = _
    rw [h.minusFrame e he]
    rfl
  · filter_upwards [hae] with e he
    exact h.minus_regularized_vector o hflow hε s e he

theorem regularized_H_minus_variance
    (o : OppositeWeylData d) (orientation : FrameOrientation g)
    (h : PetersenOrientedNormInput orientation)
    (hflow : OrientationPreservingFlow d orientation)
    (hae : ∀ᵐ e ∂μ, e ∈ orientation.positive)
    (hcalc : PetersenScalarCalculusInput d) (hpoisson : PetersenPoissonInput g μ)
    (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    {ε : ℝ} (hε : 0 < ε) :
    (∫ e, Variance.hRegularizedValue (normalizedBlockNorm (minusWeyl g e.base e.frame)) ε ^ 2 ∂μ) -
      (∫ e, Variance.hRegularizedValue (normalizedBlockNorm (minusWeyl g e.base e.frame)) ε ∂μ) ^ 2 ≤
      ∫ e, Variance.hRegularizedEnergy (normalizedBlockNorm (minusWeyl g e.base e.frame)) ε
        (‖blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)‖ ^ 2) (scalarVarianceWeight g e) ∂μ := by
  let a := orientedNormRegularization (minusNorm orientation) ε
  have ha := orientedNormRegularization_smooth h.minusSquareSmooth hε
  have hap (c : M) : 0 < a c := Variance.hRegularizedArgument_pos _ _ hε
  have hH := contMDiff_H_of_pos ha hap
  obtain ⟨sa⟩ := hcalc a ha
  obtain ⟨sH⟩ := hcalc (fun c => MomentObstruction.H (a c)) hH
  have hv := smooth_weighted_variance_ae o hcalc hpoisson hp hdecomp
    (fun c => MomentObstruction.H (a c)) hH
    (fun e => Variance.hRegularizedValue (normalizedBlockNorm (minusWeyl g e.base e.frame)) ε)
    (fun e => Variance.hRegularizedDerivative (normalizedBlockNorm (minusWeyl g e.base e.frame)) ε • (blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)))
    (by
      filter_upwards [hae] with e he
      change MomentObstruction.H (Real.sqrt (minusNorm orientation e.base ^ 2 + ε ^ 2)) = _
      rw [h.minusFrame e he]
      rfl)
    (by
      filter_upwards [hae] with e he
      have hgrad := h.minus_regularized_vector o hflow hε sa e he
      have hc : scalarGradientVector g (fun c => MomentObstruction.H (a c)) e =
          (Variance.derivativeRatio (a e.base) / (2 * Real.sqrt (a e.base))) •
            scalarGradientVector g a e := by
        ext i
        exact scalarGradient_H_of_data sa sH e (hap e.base) i
      rw [hc, hgrad, Variance.regularizedRadialVector, smul_smul]
      dsimp only [a, orientedNormRegularization]
      rw [h.minusFrame e he]
      rfl)
  have henergy (e : FrameBundle g) := Variance.hRegularizedGradient_energy
    (normalizedBlockNorm (minusWeyl g e.base e.frame)) ε (scalarVarianceWeight g e) (blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)) hε
  simpa only [henergy] using hv

end
end PositiveEinsteinFour.Geometry
end


section

/-! Pass the actual weak norm equation through bounded smooth test
approximations, including their first derivatives. This is the limit used
for the polynomial multiplier in the two-block coupling. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators Topology Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

def scalarNormField (d : MetricGreenData g μ) (ε : ℝ) (hε : 0 < ε) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => scalarNormExpression ε (plusWeyl g e.base e.frame)
    (plusWeylGradient g e.base e.frame), by
    have hP : Continuous (fun e => ∑ i, (d.regularizedRadialField ε hε i e) ^ 2) := by
      fun_prop
    exact ((d.gradientEnergyField.continuous.sub hP).div (d.regularizedNormField ε).continuous
      (fun e => (regularizedBlockNorm_pos ε hε _).ne')).add
        (continuous_regularizedRadialDerivative ε hε _ _ d.continuousWeyl
          (continuous_weylLaplacian.comp d.continuousWeyl))⟩

theorem testedNormEquation_of_limits (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hkato : ∀ e : FrameBundle g, (5 / 3 : ℝ) *
      ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2 ≤
        weylGradientEnergy (plusWeylGradient g e.base e.frame))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (k : ℕ → C(FrameBundle g, ℝ)) (dk : ℕ → Fin 4 → C(FrameBundle g, ℝ))
    (hk : ∀ n i t e, HasDerivAt (fun s => k n ((d.flow i).map s e))
      (dk n i ((d.flow i).map t e)) t)
    (k₀ : FrameBundle g → ℝ) (dk₀ : Fin 4 → FrameBundle g → ℝ)
    (hklim : ∀ e, Tendsto (fun n => k n e) atTop (𝓝 (k₀ e)))
    (hdlim : ∀ i e, Tendsto (fun n => dk n i e) atTop (𝓝 (dk₀ i e)))
    (C : ℝ) (hC : 0 ≤ C) (hkbound : ∀ n e, |k n e| ≤ C)
    (B : Fin 4 → C(FrameBundle g, ℝ)) (hdbound : ∀ n i e, |dk n i e| ≤ B i e) :
    (∫ e, k₀ e * scalarNormExpression 0 (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) +
      ∑ i, dk₀ i e * regularizedRadialDerivative 0 (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) ∂μ) = 0 := by
  let F : ℕ → FrameBundle g → ℝ := fun n e =>
    k n e * d.scalarNormField (ε n) (hε n) e +
      ∑ i, dk n i e * d.regularizedRadialField (ε n) (hε n) i e
  let H : FrameBundle g → ℝ := fun e =>
    weylGradientEnergy (plusWeylGradient g e.base e.frame) /
      normalizedBlockNorm (plusWeyl g e.base e.frame) + d.laplacianNormField e
  let J : C(FrameBundle g, ℝ) := ⟨fun e =>
    ∑ i, B i e * normalizedBlockNorm (plusWeylGradient g e.base e.frame i), by
      apply continuous_finsetSum
      intro i _
      exact (B i).continuous.mul (continuous_normalizedBlockNorm.comp (d.continuousGradient i))⟩
  have hF (n) : Continuous (F n) := by
    exact ((k n).continuous.mul (d.scalarNormField (ε n) (hε n)).continuous).add
      (continuous_finsetSum _ (fun i _ => (dk n i).continuous.mul
        (d.regularizedRadialField (ε n) (hε n) i).continuous))
  have hH : Integrable H μ := (d.integrableEnergyQuotient hkato).add
    (d.laplacianNormField.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hconv : Tendsto (fun n => ∫ e, F n e ∂μ) atTop
      (𝓝 (∫ e, k₀ e * scalarNormExpression 0 (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) +
        ∑ i, dk₀ i e * regularizedRadialDerivative 0 (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame i) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun e => C * H e + J e)
    · exact fun n => (hF n).aestronglyMeasurable
    · exact (hH.const_mul C).add (J.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
    · intro n
      filter_upwards [d.gradient_zero_ae_on_zero] with e he
      have hs := abs_scalarNormExpression_le (ε n) (hε n) _ _ (d.weyl.symmetric e)
        (fun hv => funext (he ((normalizedBlockNorm_eq_zero_iff _).mp hv)))
        (by
          have h := hkato e
          have hp := sq_nonneg ‖blockRadialGradient (plusWeyl g e.base e.frame)
            (plusWeylGradient g e.base e.frame)‖
          nlinarith)
      rw [Real.norm_eq_abs]
      change |k n e * d.scalarNormField (ε n) (hε n) e +
        ∑ i, dk n i e * d.regularizedRadialField (ε n) (hε n) i e| ≤ _
      calc
        _ ≤ |k n e * d.scalarNormField (ε n) (hε n) e| +
            ∑ i, |dk n i e * d.regularizedRadialField (ε n) (hε n) i e| :=
          (abs_add_le _ _).trans (add_le_add (le_refl _) (Finset.abs_sum_le_sum_abs _ _))
        _ ≤ C * H e + J e := by
          apply add_le_add
          · rw [abs_mul]
            exact mul_le_mul (hkbound n e) hs (abs_nonneg _) hC
          · change _ ≤ ∑ i, B i e * normalizedBlockNorm (plusWeylGradient g e.base e.frame i)
            apply Finset.sum_le_sum
            intro i _
            rw [abs_mul]
            exact mul_le_mul (hdbound n i e)
              (abs_regularizedRadialDerivative_le (ε n) (hε n) _ _ ((d.gradientConstraints e).1 i))
              (abs_nonneg _) ((abs_nonneg _).trans (hdbound n i e))
    · filter_upwards [d.gradient_zero_ae_on_zero] with e he
      apply Tendsto.add
      · exact (hklim e).mul ((tendsto_scalarNormExpression _ _
          (fun hv => funext (he ((normalizedBlockNorm_eq_zero_iff _).mp hv)))).comp hlim)
      · apply tendsto_finsetSum
        intro i _
        apply (hdlim i e).mul
        simpa only [regularizedRadialField, ContinuousMap.coe_mk, regularizedRadialDerivative,
          regularizedBlockNorm_zero, Function.comp_def] using
          (tendsto_regularizedRadialDerivative (plusWeyl g e.base e.frame)
            (plusWeylGradient g e.base e.frame i)).comp hlim
  have hz (n) : (∫ e, F n e ∂μ) = 0 := by
    have h := d.testedRegularizedNormEquation (ε n) (hε n) (k n) (dk n) (hk n)
    simpa only [F, scalarNormField, scalarNormExpression, regularizedNormField, regularizedRadialField,
      ContinuousMap.coe_mk, regularized_norm_laplacian_split] using h
  simp only [hz] at hconv
  exact tendsto_nhds_unique hconv tendsto_const_nhds

theorem testedNormEquation (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hkato : ∀ e : FrameBundle g, (5 / 3 : ℝ) *
      ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2 ≤
        weylGradientEnergy (plusWeylGradient g e.base e.frame))
    (k : C(FrameBundle g, ℝ)) (dk : Fin 4 → C(FrameBundle g, ℝ))
    (hk : ∀ i t e, HasDerivAt (fun s => k ((d.flow i).map s e))
      (dk i ((d.flow i).map t e)) t) :
    (∫ e, k e * scalarNormExpression 0 (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) +
      ∑ i, dk i e * regularizedRadialDerivative 0 (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) ∂μ) = 0 := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn k.continuous.continuousOn
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  let B : Fin 4 → C(FrameBundle g, ℝ) := fun i =>
    ⟨fun e => |dk i e|, (dk i).continuous.abs⟩
  apply d.testedNormEquation_of_limits hkato ε hε tendsto_one_div_add_atTop_nhds_zero_nat
    (fun _ => k) (fun _ => dk) (fun _ => hk) (fun e => k e) (fun i e => dk i e)
    (fun _ => tendsto_const_nhds) (fun _ _ => tendsto_const_nhds) |C| (abs_nonneg C)
    (fun _ e => ?_) B (fun _ _ _ => le_rfl)
  have hc : |k e| ≤ C := by simpa only [Real.norm_eq_abs] using hC e (Set.mem_univ e)
  exact hc.trans (le_abs_self C)

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Contract the actual Weyl equation with the Weyl tensor. The cubic
trace is its determinant, so the result uses the canonical shape even
where the Weyl block is zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped BigOperators

noncomputable section

theorem traceCube_eq_three_det (A : Mat3) (hs : symmetric A) (ht : traceFree A) :
    Matrix.trace (A * (A * A)) = 3 * A.det := by
  rw [← coordinates_eq A hs ht]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.det_fin_three, Fin.sum_univ_three]
  norm_num [ofCoordinates]
  ring

theorem weylLaplacian_pairing (A : Mat3) (hs : symmetric A) (ht : traceFree A) :
    matrixPairing A (weylLaplacian A) =
      36 * (normalizedBlockNorm A ^ 2 -
        normalizedDeterminantShape A * normalizedBlockNorm A ^ 3) := by
  have hsym : (weylLaplacian A)ᵀ = weylLaplacian A := by
    ext i j
    exact weylLaplacian_symmetric A hs j i
  have htr : Matrix.trace A = 0 := ht
  rw [matrixPairing_eq_trace, hsym]
  simp only [weylLaplacian, traceFreeSquare, mul_smul_comm, Matrix.mul_sub,
    Matrix.trace_smul, Matrix.trace_sub, Matrix.mul_one, htr, smul_eq_mul,
    mul_zero, sub_zero, trace_square_eq_six_norm_sq A hs,
    traceCube_eq_three_det A hs ht, normalizedDeterminantShape_mul A]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The finite covector-slot action used by the actual tensor commutator.
The anti-representation sign comes from acting on covariant slots. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

/-- Apply a matrix in one covariant slot. -/
def covariantSlotAction {n : ℕ} (s : Fin n) (A : Mat4)
    (T : CovariantCoordinates n) : CovariantCoordinates n := fun a =>
  ∑ b, A b (a s) * T (Function.update a s b)

/-- The induced action on all covariant slots. -/
def tensorSlotAction {n : ℕ} (A : Mat4) (T : CovariantCoordinates n) :
    CovariantCoordinates n := fun a => ∑ s, covariantSlotAction s A T a

theorem covariantSlotAction_add_matrix {n : ℕ} (s : Fin n) (A B : Mat4)
    (T : CovariantCoordinates n) :
    covariantSlotAction s (A + B) T =
      covariantSlotAction s A T + covariantSlotAction s B T := by
  funext a
  simp only [covariantSlotAction, Matrix.add_apply, add_mul,
    Finset.sum_add_distrib, Pi.add_apply]

theorem covariantSlotAction_sub_matrix {n : ℕ} (s : Fin n) (A B : Mat4)
    (T : CovariantCoordinates n) :
    covariantSlotAction s (A - B) T =
      covariantSlotAction s A T - covariantSlotAction s B T := by
  funext a
  simp only [covariantSlotAction, Matrix.sub_apply, sub_mul,
    Finset.sum_sub_distrib, Pi.sub_apply]

theorem covariantSlotAction_add_tensor {n : ℕ} (s : Fin n) (A : Mat4)
    (S T : CovariantCoordinates n) :
    covariantSlotAction s A (S + T) =
      covariantSlotAction s A S + covariantSlotAction s A T := by
  funext a
  simp only [covariantSlotAction, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem covariantSlotAction_sub_tensor {n : ℕ} (s : Fin n) (A : Mat4)
    (S T : CovariantCoordinates n) :
    covariantSlotAction s A (S - T) =
      covariantSlotAction s A S - covariantSlotAction s A T := by
  funext a
  simp only [covariantSlotAction, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem covariantSlotAction_same {n : ℕ} (s : Fin n) (A B : Mat4)
    (T : CovariantCoordinates n) :
    covariantSlotAction s A (covariantSlotAction s B T) =
      covariantSlotAction s (B * A) T := by
  funext a
  simp only [covariantSlotAction, Function.update_self, Function.update_idem,
    Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem covariantSlotAction_distinct {n : ℕ} (s t : Fin n) (hst : s ≠ t)
    (A B : Mat4) (T : CovariantCoordinates n) :
    covariantSlotAction s A (covariantSlotAction t B T) =
      covariantSlotAction t B (covariantSlotAction s A T) := by
  funext a
  simp only [covariantSlotAction, Function.update_of_ne hst,
    Function.update_of_ne hst.symm, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro b _
  rw [Function.update_comm hst]
  ring

theorem covariantSlotAction_commutator {n : ℕ} (s t : Fin n)
    (A B : Mat4) (T : CovariantCoordinates n) :
    covariantSlotAction s A (covariantSlotAction t B T) -
      covariantSlotAction t B (covariantSlotAction s A T) =
        if s = t then covariantSlotAction s (B * A - A * B) T else 0 := by
  by_cases hst : s = t
  · subst t
    rw [ite_eq_left rfl, covariantSlotAction_same, covariantSlotAction_same,
      covariantSlotAction_sub_matrix]
  · rw [ite_eq_right hst, covariantSlotAction_distinct s t hst, sub_self]

theorem tensorSlotAction_add_matrix {n : ℕ} (A B : Mat4)
    (T : CovariantCoordinates n) :
    tensorSlotAction (A + B) T = tensorSlotAction A T + tensorSlotAction B T := by
  funext a
  simp only [tensorSlotAction, covariantSlotAction_add_matrix, Pi.add_apply,
    Finset.sum_add_distrib]

theorem tensorSlotAction_sub_matrix {n : ℕ} (A B : Mat4)
    (T : CovariantCoordinates n) :
    tensorSlotAction (A - B) T = tensorSlotAction A T - tensorSlotAction B T := by
  funext a
  simp only [tensorSlotAction, covariantSlotAction_sub_matrix, Pi.sub_apply,
    Finset.sum_sub_distrib]

theorem tensorSlotAction_add_tensor {n : ℕ} (A : Mat4)
    (S T : CovariantCoordinates n) :
    tensorSlotAction A (S + T) = tensorSlotAction A S + tensorSlotAction A T := by
  funext a
  simp only [tensorSlotAction, covariantSlotAction_add_tensor, Pi.add_apply,
    Finset.sum_add_distrib]

theorem tensorSlotAction_sub_tensor {n : ℕ} (A : Mat4)
    (S T : CovariantCoordinates n) :
    tensorSlotAction A (S - T) = tensorSlotAction A S - tensorSlotAction A T := by
  funext a
  simp only [tensorSlotAction, covariantSlotAction_sub_tensor, Pi.sub_apply,
    Finset.sum_sub_distrib]

private theorem tensorSlotAction_compose {n : ℕ} (A B : Mat4)
    (T : CovariantCoordinates n) (a : Fin n → Fin 4) :
    tensorSlotAction A (tensorSlotAction B T) a =
      ∑ s, ∑ t, covariantSlotAction s A (covariantSlotAction t B T) a := by
  unfold tensorSlotAction
  apply Finset.sum_congr rfl
  intro s _
  simp only [covariantSlotAction, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Covariant tensors form the anti-representation of the matrix slot
operation; the opposite sign is the covector curvature sign. -/
theorem tensorSlotAction_commutator {n : ℕ} (A B : Mat4)
    (T : CovariantCoordinates n) :
    tensorSlotAction A (tensorSlotAction B T) -
      tensorSlotAction B (tensorSlotAction A T) =
        tensorSlotAction (B * A - A * B) T := by
  funext a
  rw [Pi.sub_apply, tensorSlotAction_compose, tensorSlotAction_compose]
  rw [Finset.sum_comm (f := fun s t => covariantSlotAction s B (covariantSlotAction t A T) a)]
  rw [← Finset.sum_sub_distrib]
  change (∑ s, ((∑ t, covariantSlotAction s A (covariantSlotAction t B T) a) -
    (∑ t, covariantSlotAction t B (covariantSlotAction s A T) a))) = _
  simp only [← Finset.sum_sub_distrib]
  have he (s t : Fin n) :
      covariantSlotAction s A (covariantSlotAction t B T) a -
        covariantSlotAction t B (covariantSlotAction s A T) a =
      if s = t then covariantSlotAction s (B * A - A * B) T a else 0 := by
    have h := congrFun (covariantSlotAction_commutator s t A B T) a
    simpa only [Pi.sub_apply, Pi.zero_apply, ite_apply] using h
  simp only [he]
  simp [tensorSlotAction]

end
end PositiveEinsteinFour.Geometry
end


section

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

private def pairSwap : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 0, 1]
  invFun := ![2, 3, 0, 1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private def curvatureArray (T : CovariantCoordinates 4) : Angular.CurvatureArray :=
  fun i j k l => T ![i, j, k, l]

private theorem firstSkew_permute (T : CovariantCoordinates 4)
    (h : AlgebraicCurvature.FirstSkew (curvatureArray T)) (a : Fin 4 → Fin 4) :
    T (a ∘ Equiv.swap 0 1) = -T a := by
  have h1 : a ∘ Equiv.swap 0 1 = ![a 1, a 0, a 2, a 3] := by
    funext i
    fin_cases i <;> rfl
  have h0 : a = ![a 0, a 1, a 2, a 3] := by
    funext i
    fin_cases i <;> rfl
  rw [h1, h0]
  exact h _ _ _ _

private theorem lastSkew_permute (T : CovariantCoordinates 4)
    (h : AlgebraicCurvature.LastSkew (curvatureArray T)) (a : Fin 4 → Fin 4) :
    T (a ∘ Equiv.swap 2 3) = -T a := by
  have h1 : a ∘ Equiv.swap 2 3 = ![a 0, a 1, a 3, a 2] := by
    funext i
    fin_cases i <;> rfl
  have h0 : a = ![a 0, a 1, a 2, a 3] := by
    funext i
    fin_cases i <;> rfl
  rw [h1, h0]
  exact h _ _ _ _

private theorem pairSymmetric_permute (T : CovariantCoordinates 4)
    (h : AlgebraicCurvature.PairSymmetric (curvatureArray T)) (a : Fin 4 → Fin 4) :
    T (a ∘ pairSwap) = T a := by
  have h1 : a ∘ pairSwap = ![a 2, a 3, a 0, a 1] := by
    funext i
    fin_cases i <;> rfl
  have h0 : a = ![a 0, a 1, a 2, a 3] := by
    funext i
    fin_cases i <;> rfl
  rw [h1, h0]
  exact h _ _ _ _

private theorem coordinate_curvature_firstSkew (g : SmoothMetric M) (c : M)
    (z : FourSpace) : AlgebraicCurvature.FirstSkew
      (curvatureArray (curvatureCoordinates g c z)) := by
  intro i j k l
  change (∑ r, metricInChart g c z r l * curvatureComponent g c z r j i k) =
    -(∑ r, metricInChart g c z r l * curvatureComponent g c z r i j k)
  simp_rw [curvatureComponent_first_skew g c z _ j i k]
  simp only [mul_neg, Finset.sum_neg_distrib]

private theorem coordinate_curvature_lastSkew (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) : AlgebraicCurvature.LastSkew
      (curvatureArray (curvatureCoordinates g c z)) := by
  intro i j k l
  exact lowered_curvature_last_skew g c z hz hdet i j k l

theorem coordinate_curvature_firstBianchi (g : SmoothMetric M) (c : M)
    (z : FourSpace) : AlgebraicCurvature.FirstBianchi
      (curvatureArray (curvatureCoordinates g c z)) := by
  intro i j k l
  change (∑ r, metricInChart g c z r l * curvatureComponent g c z r i j k) +
    (∑ r, metricInChart g c z r l * curvatureComponent g c z r j k i) +
    (∑ r, metricInChart g c z r l * curvatureComponent g c z r k i j) = 0
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro r _
  linear_combination metricInChart g c z r l * curvatureComponent_first_bianchi g c z r i j k

private theorem coordinate_curvature_pairSymmetric (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) : AlgebraicCurvature.PairSymmetric
      (curvatureArray (curvatureCoordinates g c z)) :=
  AlgebraicCurvature.pairSymmetric_of_bianchi
    (coordinate_curvature_firstSkew g c z)
    (coordinate_curvature_lastSkew g c z hz hdet)
    (coordinate_curvature_firstBianchi g c z)

theorem curvatureDerivative_firstSkew (g : SmoothMetric M) (c : M)
    (z : FourSpace) (d : Fin 4) : AlgebraicCurvature.FirstSkew
      (curvatureDerivativeArray (covariantDerivative g c (curvatureCoordinates g c) z) d) := by
  have h : (fun w b => curvatureCoordinates g c w (b ∘ Equiv.swap 0 1)) =ᶠ[nhds z]
      fun w => -curvatureCoordinates g c w := by
    filter_upwards [] with w
    funext a
    exact firstSkew_permute (curvatureCoordinates g c w) (coordinate_curvature_firstSkew g c w) a
  intro i j k l
  have hv : ![i, j, k, l] ∘ Equiv.swap 0 1 = ![j, i, k, l] := by
    funext a
    fin_cases a <;> rfl
  have he := covariantDerivative_permute_neg g c (curvatureCoordinates g c)
    (Equiv.swap 0 1) z h d ![i, j, k, l]
  rw [hv] at he
  exact he

theorem curvatureDerivative_lastSkew (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (d : Fin 4) :
    AlgebraicCurvature.LastSkew
      (curvatureDerivativeArray (covariantDerivative g c (curvatureCoordinates g c) z) d) := by
  have h : (fun w b => curvatureCoordinates g c w (b ∘ Equiv.swap 2 3)) =ᶠ[nhds z]
      fun w => -curvatureCoordinates g c w := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
    funext a
    exact lastSkew_permute (curvatureCoordinates g c w) (coordinate_curvature_lastSkew g c w hw
      (metricInChart_posDef g c w hw).det_pos.ne') a
  intro i j k l
  have hv : ![i, j, k, l] ∘ Equiv.swap 2 3 = ![i, j, l, k] := by
    funext a
    fin_cases a <;> rfl
  have he := covariantDerivative_permute_neg g c (curvatureCoordinates g c)
    (Equiv.swap 2 3) z h d ![i, j, k, l]
  rw [hv] at he
  exact he

theorem curvatureDerivative_pairSymmetric (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (d : Fin 4) :
    AlgebraicCurvature.PairSymmetric
      (curvatureDerivativeArray (covariantDerivative g c (curvatureCoordinates g c) z) d) := by
  have h : (fun w b => curvatureCoordinates g c w (b ∘ pairSwap)) =ᶠ[nhds z]
      curvatureCoordinates g c := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
    funext a
    exact pairSymmetric_permute (curvatureCoordinates g c w) (coordinate_curvature_pairSymmetric g c w hw
      (metricInChart_posDef g c w hw).det_pos.ne') a
  intro i j k l
  have hv : ![i, j, k, l] ∘ pairSwap = ![k, l, i, j] := by
    funext a
    fin_cases a <;> rfl
  have he := covariantDerivative_permute_eq g c (curvatureCoordinates g c)
    pairSwap z h d ![i, j, k, l]
  rw [hv] at he
  exact he


private def derivativePairSwap : Equiv.Perm (Fin 5) where
  toFun := ![0, 3, 4, 1, 2]
  invFun := ![0, 3, 4, 1, 2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem frameTensor_firstSkew (E : Mat4) (T : CovariantCoordinates 5)
    (h : ∀ d, AlgebraicCurvature.FirstSkew (curvatureDerivativeArray T d))
    (d : Fin 4) : AlgebraicCurvature.FirstSkew
      (curvatureDerivativeArray (frameTensor E T) d) := by
  have hp (b : Fin 5 → Fin 4) : T (b ∘ Equiv.swap 1 2) = -T b := by
    have h1 : b ∘ Equiv.swap 1 2 = ![b 0, b 2, b 1, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    have h0 : b = ![b 0, b 1, b 2, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    rw [h1, h0]
    exact h _ _ _ _ _
  intro i j k l
  have hv : ![d, i, j, k, l] ∘ Equiv.swap 1 2 = ![d, j, i, k, l] := by
    funext a
    fin_cases a <;> rfl
  change frameTensor E T ![d, j, i, k, l] = -frameTensor E T ![d, i, j, k, l]
  rw [← hv, frameTensor_permute]
  have he : (fun b => T (b ∘ Equiv.swap 1 2)) = -T := funext hp
  rw [he, frameTensor_neg]

theorem frameTensor_lastSkew (E : Mat4) (T : CovariantCoordinates 5)
    (h : ∀ d, AlgebraicCurvature.LastSkew (curvatureDerivativeArray T d))
    (d : Fin 4) : AlgebraicCurvature.LastSkew
      (curvatureDerivativeArray (frameTensor E T) d) := by
  have hp (b : Fin 5 → Fin 4) : T (b ∘ Equiv.swap 3 4) = -T b := by
    have h1 : b ∘ Equiv.swap 3 4 = ![b 0, b 1, b 2, b 4, b 3] := by
      funext i
      fin_cases i <;> rfl
    have h0 : b = ![b 0, b 1, b 2, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    rw [h1, h0]
    exact h _ _ _ _ _
  intro i j k l
  have hv : ![d, i, j, k, l] ∘ Equiv.swap 3 4 = ![d, i, j, l, k] := by
    funext a
    fin_cases a <;> rfl
  change frameTensor E T ![d, i, j, l, k] = -frameTensor E T ![d, i, j, k, l]
  rw [← hv, frameTensor_permute]
  have he : (fun b => T (b ∘ Equiv.swap 3 4)) = -T := funext hp
  rw [he, frameTensor_neg]

theorem frameTensor_pairSymmetric (E : Mat4) (T : CovariantCoordinates 5)
    (h : ∀ d, AlgebraicCurvature.PairSymmetric (curvatureDerivativeArray T d))
    (d : Fin 4) : AlgebraicCurvature.PairSymmetric
      (curvatureDerivativeArray (frameTensor E T) d) := by
  have hp (b : Fin 5 → Fin 4) : T (b ∘ derivativePairSwap) = T b := by
    have h1 : b ∘ derivativePairSwap = ![b 0, b 3, b 4, b 1, b 2] := by
      funext i
      fin_cases i <;> rfl
    have h0 : b = ![b 0, b 1, b 2, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    rw [h1, h0]
    exact h _ _ _ _ _
  intro i j k l
  have hv : ![d, i, j, k, l] ∘ derivativePairSwap = ![d, k, l, i, j] := by
    funext a
    fin_cases a <;> rfl
  change frameTensor E T ![d, k, l, i, j] = frameTensor E T ![d, i, j, k, l]
  rw [← hv, frameTensor_permute]
  have he : (fun b => T (b ∘ derivativePairSwap)) = T := funext hp
  rw [he]

/-- Every derivative slice of the actual Weyl tensor retains all three
algebraic curvature symmetries in any actual orthonormal frame. -/
theorem frame_normalizedWeyl_derivative_symmetries (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (d : Fin 4) :
    let D := curvatureDerivativeArray (frameTensor e.matrix
      (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c))) d
    AlgebraicCurvature.FirstSkew D ∧ AlgebraicCurvature.LastSkew D ∧
      AlgebraicCurvature.PairSymmetric D := by
  dsimp only
  have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  rw [covariantDerivative_normalizedWeyl g c (chartAt FourSpace c c) hz (chartMetric_posDef g c).det_pos.ne']
  let T := covariantDerivative g c (curvatureCoordinates g c) (chartAt FourSpace c c)
  exact ⟨frameTensor_firstSkew e.matrix T
      (curvatureDerivative_firstSkew g c (chartAt FourSpace c c)) d,
    frameTensor_lastSkew e.matrix T
      (curvatureDerivative_lastSkew g c (chartAt FourSpace c c) hz) d,
    frameTensor_pairSymmetric e.matrix T
      (curvatureDerivative_pairSymmetric g c (chartAt FourSpace c c) hz) d⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The weak Bochner equation for the actual Weyl derivative energy.
This is the identity used to prove the sign of equation (16). -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

def energyDerivativeField (d : MetricGreenData g μ) (i : Fin 4) : C(FrameBundle g, ℝ) :=
  ⟨fun e => inner ℝ (frameGradientVector g e) (frameHessianVector g i e) / 3,
    (d.continuousGradientVector.inner (d.continuousHessianVector i)).div_const 3⟩

theorem energyDerivative (d : MetricGreenData g μ) (i : Fin 4) (t : ℝ) (e : FrameBundle g) :
    HasDerivAt (fun s => d.gradientEnergyField ((d.flow i).map s e))
      (d.energyDerivativeField i ((d.flow i).map t e)) t := by
  have h := ((d.derivativeGradientVector i t e).inner ℝ
    (d.derivativeGradientVector i t e)).div_const 6
  convert! h using 1
  · funext s
    change weylGradientEnergy _ = inner ℝ (frameGradientVector g _) (frameGradientVector g _) / 6
    rw [frameGradientVector, gradientVector_pairing]
    rfl
  · change inner ℝ (frameGradientVector g _) (frameHessianVector g i _) / 3 = _
    rw [real_inner_comm (frameHessianVector g i _)]
    ring

def energyLaplacianField (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => hessianNormSq (plusWeylHessian g e.base e.frame) / 3 +
      26 * weylGradientEnergy (plusWeylGradient g e.base e.frame) -
      40 * weylMatrixEnergy (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame), by
    have hX : Continuous (fun e : FrameBundle g => hessianNormSq (plusWeylHessian g e.base e.frame)) := by
      simpa only [hessianPairing_self, hessianMap, ContinuousMap.coe_mk] using
        continuous_hessianPairing d.hessianMap.continuous d.hessianMap.continuous
    exact ((hX.div_const 3).add (continuous_const.mul d.gradientEnergyField.continuous)).sub
      (continuous_const.mul d.matrixEnergyField.continuous)⟩

theorem testedEnergyEquation (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hm : ∀ i t e, HasDerivAt (fun s => m ((d.flow i).map s e))
      (dm i ((d.flow i).map t e)) t) :
    (∫ e, m e * d.energyLaplacianField e +
      ∑ i, dm i e * d.energyDerivativeField i e ∂μ) = 0 := by
  let L : C(FrameBundle g, ℝ) := d.hessianIdentityField m dm
  let R : C(FrameBundle g, ℝ) :=
    ⟨fun e => m e * (-13 * weylGradientEnergy (plusWeylGradient g e.base e.frame) +
      20 * weylMatrixEnergy (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)),
      m.continuous.mul ((continuous_const.mul d.gradientEnergyField.continuous).add
        (continuous_const.mul d.matrixEnergyField.continuous))⟩
  have hL : Integrable L μ := L.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hR : Integrable R μ := R.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hG : (∫ e, L e ∂μ) = ∫ e, R e ∂μ := d.identityGreen m dm hm
  have hpoint (e : FrameBundle g) :
      m e * d.energyLaplacianField e + ∑ i, dm i e * d.energyDerivativeField i e =
        2 * (L e - R e) := by
    change m e * (hessianNormSq (plusWeylHessian g e.base e.frame) / 3 +
        26 * weylGradientEnergy (plusWeylGradient g e.base e.frame) -
        40 * weylMatrixEnergy (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)) +
      (∑ i, dm i e * (inner ℝ (frameGradientVector g e) (frameHessianVector g i e) / 3)) =
      2 * (weightedQuadratic hessianNormSq (m e) (plusWeylHessian g e.base e.frame)
        (weightTensor (WithLp.toLp 2 (fun i => dm i e)) (plusGradientTensor g e.base e.frame)) -
        m e * (-13 * weylGradientEnergy (plusWeylGradient g e.base e.frame) +
          20 * weylMatrixEnergy (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)))
    rw [weightedQuadratic_identity_green]
    simp only [plusGradientTensor, tensorGradientVector_gradientTensor _ (d.gradientConstraints e).1,
      frameGradientVector, frameHessianVector]
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    ring
  calc
    _ = ∫ e, 2 * (L e - R e) ∂μ := integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = 0 := by rw [integral_const_mul, integral_sub hL hR, hG, sub_self, mul_zero]

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Weyl norm equation tested against the specific polynomial
κ(v,b). Its smooth approximation is constructed from the two tensor norms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators Topology Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem MetricGreenData.kappaNormEquation (d : MetricGreenData g μ) (o : OppositeWeylData d)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hkato : ∀ e : FrameBundle g, (5 / 3 : ℝ) *
      ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2 ≤
        weylGradientEnergy (plusWeylGradient g e.base e.frame))
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    (∫ e, regularizedKappa 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) *
        scalarNormExpression 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) +
      ∑ i, regularizedKappaDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
        regularizedRadialDerivative 0 (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame i) ∂μ) = 0 := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  have hε1 (n) : ε n ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  let k : ℕ → C(FrameBundle g, ℝ) := fun n =>
    ⟨fun e => regularizedKappa (ε n) (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame),
      continuous_regularizedKappa (ε n) _ _ d.continuousWeyl o.continuousWeyl⟩
  let dk : ℕ → Fin 4 → C(FrameBundle g, ℝ) := fun n i =>
    ⟨fun e => regularizedKappaDerivative (ε n) (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i),
      continuous_regularizedKappaDerivative (ε n) (hε n) _ _ _ _ d.continuousWeyl
        o.continuousWeyl (d.continuousGradient i) (o.continuousGradient i)⟩
  obtain ⟨C, hC0, hC⟩ := kappa_rectangle_bound
  let B : Fin 4 → C(FrameBundle g, ℝ) := fun i =>
    ⟨fun e => C * (normalizedBlockNorm (plusWeylGradient g e.base e.frame i) +
      normalizedBlockNorm (minusWeylGradient g e.base e.frame i)),
      continuous_const.mul ((continuous_normalizedBlockNorm.comp (d.continuousGradient i)).add
        (continuous_normalizedBlockNorm.comp (o.continuousGradient i)))⟩
  apply d.testedNormEquation_of_limits hkato ε hε tendsto_one_div_add_atTop_nhds_zero_nat k dk
    (C := C) (B := B)
  · intro n i t e
    exact hasDerivAt_regularizedKappa (d.derivativeWeyl i t e) (o.derivativeWeyl i t e)
      (fun s => d.weyl.symmetric ((d.flow i).map s e))
      (fun s => o.symmetric ((d.flow i).map s e)) (hε n)
  · intro e
    exact (tendsto_regularizedKappa _ _).comp tendsto_one_div_add_atTop_nhds_zero_nat
  · intro i e
    exact (tendsto_regularizedKappaDerivative _ _ _ _).comp tendsto_one_div_add_atTop_nhds_zero_nat
  · exact hC0
  · intro n e
    exact (regularizedKappa_bounds C hC (hε n) (hε1 n) _ _ _ _
      ((d.gradientConstraints e).1 0) ((o.gradientConstraints e).1 0) (hpinch e)).1
  · intro n i e
    exact (regularizedKappa_bounds C hC (hε n) (hε1 n) _ _ _ _
      ((d.gradientConstraints e).1 i) ((o.gradientConstraints e).1 i) (hpinch e)).2

end
end PositiveEinsteinFour.Geometry
end


section

/-! The cube root of the positive regularized Weyl norm satisfies the
scalar differential inequality forced by the Weyl equation and refined Kato. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance rootKatoNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance rootKatoNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance rootKatoNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

def regularizedWeylRoot (ε : ℝ) (A : Mat) : ℝ :=
  regularizedBlockNorm ε A ^ (1 / 3 : ℝ)

def regularizedWeylRootFirst (ε : ℝ) (A Z : Mat) : ℝ :=
  (1 / 3 : ℝ) * regularizedBlockNorm ε A ^ (-2 / 3 : ℝ) *
    regularizedRadialDerivative ε A Z

def regularizedWeylRootSecond (ε : ℝ) (A Z X : Mat) : ℝ :=
  (1 / 3 : ℝ) * regularizedBlockNorm ε A ^ (-2 / 3 : ℝ) *
      regularizedRadialSecond ε A Z X -
    (2 / 9 : ℝ) * regularizedBlockNorm ε A ^ (-5 / 3 : ℝ) *
      regularizedRadialDerivative ε A Z ^ 2

theorem regularizedWeylRoot_eq (ε : ℝ) (A : Mat) :
    regularizedWeylRoot ε A =
      (normalizedBlockNorm A ^ 2 + ε ^ 2) ^ (1 / 6 : ℝ) := by
  unfold regularizedWeylRoot regularizedBlockNorm
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  norm_num

theorem hasDerivAt_regularizedWeylRoot
    {A : ℝ → Mat} {Z : Mat} {t ε : ℝ}
    (hA : HasDerivAt A Z t) (hs : ∀ s, symmetric (A s)) (hε : 0 < ε) :
    HasDerivAt (fun s => regularizedWeylRoot ε (A s))
      (regularizedWeylRootFirst ε (A t) Z) t := by
  have h := (hasDerivAt_regularizedBlockNorm hA hs hε).rpow_const
    (p := (1 / 3 : ℝ)) (Or.inl (regularizedBlockNorm_pos ε hε (A t)).ne')
  change HasDerivAt (fun s => regularizedWeylRoot ε (A s)) _ t at h
  convert h using 1
  unfold regularizedWeylRootFirst
  norm_num
  ring

theorem hasDerivAt_regularizedWeylRootFirst
    {A Z : ℝ → Mat} {X : Mat} {t ε : ℝ}
    (hA : HasDerivAt A (Z t) t) (hZ : HasDerivAt Z X t)
    (hs : ∀ s, symmetric (A s)) (hε : 0 < ε) :
    HasDerivAt (fun s => regularizedWeylRootFirst ε (A s) (Z s))
      (regularizedWeylRootSecond ε (A t) (Z t) X) t := by
  have hu := hasDerivAt_regularizedBlockNorm hA hs hε
  have hp := hu.rpow_const (p := (-2 / 3 : ℝ))
    (Or.inl (regularizedBlockNorm_pos ε hε (A t)).ne')
  have hq := hasDerivAt_regularizedRadialDerivative hA hZ hs hε
  have h := (hp.const_mul (1 / 3 : ℝ)).mul hq
  change HasDerivAt (fun s => regularizedWeylRootFirst ε (A s) (Z s)) _ t at h
  convert h using 1
  simp only [regularizedWeylRootSecond]
  norm_num
  ring

theorem regularized_radial_refined_kato (ε : ℝ) (hε : 0 < ε)
    (A : Mat) (Z : Fin 4 → Mat) (hA : symmetric A) (htA : traceFree A)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0) :
    (5 / 3 : ℝ) * (∑ i, regularizedRadialDerivative ε A (Z i) ^ 2) ≤
      weylGradientEnergy Z := by
  have hk := QuaternionFrame.blockRadialGradient_refined_kato A Z hA htA hs ht hb
  have hr := regularized_radial_energy_le ε hε A Z
  linarith

theorem regularizedWeylRootSecond_sum (ε : ℝ) (hε : 0 < ε)
    (A : Mat) (Z : Fin 4 → Mat) (X : Hessian)
    (hZ : ∀ i, symmetric (Z i)) (hX : hessianTrace X = weylLaplacian A) :
    (∑ i, regularizedWeylRootSecond ε A (Z i) (X i i)) =
      (1 / 3 : ℝ) * regularizedBlockNorm ε A ^ (-5 / 3 : ℝ) *
        (weylGradientEnergy Z + Matrix.trace (A * weylLaplacian A) / 6 -
          (5 / 3 : ℝ) * ∑ i, regularizedRadialDerivative ε A (Z i) ^ 2) := by
  have hn := regularizedBlockNorm_pos ε hε A
  have hp : regularizedBlockNorm ε A ^ (-2 / 3 : ℝ) =
      regularizedBlockNorm ε A ^ (-5 / 3 : ℝ) * regularizedBlockNorm ε A := by
    simpa only [show (-5 / 3 : ℝ) + 1 = -2 / 3 by norm_num] using
      Real.rpow_add_one hn.ne' (-5 / 3 : ℝ)
  simp only [regularizedWeylRootSecond, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [regularizedRadialSecond_sum ε A Z X hZ hX, hp]
  field_simp [hn.ne']
  ring

theorem regularizedWeylRootSecond_trace_lower (ε : ℝ) (hε : 0 < ε)
    (A : Mat) (Z : Fin 4 → Mat) (X : Hessian)
    (hA : symmetric A) (htA : traceFree A)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0)
    (hX : hessianTrace X = weylLaplacian A) :
    Matrix.trace (A * weylLaplacian A) /
        (18 * regularizedBlockNorm ε A ^ (5 / 3 : ℝ)) ≤
      ∑ i, regularizedWeylRootSecond ε A (Z i) (X i i) := by
  rw [regularizedWeylRootSecond_sum ε hε A Z X hs hX]
  have hk := regularized_radial_refined_kato ε hε A Z hA htA hs ht hb
  have hn := regularizedBlockNorm_pos ε hε A
  have hh := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (Real.rpow_nonneg hn.le (-5 / 3 : ℝ)))
    (sub_nonneg.mpr hk)
  have hexp : regularizedBlockNorm ε A ^ (-5 / 3 : ℝ) =
      (regularizedBlockNorm ε A ^ (5 / 3 : ℝ))⁻¹ := by
    simpa only [neg_div] using Real.rpow_neg hn.le (5 / 3 : ℝ)
  have heq : Matrix.trace (A * weylLaplacian A) /
      (18 * regularizedBlockNorm ε A ^ (5 / 3 : ℝ)) =
      (1 / 3 : ℝ) * regularizedBlockNorm ε A ^ (-5 / 3 : ℝ) *
        (Matrix.trace (A * weylLaplacian A) / 6) := by
    rw [hexp]
    ring
  rw [heq]
  nlinarith only [hh]

theorem weylLaplacian_trace_lower (A : Mat) (hA : symmetric A) (htA : traceFree A) :
    36 * normalizedBlockNorm A ^ 2 * (1 - normalizedBlockNorm A) ≤
      Matrix.trace (A * weylLaplacian A) := by
  have ht : matrixPairing A (weylLaplacian A) = Matrix.trace (A * weylLaplacian A) := by
    rw [matrixPairing_eq_trace]
    congr 2
    ext i j
    exact weylLaplacian_symmetric A hA j i
  rw [← ht, weylLaplacian_pairing A hA htA]
  have hshape := normalizedDeterminantShape_le_one A hA htA
  have hv := normalizedBlockNorm_nonneg A
  have hh := mul_nonneg (sub_nonneg.mpr hshape) (pow_nonneg hv 3)
  nlinarith only [hh]

/-- The pointwise differential inequality for
`(normalizedBlockNorm A ^ 2 + ε ^ 2) ^ (1/6)`. -/
theorem regularizedWeylRootSecond_lower (ε : ℝ) (hε : 0 < ε)
    (A : Mat) (Z : Fin 4 → Mat) (X : Hessian)
    (hA : symmetric A) (htA : traceFree A)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0)
    (hX : hessianTrace X = weylLaplacian A) :
    2 * normalizedBlockNorm A ^ 2 * (1 - normalizedBlockNorm A) /
        regularizedBlockNorm ε A ^ (5 / 3 : ℝ) ≤
      ∑ i, regularizedWeylRootSecond ε A (Z i) (X i i) := by
  refine le_trans ?_ (regularizedWeylRootSecond_trace_lower ε hε A Z X
    hA htA hs ht hb hX)
  have hn := regularizedBlockNorm_pos ε hε A
  have h := div_le_div_of_nonneg_right (weylLaplacian_trace_lower A hA htA)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 18) (Real.rpow_nonneg hn.le (5 / 3 : ℝ)))
  convert h using 1
  ring

theorem continuous_regularizedWeylRoot (ε : ℝ) :
    Continuous (regularizedWeylRoot ε) := by
  exact (continuous_regularizedBlockNorm ε).rpow_const
    (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 3))

theorem continuous_regularizedWeylRootFirst {Ω : Type*} [TopologicalSpace Ω]
    (ε : ℝ) (hε : 0 < ε) (A Z : Ω → Mat)
    (hA : Continuous A) (hZ : Continuous Z) :
    Continuous (fun x => regularizedWeylRootFirst ε (A x) (Z x)) := by
  have hp := ((continuous_regularizedBlockNorm ε).comp hA).rpow_const
    (p := (-2 / 3 : ℝ)) (fun x => Or.inl (regularizedBlockNorm_pos ε hε (A x)).ne')
  exact (hp.const_mul (1 / 3 : ℝ)).mul
    (continuous_regularizedRadialDerivative ε hε A Z hA hZ)

theorem continuous_regularizedWeylRootSecond {Ω : Type*} [TopologicalSpace Ω]
    (ε : ℝ) (hε : 0 < ε) (A Z X : Ω → Mat)
    (hA : Continuous A) (hZ : Continuous Z) (hX : Continuous X) :
    Continuous (fun x => regularizedWeylRootSecond ε (A x) (Z x) (X x)) := by
  have hp := ((continuous_regularizedBlockNorm ε).comp hA).rpow_const
    (p := (-2 / 3 : ℝ)) (fun x => Or.inl (regularizedBlockNorm_pos ε hε (A x)).ne')
  have hq := ((continuous_regularizedBlockNorm ε).comp hA).rpow_const
    (p := (-5 / 3 : ℝ)) (fun x => Or.inl (regularizedBlockNorm_pos ε hε (A x)).ne')
  exact ((hp.const_mul (1 / 3 : ℝ)).mul
    (continuous_regularizedRadialSecond ε hε A Z X hA hZ hX)).sub
      ((hq.const_mul (2 / 9 : ℝ)).mul
        ((continuous_regularizedRadialDerivative ε hε A Z hA hZ).pow 2))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem regularizedWeylRoot_derivative (d : MetricGreenData g μ)
    (ε : ℝ) (hε : 0 < ε) (i : Fin 4) (t : ℝ) (e : FrameBundle g) :
    HasDerivAt (fun s => regularizedWeylRoot ε
      (plusWeyl g ((d.flow i).map s e).base ((d.flow i).map s e).frame))
      (regularizedWeylRootFirst ε
        (plusWeyl g ((d.flow i).map t e).base ((d.flow i).map t e).frame)
        (plusWeylGradient g ((d.flow i).map t e).base ((d.flow i).map t e).frame i)) t :=
  hasDerivAt_regularizedWeylRoot (d.derivativeWeyl i t e)
    (fun s => d.weyl.symmetric ((d.flow i).map s e)) hε

theorem regularizedWeylRootFirst_derivative (d : MetricGreenData g μ)
    (ε : ℝ) (hε : 0 < ε) (i : Fin 4) (t : ℝ) (e : FrameBundle g) :
    HasDerivAt (fun s => regularizedWeylRootFirst ε
      (plusWeyl g ((d.flow i).map s e).base ((d.flow i).map s e).frame)
      (plusWeylGradient g ((d.flow i).map s e).base ((d.flow i).map s e).frame i))
      (regularizedWeylRootSecond ε
        (plusWeyl g ((d.flow i).map t e).base ((d.flow i).map t e).frame)
        (plusWeylGradient g ((d.flow i).map t e).base ((d.flow i).map t e).frame i)
        (plusWeylHessian g ((d.flow i).map t e).base ((d.flow i).map t e).frame i i)) t :=
  hasDerivAt_regularizedWeylRootFirst (d.derivativeWeyl i t e)
    (d.derivativeGradient i i t e) (fun s => d.weyl.symmetric ((d.flow i).map s e)) hε

/-- The actual metric flow has the regularized lower Laplacian bound;
all algebraic gradient and Weyl-equation hypotheses come from its proved data. -/
theorem regularizedWeylRoot_lower (d : MetricGreenData g μ)
    (ε : ℝ) (hε : 0 < ε) (e : FrameBundle g) :
    2 * normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 *
        (1 - normalizedBlockNorm (plusWeyl g e.base e.frame)) /
        regularizedBlockNorm ε (plusWeyl g e.base e.frame) ^ (5 / 3 : ℝ) ≤
      ∑ i, regularizedWeylRootSecond ε (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) (plusWeylHessian g e.base e.frame i i) :=
  regularizedWeylRootSecond_lower ε hε _ _ _ (d.weyl.symmetric e) (d.weyl.traceFree e)
    (d.gradientConstraints e).1 (d.gradientConstraints e).2 (d.gradientBianchi e)
    (metric_weyl_trace g d.weyl e)

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual commutation of the coordinate Levi-Civita derivative on the
covariant tensors used for the Weyl Hessian and its first derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

def tensorPartial {n : ℕ} (T : FourSpace → CovariantCoordinates n)
    (i : Fin 4) (z : FourSpace) : CovariantCoordinates n :=
  fun a => partialDeriv (fun w => T w a) i z

def tensorCovariantDirection {n : ℕ} (G : Fin 4 → FourSpace → Mat4)
    (T : FourSpace → CovariantCoordinates n) (i : Fin 4) (z : FourSpace) :
    CovariantCoordinates n := tensorPartial T i z - tensorSlotAction (G i z) (T z)

private theorem tensor_partial_sum {ι : Type*} [Fintype ι]
    (F : ι → FourSpace → ℝ) (z : FourSpace)
    (hF : ∀ a, DifferentiableAt ℝ (F a) z) (i : Fin 4) :
    partialDeriv (fun w => ∑ a, F a w) i z = ∑ a, partialDeriv (F a) i z := by
  unfold partialDeriv
  rw [fderiv_fun_sum (u := Finset.univ) (A := F) (fun a _ => hF a), _root_.sum_apply]

private theorem tensor_partial_mul {f h : FourSpace → ℝ} {z : FourSpace}
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) (i : Fin 4) :
    partialDeriv (fun w => f w * h w) i z =
      partialDeriv f i z * h z + f z * partialDeriv h i z := by
  simp only [partialDeriv, fderiv_fun_mul hf hh, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

theorem tensorPartial_sub {n : ℕ} (S T : FourSpace → CovariantCoordinates n)
    (z : FourSpace) (hS : ∀ a, DifferentiableAt ℝ (fun w => S w a) z)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) z) (i : Fin 4) :
    tensorPartial (fun w => S w - T w) i z = tensorPartial S i z - tensorPartial T i z := by
  funext a
  exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i))
    (fderiv_fun_sub (hS a) (hT a))

theorem tensorPartial_slotAction {n : ℕ} (A : FourSpace → Mat4)
    (T : FourSpace → CovariantCoordinates n) (z : FourSpace)
    (hA : ∀ b c, DifferentiableAt ℝ (fun w => A w b c) z)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) z) (i : Fin 4) :
    tensorPartial (fun w => tensorSlotAction (A w) (T w)) i z =
      tensorSlotAction (matrixPartial A i z) (T z) +
        tensorSlotAction (A z) (tensorPartial T i z) := by
  funext a
  have hd (s : Fin n) : DifferentiableAt ℝ
      (fun w => ∑ b, A w b (a s) * T w (Function.update a s b)) z :=
    DifferentiableAt.fun_sum (u := Finset.univ)
      (fun b _ => (hA b (a s)).mul (hT (Function.update a s b)))
  have hi (s : Fin n) :
      partialDeriv (fun w => ∑ b, A w b (a s) * T w (Function.update a s b)) i z =
        ∑ b, partialDeriv (fun w => A w b (a s) * T w (Function.update a s b)) i z :=
    tensor_partial_sum _ z (fun b => (hA b (a s)).mul (hT (Function.update a s b))) i
  have hp (s : Fin n) (b : Fin 4) :
      partialDeriv (fun w => A w b (a s) * T w (Function.update a s b)) i z =
        partialDeriv (fun w => A w b (a s)) i z * T z (Function.update a s b) +
          A z b (a s) * partialDeriv (fun w => T w (Function.update a s b)) i z :=
    tensor_partial_mul (hA b (a s)) (hT (Function.update a s b)) i
  change partialDeriv (fun w => ∑ s, ∑ b, A w b (a s) *
    T w (Function.update a s b)) i z = _
  rw [tensor_partial_sum _ z hd i]
  simp only [hi, hp, Finset.sum_add_distrib,
    tensorSlotAction, covariantSlotAction, matrixPartial, tensorPartial, Pi.add_apply]

theorem tensorPartial_comm {n : ℕ} (T : FourSpace → CovariantCoordinates n)
    (z : FourSpace) (hT : ∀ a, ContDiffAt ℝ ∞ (fun w => T w a) z)
    (i j : Fin 4) :
    tensorPartial (tensorPartial T j) i z = tensorPartial (tensorPartial T i) j z := by
  funext a
  have hd := ((hT a).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have he (r s : Fin 4) :
      partialDeriv (fun w => partialDeriv (fun y => T y a) s w) r z =
        fderiv ℝ (fderiv ℝ (fun y => T y a)) z (coordinateVector r) (coordinateVector s) := by
    unfold partialDeriv
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  change partialDeriv (fun w => partialDeriv (fun y => T y a) j w) i z =
    partialDeriv (fun w => partialDeriv (fun y => T y a) i w) j z
  rw [he, he]
  exact ((hT a).isSymmSndFDerivAt (by simp)).eq _ _

private theorem slotAction_contDiffAt {n : ℕ} (A : FourSpace → Mat4)
    (T : FourSpace → CovariantCoordinates n) (z : FourSpace)
    (hA : ∀ b c, ContDiffAt ℝ ∞ (fun w => A w b c) z)
    (hT : ∀ a, ContDiffAt ℝ ∞ (fun w => T w a) z) (a : Fin n → Fin 4) :
    ContDiffAt ℝ ∞ (fun w => tensorSlotAction (A w) (T w) a) z := by
  apply ContDiffAt.sum
  intro s _
  apply ContDiffAt.sum
  intro b _
  exact (hA b _).mul (hT _)

theorem tensorCovariantDirection_commutator {n : ℕ}
    (G : Fin 4 → FourSpace → Mat4) (T : FourSpace → CovariantCoordinates n)
    (z : FourSpace) (hG : ∀ i b c, ContDiffAt ℝ ∞ (fun w => G i w b c) z)
    (hT : ∀ a, ContDiffAt ℝ ∞ (fun w => T w a) z) (i j : Fin 4) :
    tensorCovariantDirection G (tensorCovariantDirection G T j) i z -
      tensorCovariantDirection G (tensorCovariantDirection G T i) j z =
        -tensorSlotAction
          (matrixPartial (G j) i z - matrixPartial (G i) j z +
            (G i z * G j z - G j z * G i z)) (T z) := by
  have hp (r : Fin 4) (a : Fin n → Fin 4) :
      DifferentiableAt ℝ (fun w => tensorPartial T r w a) z :=
    (((hT a).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt
      (by simp)
  have hs (r : Fin 4) (a : Fin n → Fin 4) :
      DifferentiableAt ℝ (fun w => tensorSlotAction (G r w) (T w) a) z :=
    (slotAction_contDiffAt (G r) T z (hG r) hT a).differentiableAt (by simp)
  unfold tensorCovariantDirection
  rw [tensorPartial_sub _ _ z (hp j) (hs j),
    tensorPartial_sub _ _ z (hp i) (hs i),
    tensorPartial_slotAction (G j) T z (fun b c => (hG j b c).differentiableAt (by simp))
      (fun a => (hT a).differentiableAt (by simp)),
    tensorPartial_slotAction (G i) T z (fun b c => (hG i b c).differentiableAt (by simp))
      (fun a => (hT a).differentiableAt (by simp)),
    tensorSlotAction_sub_tensor, tensorSlotAction_sub_tensor,
    tensorPartial_comm T z hT i j,
    tensorSlotAction_add_matrix, tensorSlotAction_sub_matrix,
    tensorSlotAction_sub_matrix]
  have hc := tensorSlotAction_commutator (G i z) (G j z) (T z)
  rw [tensorSlotAction_sub_matrix] at hc
  have hh := congrArg (fun X : CovariantCoordinates n =>
    X - tensorSlotAction (matrixPartial (G j) i z) (T z) +
      tensorSlotAction (matrixPartial (G i) j z) (T z)) hc
  abel_nf at hh ⊢
  exact hh

theorem tensorCovariantDirection_cons {n : ℕ}
    (G : Fin 4 → FourSpace → Mat4) (S : FourSpace → CovariantCoordinates (n + 1))
    (z : FourSpace) (i j : Fin 4) (a : Fin n → Fin 4) :
    tensorCovariantDirection G S i z (Fin.cons j a) =
      tensorCovariantDirection G (fun w b => S w (Fin.cons j b)) i z a -
        ∑ b, G i z b j * S z (Fin.cons b a) := by
  simp only [tensorCovariantDirection, tensorPartial, tensorSlotAction,
    covariantSlotAction, Pi.sub_apply, Fin.sum_univ_succ, Fin.cons_zero,
    Fin.cons_succ, Fin.update_cons_zero, ← Fin.cons_update]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem covariantDerivative_direction {n : ℕ} (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates n) (z : FourSpace)
    (i : Fin 4) (a : Fin n → Fin 4) :
    covariantDerivative g c T z (Fin.cons i a) =
      tensorCovariantDirection (connectionMatrix g c) T i z a := rfl

theorem covariantDerivative_iterated_direction {n : ℕ} (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates n) (z : FourSpace)
    (i j : Fin 4) (a : Fin n → Fin 4) :
    covariantDerivative g c (covariantDerivative g c T) z (Fin.cons i (Fin.cons j a)) =
      tensorCovariantDirection (connectionMatrix g c)
        (tensorCovariantDirection (connectionMatrix g c) T j) i z a -
          ∑ b, christoffel g c z b i j *
            tensorCovariantDirection (connectionMatrix g c) T b z a := by
  rw [covariantDerivative_direction, tensorCovariantDirection_cons]
  have he (r : Fin 4) :
      (fun w b => covariantDerivative g c T w (Fin.cons r b)) =
        tensorCovariantDirection (connectionMatrix g c) T r := by
    funext w b
    exact covariantDerivative_direction g c T w r b
  rw [he j]
  simp only [covariantDerivative_direction, connectionMatrix]

/-- The actual Ricci commutator. Torsion freedom removes the extra
connection term from the derivative slot. -/
theorem covariantDerivative_commutator {n : ℕ} (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates n) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0)
    (hT : ∀ a, ContDiffAt ℝ ∞ (fun w => T w a) z)
    (i j : Fin 4) (a : Fin n → Fin 4) :
    covariantDerivative g c (covariantDerivative g c T) z (Fin.cons i (Fin.cons j a)) -
      covariantDerivative g c (covariantDerivative g c T) z (Fin.cons j (Fin.cons i a)) =
        -tensorSlotAction (coordinateCurvatureMatrix g c i j z) (T z) a := by
  have hG (r b d : Fin 4) :
      ContDiffAt ℝ ∞ (fun w => connectionMatrix g c r w b d) z :=
    christoffel_contDiffAt g c z hz hdet b r d
  have h := congrFun (tensorCovariantDirection_commutator
    (connectionMatrix g c) T z hG hT i j) a
  rw [covariantDerivative_iterated_direction, covariantDerivative_iterated_direction]
  simp_rw [christoffel_comm g c z _ j i]
  have hC : coordinateCurvatureMatrix g c i j z =
      matrixPartial (connectionMatrix g c j) i z -
        matrixPartial (connectionMatrix g c i) j z +
          (connectionMatrix g c i z * connectionMatrix g c j z -
            connectionMatrix g c j z * connectionMatrix g c i z) := by
    unfold coordinateCurvatureMatrix
    abel
  rw [hC]
  simp only [Pi.sub_apply, Pi.neg_apply] at h
  linarith only [h]


/-- The rank-four instance used by the Weyl Hessian. -/
theorem normalizedWeyl_commutator (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j : Fin 4)
    (a : Fin 4 → Fin 4) :
    covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c)) z
      (Fin.cons i (Fin.cons j a)) -
      covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c)) z
        (Fin.cons j (Fin.cons i a)) =
      -tensorSlotAction (coordinateCurvatureMatrix g c i j z)
        (normalizedWeylCoordinates g c z) a :=
  covariantDerivative_commutator g c (normalizedWeylCoordinates g c) z hz hdet
    (normalizedWeylCoordinates_contDiffAt g c z hz hdet) i j a

/-- The rank-five instance used by the outer commutator of the Weyl gradient. -/
theorem normalizedWeyl_gradient_commutator (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j : Fin 4)
    (a : Fin 5 → Fin 4) :
    covariantDerivative g c
      (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))) z
        (Fin.cons i (Fin.cons j a)) -
      covariantDerivative g c
        (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))) z
          (Fin.cons j (Fin.cons i a)) =
      -tensorSlotAction (coordinateCurvatureMatrix g c i j z)
        (covariantDerivative g c (normalizedWeylCoordinates g c) z) a :=
  covariantDerivative_commutator g c
    (covariantDerivative g c (normalizedWeylCoordinates g c)) z hz hdet
    (covariantDerivative_contDiffAt g c z hz hdet (normalizedWeylCoordinates g c)
      (normalizedWeylCoordinates_contDiffAt g c z hz hdet)) i j a

end
end PositiveEinsteinFour.Geometry
end


section

/-! Covariant differentiation and framing preserve the algebraic first
Bianchi identity as well as the pair and alternating symmetries. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem covariantDerivative_add {n : ℕ} (g : SmoothMetric M) (c : M)
    (S T : FourSpace → CovariantCoordinates n) (z : FourSpace)
    (hS : ∀ a, DifferentiableAt ℝ (fun w => S w a) z)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) z) :
    covariantDerivative g c (fun w => S w + T w) z =
      covariantDerivative g c S z + covariantDerivative g c T z := by
  funext a
  have hd : partialDeriv (fun w => S w (fun i => a i.succ) +
        T w (fun i => a i.succ)) (a 0) z =
      partialDeriv (fun w => S w (fun i => a i.succ)) (a 0) z +
        partialDeriv (fun w => T w (fun i => a i.succ)) (a 0) z := by
    exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector (a 0)))
      (fderiv_fun_add (hS _) (hT _))
  simp only [covariantDerivative, Pi.add_apply, hd, mul_add, Finset.sum_add_distrib]
  ring

private def curvatureCycle : Equiv.Perm (Fin 4) where
  toFun := ![1, 2, 0, 3]
  invFun := ![2, 0, 1, 3]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private def frameCurvatureCycle : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 3, 1, 4]
  invFun := ![0, 3, 1, 2, 4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem covariantDerivative_firstBianchi (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates 4) (z : FourSpace)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) z)
    (hB : ∀ w i j k l, T w ![i, j, k, l] + T w ![j, k, i, l] +
      T w ![k, i, j, l] = 0) (d : Fin 4) :
    AlgebraicCurvature.FirstBianchi
      (curvatureDerivativeArray (covariantDerivative g c T z) d) := by
  let P : FourSpace → CovariantCoordinates 4 := fun w a => T w (a ∘ curvatureCycle)
  let V : FourSpace → CovariantCoordinates 4 :=
    fun w a => T w (a ∘ (curvatureCycle.trans curvatureCycle))
  have hP : ∀ a, DifferentiableAt ℝ (fun w => P w a) z := fun a => hT _
  have hV : ∀ a, DifferentiableAt ℝ (fun w => V w a) z := fun a => hT _
  have hfield : (fun w => T w + P w + V w) = fun _ => 0 := by
    funext w a
    have ha : a = ![a 0, a 1, a 2, a 3] := by
      funext i
      fin_cases i <;> rfl
    have hp : a ∘ curvatureCycle = ![a 1, a 2, a 0, a 3] := by
      funext i
      fin_cases i <;> rfl
    have hv : a ∘ (curvatureCycle.trans curvatureCycle) = ![a 2, a 0, a 1, a 3] := by
      funext i
      fin_cases i <;> rfl
    change T w a + T w (a ∘ curvatureCycle) +
      T w (a ∘ (curvatureCycle.trans curvatureCycle)) = 0
    rw [hp, hv, ha]
    exact hB _ _ _ _ _
  have hd : covariantDerivative g c T z + covariantDerivative g c P z +
      covariantDerivative g c V z = 0 := by
    rw [← covariantDerivative_add g c T P z hT hP,
      ← covariantDerivative_add g c (fun w => T w + P w) V z
        (fun a => (hT a).add (hP a)) hV, hfield]
    funext a
    simp [covariantDerivative, partialDeriv]
  intro i j k l
  have h := congrFun hd (Fin.cons d ![i, j, k, l])
  change covariantDerivative g c T z (Fin.cons d ![i, j, k, l]) +
    covariantDerivative g c P z (Fin.cons d ![i, j, k, l]) +
    covariantDerivative g c V z (Fin.cons d ![i, j, k, l]) = 0 at h
  change covariantDerivative g c T z (Fin.cons d ![i, j, k, l]) +
    covariantDerivative g c (fun w a => T w (a ∘ curvatureCycle)) z
      (Fin.cons d ![i, j, k, l]) +
    covariantDerivative g c (fun w a => T w (a ∘ (curvatureCycle.trans curvatureCycle))) z
      (Fin.cons d ![i, j, k, l]) = 0 at h
  rw [covariantDerivative_permute, covariantDerivative_permute] at h
  have hv1 : ![i, j, k, l] ∘ curvatureCycle = ![j, k, i, l] := by
    funext a
    fin_cases a <;> rfl
  have hv2 : ![i, j, k, l] ∘ (curvatureCycle.trans curvatureCycle) = ![k, i, j, l] := by
    funext a
    fin_cases a <;> rfl
  rw [hv1, hv2] at h
  exact h

theorem curvatureDerivative_firstBianchi (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (d : Fin 4) :
    AlgebraicCurvature.FirstBianchi
      (curvatureDerivativeArray (covariantDerivative g c (curvatureCoordinates g c) z) d) := by
  apply covariantDerivative_firstBianchi
  · intro a
    exact (curvatureCoordinates_contDiffAt g c z hz hdet a).differentiableAt (by simp)
  · intro w i j k l
    exact coordinate_curvature_firstBianchi g c w i j k l

theorem frameTensor_firstBianchi (E : Mat4) (T : CovariantCoordinates 5)
    (h : ∀ d, AlgebraicCurvature.FirstBianchi (curvatureDerivativeArray T d))
    (d : Fin 4) : AlgebraicCurvature.FirstBianchi
      (curvatureDerivativeArray (frameTensor E T) d) := by
  have hc (b : Fin 5 → Fin 4) : T b + T (b ∘ frameCurvatureCycle) +
      T (b ∘ (frameCurvatureCycle.trans frameCurvatureCycle)) = 0 := by
    have hb : b = ![b 0, b 1, b 2, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    have h1 : b ∘ frameCurvatureCycle = ![b 0, b 2, b 3, b 1, b 4] := by
      funext i
      fin_cases i <;> rfl
    have h2 : b ∘ (frameCurvatureCycle.trans frameCurvatureCycle) =
        ![b 0, b 3, b 1, b 2, b 4] := by
      funext i
      fin_cases i <;> rfl
    rw [h1, h2, hb]
    exact h _ _ _ _ _
  intro i j k l
  let v : Fin 5 → Fin 4 := ![d, i, j, k, l]
  have h1 : v ∘ frameCurvatureCycle = ![d, j, k, i, l] := by
    funext a
    fin_cases a <;> rfl
  have h2 : v ∘ (frameCurvatureCycle.trans frameCurvatureCycle) = ![d, k, i, j, l] := by
    funext a
    fin_cases a <;> rfl
  have hh : frameTensor E T v + frameTensor E T (v ∘ frameCurvatureCycle) +
      frameTensor E T (v ∘ (frameCurvatureCycle.trans frameCurvatureCycle)) = 0 := by
    rw [frameTensor_permute E T frameCurvatureCycle,
      frameTensor_permute E T (frameCurvatureCycle.trans frameCurvatureCycle)]
    unfold frameTensor
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro b _
    linear_combination (∏ s, E (b s) (v s)) * hc b
  rw [h1, h2] at hh
  exact hh

theorem frame_normalizedWeyl_derivative_firstBianchi (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (d : Fin 4) :
    AlgebraicCurvature.FirstBianchi (curvatureDerivativeArray (frameTensor e.matrix
      (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c))) d) := by
  have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  rw [covariantDerivative_normalizedWeyl g c (chartAt FourSpace c c) hz (chartMetric_posDef g c).det_pos.ne']
  exact frameTensor_firstBianchi e.matrix
    (covariantDerivative g c (curvatureCoordinates g c) (chartAt FourSpace c c))
    (curvatureDerivative_firstBianchi g c (chartAt FourSpace c c) hz
      (chartMetric_posDef g c).det_pos.ne') d

end
end PositiveEinsteinFour.Geometry
end


section

/-! Algebraic curvature symmetries persist through a second covariant
derivative; all derivative slots remain separate from curvature slots. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def curvatureHessianArray (T : CovariantCoordinates 6) (d e : Fin 4) :
    Angular.CurvatureArray := fun i j k l => T ![d, e, i, j, k, l]

private def hessianPairSwap : Equiv.Perm (Fin 5) where
  toFun := ![0, 3, 4, 1, 2]
  invFun := ![0, 3, 4, 1, 2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem curvatureHessian_firstSkew (g : SmoothMetric M) (c : M)
    (z : FourSpace) (d e : Fin 4) : AlgebraicCurvature.FirstSkew
      (curvatureHessianArray
        (covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c)) z) d e) := by
  let T := covariantDerivative g c (curvatureCoordinates g c)
  have he : (fun w b => T w (b ∘ Equiv.swap 1 2)) =ᶠ[𝓝 z]
      (fun w => -T w) := by
    filter_upwards [] with w
    funext b
    have h1 : b ∘ Equiv.swap 1 2 = ![b 0, b 2, b 1, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    have h0 : b = ![b 0, b 1, b 2, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    rw [h1, h0]
    exact curvatureDerivative_firstSkew g c w (b 0) (b 1) (b 2) (b 3) (b 4)
  intro i j k l
  have hp : ![e, i, j, k, l] ∘ Equiv.swap 1 2 = ![e, j, i, k, l] := by
    funext a
    fin_cases a <;> rfl
  have h := covariantDerivative_permute_neg g c T (Equiv.swap 1 2) z he d ![e, i, j, k, l]
  rw [hp] at h
  exact h

theorem curvatureHessian_lastSkew (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (d e : Fin 4) :
    AlgebraicCurvature.LastSkew (curvatureHessianArray
      (covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c)) z) d e) := by
  let T := covariantDerivative g c (curvatureCoordinates g c)
  have he : (fun w b => T w (b ∘ Equiv.swap 3 4)) =ᶠ[𝓝 z]
      (fun w => -T w) := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
    funext b
    have h1 : b ∘ Equiv.swap 3 4 = ![b 0, b 1, b 2, b 4, b 3] := by
      funext i
      fin_cases i <;> rfl
    have h0 : b = ![b 0, b 1, b 2, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    rw [h1, h0]
    exact curvatureDerivative_lastSkew g c w hw (b 0) (b 1) (b 2) (b 3) (b 4)
  intro i j k l
  have hp : ![e, i, j, k, l] ∘ Equiv.swap 3 4 = ![e, i, j, l, k] := by
    funext a
    fin_cases a <;> rfl
  have h := covariantDerivative_permute_neg g c T (Equiv.swap 3 4) z he d ![e, i, j, k, l]
  rw [hp] at h
  exact h

theorem curvatureHessian_pairSymmetric (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (d e : Fin 4) :
    AlgebraicCurvature.PairSymmetric (curvatureHessianArray
      (covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c)) z) d e) := by
  let T := covariantDerivative g c (curvatureCoordinates g c)
  have he : (fun w b => T w (b ∘ hessianPairSwap)) =ᶠ[𝓝 z] T := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
    funext b
    have h1 : b ∘ hessianPairSwap = ![b 0, b 3, b 4, b 1, b 2] := by
      funext i
      fin_cases i <;> rfl
    have h0 : b = ![b 0, b 1, b 2, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    rw [h1, h0]
    exact curvatureDerivative_pairSymmetric g c w hw (b 0) (b 1) (b 2) (b 3) (b 4)
  intro i j k l
  have hp : ![e, i, j, k, l] ∘ hessianPairSwap = ![e, k, l, i, j] := by
    funext a
    fin_cases a <;> rfl
  have h := covariantDerivative_permute_eq g c T hessianPairSwap z he d ![e, i, j, k, l]
  rw [hp] at h
  exact h

theorem covariantHessian_normalizedWeyl (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c)) z =
      covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c)) z := by
  apply covariantDerivative_congr g c
  filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
  exact covariantDerivative_normalizedWeyl g c w hw
    (metricInChart_posDef g c w hw).det_pos.ne'

theorem frameHessian_firstSkew (E : Mat4) (T : CovariantCoordinates 6)
    (h : ∀ d e, AlgebraicCurvature.FirstSkew (curvatureHessianArray T d e))
    (d e : Fin 4) : AlgebraicCurvature.FirstSkew
      (curvatureHessianArray (frameTensor E T) d e) := by
  intro i j k l
  change frameTensor E T (Fin.cons d ![e, j, i, k, l]) =
    -frameTensor E T (Fin.cons d ![e, i, j, k, l])
  rw [frameTensor_cons E T d ![e, j, i, k, l],
    frameTensor_cons E T d ![e, i, j, k, l]]
  have hp (p : Fin 4) :
      frameTensor E (fun w => T (Fin.cons p w)) ![e, j, i, k, l] =
        -frameTensor E (fun w => T (Fin.cons p w)) ![e, i, j, k, l] :=
    frameTensor_firstSkew E (fun w => T (Fin.cons p w)) (h p) e i j k l
  simp only [hp, mul_neg, Finset.sum_neg_distrib]

theorem frameHessian_lastSkew (E : Mat4) (T : CovariantCoordinates 6)
    (h : ∀ d e, AlgebraicCurvature.LastSkew (curvatureHessianArray T d e))
    (d e : Fin 4) : AlgebraicCurvature.LastSkew
      (curvatureHessianArray (frameTensor E T) d e) := by
  intro i j k l
  change frameTensor E T (Fin.cons d ![e, i, j, l, k]) =
    -frameTensor E T (Fin.cons d ![e, i, j, k, l])
  rw [frameTensor_cons E T d ![e, i, j, l, k],
    frameTensor_cons E T d ![e, i, j, k, l]]
  have hp (p : Fin 4) :
      frameTensor E (fun w => T (Fin.cons p w)) ![e, i, j, l, k] =
        -frameTensor E (fun w => T (Fin.cons p w)) ![e, i, j, k, l] :=
    frameTensor_lastSkew E (fun w => T (Fin.cons p w)) (h p) e i j k l
  simp only [hp, mul_neg, Finset.sum_neg_distrib]

theorem frameHessian_pairSymmetric (E : Mat4) (T : CovariantCoordinates 6)
    (h : ∀ d e, AlgebraicCurvature.PairSymmetric (curvatureHessianArray T d e))
    (d e : Fin 4) : AlgebraicCurvature.PairSymmetric
      (curvatureHessianArray (frameTensor E T) d e) := by
  intro i j k l
  change frameTensor E T (Fin.cons d ![e, k, l, i, j]) =
    frameTensor E T (Fin.cons d ![e, i, j, k, l])
  rw [frameTensor_cons E T d ![e, k, l, i, j],
    frameTensor_cons E T d ![e, i, j, k, l]]
  have hp (p : Fin 4) :
      frameTensor E (fun w => T (Fin.cons p w)) ![e, k, l, i, j] =
        frameTensor E (fun w => T (Fin.cons p w)) ![e, i, j, k, l] :=
    frameTensor_pairSymmetric E (fun w => T (Fin.cons p w)) (h p) e i j k l
  simp only [hp]

theorem frame_normalizedWeyl_hessian_symmetries (g : SmoothMetric M) (c : M)
    (f : OrthonormalFrame g c) (d e : Fin 4) :
    let H := curvatureHessianArray (frameTensor f.matrix
      (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))
        (chartAt FourSpace c c))) d e
    AlgebraicCurvature.FirstSkew H ∧ AlgebraicCurvature.LastSkew H ∧
      AlgebraicCurvature.PairSymmetric H := by
  dsimp only
  have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  rw [covariantHessian_normalizedWeyl g c (chartAt FourSpace c c) hz]
  let T := covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c))
    (chartAt FourSpace c c)
  exact ⟨frameHessian_firstSkew f.matrix T
      (curvatureHessian_firstSkew g c (chartAt FourSpace c c)) d e,
    frameHessian_lastSkew f.matrix T
      (curvatureHessian_lastSkew g c (chartAt FourSpace c c) hz) d e,
    frameHessian_pairSymmetric f.matrix T
      (curvatureHessian_pairSymmetric g c (chartAt FourSpace c c) hz) d e⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite frame covariance for the curvature action on covariant tensors. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem frameTensor_add {n : ℕ} (E : Mat4) (S T : CovariantCoordinates n)
    (a : Fin n → Fin 4) :
    frameTensor E (S + T) a = frameTensor E S a + frameTensor E T a := by
  simp only [frameTensor, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem frameTensor_const_mul {n : ℕ} (E : Mat4) (r : ℝ)
    (T : CovariantCoordinates n) (a : Fin n → Fin 4) :
    frameTensor E (fun b => r * T b) a = r * frameTensor E T a := by
  simp only [frameTensor, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem frameTensor_sum {n : ℕ} {ι : Type*} [Fintype ι] (E : Mat4)
    (F : ι → CovariantCoordinates n) (a : Fin n → Fin 4) :
    frameTensor E (fun b => ∑ k, F k b) a = ∑ k, frameTensor E (F k) a := by
  simp only [frameTensor, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem tensorSlotAction_const_mul {n : ℕ} (A : Mat4) (r : ℝ)
    (T : CovariantCoordinates n) (a : Fin n → Fin 4) :
    tensorSlotAction A (fun b => r * T b) a = r * tensorSlotAction A T a := by
  simp only [tensorSlotAction, covariantSlotAction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem tensorSlotAction_sum {n : ℕ} {ι : Type*} [Fintype ι] (A : Mat4)
    (F : ι → CovariantCoordinates n) (a : Fin n → Fin 4) :
    tensorSlotAction A (fun b => ∑ k, F k b) a = ∑ k, tensorSlotAction A (F k) a := by
  simp only [tensorSlotAction, covariantSlotAction, Finset.mul_sum]
  calc
    _ = ∑ s, ∑ k, ∑ b, A b (a s) * F k (Function.update a s b) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

theorem tensorSlotAction_cons {n : ℕ} (A : Mat4)
    (T : CovariantCoordinates (n + 1)) (i : Fin 4) (a : Fin n → Fin 4) :
    tensorSlotAction A T (Fin.cons i a) =
      (∑ b, A b i * T (Fin.cons b a)) +
        tensorSlotAction A (fun w => T (Fin.cons i w)) a := by
  simp only [tensorSlotAction, covariantSlotAction, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero, ← Fin.cons_update]

private theorem intertwining_pairing (E A B : Mat4) (h : A * E = E * B)
    (f : Fin 4 → ℝ) (i : Fin 4) :
    (∑ b, E b i * ∑ c, A c b * f c) =
      ∑ b, B b i * ∑ c, E c b * f c := by
  calc
    _ = ∑ c, (A * E) c i * f c := by
      simp only [Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ∑ c, (E * B) c i * f c := by rw [h]
    _ = _ := by
      simp only [Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      ring

/-- An intertwining frame acts simultaneously on every covariant slot.
The proof uses one fresh slot at a time, so no large coordinate sum is expanded. -/
theorem frameTensor_slotAction_intertwine (E A B : Mat4) (h : A * E = E * B)
    {n : ℕ} (T : CovariantCoordinates n) :
    frameTensor E (tensorSlotAction A T) = tensorSlotAction B (frameTensor E T) := by
  induction n with
  | zero =>
    funext a
    simp [tensorSlotAction, frameTensor]
  | succ n ih =>
    funext a
    obtain ⟨i, v, rfl⟩ := Fin.exists_cons a
    let F (b : Fin 4) : CovariantCoordinates n := fun w => T (Fin.cons b w)
    have hT (b : Fin 4) :
        (fun w => tensorSlotAction A T (Fin.cons b w)) =
          (fun w => ∑ c, A c b * F c w) + tensorSlotAction A (F b) := by
      funext w
      exact tensorSlotAction_cons A T b w
    have hL (b : Fin 4) :
        frameTensor E (fun w => tensorSlotAction A T (Fin.cons b w)) v =
          (∑ c, A c b * frameTensor E (F c) v) +
            tensorSlotAction B (frameTensor E (F b)) v := by
      rw [hT, frameTensor_add, frameTensor_sum]
      simp only [frameTensor_const_mul]
      rw [ih (F b)]
    have hR :
        tensorSlotAction B (fun w => frameTensor E T (Fin.cons i w)) v =
          ∑ b, E b i * tensorSlotAction B (frameTensor E (F b)) v := by
      have hf : (fun w => frameTensor E T (Fin.cons i w)) =
          fun w => ∑ b, E b i * frameTensor E (F b) w := by
        funext w
        exact frameTensor_cons E T i w
      rw [hf, tensorSlotAction_sum]
      simp only [tensorSlotAction_const_mul]
    rw [frameTensor_cons, tensorSlotAction_cons]
    simp only [hL, mul_add, Finset.sum_add_distrib]
    rw [hR]
    congr 1
    simp only [frameTensor_cons]
    exact intertwining_pairing E A B h (fun c => frameTensor E (F c) v) i

theorem frameTensor_slotAction {n : ℕ} (E A : Mat4) (hE : IsUnit E.det)
    (T : CovariantCoordinates n) :
    frameTensor E (tensorSlotAction A T) =
      tensorSlotAction (E⁻¹ * A * E) (frameTensor E T) := by
  apply frameTensor_slotAction_intertwine
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv E hE, one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The weak energy equation tested against the actual nonsmooth deficit
δ=2-v-b. This supplies one side of the integration by parts in (16). -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators Topology Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem MetricGreenData.deficitEnergyEquation (d : MetricGreenData g μ) (o : OppositeWeylData d)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    (∫ e, regularizedDeficit 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) *
        d.energyLaplacianField e +
      ∑ i, regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
        d.energyDerivativeField i e ∂μ) = 0 := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  have hε1 (n) : ε n ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let m : ℕ → C(FrameBundle g, ℝ) := fun n =>
    ⟨fun e => regularizedDeficit (ε n) (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame),
      (continuous_const.sub ((d.regularizedNormField (ε n)).continuous)).sub
        ((continuous_regularizedBlockNorm (ε n)).comp o.continuousWeyl)⟩
  let dm : ℕ → Fin 4 → C(FrameBundle g, ℝ) := fun n i =>
    ⟨fun e => regularizedDeficitDerivative (ε n) (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i),
      ((d.regularizedRadialField (ε n) (hε n) i).continuous.neg).sub
        (continuous_regularizedRadialDerivative (ε n) (hε n) _ _ o.continuousWeyl (o.continuousGradient i))⟩
  let F : ℕ → C(FrameBundle g, ℝ) := fun n =>
    ⟨fun e => m n e * d.energyLaplacianField e + ∑ i, dm n i e * d.energyDerivativeField i e,
      ((m n).continuous.mul d.energyLaplacianField.continuous).add
        (continuous_finsetSum _ (fun i _ => (dm n i).continuous.mul
          (d.energyDerivativeField i).continuous))⟩
  have hF (n) : (∫ e, F n e ∂μ) = 0 := by
    apply d.testedEnergyEquation (m n) (dm n)
    intro i t e
    exact hasDerivAt_regularizedDeficit (d.derivativeWeyl i t e) (o.derivativeWeyl i t e)
      (fun s => d.weyl.symmetric ((d.flow i).map s e))
      (fun s => o.symmetric ((d.flow i).map s e)) (hε n)
  let H : C(FrameBundle g, ℝ) := ⟨fun e => 6 * |d.energyLaplacianField e| +
    ∑ i, (normalizedBlockNorm (plusWeylGradient g e.base e.frame i) +
      normalizedBlockNorm (minusWeylGradient g e.base e.frame i)) * |d.energyDerivativeField i e|, by
        apply Continuous.add (continuous_const.mul d.energyLaplacianField.continuous.abs)
        apply continuous_finsetSum
        intro i _
        exact ((continuous_normalizedBlockNorm.comp (d.continuousGradient i)).add
          (continuous_normalizedBlockNorm.comp (o.continuousGradient i))).mul
            (d.energyDerivativeField i).continuous.abs⟩
  have hc : Tendsto (fun n => ∫ e, F n e ∂μ) atTop
      (𝓝 (∫ e, regularizedDeficit 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) *
        d.energyLaplacianField e +
        ∑ i, regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
          d.energyDerivativeField i e ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence H
    · exact fun n => (F n).continuous.aestronglyMeasurable
    · exact H.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · intro n
      filter_upwards [] with e
      rw [Real.norm_eq_abs]
      change |m n e * d.energyLaplacianField e + ∑ i, dm n i e * d.energyDerivativeField i e| ≤ _
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (abs_regularizedDeficit_le (hε n).le (hε1 n) _ _
          (hpinch e)) (abs_nonneg _)
      · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (abs_regularizedDeficitDerivative_le (hε n) _ _ _ _
          ((d.gradientConstraints e).1 i) ((o.gradientConstraints e).1 i)) (abs_nonneg _)
    · filter_upwards [] with e
      apply Tendsto.add
      · exact ((tendsto_regularizedDeficit _ _).comp hlim).mul tendsto_const_nhds
      · apply tendsto_finsetSum
        intro i _
        exact ((tendsto_regularizedDeficitDerivative _ _ _ _).comp hlim).mul tendsto_const_nhds
  simp only [hF] at hc
  exact tendsto_nhds_unique hc tendsto_const_nhds

end
end PositiveEinsteinFour.Geometry
end


section

/-! The invariant Bianchi refined Kato inequality for the metric. The weak
norm equations and singular quotient integrability follow from parallel-frame
covariant calculus. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem refinedKato (d : MetricGreenData g μ) (e : FrameBundle g) :
    (5 / 3 : ℝ) * ‖blockRadialGradient (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame)‖ ^ 2 ≤
        weylGradientEnergy (plusWeylGradient g e.base e.frame) :=
  QuaternionFrame.blockRadialGradient_refined_kato _ _ (d.weyl.symmetric e)
    (d.weyl.traceFree e) (d.gradientConstraints e).1 (d.gradientConstraints e).2
    (d.gradientBianchi e)

theorem energyQuotient_integrable (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ] :
    Integrable (fun e => weylGradientEnergy (plusWeylGradient g e.base e.frame) /
      normalizedBlockNorm (plusWeyl g e.base e.frame)) μ :=
  d.integrableEnergyQuotient d.refinedKato

theorem weakNormEquation (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ] :
    (∫ e, scalarNormExpression 0 (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame) ∂μ) = 0 :=
  d.scalarNormEquation d.refinedKato

theorem kappaTest (d : MetricGreenData g μ) (o : OppositeWeylData d)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    (∫ e, regularizedKappa 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) *
        scalarNormExpression 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) +
      ∑ i, regularizedKappaDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
        regularizedRadialDerivative 0 (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame i) ∂μ) = 0 :=
  d.kappaNormEquation o d.refinedKato hpinch

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The positive trace-free Hessian energy behind the integral addition
in equation (16). The entire prescribed trace component is subtracted. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem prescribed_trace_norm_subtraction (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (X : Hessian) (hmatrix : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbianchi : ∀ i r, divergence X i r = 0) (htrace : hessianTrace X = M) :
    hessianNormSq (X - traceComponent M) = hessianNormSq X - (5 / 12) * matrixNormSq M := by
  rw [hessianNormSq_sub, hessianPairing_comm,
    traceComponent_pairing_hessian M hs ht X hmatrix hbianchi,
    htrace, traceComponent_norm M hs ht]
  have hM : matrixPairing M M = matrixNormSq M := by
    simp only [matrixPairing, matrixNormSq, pow_two]
  rw [hM]
  ring

def traceEnergy (A : Mat) : ℝ := (5 / 36 : ℝ) * matrixNormSq (weylLaplacian A)

theorem continuous_traceEnergy : Continuous traceEnergy := by
  unfold traceEnergy matrixNormSq
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro a _
  apply continuous_finsetSum
  intro b _
  exact (((matrixEntryMap a b).continuous.comp continuous_weylLaplacian).pow 2)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem traceEnergy_remainder (d : MetricGreenData g μ) (e : FrameBundle g) :
    hessianNormSq (plusWeylHessian g e.base e.frame) / 3 -
      traceEnergy (plusWeyl g e.base e.frame) =
    hessianNormSq (plusWeylHessian g e.base e.frame -
      traceComponent (weylLaplacian (plusWeyl g e.base e.frame))) / 3 := by
  rw [prescribed_trace_norm_subtraction _
    (weylLaplacian_symmetric _ (d.weyl.symmetric e))
    (weylLaplacian_traceFree _ (d.weyl.traceFree e)) _
    (d.weyl.hessianMatrix e) (d.weyl.hessianBianchi e) (metric_weyl_trace g d.weyl e)]
  unfold traceEnergy
  ring

theorem traceEnergy_le_hessian (d : MetricGreenData g μ) (e : FrameBundle g) :
    traceEnergy (plusWeyl g e.base e.frame) ≤
      hessianNormSq (plusWeylHessian g e.base e.frame) / 3 := by
  have h : 0 ≤ hessianNormSq (plusWeylHessian g e.base e.frame -
      traceComponent (weylLaplacian (plusWeyl g e.base e.frame))) := by
    unfold hessianNormSq
    positivity
  have he := d.traceEnergy_remainder e
  linarith

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrating the positive regularized cube root gives an energy
bound with an error tending to zero, without singular gradient limits. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem cubeRoot_regularization_error_le (v ε u : ℝ)
    (hv : 0 ≤ v) (hε : 0 < ε) (hu : 0 < u) (hsq : u ^ 2 = v ^ 2 + ε ^ 2) :
    2 * (u ^ (1 / 3 : ℝ)) ^ 2 - 2 * v * (u ^ (1 / 3 : ℝ)) ^ 2 -
        u ^ (1 / 3 : ℝ) * (2 * v ^ 2 * (1 - v) / u ^ (5 / 3 : ℝ)) ≤
      2 * ε ^ (2 / 3 : ℝ) := by
  have hu4 : 0 < u ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hu _
  have he4 : 0 < ε ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hε _
  have hf : (u ^ (1 / 3 : ℝ)) ^ 2 = u ^ 2 / u ^ (4 / 3 : ℝ) := by
    calc
      _ = u ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_mul_natCast hu.le]
        norm_num
      _ = _ := by
        simpa only [show (2 : ℝ) - 4 / 3 = 2 / 3 by norm_num,
          Real.rpow_two] using Real.rpow_sub hu 2 (4 / 3 : ℝ)
  have hr : u ^ (1 / 3 : ℝ) / u ^ (5 / 3 : ℝ) = (u ^ (4 / 3 : ℝ))⁻¹ := by
    rw [← Real.rpow_sub hu]
    rw [show (1 / 3 : ℝ) - 5 / 3 = -(4 / 3 : ℝ) by norm_num,
      Real.rpow_neg hu.le]
  have hid : 2 * (u ^ (1 / 3 : ℝ)) ^ 2 - 2 * v * (u ^ (1 / 3 : ℝ)) ^ 2 -
      u ^ (1 / 3 : ℝ) * (2 * v ^ 2 * (1 - v) / u ^ (5 / 3 : ℝ)) =
      2 * ε ^ 2 * (1 - v) / u ^ (4 / 3 : ℝ) := by
    rw [hf]
    calc
      _ = 2 * u ^ 2 / u ^ (4 / 3 : ℝ) - 2 * v * u ^ 2 / u ^ (4 / 3 : ℝ) -
          2 * v ^ 2 * (1 - v) * (u ^ (1 / 3 : ℝ) / u ^ (5 / 3 : ℝ)) := by ring
      _ = _ := by rw [hr, hsq]; ring
  have heu : ε ≤ u := by nlinarith [sq_nonneg v]
  have hpow : ε ^ (4 / 3 : ℝ) ≤ u ^ (4 / 3 : ℝ) :=
    Real.rpow_le_rpow hε.le heu (by norm_num)
  have hb : ε ^ 2 / u ^ (4 / 3 : ℝ) ≤ ε ^ (2 / 3 : ℝ) := by
    calc
      _ ≤ ε ^ 2 / ε ^ (4 / 3 : ℝ) :=
        div_le_div_of_nonneg_left (sq_nonneg ε) he4 hpow
      _ = _ := by
        symm
        simpa only [show (2 : ℝ) - 4 / 3 = 2 / 3 by norm_num,
          Real.rpow_two] using Real.rpow_sub hε 2 (4 / 3 : ℝ)
  rw [hid]
  calc
    _ ≤ 2 * ε ^ 2 / u ^ (4 / 3 : ℝ) := by
      apply div_le_div_of_nonneg_right _ hu4.le
      nlinarith [mul_nonneg (sq_nonneg ε) hv]
    _ = 2 * (ε ^ 2 / u ^ (4 / 3 : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by norm_num)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace MetricGreenData

def weylRootField (d : MetricGreenData g μ) (ε : ℝ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => regularizedWeylRoot ε (plusWeyl g e.base e.frame),
    (continuous_regularizedWeylRoot ε).comp d.continuousWeyl⟩

def weylRootFirstField (d : MetricGreenData g μ) (ε : ℝ) (hε : 0 < ε) (i : Fin 4) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => regularizedWeylRootFirst ε (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i),
    continuous_regularizedWeylRootFirst ε hε _ _ d.continuousWeyl (d.continuousGradient i)⟩

def weylRootSecondField (d : MetricGreenData g μ) (ε : ℝ) (hε : 0 < ε) (i : Fin 4) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => regularizedWeylRootSecond ε (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i) (plusWeylHessian g e.base e.frame i i),
    continuous_regularizedWeylRootSecond ε hε _ _ _ d.continuousWeyl
      (d.continuousGradient i) (d.continuousHessian i i)⟩

theorem weylRoot_error_le (d : MetricGreenData g μ) (ε : ℝ) (hε : 0 < ε)
    (e : FrameBundle g) :
    2 * d.weylRootField ε e ^ 2 -
        2 * normalizedBlockNorm (plusWeyl g e.base e.frame) * d.weylRootField ε e ^ 2 -
        d.weylRootField ε e * (∑ i, d.weylRootSecondField ε hε i e) ≤
      2 * ε ^ (2 / 3 : ℝ) := by
  let A := plusWeyl g e.base e.frame
  let u := regularizedBlockNorm ε A
  have hu : 0 < u := regularizedBlockNorm_pos ε hε A
  have hs : u ^ 2 = normalizedBlockNorm A ^ 2 + ε ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hb := cubeRoot_regularization_error_le (normalizedBlockNorm A) ε u
    (normalizedBlockNorm_nonneg A) hε hu hs
  have hl := mul_le_mul_of_nonneg_left (d.regularizedWeylRoot_lower ε hε e)
    (Real.rpow_nonneg hu.le (1 / 3 : ℝ))
  change 2 * (u ^ (1 / 3 : ℝ)) ^ 2 -
      2 * normalizedBlockNorm A * (u ^ (1 / 3 : ℝ)) ^ 2 -
      u ^ (1 / 3 : ℝ) * (∑ i, d.weylRootSecondField ε hε i e) ≤ _
  change u ^ (1 / 3 : ℝ) *
      (2 * normalizedBlockNorm A ^ 2 * (1 - normalizedBlockNorm A) /
        u ^ (5 / 3 : ℝ)) ≤
      u ^ (1 / 3 : ℝ) * (∑ i, d.weylRootSecondField ε hε i e) at hl
  linarith

variable [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

theorem weylRoot_energy_eq (d : MetricGreenData g μ) (ε : ℝ) (hε : 0 < ε) :
    (∫ e, ∑ i, d.weylRootFirstField ε hε i e ^ 2 ∂μ) =
      -(∫ e, d.weylRootField ε e * (∑ i, d.weylRootSecondField ε hε i e) ∂μ) := by
  have hi (i : Fin 4) := scalar_flow_green (d := d) i (d.weylRootField ε)
    (d.weylRootFirstField ε hε i) (d.weylRootFirstField ε hε i)
    (d.weylRootSecondField ε hε i) (d.regularizedWeylRoot_derivative ε hε i)
    (d.regularizedWeylRootFirst_derivative ε hε i)
  have hfirst (i : Fin 4) : Integrable (fun e => d.weylRootFirstField ε hε i e ^ 2) μ :=
    ((d.weylRootFirstField ε hε i).continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsecond (i : Fin 4) : Integrable
      (fun e => d.weylRootField ε e * d.weylRootSecondField ε hε i e) μ :=
    ((d.weylRootField ε).continuous.mul (d.weylRootSecondField ε hε i).continuous)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [← pow_two] at hi
  rw [integral_finsetSum _ (fun i _ => hfirst i)]
  simp_rw [hi]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hsecond i)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with e
  exact (Finset.mul_sum _ _ _).symm

/-- The regularized gap energy estimate has a uniform vanishing error,
and needs no limiting statement about the singular norm gradient. -/
theorem weylRoot_energy_le (d : MetricGreenData g μ) (ε : ℝ) (hε : 0 < ε) :
    (∫ e, (∑ i, d.weylRootFirstField ε hε i e ^ 2) +
        2 * d.weylRootField ε e ^ 2 ∂μ) ≤
      2 * (∫ e, normalizedBlockNorm (plusWeyl g e.base e.frame) *
        d.weylRootField ε e ^ 2 ∂μ) + 2 * ε ^ (2 / 3 : ℝ) * μ.real univ := by
  let F := d.weylRootField ε
  let G := d.weylRootFirstField ε hε
  let H := d.weylRootSecondField ε hε
  let V : C(FrameBundle g, ℝ) := ⟨fun e => normalizedBlockNorm (plusWeyl g e.base e.frame),
    continuous_normalizedBlockNorm.comp d.continuousWeyl⟩
  have hF : Integrable (fun e => F e ^ 2) μ :=
    (F.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hV : Integrable (fun e => V e * F e ^ 2) μ :=
    (V.continuous.mul (F.continuous.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hH : Integrable (fun e => F e * ∑ i, H i e) μ :=
    (F.continuous.mul (continuous_finsetSum _ (fun i _ => (H i).continuous)))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hG : Integrable (fun e => ∑ i, G i e ^ 2) μ :=
    (continuous_finsetSum _ (fun i _ => (G i).continuous.pow 2))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbound : (∫ e, 2 * F e ^ 2 - 2 * (V e * F e ^ 2) -
      F e * (∑ i, H i e) ∂μ) ≤ ∫ _e : FrameBundle g, 2 * ε ^ (2 / 3 : ℝ) ∂μ := by
    apply integral_mono (((hF.const_mul 2).sub (hV.const_mul 2)).sub hH)
      (integrable_const (2 * ε ^ (2 / 3 : ℝ)))
    intro e
    have h := d.weylRoot_error_le ε hε e
    change 2 * F e ^ 2 - 2 * V e * F e ^ 2 - F e * (∑ i, H i e) ≤ _ at h
    change 2 * F e ^ 2 - 2 * (V e * F e ^ 2) - F e * (∑ i, H i e) ≤ _
    nlinarith only [h]
  have hsplit : (∫ e, 2 * F e ^ 2 - 2 * (V e * F e ^ 2) ∂μ) =
      2 * (∫ e, F e ^ 2 ∂μ) - 2 * (∫ e, V e * F e ^ 2 ∂μ) := by
    calc
      _ = (∫ e, 2 * F e ^ 2 ∂μ) - (∫ e, 2 * (V e * F e ^ 2) ∂μ) :=
        integral_sub (hF.const_mul 2) (hV.const_mul 2)
      _ = _ := by rw [integral_const_mul, integral_const_mul]
  have hsplit' : (∫ e, 2 * F e ^ 2 - 2 * (V e * F e ^ 2) -
      F e * (∑ i, H i e) ∂μ) =
      2 * (∫ e, F e ^ 2 ∂μ) - 2 * (∫ e, V e * F e ^ 2 ∂μ) -
        (∫ e, F e * (∑ i, H i e) ∂μ) := by
    calc
      _ = (∫ e, 2 * F e ^ 2 - 2 * (V e * F e ^ 2) ∂μ) -
          (∫ e, F e * (∑ i, H i e) ∂μ) :=
        integral_sub ((hF.const_mul 2).sub (hV.const_mul 2)) hH
      _ = _ := by rw [hsplit]
  rw [hsplit', integral_const] at hbound
  have he := d.weylRoot_energy_eq ε hε
  change (∫ e, ∑ i, G i e ^ 2 ∂μ) = -(∫ e, F e * ∑ i, H i e ∂μ) at he
  change (∫ e, (∑ i, G i e ^ 2) + 2 * F e ^ 2 ∂μ) ≤
    2 * (∫ e, V e * F e ^ 2 ∂μ) + _
  rw [integral_add hG (hF.const_mul 2), integral_const_mul]
  simp only [smul_eq_mul] at hbound
  nlinarith only [hbound, he]

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Contraction of the actual covariant slot action with two-form matrices. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

/-- The bilinear two-form contraction defining each Weyl block entry. -/
def twoFormPairing (T : CovariantCoordinates 4) (P Q : Mat4) : ℝ :=
  (1 / 8 : ℝ) * ∑ a, ∑ b, ∑ c, ∑ d, T ![a, b, d, c] * P a b * Q c d

private theorem sumFive_swap0
    (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ x, f a b c d x) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, f x b c d a := by
  let e : (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) ≃
      (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) := {
    toFun := fun ⟨a, b, c, d, x⟩ => (x, b, c, d, a)
    invFun := fun ⟨a, b, c, d, x⟩ => (x, b, c, d, a)
    left_inv := by rintro ⟨a, b, c, d, x⟩; rfl
    right_inv := by rintro ⟨a, b, c, d, x⟩; rfl }
  simpa only [e, Equiv.coe_fn_mk, Fintype.sum_prod_type] using
    (e.sum_comp (fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)).symm

private theorem sumFive_swap1
    (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ x, f a b c d x) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, f a x c d b := by
  let e : (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) ≃
      (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) := {
    toFun := fun ⟨a, b, c, d, x⟩ => (a, x, c, d, b)
    invFun := fun ⟨a, b, c, d, x⟩ => (a, x, c, d, b)
    left_inv := by rintro ⟨a, b, c, d, x⟩; rfl
    right_inv := by rintro ⟨a, b, c, d, x⟩; rfl }
  simpa only [e, Equiv.coe_fn_mk, Fintype.sum_prod_type] using
    (e.sum_comp (fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)).symm

private theorem sumFive_swap2
    (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ x, f a b c d x) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, f a b x d c := by
  let e : (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) ≃
      (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) := {
    toFun := fun ⟨a, b, c, d, x⟩ => (a, b, x, d, c)
    invFun := fun ⟨a, b, c, d, x⟩ => (a, b, x, d, c)
    left_inv := by rintro ⟨a, b, c, d, x⟩; rfl
    right_inv := by rintro ⟨a, b, c, d, x⟩; rfl }
  simpa only [e, Equiv.coe_fn_mk, Fintype.sum_prod_type] using
    (e.sum_comp (fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)).symm

private theorem sumFive_swap3
    (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ x, f a b c d x) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, f a b c x d := by
  let e : (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) ≃
      (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) := {
    toFun := fun ⟨a, b, c, d, x⟩ => (a, b, c, x, d)
    invFun := fun ⟨a, b, c, d, x⟩ => (a, b, c, x, d)
    left_inv := by rintro ⟨a, b, c, d, x⟩; rfl
    right_inv := by rintro ⟨a, b, c, d, x⟩; rfl }
  simpa only [e, Equiv.coe_fn_mk, Fintype.sum_prod_type] using
    (e.sum_comp (fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)).symm

theorem twoFormPairing_add_tensor (S T : CovariantCoordinates 4) (P Q : Mat4) :
    twoFormPairing (S + T) P Q = twoFormPairing S P Q + twoFormPairing T P Q := by
  simp only [twoFormPairing, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem twoFormPairing_add_left (T : CovariantCoordinates 4) (P R Q : Mat4) :
    twoFormPairing T (P + R) Q = twoFormPairing T P Q + twoFormPairing T R Q := by
  simp only [twoFormPairing, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem twoFormPairing_add_right (T : CovariantCoordinates 4) (P Q R : Mat4) :
    twoFormPairing T P (Q + R) = twoFormPairing T P Q + twoFormPairing T P R := by
  simp only [twoFormPairing, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

private theorem updateFour_0 (a b c d x : Fin 4) :
    Function.update ![a, b, d, c] 0 x = ![x, b, d, c] := by
  funext i
  fin_cases i <;> simp

theorem twoFormPairing_slot0 (A : Mat4) (T : CovariantCoordinates 4)
    (P Q : Mat4) :
    twoFormPairing (covariantSlotAction 0 A T) P Q =
      twoFormPairing T (A * P) Q := by
  unfold twoFormPairing
  congr 1
  simp only [covariantSlotAction, updateFour_0,
    Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sumFive_swap0]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  dsimp
  ring

private theorem updateFour_1 (a b c d x : Fin 4) :
    Function.update ![a, b, d, c] 1 x = ![a, x, d, c] := by
  funext i
  fin_cases i <;> simp

theorem twoFormPairing_slot1 (A : Mat4) (T : CovariantCoordinates 4)
    (P Q : Mat4) :
    twoFormPairing (covariantSlotAction 1 A T) P Q =
      twoFormPairing T (P * Aᵀ) Q := by
  unfold twoFormPairing
  congr 1
  simp only [covariantSlotAction, updateFour_1,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sumFive_swap1]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  dsimp
  ring

private theorem updateFour_2 (a b c d x : Fin 4) :
    Function.update ![a, b, d, c] 2 x = ![a, b, x, c] := by
  funext i
  fin_cases i <;> simp

theorem twoFormPairing_slot2 (A : Mat4) (T : CovariantCoordinates 4)
    (P Q : Mat4) :
    twoFormPairing (covariantSlotAction 2 A T) P Q =
      twoFormPairing T P (Q * Aᵀ) := by
  unfold twoFormPairing
  congr 1
  simp only [covariantSlotAction, updateFour_2,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sumFive_swap3]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  dsimp
  ring

private theorem updateFour_3 (a b c d x : Fin 4) :
    Function.update ![a, b, d, c] 3 x = ![a, b, d, x] := by
  funext i
  fin_cases i <;> simp

theorem twoFormPairing_slot3 (A : Mat4) (T : CovariantCoordinates 4)
    (P Q : Mat4) :
    twoFormPairing (covariantSlotAction 3 A T) P Q =
      twoFormPairing T P (A * Q) := by
  unfold twoFormPairing
  congr 1
  simp only [covariantSlotAction, updateFour_3,
    Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sumFive_swap2]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  dsimp
  ring

/-- Contracting all four covariant slots acts on each two-form factor. -/
theorem twoFormPairing_slotAction (A : Mat4) (T : CovariantCoordinates 4)
    (P Q : Mat4) :
    twoFormPairing (tensorSlotAction A T) P Q =
      twoFormPairing T (A * P + P * Aᵀ) Q +
        twoFormPairing T P (Q * Aᵀ + A * Q) := by
  have hT : tensorSlotAction A T = covariantSlotAction 0 A T +
      covariantSlotAction 1 A T + covariantSlotAction 2 A T + covariantSlotAction 3 A T := by
    funext a
    simp only [tensorSlotAction, Fin.sum_univ_four, Pi.add_apply]
  rw [hT]
  simp only [twoFormPairing_add_tensor, twoFormPairing_slot0,
    twoFormPairing_slot1, twoFormPairing_slot2, twoFormPairing_slot3,
    twoFormPairing_add_left, twoFormPairing_add_right]
  ring

theorem twoFormPairing_skew_slotAction (A : Mat4) (hA : Aᵀ = -A)
    (T : CovariantCoordinates 4) (P Q : Mat4) :
    twoFormPairing (tensorSlotAction A T) P Q =
      twoFormPairing T (A * P - P * A) Q +
        twoFormPairing T P (A * Q - Q * A) := by
  rw [twoFormPairing_slotAction, hA, Matrix.mul_neg, Matrix.mul_neg]
  have he : -(Q * A) + A * Q = A * Q - Q * A := by
    abel
  rw [he]
  rfl


theorem twoFormPairing_smul_left (T : CovariantCoordinates 4) (P Q : Mat4) (r : ℝ) :
    twoFormPairing T (r • P) Q = r * twoFormPairing T P Q := by
  simp only [twoFormPairing, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

theorem twoFormPairing_smul_right (T : CovariantCoordinates 4) (P Q : Mat4) (r : ℝ) :
    twoFormPairing T P (r • Q) = r * twoFormPairing T P Q := by
  simp only [twoFormPairing, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

theorem twoFormPairing_zero_left (T : CovariantCoordinates 4) (Q : Mat4) :
    twoFormPairing T 0 Q = 0 := by simp [twoFormPairing]

theorem twoFormPairing_zero_right (T : CovariantCoordinates 4) (P : Mat4) :
    twoFormPairing T P 0 = 0 := by simp [twoFormPairing]

theorem blockCoordinates_pairing (T : CovariantCoordinates 4) (Q : Fin 3 → Mat4)
    (a b : Fin 3) : blockCoordinates T Q a b = twoFormPairing T (Q a) (Q b) := by
  simp only [blockCoordinates, curvatureBlock, twoFormPairing, Fintype.sum_prod_type]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Weyl gradient satisfies the finite Bianchi constraints as
soon as the actual fixed-chart Ricci field is covariantly constant. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

/-- The Ricci-parallel hypothesis concerns the fixed-chart Ricci field
throughout the chart. -/
theorem plusWeylGradient_bianchi_of_ricci_parallel (e : OrthonormalFrame g c)
    (hRic : covariantDerivative g c (ricciTensorCoordinates g c)
      (chartAt FourSpace c c) = 0) (r : Fin 3) (i : Fin 4) :
    gradientDivergence (plusWeylGradient g c e) r i = 0 := by
  let T := frameTensor e.matrix
    (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c))
  have hs := frame_normalizedWeyl_derivative_symmetries g c e
  have hR (a j k : Fin 4) : (∑ l, T ![a, l, j, k, l]) = 0 := by
    dsimp only [T]
    have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
    rw [covariantDerivative_normalizedWeyl g c (chartAt FourSpace c c) hz (chartMetric_posDef g c).det_pos.ne']
    exact frame_curvature_derivative_trace_zero e hRic a j k
  exact gradientBlock_divergence_of_ricci_parallel T
    (fun a => (hs a).1) (fun a => (hs a).2.1) (fun a => (hs a).2.2)
    (frame_normalizedWeyl_second_bianchi g c e) hR r i

/-- The Ricci-parallel hypothesis concerns the fixed-chart Ricci field
throughout the chart. -/
theorem minusWeylGradient_bianchi_of_ricci_parallel (e : OrthonormalFrame g c)
    (hRic : covariantDerivative g c (ricciTensorCoordinates g c)
      (chartAt FourSpace c c) = 0) (r : Fin 3) (i : Fin 4) :
    (∑ s, ∑ j, Angular.oppositeMatrix s i j * minusWeylGradient g c e j s r) = 0 := by
  let T := frameTensor e.matrix
    (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c))
  have hs := frame_normalizedWeyl_derivative_symmetries g c e
  have hR (a j k : Fin 4) : (∑ l, T ![a, l, j, k, l]) = 0 := by
    dsimp only [T]
    have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
    rw [covariantDerivative_normalizedWeyl g c (chartAt FourSpace c c) hz (chartMetric_posDef g c).det_pos.ne']
    exact frame_curvature_derivative_trace_zero e hRic a j k
  exact opposite_gradientBlock_divergence_of_ricci_parallel T
    (fun a => (hs a).1) (fun a => (hs a).2.1) (fun a => (hs a).2.2)
    (frame_normalizedWeyl_second_bianchi g c e) hR r i

/-- Both block derivatives are symmetric and trace-free, obtained directly
from the five-tensor identities rather than a moving eigenframe. -/
theorem weylGradient_constraints_of_ricci_parallel (e : OrthonormalFrame g c)
    (hRic : covariantDerivative g c (ricciTensorCoordinates g c)
      (chartAt FourSpace c c) = 0) :
    (∀ i, TraceHessian.symmetric (plusWeylGradient g c e i) ∧
      TraceHessian.traceFree (plusWeylGradient g c e i)) ∧
    (∀ i, TraceHessian.symmetric (minusWeylGradient g c e i) ∧
      TraceHessian.traceFree (minusWeylGradient g c e i)) := by
  let T := frameTensor e.matrix
    (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c))
  have hs := frame_normalizedWeyl_derivative_symmetries g c e
  have hb := frame_normalizedWeyl_derivative_firstBianchi g c e
  have hR (a j k : Fin 4) : (∑ l, T ![a, l, j, k, l]) = 0 := by
    dsimp only [T]
    have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
    rw [covariantDerivative_normalizedWeyl g c (chartAt FourSpace c c) hz (chartMetric_posDef g c).det_pos.ne']
    exact frame_curvature_derivative_trace_zero e hRic a j k
  have ht (i : Fin 4) := AlgebraicCurvature.ricci_zero_blocks_traceFree
    (curvatureDerivativeArray T i) (hs i).1 (hs i).2.1 (hb i)
    (fun j => hR i j j)
  have hsym (i : Fin 4) (Q : Fin 3 → Mat4) :
      TraceHessian.symmetric (gradientBlock T Q i) := by
    have hh := curvatureBlock_symmetric
      (AlgebraicCurvature.curvaturePairing_symmetric
        (curvatureDerivativeArray T i) (hs i).1 (hs i).2.1 (hs i).2.2) Q
    intro a b
    exact congrArg (fun A : Mat3 => A b a) hh
  exact ⟨fun i => ⟨hsym i _, (ht i).1⟩, fun i => ⟨hsym i _, (ht i).2⟩⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Curvature-slot identities of the actual Weyl Hessian, kept separate
from its derivative-slot commutator and trace equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem actual_weylHessian_symmetric (e : OrthonormalFrame g c) (i j : Fin 4) :
    TraceHessian.symmetric (plusWeylHessian g c e i j) ∧
      TraceHessian.symmetric (minusWeylHessian g c e i j) := by
  let T := frameTensor e.matrix
    (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))
      (chartAt FourSpace c c))
  have hs := frame_normalizedWeyl_hessian_symmetries g c e i j
  have hp := AlgebraicCurvature.curvaturePairing_symmetric
    (curvatureHessianArray T i j) hs.1 hs.2.1 hs.2.2
  have hsym (Q : Fin 3 → Mat4) : TraceHessian.symmetric (hessianBlock T Q i j) := by
    have hh := curvatureBlock_symmetric hp Q
    intro a b
    exact congrArg (fun A : Mat3 => A b a) hh
  exact ⟨hsym _, hsym _⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Einstein curvature Hessian has zero Ricci contraction.
The first Ricci contraction vanishes on an open chart before differentiating. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators Topology

noncomputable section

private theorem sum_five (f : Fin 5 → ℝ) :
    (∑ i, f i) = f 0 + (f 1 + f 2 + f 3 + f 4) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_four]
  rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem covariantDerivative_five_apply (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates 5) (z : FourSpace)
    (d a b j k l : Fin 4) :
    covariantDerivative g c T z ![d, a, b, j, k, l] =
      partialDeriv (fun w => T w ![a, b, j, k, l]) d z -
      ((∑ p, christoffel g c z p d a * T z ![p, b, j, k, l]) +
       (∑ p, christoffel g c z p d b * T z ![a, p, j, k, l]) +
       (∑ p, christoffel g c z p d j * T z ![a, b, p, k, l]) +
       (∑ p, christoffel g c z p d k * T z ![a, b, j, p, l]) +
       (∑ p, christoffel g c z p d l * T z ![a, b, j, k, p])) := by
  have hu (s : Fin 5) (p : Fin 4) :
      Function.update ![a, b, j, k, l] s p =
        ![(if s = 0 then p else a), (if s = 1 then p else b),
          (if s = 2 then p else j), (if s = 3 then p else k),
          (if s = 4 then p else l)] := by
    funext t
    fin_cases s <;> fin_cases t <;> rfl
  change partialDeriv (fun w => T w ![a, b, j, k, l]) d z -
    (∑ s : Fin 5, ∑ p, christoffel g c z p d (![a, b, j, k, l] s) *
      T z (Function.update ![a, b, j, k, l] s p)) = _
  rw [sum_five]
  simp only [hu]
  norm_num only [Fin.reduceEq, ite_true, ite_false]
  change partialDeriv (fun w => T w ![a, b, j, k, l]) d z -
    ((∑ p, christoffel g c z p d a * T z ![p, b, j, k, l]) +
      ((∑ p, christoffel g c z p d b * T z ![a, p, j, k, l]) +
       (∑ p, christoffel g c z p d j * T z ![a, b, p, k, l]) +
       (∑ p, christoffel g c z p d k * T z ![a, b, j, p, l]) +
       (∑ p, christoffel g c z p d l * T z ![a, b, j, k, p]))) = _
  ring

/-- Put the two contracted curvature slots into the row/column positions. -/
def fiveTensorMatrix (T : FourSpace → CovariantCoordinates 5)
    (a j k : Fin 4) (z : FourSpace) : Mat4 :=
  fun p q => T z ![a, q, j, k, p]

theorem fiveTensorMatrix_covariantDerivative (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates 5) (z : FourSpace) (d a j k : Fin 4) :
    (fun p q => covariantDerivative g c T z ![d, a, q, j, k, p]) =
      matrixPartial (fiveTensorMatrix T a j k) d z -
        (connectionMatrix g c d z)ᵀ * fiveTensorMatrix T a j k z -
        fiveTensorMatrix T a j k z * connectionMatrix g c d z -
        (∑ b, christoffel g c z b d a • fiveTensorMatrix T b j k z) -
        (∑ b, christoffel g c z b d j • fiveTensorMatrix T a b k z) -
        (∑ b, christoffel g c z b d k • fiveTensorMatrix T a j b z) := by
  have hright (p q : Fin 4) :
      (fiveTensorMatrix T a j k z * connectionMatrix g c d z) p q =
        ∑ b, christoffel g c z b d q * T z ![a, b, j, k, p] := by
    simp only [Matrix.mul_apply, fiveTensorMatrix, connectionMatrix]
    apply Finset.sum_congr rfl
    intro b _
    ring
  ext p q
  rw [covariantDerivative_five_apply]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, matrixPartial,
    fiveTensorMatrix, connectionMatrix] at hright ⊢
  rw [hright]
  ring

def curvatureDerivativeMatrix (g : SmoothMetric M) (c : M) (a j k : Fin 4) :
    FourSpace → Mat4 :=
  fiveTensorMatrix (covariantDerivative g c (curvatureCoordinates g c)) a j k

theorem curvatureDerivativeMatrix_trace_zero (g : SmoothMetric M) (hRic : RicciThree g)
    (c : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (a j k : Fin 4) :
    ((metricInChart g c z)⁻¹ * curvatureDerivativeMatrix g c a j k z).trace = 0 := by
  change (∑ r, ∑ s, (metricInChart g c z)⁻¹ r s *
    covariantDerivative g c (curvatureCoordinates g c) z ![a, r, j, k, s]) = 0
  rw [lowered_curvature_derivative_contraction g c z hz
    (metricInChart_posDef g c z hz).det_pos.ne', actual_ricci_parallel g hRic c z hz]
  rfl

theorem curvatureHessian_contraction_zero (g : SmoothMetric M) (hRic : RicciThree g)
    (c : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (d a j k : Fin 4) :
    (∑ r, ∑ s, (metricInChart g c z)⁻¹ r s *
      covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c)) z
        ![d, a, r, j, k, s]) = 0 := by
  let T := covariantDerivative g c (curvatureCoordinates g c)
  let S := curvatureDerivativeMatrix g c
  have hzero (b l m : Fin 4) :
      ((metricInChart g c z)⁻¹ * S b l m z).trace = 0 :=
    curvatureDerivativeMatrix_trace_zero g hRic c z hz b l m
  have he : (fun w => ((metricInChart g c w)⁻¹ * S a j k w).trace) =ᶠ[𝓝 z]
      (fun _ => 0) := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
    exact curvatureDerivativeMatrix_trace_zero g hRic c w hw a j k
  have hd : partialDeriv (fun w => ((metricInChart g c w)⁻¹ * S a j k w).trace) d z = 0 := by
    simp only [partialDeriv, he.fderiv_eq, fderiv_const_apply, _root_.zero_apply]
  have hdet := (metricInChart_posDef g c z hz).det_pos.ne'
  have hS (p q : Fin 4) : DifferentiableAt ℝ (fun w => S a j k w p q) z :=
    (covariantDerivative_contDiffAt g c z hz hdet (curvatureCoordinates g c)
      (curvatureCoordinates_contDiffAt g c z hz hdet) ![a, q, j, k, p]).differentiableAt
        (by simp)
  rw [partialDeriv_metric_contraction g c (S a j k) z hz hS d] at hd
  change ((metricInChart g c z)⁻¹ *
    (show Mat4 from fun p q => covariantDerivative g c T z ![d, a, q, j, k, p])).trace = 0
  rw [fiveTensorMatrix_covariantDerivative g c T z d a j k]
  change ((metricInChart g c z)⁻¹ *
    (matrixPartial (S a j k) d z - (connectionMatrix g c d z)ᵀ * S a j k z -
      S a j k z * connectionMatrix g c d z -
      (∑ b, christoffel g c z b d a • S b j k z) -
      (∑ b, christoffel g c z b d j • S a b k z) -
      (∑ b, christoffel g c z b d k • S a j b z))).trace = 0
  simp only [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_sum, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, hzero, smul_zero, Finset.sum_const_zero, sub_zero]
  simpa only [Matrix.mul_sub, Matrix.trace_sub] using hd

end
end PositiveEinsteinFour.Geometry
end


section

/-! The raw orthogonal-frame invariance used from Brin--Karcher, §1:
the uniform frame measure is invariant under a fixed reflection, and
parallel transport intertwines reflection with reversal of the first
flow direction. This gives integral and tensor identities for reflected frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem regularizedRadialDerivative_smul (ε : ℝ) (A Z : Mat) (c : ℝ) :
    regularizedRadialDerivative ε A (c • Z) = c * regularizedRadialDerivative ε A Z := by
  simp only [regularizedRadialDerivative, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  ring

theorem reflectedGradient_radial_sum (ε : ℝ) (A : Mat) (Z : Angular.Gradient) :
    (∑ i, regularizedRadialDerivative ε A (reflectedGradient Z i) ^ 2) =
      ∑ i, regularizedRadialDerivative ε A (Z i) ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  rw [reflectedGradient, regularizedRadialDerivative_smul, mul_pow, orientationSign_sq, one_mul]

theorem scalarNormExpression_reflected (ε : ℝ) (A : Mat) (Z : Angular.Gradient) :
    scalarNormExpression ε A (reflectedGradient Z) = scalarNormExpression ε A Z := by
  unfold scalarNormExpression
  rw [reflectedGradient_energy, reflectedGradient_radial_sum]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

/-- The two elementary reflection compatibilities of uniform parallel
frame flow. These are classical input, not a curvature estimate. -/
structure FrameReflectionData (d : MetricGreenData g μ) where
  preserves : MeasurePreserving (frameReflection : FrameBundle g → FrameBundle g) μ μ
  parallel : ∀ i t e, frameReflection ((d.flow i).map t e) =
    (d.flow i).map (orientationSign i * t) (frameReflection e)

namespace FrameReflectionData

variable {d : MetricGreenData g μ} (r : FrameReflectionData d)

include r in
theorem integral_reflection (F : FrameBundle g → ℝ) :
    (∫ e, F (frameReflection e) ∂μ) = ∫ e, F e ∂μ := by
  have h : MeasurePreserving (frameReflectionEquiv g) μ μ := r.preserves
  exact h.integral_comp' F

def reflectTest (_r : FrameReflectionData d) (k : C(FrameBundle g, ℝ)) : C(FrameBundle g, ℝ) :=
  k.comp ⟨frameReflection, continuous_frameReflection g⟩

def reflectTestDerivative (_r : FrameReflectionData d)
    (dk : Fin 4 → C(FrameBundle g, ℝ)) (i : Fin 4) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => orientationSign i * dk i (frameReflection e),
    continuous_const.mul ((dk i).continuous.comp (continuous_frameReflection g))⟩

theorem reflectTest_derivative (k : C(FrameBundle g, ℝ))
    (dk : Fin 4 → C(FrameBundle g, ℝ))
    (hk : ∀ i t e, HasDerivAt (fun s => k ((d.flow i).map s e))
      (dk i ((d.flow i).map t e)) t) :
    ∀ i t e, HasDerivAt (fun s => r.reflectTest k ((d.flow i).map s e))
      (r.reflectTestDerivative dk i ((d.flow i).map t e)) t := by
  intro i t e
  have h := (hk i (orientationSign i * t) (frameReflection e)).comp t
    ((hasDerivAt_id t).const_mul (orientationSign i))
  convert! h using 1
  · funext s
    exact congrArg k (r.parallel i s e)
  · change orientationSign i * dk i (frameReflection ((d.flow i).map t e)) = _
    rw [r.parallel]
    ring

include r in
theorem opposite_testedNormEquation [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (k : C(FrameBundle g, ℝ)) (dk : Fin 4 → C(FrameBundle g, ℝ))
    (hk : ∀ i t e, HasDerivAt (fun s => k ((d.flow i).map s e))
      (dk i ((d.flow i).map t e)) t) :
    (∫ e, k e * scalarNormExpression 0 (minusWeyl g e.base e.frame)
        (minusWeylGradient g e.base e.frame) +
      ∑ i, dk i e * regularizedRadialDerivative 0 (minusWeyl g e.base e.frame)
        (minusWeylGradient g e.base e.frame i) ∂μ) = 0 := by
  let F : FrameBundle g → ℝ := fun e => r.reflectTest k e *
      scalarNormExpression 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) +
    ∑ i, r.reflectTestDerivative dk i e * regularizedRadialDerivative 0
      (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame i)
  have hF : (∫ e, F e ∂μ) = 0 :=
    d.testedNormEquation d.refinedKato (r.reflectTest k) (r.reflectTestDerivative dk)
      (r.reflectTest_derivative k dk hk)
  rw [← r.integral_reflection F] at hF
  convert! hF using 1
  apply integral_congr_ae
  filter_upwards [] with e
  have hZ : plusWeylGradient g (frameReflection e).base (frameReflection e).frame =
      reflectedGradient (minusWeylGradient g e.base e.frame) := by
    funext i
    exact plusWeylGradient_reflect g e.base e.frame i
  change k e * _ + _ = F (frameReflection e)
  dsimp only [F, reflectTest, reflectTestDerivative, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk]
  rw [frameReflection_involutive g e]
  change _ = k e * scalarNormExpression 0 (plusWeyl g e.base e.frame.reflect)
    (plusWeylGradient g e.base e.frame.reflect) + _
  dsimp only [frameReflection] at hZ ⊢
  rw [plusWeyl_reflect, hZ, scalarNormExpression_reflected]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [reflectedGradient, regularizedRadialDerivative_smul]
  symm
  calc
    _ = orientationSign i ^ 2 *
        (dk i e * regularizedRadialDerivative 0 (minusWeyl g e.base e.frame)
          (minusWeylGradient g e.base e.frame i)) := by ring
    _ = _ := by rw [orientationSign_sq, one_mul]

end FrameReflectionData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The quaternion basis converts the actual four covector actions into
the matrix commutator used by the Weyl block equations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped BigOperators

noncomputable section

theorem quaternion_generator_commutator (s r : Fin 3) :
    quaternionMatrix s * quaternionMatrix r - quaternionMatrix r * quaternionMatrix s =
      ∑ k, rotation s k r • quaternionMatrix k := by
  have h := QuaternionFrame.imaginaryLeft_commutator s (Pi.single r (1 : ℝ))
  simpa [QuaternionFrame.imaginaryCombination, Matrix.mulVec, dotProduct, Pi.single_apply] using h

/-- The negative of the actual covector action is the spin-two matrix action. -/
theorem blockCoordinates_quaternion_action (T : CovariantCoordinates 4) (s : Fin 3) :
    blockCoordinates (tensorSlotAction (quaternionMatrix s) T) quaternionMatrix =
      -matrixAction s (blockCoordinates T quaternionMatrix) := by
  ext a b
  rw [blockCoordinates_pairing,
    twoFormPairing_skew_slotAction (quaternionMatrix s) (Angular.quaternionMatrix_transpose s),
    quaternion_generator_commutator s a, quaternion_generator_commutator s b]
  simp only [Fin.sum_univ_three, twoFormPairing_add_left, twoFormPairing_add_right,
    twoFormPairing_smul_left, twoFormPairing_smul_right, Matrix.neg_apply,
    matrixAction]
  simp only [← blockCoordinates_pairing]
  rw [rotation_skew s 0 a, rotation_skew s 1 a, rotation_skew s 2 a]
  ring

/-- The commuting quaternion triple has no action on the positive Weyl block. -/
theorem blockCoordinates_opposite_action (T : CovariantCoordinates 4) (s : Fin 3) :
    blockCoordinates (tensorSlotAction (Angular.oppositeMatrix s) T) quaternionMatrix = 0 := by
  ext a b
  rw [blockCoordinates_pairing,
    twoFormPairing_skew_slotAction (Angular.oppositeMatrix s)
      (QuaternionFrame.oppositeMatrix_transpose s),
    Angular.oppositeMatrix_commute s a, Angular.oppositeMatrix_commute s b,
    sub_self, sub_self, twoFormPairing_zero_left, twoFormPairing_zero_right, add_zero]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrability of the scalar weak equation and of its radial terms.
The estimates use the actual metric Kato bound, including the zero set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators Topology Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

namespace MetricGreenData

theorem scalarNorm_integrable (d : MetricGreenData g μ) :
    Integrable (fun e => scalarNormExpression 0 (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame)) μ := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  let H : FrameBundle g → ℝ := fun e =>
    weylGradientEnergy (plusWeylGradient g e.base e.frame) /
      normalizedBlockNorm (plusWeyl g e.base e.frame) + d.laplacianNormField e
  have hH : Integrable H μ := d.energyQuotient_integrable.add
    (d.laplacianNormField.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hF (n) : Integrable (fun e => d.scalarNormField (ε n) (hε n) e) μ :=
    (d.scalarNormField (ε n) (hε n)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply integrable_of_ae_limit_norm_bound μ
    (fun n e => d.scalarNormField (ε n) (hε n) e) _ (∫ e, H e ∂μ) hF
  · filter_upwards [d.gradient_zero_ae_on_zero] with e he
    exact (tendsto_scalarNormExpression _ _ (fun hv =>
      funext (he ((normalizedBlockNorm_eq_zero_iff _).mp hv)))).comp
        tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n
    apply integral_mono_ae (hF n).norm hH
    filter_upwards [d.gradient_zero_ae_on_zero] with e he
    rw [Real.norm_eq_abs]
    apply abs_scalarNormExpression_le (ε n) (hε n) _ _ (d.weyl.symmetric e)
    · intro hv
      exact funext (he ((normalizedBlockNorm_eq_zero_iff _).mp hv))
    · have hk := d.refinedKato e
      nlinarith [sq_nonneg ‖blockRadialGradient (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame)‖]

theorem radial_integrable (d : MetricGreenData g μ) (i : Fin 4) :
    Integrable (fun e => regularizedRadialDerivative 0 (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i)) μ := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  let H : C(FrameBundle g, ℝ) := ⟨fun e => normalizedBlockNorm
    (plusWeylGradient g e.base e.frame i),
    continuous_normalizedBlockNorm.comp (d.continuousGradient i)⟩
  have hF (n) : Integrable (fun e => d.regularizedRadialField (ε n) (hε n) i e) μ :=
    (d.regularizedRadialField (ε n) (hε n) i).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply integrable_of_ae_limit_norm_bound μ
    (fun n e => d.regularizedRadialField (ε n) (hε n) i e) _ (∫ e, H e ∂μ) hF
  · filter_upwards [] with e
    simpa only [ε, regularizedRadialField, ContinuousMap.coe_mk, Function.comp_def,
      regularizedRadialDerivative, regularizedBlockNorm_zero] using
      (tendsto_regularizedRadialDerivative (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i)).comp tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n
    apply integral_mono_ae (hF n).norm
      (H.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    filter_upwards [] with e
    rw [Real.norm_eq_abs]
    exact abs_regularizedRadialDerivative_le (ε n) (hε n) _ _ ((d.gradientConstraints e).1 i)

end MetricGreenData

omit [IsFiniteMeasure μ] in
theorem integrable_continuous_weight {f : FrameBundle g → ℝ} (hf : Integrable f μ)
    (k : C(FrameBundle g, ℝ)) : Integrable (fun e => k e * f e) μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn k.continuous.continuousOn
  exact hf.bdd_mul k.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => hC e (Set.mem_univ e)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identify the scalar terms in the metric norm and trace-energy
equations in a single pointwise spectral frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi QuaternionFrame Matrix
open scoped BigOperators

noncomputable section

theorem shape_fourth_moment (S : Shape) : (∑ i, S.s i ^ 4) = 18 := by
  have ht := S.trace
  simp only [Fin.sum_univ_three] at ht
  have hz : S.s 2 = -S.s 0 - S.s 1 := by linarith
  calc
    _ = (∑ i, S.s i ^ 2) ^ 2 / 2 := by
      simp only [Fin.sum_univ_three]
      rw [hz]
      ring
    _ = 18 := by rw [S.square]; norm_num

theorem weylLaplacian_shape (S : Shape) (v : ℝ) :
    weylLaplacian (Matrix.diagonal (fun i => v * S.s i)) =
      Matrix.diagonal (fun i => 6 * (v * S.s i - v ^ 2 * (S.s i ^ 2 - 2))) := by
  unfold weylLaplacian
  rw [shape_traceFreeSquare]
  ext a b
  by_cases hab : a = b
  · subst b
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal_apply_eq,
      smul_eq_mul, Shape.squareWeight]
  · simp [Matrix.smul_apply, Matrix.diagonal_apply_ne _ hab]

theorem matrixNormSq_diagonal (t : Fin 3 → ℝ) :
    matrixNormSq (Matrix.diagonal t) = ∑ i, t i ^ 2 := by
  simp [matrixNormSq, Matrix.diagonal_apply]

theorem traceEnergy_shape (S : Shape) (v : ℝ) :
    traceEnergy (Matrix.diagonal (fun i => v * S.s i)) =
      30 * v ^ 2 * (1 - 2 * S.sigma * v + v ^ 2) := by
  have h3 : (∑ i, S.s i ^ 3) = 6 * S.sigma := by
    unfold Shape.sigma
    ring
  have hp (i : Fin 3) : (6 * (v * S.s i - v ^ 2 * (S.s i ^ 2 - 2))) ^ 2 =
      (36 * v ^ 2) * S.s i ^ 2 - (72 * v ^ 3) * S.s i ^ 3 +
      (144 * v ^ 3) * S.s i + (36 * v ^ 4) * S.s i ^ 4 -
      (144 * v ^ 4) * S.s i ^ 2 + 144 * v ^ 4 := by ring
  unfold traceEnergy
  rw [weylLaplacian_shape, matrixNormSq_diagonal]
  simp only [hp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    S.square, S.trace, h3, shape_fourth_moment, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

theorem weylLaplacian_conjugate (R A : Mat) (hR : Rᵀ * R = 1) :
    weylLaplacian (conjugateMatrix R A) = conjugateMatrix R (weylLaplacian A) := by
  simp only [weylLaplacian, conjugateMatrix_traceFreeSquare R hR,
    conjugateMatrix_smul, conjugateMatrix_sub]

theorem traceEnergy_conjugate (R A : Mat) (hR : Rᵀ * R = 1) :
    traceEnergy (conjugateMatrix R A) = traceEnergy A := by
  unfold traceEnergy
  rw [weylLaplacian_conjugate R A hR]
  have hp := conjugateMatrix_pairing R (mul_eq_one_comm.mp hR) (weylLaplacian A) (weylLaplacian A)
  have hn : matrixNormSq (conjugateMatrix R (weylLaplacian A)) = matrixNormSq (weylLaplacian A) := by
    simpa only [matrixNormSq, matrixPairing, pow_two] using hp
  rw [hn]

theorem traceEnergy_spectral (A R : Mat) (hR : Rᵀ * R = 1) (S : Shape) (v : ℝ)
    (hdiag : conjugateMatrix R A = Matrix.diagonal (fun i => v * S.s i)) :
    traceEnergy A = 30 * v ^ 2 * (1 - 2 * S.sigma * v + v ^ 2) := by
  rw [← traceEnergy_conjugate R A hR, hdiag, traceEnergy_shape]

theorem trace_mul_weylLaplacian_shape (S : Shape) (v : ℝ) :
    Matrix.trace (Matrix.diagonal (fun i => v * S.s i) *
      weylLaplacian (Matrix.diagonal (fun i => v * S.s i))) =
      36 * v ^ 2 * (1 - S.sigma * v) := by
  rw [weylLaplacian_shape, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  have hp (i : Fin 3) : v * S.s i * (6 * (v * S.s i - v ^ 2 * (S.s i ^ 2 - 2))) =
      (6 * v ^ 2) * S.s i ^ 2 - (6 * v ^ 3) * S.s i ^ 3 + (12 * v ^ 3) * S.s i := by ring
  have h3 : (∑ i, S.s i ^ 3) = 6 * S.sigma := by unfold Shape.sigma; ring
  simp only [hp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    S.square, S.trace, h3]
  ring

theorem radialLaplacian_spectral (A R : Mat) (hR : Rᵀ * R = 1) (S : Shape)
    (hv : 0 < normalizedBlockNorm A)
    (hdiag : conjugateMatrix R A = Matrix.diagonal (fun i => normalizedBlockNorm A * S.s i)) :
    regularizedRadialDerivative 0 A (weylLaplacian A) =
      6 * normalizedBlockNorm A * (1 - S.sigma * normalizedBlockNorm A) := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  have ht : Matrix.trace (A * weylLaplacian A) =
      36 * normalizedBlockNorm A ^ 2 * (1 - S.sigma * normalizedBlockNorm A) := by
    calc
      _ = Matrix.trace (conjugateMatrix R (A * weylLaplacian A)) :=
        (conjugateMatrix_trace R hR' _).symm
      _ = Matrix.trace (conjugateMatrix R A * weylLaplacian (conjugateMatrix R A)) := by
        rw [weylLaplacian_conjugate R A hR, conjugateMatrix_mul R hR']
      _ = _ := by rw [hdiag, trace_mul_weylLaplacian_shape]
  unfold regularizedRadialDerivative
  rw [regularizedBlockNorm_zero, ht]
  field_simp [ne_of_gt hv]
  ring

theorem scalarNormExpression_spectral (A R : Mat) (hR : Rᵀ * R = 1)
    (S : Shape) (Z : Angular.Gradient) (hv : 0 < normalizedBlockNorm A)
    (hdiag : conjugateMatrix R A = Matrix.diagonal (fun i => normalizedBlockNorm A * S.s i)) :
    scalarNormExpression 0 A Z =
      (weylGradientEnergy Z - ‖blockRadialGradient A Z‖ ^ 2) / normalizedBlockNorm A +
        6 * normalizedBlockNorm A * (1 - S.sigma * normalizedBlockNorm A) := by
  unfold scalarNormExpression
  rw [regularizedBlockNorm_zero, radialLaplacian_spectral A R hR S hv hdiag,
    EuclideanSpace.real_norm_sq_eq]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normalized Einstein Weyl gradients satisfy the algebraic
and differential constraints used by the energy argument. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem actual_weylGradient_constraints (e : OrthonormalFrame g c) (hRic : RicciThree g) :
    (∀ i, TraceHessian.symmetric (plusWeylGradient g c e i) ∧
      TraceHessian.traceFree (plusWeylGradient g c e i)) ∧
    (∀ i, TraceHessian.symmetric (minusWeylGradient g c e i) ∧
      TraceHessian.traceFree (minusWeylGradient g c e i)) :=
  weylGradient_constraints_of_ricci_parallel e (actual_ricci_parallel_at_center g hRic c)

theorem actual_plusWeylGradient_symmetric (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (i : Fin 4) :
    (plusWeylGradient g c e i)ᵀ = plusWeylGradient g c e i := by
  ext a b
  exact ((actual_weylGradient_constraints e hRic).1 i).1 b a

theorem actual_plusWeylGradient_trace (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (i : Fin 4) :
    (plusWeylGradient g c e i).trace = 0 :=
  ((actual_weylGradient_constraints e hRic).1 i).2

theorem actual_plusWeylGradient_bianchi (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (r : Fin 3) (i : Fin 4) :
    gradientDivergence (plusWeylGradient g c e) r i = 0 :=
  plusWeylGradient_bianchi_of_ricci_parallel e (actual_ricci_parallel_at_center g hRic c) r i

theorem actual_minusWeylGradient_bianchi (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (r : Fin 3) (i : Fin 4) :
    (∑ s, ∑ j, Angular.oppositeMatrix s i j * minusWeylGradient g c e j s r) = 0 :=
  minusWeylGradient_bianchi_of_ricci_parallel e (actual_ricci_parallel_at_center g hRic c) r i

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual curvature endomorphism acts on the quaternionic Weyl block.
This is a finite contraction of the full tensor, before any diagonalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped BigOperators

noncomputable section

private theorem twoFormPairing_smul_tensor (T : CovariantCoordinates 4)
    (P Q : Mat4) (r : ℝ) :
    twoFormPairing (r • T) P Q = r * twoFormPairing T P Q := by
  simp only [twoFormPairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

/-- The fixed two-form contraction is linear in the four-tensor. -/
def blockCoordinatesLinear (Q : Fin 3 → Mat4) : CovariantCoordinates 4 →ₗ[ℝ] Mat3 where
  toFun T := blockCoordinates T Q
  map_add' S T := by
    ext a b
    simpa only [blockCoordinates_pairing, Matrix.add_apply] using
      twoFormPairing_add_tensor S T (Q a) (Q b)
  map_smul' r T := by
    ext a b
    simpa only [blockCoordinates_pairing, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply] using
      twoFormPairing_smul_tensor T (Q a) (Q b) r

/-- Slots are arranged as the endomorphism `R(e_i,e_j)` on vectors. -/
def curvatureEndomorphism (R : Angular.CurvatureArray) (i j : Fin 4) : Mat4 :=
  fun a b => R i j b a

theorem curvatureEndomorphism_blockTensor (A : Mat3) (Q : Fin 3 → Mat4)
    (i j : Fin 4) :
    curvatureEndomorphism (Angular.blockTensor A Q) i j =
      (1 / 2 : ℝ) • ∑ r, ∑ s, (A r s * Q r i j) • Q s := by
  ext a b
  simp only [curvatureEndomorphism, Angular.blockTensor, Angular.twoFormProduct,
    Pi.smul_apply, Finset.sum_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem tensorSlotAction_smul_matrix {n : ℕ} (r : ℝ) (A : Mat4)
    (T : CovariantCoordinates n) :
    tensorSlotAction (r • A) T = r • tensorSlotAction A T := by
  funext a
  simp only [tensorSlotAction, covariantSlotAction, Matrix.smul_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem tensorSlotAction_sum_matrix {n : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → Mat4) (T : CovariantCoordinates n) :
    tensorSlotAction (∑ r, A r) T = ∑ r, tensorSlotAction (A r) T := by
  funext a
  simp only [tensorSlotAction, covariantSlotAction, Finset.sum_apply, Matrix.sum_apply,
    Finset.sum_mul]
  calc
    _ = ∑ s, ∑ r, ∑ b, A r b (a s) * T (Function.update a s b) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

theorem blockCoordinates_blockTensor_plus_action (A : Mat3)
    (T : CovariantCoordinates 4) (i j : Fin 4) :
    blockCoordinates (tensorSlotAction
      (curvatureEndomorphism (Angular.blockTensor A quaternionMatrix) i j) T)
      quaternionMatrix =
      -(1 / 2 : ℝ) • ∑ r, ∑ s,
        (A r s * quaternionMatrix r i j) • matrixAction s (blockCoordinates T quaternionMatrix) := by
  rw [curvatureEndomorphism_blockTensor]
  simp only [tensorSlotAction_smul_matrix, tensorSlotAction_sum_matrix]
  change blockCoordinatesLinear quaternionMatrix _ = _
  simp only [map_smul, map_sum]
  change (1 / 2 : ℝ) • (∑ r, ∑ s, (A r s * quaternionMatrix r i j) •
    blockCoordinates (tensorSlotAction (quaternionMatrix s) T) quaternionMatrix) = _
  simp_rw [blockCoordinates_quaternion_action]
  simp only [smul_neg, Finset.sum_neg_distrib, neg_smul]

theorem blockCoordinates_blockTensor_opposite_action (A : Mat3)
    (T : CovariantCoordinates 4) (i j : Fin 4) :
    blockCoordinates (tensorSlotAction
      (curvatureEndomorphism (Angular.blockTensor A Angular.oppositeMatrix) i j) T)
      quaternionMatrix = 0 := by
  rw [curvatureEndomorphism_blockTensor]
  simp only [tensorSlotAction_smul_matrix, tensorSlotAction_sum_matrix]
  change blockCoordinatesLinear quaternionMatrix _ = _
  simp only [map_smul, map_sum]
  change (1 / 2 : ℝ) • (∑ r, ∑ s, (A r s * Angular.oppositeMatrix r i j) •
    blockCoordinates (tensorSlotAction (Angular.oppositeMatrix s) T) quaternionMatrix) = _
  simp only [blockCoordinates_opposite_action, smul_zero, Finset.sum_const_zero]

theorem blockCoordinates_einstein_curvature_action (A U : Mat3)
    (T : CovariantCoordinates 4) (i j : Fin 4) :
    blockCoordinates (-tensorSlotAction
      (curvatureEndomorphism (Angular.einsteinCurvatureTensor A U) i j) T)
      quaternionMatrix = bundleCurvatureAction A i j (blockCoordinates T quaternionMatrix) := by
  have hc : curvatureEndomorphism (Angular.einsteinCurvatureTensor A U) i j =
      curvatureEndomorphism (Angular.blockTensor (1 + A) quaternionMatrix) i j +
        curvatureEndomorphism (Angular.blockTensor (1 + U) Angular.oppositeMatrix) i j := rfl
  rw [hc, tensorSlotAction_add_matrix]
  change blockCoordinatesLinear quaternionMatrix (-(_ + _)) = _
  rw [map_neg, map_add]
  change -(blockCoordinates (tensorSlotAction
    (curvatureEndomorphism (Angular.blockTensor (1 + A) quaternionMatrix) i j) T)
      quaternionMatrix + blockCoordinates (tensorSlotAction
    (curvatureEndomorphism (Angular.blockTensor (1 + U) Angular.oppositeMatrix) i j) T)
      quaternionMatrix) = _
  rw [blockCoordinates_blockTensor_plus_action, blockCoordinates_blockTensor_opposite_action,
    add_zero, neg_smul, neg_neg]
  ext a b
  simp only [bundleCurvatureAction, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, Matrix.add_apply, Matrix.one_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  simp only [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transport the zero Ricci contraction of the actual curvature Hessian
to any orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem frame_curvature_hessian_trace_zero (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (d a j k : Fin 4) :
    (∑ r, frameTensor e.matrix
      (covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c))
        (chartAt FourSpace c c)) ![d, a, r, j, k, r]) = 0 := by
  let H := covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c))
    (chartAt FourSpace c c)
  have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  have htrace (u v b f : Fin 4) :
      (∑ r, ∑ s, (chartMetric g c)⁻¹ r s * H ![u, v, r, b, f, s]) = 0 :=
    curvatureHessian_contraction_zero g hRic c (chartAt FourSpace c c) hz u v b f
  have hslice (u v : Fin 4) :
      (∑ r, frameTensor e.matrix (fun b => H (Fin.cons u (Fin.cons v b)))
        ![r, j, k, r]) = 0 := by
    rw [frameTensor_trace_inverse]
    have ht (b f : Fin 4) :
        (∑ r, ∑ s, (chartMetric g c)⁻¹ r s *
          H (Fin.cons u (Fin.cons v ![r, b, f, s]))) = 0 := htrace u v b f
    simp only [ht, mul_zero, Finset.sum_const_zero]
  change (∑ r, frameTensor e.matrix H (Fin.cons d (Fin.cons a ![r, j, k, r]))) = 0
  simp only [frameTensor_cons (n := 5), frameTensor_cons (n := 4), Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro u _
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hslice, mul_zero, Finset.sum_const_zero]

theorem frame_normalizedWeyl_hessian_trace_zero (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (d a j k : Fin 4) :
    (∑ r, frameTensor e.matrix
      (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))
        (chartAt FourSpace c c)) ![d, a, r, j, k, r]) = 0 := by
  have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  rw [covariantHessian_normalizedWeyl g c (chartAt FourSpace c c) hz]
  exact frame_curvature_hessian_trace_zero e hRic d a j k

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transport the weak energy equation through the actual reflected
frame. The reflected energy is the energy of the opposite Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace MetricGreenData

def oppositeEnergyField (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  d.gradientEnergyField.comp ⟨frameReflection, continuous_frameReflection g⟩

def oppositeEnergyDerivativeField (d : MetricGreenData g μ) (i : Fin 4) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => orientationSign i * d.energyDerivativeField i (frameReflection e),
    continuous_const.mul ((d.energyDerivativeField i).continuous.comp (continuous_frameReflection g))⟩

def oppositeEnergyLaplacianField (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  d.energyLaplacianField.comp ⟨frameReflection, continuous_frameReflection g⟩

def totalEnergyField (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  d.gradientEnergyField + d.oppositeEnergyField

def totalEnergyDerivativeField (d : MetricGreenData g μ) (i : Fin 4) : C(FrameBundle g, ℝ) :=
  d.energyDerivativeField i + d.oppositeEnergyDerivativeField i

theorem oppositeEnergyField_apply (d : MetricGreenData g μ) (e : FrameBundle g) :
    d.oppositeEnergyField e = weylGradientEnergy (minusWeylGradient g e.base e.frame) := by
  have hz : plusWeylGradient g (frameReflection e).base (frameReflection e).frame =
      reflectedGradient (minusWeylGradient g e.base e.frame) := by
    funext i
    exact plusWeylGradient_reflect g e.base e.frame i
  change weylGradientEnergy (plusWeylGradient g (frameReflection e).base
    (frameReflection e).frame) = _
  rw [hz, reflectedGradient_energy]

end MetricGreenData

namespace FrameReflectionData

variable {d : MetricGreenData g μ} (r : FrameReflectionData d)

include r

theorem oppositeEnergy_derivative (i : Fin 4) (t : ℝ) (e : FrameBundle g) :
    HasDerivAt (fun s => d.oppositeEnergyField ((d.flow i).map s e))
      (d.oppositeEnergyDerivativeField i ((d.flow i).map t e)) t :=
  r.reflectTest_derivative d.gradientEnergyField d.energyDerivativeField d.energyDerivative i t e

theorem totalEnergy_derivative (i : Fin 4) (t : ℝ) (e : FrameBundle g) :
    HasDerivAt (fun s => d.totalEnergyField ((d.flow i).map s e))
      (d.totalEnergyDerivativeField i ((d.flow i).map t e)) t :=
  (d.energyDerivative i t e).add (r.oppositeEnergy_derivative i t e)

theorem opposite_testedEnergyEquation [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (k : C(FrameBundle g, ℝ)) (dk : Fin 4 → C(FrameBundle g, ℝ))
    (hk : ∀ i t e, HasDerivAt (fun s => k ((d.flow i).map s e))
      (dk i ((d.flow i).map t e)) t) :
    (∫ e, k e * d.oppositeEnergyLaplacianField e +
      ∑ i, dk i e * d.oppositeEnergyDerivativeField i e ∂μ) = 0 := by
  let F : FrameBundle g → ℝ := fun e => r.reflectTest k e * d.energyLaplacianField e +
    ∑ i, r.reflectTestDerivative dk i e * d.energyDerivativeField i e
  have hF : (∫ e, F e ∂μ) = 0 :=
    d.testedEnergyEquation (r.reflectTest k) (r.reflectTestDerivative dk)
      (r.reflectTest_derivative k dk hk)
  rw [← r.integral_reflection F] at hF
  convert! hF using 1
  apply integral_congr_ae
  filter_upwards [] with e
  change k e * d.energyLaplacianField (frameReflection e) +
    (∑ i, dk i e * (orientationSign i * d.energyDerivativeField i (frameReflection e))) =
      r.reflectTest k (frameReflection e) * d.energyLaplacianField (frameReflection e) +
        ∑ i, r.reflectTestDerivative dk i (frameReflection e) *
          d.energyDerivativeField i (frameReflection e)
  simp only [reflectTest, reflectTestDerivative, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [frameReflection_involutive g e]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

end FrameReflectionData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The square-root norm energy bound from the actual weak Weyl equation.
The spectral estimate is pointwise; it requires no measurable eigenframe,
and every quotient retains its totalized value at a zero Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi QuaternionFrame MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem scalarNormExpression_zero (A : Mat) (Z : Fin 4 → Mat) :
    scalarNormExpression 0 A Z =
      (weylGradientEnergy Z - ‖blockRadialGradient A Z‖ ^ 2) / normalizedBlockNorm A +
        regularizedRadialDerivative 0 A (weylLaplacian A) := by
  simp only [scalarNormExpression, regularizedBlockNorm_zero,
    EuclideanSpace.real_norm_sq_eq]
  rfl

theorem radialLaplacian_lower (A : Mat) (hA : symmetric A) (ht : traceFree A) :
    6 * normalizedBlockNorm A - 6 * normalizedBlockNorm A ^ 2 ≤
      regularizedRadialDerivative 0 A (weylLaplacian A) := by
  by_cases hv : normalizedBlockNorm A = 0
  · simp [regularizedRadialDerivative, regularizedBlockNorm_zero, hv]
  · have hp : 0 < normalizedBlockNorm A :=
      lt_of_le_of_ne (normalizedBlockNorm_nonneg A) (Ne.symm hv)
    obtain ⟨R, hR, ⟨P⟩, S, hdiag⟩ := exists_lifted_spectral_shape A hA ht hp
    have hσ : S.sigma ≤ 1 := by
      nlinarith only [S.sigma_rho_circle, sq_nonneg S.rho]
    rw [radialLaplacian_spectral A R hR S hp hdiag]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hσ)
      (sq_nonneg (normalizedBlockNorm A))]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

namespace MetricGreenData

/-- The singular radial energy is integrable by the proved refined Kato
inequality and the actual full-gradient quotient estimate. -/
theorem radialEnergyQuotient_integrable (d : MetricGreenData g μ) :
    Integrable (fun e =>
      ‖blockRadialGradient (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame)‖ ^ 2 /
          normalizedBlockNorm (plusWeyl g e.base e.frame)) μ := by
  have hm : AEStronglyMeasurable (fun e =>
      ‖blockRadialGradient (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame)‖ ^ 2 /
          normalizedBlockNorm (plusWeyl g e.base e.frame)) μ := by
    have hs := Finset.univ.aestronglyMeasurable_fun_sum
      (fun i _ => (d.radial_integrable i).aestronglyMeasurable.pow 2)
    have hq := (hs.aemeasurable.div
      (continuous_normalizedBlockNorm.comp d.continuousWeyl).aemeasurable).aestronglyMeasurable
    apply hq.congr
    filter_upwards [] with e
    change (∑ i, regularizedRadialDerivative 0 (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i) ^ 2) / _ = _
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  apply d.energyQuotient_integrable.mono' hm
  filter_upwards [] with e
  have hp := sq_nonneg ‖blockRadialGradient (plusWeyl g e.base e.frame)
    (plusWeylGradient g e.base e.frame)‖
  have hv := normalizedBlockNorm_nonneg (plusWeyl g e.base e.frame)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hp hv)]
  exact div_le_div_of_nonneg_right (by linarith only [d.refinedKato e, hp]) hv

/-- The square-root norm gap on the given frame measure. In particular no
reflection invariance of an oriented frame measure is assumed. -/
theorem sqrtNormEnergyGap (d : MetricGreenData g μ) :
    (4 / 9 : ℝ) * (∫ e,
      (‖blockRadialGradient (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame)‖ ^ 2 /
          normalizedBlockNorm (plusWeyl g e.base e.frame)) / 4 ∂μ) ≤
      (∫ e, normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 ∂μ) -
        ∫ e, normalizedBlockNorm (plusWeyl g e.base e.frame) ∂μ := by
  let v : FrameBundle g → ℝ := fun e => normalizedBlockNorm (plusWeyl g e.base e.frame)
  let p : FrameBundle g → ℝ := fun e =>
    ‖blockRadialGradient (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame)‖ ^ 2
  let E : FrameBundle g → ℝ := fun e => weylGradientEnergy (plusWeylGradient g e.base e.frame)
  have hvi : Integrable v μ :=
    (continuous_normalizedBlockNorm.comp d.continuousWeyl).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hv2i : Integrable (fun e => v e ^ 2) μ :=
    ((continuous_normalizedBlockNorm.comp d.continuousWeyl).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpi : Integrable (fun e => p e / v e) μ := d.radialEnergyQuotient_integrable
  have hqi : Integrable (fun e => (E e - p e) / v e) μ := by
    apply (d.energyQuotient_integrable.sub hpi).congr
    filter_upwards [] with e
    change E e / v e - p e / v e = (E e - p e) / v e
    ring
  have henergy : (2 / 3 : ℝ) * (∫ e, p e / v e ∂μ) ≤
      ∫ e, (E e - p e) / v e ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hpi.const_mul (2 / 3)) hqi
    filter_upwards [] with e
    calc
      (2 / 3 : ℝ) * (p e / v e) = ((2 / 3) * p e) / v e := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (by have hk := d.refinedKato e; change (5 / 3 : ℝ) * p e ≤ E e at hk; linarith)
        (normalizedBlockNorm_nonneg _)
  have hbound : (∫ e, (E e - p e) / v e + 6 * v e - 6 * v e ^ 2 ∂μ) ≤ 0 := by
    calc
      _ ≤ ∫ e, scalarNormExpression 0 (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame) ∂μ := by
        apply integral_mono_ae ((hqi.add (hvi.const_mul 6)).sub (hv2i.const_mul 6))
          d.scalarNorm_integrable
        filter_upwards [] with e
        rw [scalarNormExpression_zero]
        have h := radialLaplacian_lower (plusWeyl g e.base e.frame)
          (d.weyl.symmetric e) (d.weyl.traceFree e)
        simp only [Pi.sub_apply, Pi.add_apply]
        dsimp only [v, p, E]
        linarith only [h]
      _ = 0 := d.weakNormEquation
  have hsplit : (∫ e, (E e - p e) / v e + 6 * v e - 6 * v e ^ 2 ∂μ) =
      (∫ e, (E e - p e) / v e ∂μ) + 6 * (∫ e, v e ∂μ) -
        6 * (∫ e, v e ^ 2 ∂μ) := by
    have hs := integral_sub (hqi.add (hvi.const_mul 6)) (hv2i.const_mul 6)
    have ha := integral_add hqi (hvi.const_mul 6)
    simp only [Pi.add_apply] at hs ha
    rw [hs, ha, integral_const_mul, integral_const_mul]
  rw [hsplit] at hbound
  change (4 / 9 : ℝ) * (∫ e, (p e / v e) / 4 ∂μ) ≤
    (∫ e, v e ^ 2 ∂μ) - ∫ e, v e ∂μ
  rw [integral_div]
  linarith only [henergy, hbound]

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Norm-only forms of the cubic and true projection estimates. These are
unchanged by reflecting the opposite block's covector coordinates. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian HighestHessian PositiveEinsteinFour.Geometry CurvatureContraction
open Energy QuarticEnergy Quadratic Potential

noncomputable section

def projectionBracket (v y σ ρ e radial : ℝ) : ℝ :=
  projectionCoefficient v y σ ρ * ((5 / 3) * radial) +
    defectCoefficient v y * (e - (5 / 3) * radial)

theorem projectionBracket_nonneg {v y σ ρ e radial : ℝ}
    (hv : 0 ≤ v) (hv2 : v ≤ 2) (hy : 0 ≤ y) (hσ : σ ≤ 1)
    (hrad : 0 ≤ radial) (he : (5 / 3) * radial ≤ e) :
    0 ≤ projectionBracket v y σ ρ e radial := by
  have hσv := mul_le_mul_of_nonneg_right hσ hv
  have hρ : 0 ≤ ρ ^ 2 * v ^ 2 / 4 := by positivity
  have hg : 0 ≤ projectionCoefficient v y σ ρ := by
    unfold projectionCoefficient
    nlinarith only [hσv, hρ, hy, hv2]
  have hH : 0 ≤ defectCoefficient v y := by
    unfold defectCoefficient
    positivity
  unfold projectionBracket
  exact add_nonneg (mul_nonneg hg (by positivity)) (mul_nonneg hH (sub_nonneg.mpr he))

theorem norm_of_weight_square (M : ℝ) (hM : 0 ≤ M) (a p q : Vec)
    (ha : ‖a‖ ^ 2 = (9 / 16 : ℝ) * M ^ 2 * ‖p - q‖ ^ 2) :
    ‖a‖ = (3 / 4 : ℝ) * M * ‖p - q‖ := by
  have hr : 0 ≤ (3 / 4 : ℝ) * M * ‖p - q‖ := by positivity
  have hs : ((3 / 4 : ℝ) * M * ‖p - q‖) ^ 2 = ‖a‖ ^ 2 := by
    rw [ha]
    ring
  nlinarith only [hs, hr, norm_nonneg a]

/-- Only the norm of the weight covector matters, so this also applies
to the reflected opposite block. -/
theorem cubic_bound_of_weight_square (M : ℝ) (hM : 0 ≤ M) (a p q : Vec)
    (ha : ‖a‖ ^ 2 = (9 / 16 : ℝ) * M ^ 2 * ‖p - q‖ ^ 2)
    (Z : Angular.Gradient) (hs : ∀ i, symmetric (Z i))
    (ht : ∀ i, traceFree (Z i)) (hb : ∀ r i, gradientDivergence Z r i = 0) :
    -(5 / 36 : ℝ) * weightedCubicField a Z ≤
      (1 / 2 : ℝ) * Real.sqrt (3 / 5) * (‖p‖ + ‖q‖) * M *
        (weylGradientEnergy Z * Real.sqrt (weylGradientEnergy Z)) := by
  have he : 0 ≤ weylGradientEnergy Z := by
    unfold weylGradientEnergy matrixPairing
    apply div_nonneg _ (by norm_num)
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => mul_self_nonneg (Z i j k)
  have hn : ‖a‖ ≤ (3 / 4 : ℝ) * M * (‖p‖ + ‖q‖) := by
    rw [norm_of_weight_square M hM a p q ha]
    exact mul_le_mul_of_nonneg_left (norm_sub_le p q) (by positivity)
  have hc := weightedCubicField_sharp a Z hs ht hb
  have hu := hc.trans (mul_le_mul_of_nonneg_right hn
    (show 0 ≤ (24 / 5 : ℝ) * Real.sqrt (3 / 5) * weylGradientEnergy Z *
      Real.sqrt (weylGradientEnergy Z) by positivity))
  have hlo := (abs_le.mp hu).1
  nlinarith only [hlo]

/-- The true projected cost, with a norm-specified weight derivative. -/
theorem projection_bound_of_weight_square (A U : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (x y : ℝ) (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2)
    (M : ℝ) (hM : M ≠ 0) (a p q : Vec)
    (ha : ‖a‖ ^ 2 = (9 / 16 : ℝ) * M ^ 2 * ‖p - q‖ ^ 2)
    (Z : Angular.Gradient) (hs : ∀ i, symmetric (Z i))
    (ht : ∀ i, traceFree (Z i)) (hb : ∀ r i, gradientDivergence Z r i = 0)
    (S : Shape) (p' k l : Vec)
    (he : (parameters S p' k l).squaredNorm / 6 = weylGradientEnergy Z)
    (hp : ‖p'‖ ^ 2 = ‖p‖ ^ 2)
    (hB : weylMatrixEnergy A Z =
      curvatureContraction S (normalizedBlockNorm A) (parameters S p' k l)) :
    generalCurvaturePairing A U
        (highestProjection (weightTensor a (gradientTensor Z)))
        (highestProjection (weightTensor a (gradientTensor Z))) / (24 * M ^ 2) ≤
      (9 / 64 : ℝ) * ‖p - q‖ ^ 2 *
        projectionBracket (normalizedBlockNorm A) y S.sigma S.rho
          (weylGradientEnergy Z) (‖p‖ ^ 2) := by
  have hc := invariant_projection_parameter_cost A U hA hU htA htU x y hAx hUy hxy
    a Z hs ht hb S p' k l he hB
  rw [hp] at hc
  have hd := div_le_div_of_nonneg_right hc (show 0 ≤ 4 * M ^ 2 by positivity)
  rw [ha] at hd
  unfold projectionBracket
  convert hd using 1 <;> field_simp [hM] <;> ring

theorem projection_bound_norm_sum {v y σ ρ e : ℝ} (p q : Vec)
    (hv : 0 ≤ v) (hv2 : v ≤ 2) (hy : 0 ≤ y) (hσ : σ ≤ 1)
    (he : (5 / 3) * ‖p‖ ^ 2 ≤ e) :
    (9 / 64 : ℝ) * ‖p - q‖ ^ 2 * projectionBracket v y σ ρ e (‖p‖ ^ 2) ≤
      (9 / 64 : ℝ) * (‖p‖ + ‖q‖) ^ 2 * projectionBracket v y σ ρ e (‖p‖ ^ 2) := by
  have hn := norm_sub_le p q
  have hn0 := norm_nonneg (p - q)
  have hs : ‖p - q‖ ^ 2 ≤ (‖p‖ + ‖q‖) ^ 2 := by nlinarith only [hn, hn0]
  have hc := projectionBracket_nonneg (ρ := ρ) hv hv2 hy hσ (sq_nonneg ‖p‖) he
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs (by norm_num)) hc

theorem gradientSum_radial (p q : Vec) :
    gradientSum ((5 / 3 : ℝ) * ‖p‖ ^ 2) ((5 / 3 : ℝ) * ‖q‖ ^ 2) = ‖p‖ + ‖q‖ := by
  have hp : Real.sqrt ((5 / 3 : ℝ) * ‖p‖ ^ 2) = Real.sqrt (5 / 3) * ‖p‖ := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg p)]
  have hq : Real.sqrt ((5 / 3 : ℝ) * ‖q‖ ^ 2) = Real.sqrt (5 / 3) * ‖q‖ := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg q)]
  have hroot : Real.sqrt (3 / 5 : ℝ) * Real.sqrt (5 / 3) = 1 := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  unfold gradientSum
  rw [hp, hq, mul_add, ← mul_assoc, ← mul_assoc, hroot]
  ring

/-- The part of one actual normalized Hessian Green integrand containing
its invariant quadratic form, distinguished cubic trace and projected cost. -/
def arrayHessianTerm (A U : Mat) (Z : Angular.Gradient) (a : Vec) : ℝ :=
  weight (normalizedBlockNorm A) (normalizedBlockNorm U) * invariantHessianForm A U Z -
    (5 / 36 : ℝ) * weightedCubicField a Z +
    generalCurvaturePairing A U
      (highestProjection (weightTensor a (gradientTensor Z)))
      (highestProjection (weightTensor a (gradientTensor Z))) /
      (24 * weight (normalizedBlockNorm A) (normalizedBlockNorm U))

/-- The tested scalar norm equations, trace subtraction and variance term
that are added to the two actual Hessian Green integrands. -/
def scalarCouplingTerm (v b e f B C NA NB TA TB : ℝ) (p q : Vec) : ℝ :=
  (17 / 10 : ℝ) * (-(e + f) * (NA + NB) - 26 * (2 - v - b) * (e + f) +
      40 * (2 - v - b) * (B + C) - (2 - v - b) * (TA + TB)) +
    158 * (‖p - q‖ ^ 2 / (4 + v ^ 2 + b ^ 2) -
      (1 - (2 - v - b) ^ 2 / 4) * (v - b) ^ 2) +
    kappa v b * NA + kappa b v * NB +
    kappaV v b * ‖p‖ ^ 2 + (kappaB v b + kappaB b v) * inner ℝ p q +
    kappaV b v * ‖q‖ ^ 2

def arrayCoupledIntegrand (A U : Mat) (Z V : Angular.Gradient) (a ab p q : Vec) : ℝ :=
  arrayHessianTerm A U Z a + arrayHessianTerm U A V ab +
    scalarCouplingTerm (normalizedBlockNorm A) (normalizedBlockNorm U)
      (weylGradientEnergy Z) (weylGradientEnergy V)
      (weylMatrixEnergy A Z) (weylMatrixEnergy U V)
      (scalarNormExpression 0 A Z) (scalarNormExpression 0 U V)
      (traceEnergy A) (traceEnergy U) p q

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! Symmetrize an oriented frame measure only for the reflection-invariant
Green integral. Scalar variance and Weyl gaps still use the original
oriented measure. Reflection invariance of that original measure is not
assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

def symmetricFrameMeasure (g : SmoothMetric M) (μ : Measure (FrameBundle g)) :
    Measure (FrameBundle g) := μ + μ.map frameReflection

theorem reflection_preserves_symmetricFrameMeasure :
    MeasurePreserving (frameReflection : FrameBundle g → FrameBundle g)
      (symmetricFrameMeasure g μ) (symmetricFrameMeasure g μ) := by
  have hF : Measurable (frameReflection : FrameBundle g → FrameBundle g) :=
    (frameReflectionEquiv g).measurable
  have hinv : (μ.map frameReflection).map frameReflection = μ := by
    rw [Measure.map_map hF hF]
    have hf : (frameReflection : FrameBundle g → FrameBundle g) ∘ frameReflection = id :=
      funext (frameReflection_involutive g)
    rw [hf, Measure.map_id]
  refine ⟨hF, ?_⟩
  rw [symmetricFrameMeasure, Measure.map_add _ _ hF, hinv, add_comm]

instance symmetricFrameMeasure_finite [IsFiniteMeasure μ] :
    IsFiniteMeasure (symmetricFrameMeasure g μ) := by
  unfold symmetricFrameMeasure
  infer_instance

/-- The only reflection input on the oriented measure is the ordinary
parallel-transport relation, valid independently of the measure. -/
def ParallelReflection (d : MetricGreenData g μ) : Prop :=
  ∀ i t e, frameReflection ((d.flow i).map t e) =
    (d.flow i).map (orientationSign i * t) (frameReflection e)

theorem MetricGreenData.flow_preserves_reflected (d : MetricGreenData g μ)
    (hparallel : ParallelReflection d) (i : Fin 4) (t : ℝ) :
    MeasurePreserving ((d.flow i).map t) (μ.map frameReflection) (μ.map frameReflection) := by
  have hF : MeasurePreserving (frameReflection : FrameBundle g → FrameBundle g)
      μ (μ.map frameReflection) := (frameReflectionEquiv g).measurable.measurePreserving μ
  apply hF.of_semiconj ((d.flow i).preserves (orientationSign i * t))
  · intro e
    have ht : orientationSign i * (orientationSign i * t) = t := by
      rw [← mul_assoc, ← pow_two, orientationSign_sq, one_mul]
    simpa only [ht] using hparallel i (orientationSign i * t) e
  · exact ((d.flow i).map t).measurable

def MetricGreenData.symmetricFlow (d : MetricGreenData g μ)
    (hparallel : ParallelReflection d) (i : Fin 4) :
    FrameFlow g (symmetricFrameMeasure g μ) where
  map := (d.flow i).map
  continuous := (d.flow i).continuous
  preserves t := ((d.flow i).preserves t).add_measure (d.flow_preserves_reflected hparallel i t)

def MetricGreenData.onSymmetricMeasure (d : MetricGreenData g μ)
    (hparallel : ParallelReflection d) : MetricGreenData g (symmetricFrameMeasure g μ) where
  flow := d.symmetricFlow hparallel
  weyl := d.weyl
  continuousWeyl := d.continuousWeyl
  continuousGradient := d.continuousGradient
  continuousHessian := d.continuousHessian
  continuousThird := d.continuousThird
  derivativeWeyl := d.derivativeWeyl
  derivativeGradient := d.derivativeGradient
  derivativeHessian := d.derivativeHessian
  gradientBianchi := d.gradientBianchi
  innerCommutator := d.innerCommutator
  outerCommutator := d.outerCommutator
  ricci := d.ricci

theorem OppositeWeylData.onSymmetricMeasure {d : MetricGreenData g μ}
    (o : OppositeWeylData d) (hparallel : ParallelReflection d) :
    OppositeWeylData (d.onSymmetricMeasure hparallel) where
  symmetric := o.symmetric
  traceFree := o.traceFree
  continuousWeyl := o.continuousWeyl
  continuousGradient := o.continuousGradient
  derivativeWeyl := o.derivativeWeyl
  gradientBianchi := o.gradientBianchi

theorem MetricGreenData.symmetricReflection (d : MetricGreenData g μ)
    (hparallel : ParallelReflection d) : FrameReflectionData (d.onSymmetricMeasure hparallel) where
  preserves := reflection_preserves_symmetricFrameMeasure
  parallel := hparallel

/-- Transfer a symmetric integral back to the oriented frame measure. -/
theorem integral_symmetricFrameMeasure (f : FrameBundle g → ℝ)
    (hi : Integrable f (symmetricFrameMeasure g μ))
    (hs : ∀ e, f (frameReflection e) = f e) :
    (∫ e, f e ∂symmetricFrameMeasure g μ) = 2 * ∫ e, f e ∂μ := by
  have hi' : Integrable f μ ∧ Integrable f (μ.map frameReflection) :=
    integrable_add_measure.mp hi
  rw [symmetricFrameMeasure, integral_add_measure hi'.1 hi'.2]
  have hm : (∫ e, f e ∂μ.map frameReflection) = ∫ e, f (frameReflection e) ∂μ := by
    exact (frameReflectionEquiv g).measurableEmbedding.integral_map _
  rw [hm]
  simp_rw [hs]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Algebraic first Bianchi survives a second covariant derivative.
Only an identity on the open chart is differentiated. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators Topology

noncomputable section

private def secondCurvatureCycle : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 3, 1, 4]
  invFun := ![0, 3, 1, 2, 4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem covariantHessian_firstBianchi (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates 5) (z : FourSpace)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) z)
    (hB : ∀ᶠ w in 𝓝 z, ∀ a i j k l,
      T w ![a, i, j, k, l] + T w ![a, j, k, i, l] + T w ![a, k, i, j, l] = 0)
    (d a : Fin 4) :
    AlgebraicCurvature.FirstBianchi
      (curvatureHessianArray (covariantDerivative g c T z) d a) := by
  let P : FourSpace → CovariantCoordinates 5 := fun w b => T w (b ∘ secondCurvatureCycle)
  let V : FourSpace → CovariantCoordinates 5 :=
    fun w b => T w (b ∘ (secondCurvatureCycle.trans secondCurvatureCycle))
  have hP : ∀ b, DifferentiableAt ℝ (fun w => P w b) z := fun b => hT _
  have hV : ∀ b, DifferentiableAt ℝ (fun w => V w b) z := fun b => hT _
  have hfield : (fun w => T w + P w + V w) =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [hB] with w hw
    funext b
    have hb : b = ![b 0, b 1, b 2, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    have hp : b ∘ secondCurvatureCycle = ![b 0, b 2, b 3, b 1, b 4] := by
      funext i
      fin_cases i <;> rfl
    have hv : b ∘ (secondCurvatureCycle.trans secondCurvatureCycle) =
        ![b 0, b 3, b 1, b 2, b 4] := by
      funext i
      fin_cases i <;> rfl
    change T w b + T w (b ∘ secondCurvatureCycle) +
      T w (b ∘ (secondCurvatureCycle.trans secondCurvatureCycle)) = 0
    rw [hp, hv, hb]
    exact hw _ _ _ _ _
  have hd : covariantDerivative g c T z + covariantDerivative g c P z +
      covariantDerivative g c V z = 0 := by
    rw [← covariantDerivative_add g c T P z hT hP,
      ← covariantDerivative_add g c (fun w => T w + P w) V z
        (fun b => (hT b).add (hP b)) hV,
      covariantDerivative_congr g c hfield]
    funext b
    simp [covariantDerivative, partialDeriv]
  intro i j k l
  have h := congrFun hd (Fin.cons d ![a, i, j, k, l])
  change covariantDerivative g c T z (Fin.cons d ![a, i, j, k, l]) +
    covariantDerivative g c (fun w b => T w (b ∘ secondCurvatureCycle)) z
      (Fin.cons d ![a, i, j, k, l]) +
    covariantDerivative g c
      (fun w b => T w (b ∘ (secondCurvatureCycle.trans secondCurvatureCycle))) z
      (Fin.cons d ![a, i, j, k, l]) = 0 at h
  rw [covariantDerivative_permute, covariantDerivative_permute] at h
  have hp : ![a, i, j, k, l] ∘ secondCurvatureCycle = ![a, j, k, i, l] := by
    funext b
    fin_cases b <;> rfl
  have hv : ![a, i, j, k, l] ∘ (secondCurvatureCycle.trans secondCurvatureCycle) =
      ![a, k, i, j, l] := by
    funext b
    fin_cases b <;> rfl
  rw [hp, hv] at h
  exact h

theorem curvatureHessian_firstBianchi (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (d a : Fin 4) :
    AlgebraicCurvature.FirstBianchi (curvatureHessianArray
      (covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c)) z) d a) := by
  have hdet := (metricInChart_posDef g c z hz).det_pos.ne'
  apply covariantHessian_firstBianchi
  · intro b
    exact (covariantDerivative_contDiffAt g c z hz hdet (curvatureCoordinates g c)
      (curvatureCoordinates_contDiffAt g c z hz hdet) b).differentiableAt (by simp)
  · filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
    intro a i j k l
    exact curvatureDerivative_firstBianchi g c w hw
      (metricInChart_posDef g c w hw).det_pos.ne' a i j k l

theorem frameHessian_firstBianchi (E : Mat4) (T : CovariantCoordinates 6)
    (h : ∀ d a, AlgebraicCurvature.FirstBianchi (curvatureHessianArray T d a))
    (d a : Fin 4) : AlgebraicCurvature.FirstBianchi
      (curvatureHessianArray (frameTensor E T) d a) := by
  intro i j k l
  change frameTensor E T (Fin.cons d ![a, i, j, k, l]) +
    frameTensor E T (Fin.cons d ![a, j, k, i, l]) +
    frameTensor E T (Fin.cons d ![a, k, i, j, l]) = 0
  rw [frameTensor_cons E T d ![a, i, j, k, l],
    frameTensor_cons E T d ![a, j, k, i, l], frameTensor_cons E T d ![a, k, i, j, l],
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro b _
  have hb := frameTensor_firstBianchi E (fun w => T (Fin.cons b w)) (h b) a i j k l
  simp only [curvatureDerivativeArray] at hb
  linear_combination E b d * hb

theorem frame_normalizedWeyl_hessian_firstBianchi (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (d a : Fin 4) :
    AlgebraicCurvature.FirstBianchi (curvatureHessianArray (frameTensor e.matrix
      (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))
        (chartAt FourSpace c c))) d a) := by
  have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  rw [covariantHessian_normalizedWeyl g c (chartAt FourSpace c c) hz]
  exact frameHessian_firstBianchi e.matrix
    (covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c))
      (chartAt FourSpace c c)) (curvatureHessian_firstBianchi g c (chartAt FourSpace c c) hz) d a

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Ricci commutator is transported in its two derivative slots and
all covariant tensor slots by the same actual frame matrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem frameTensor_sub {n : ℕ} (E : Mat4) (S T : CovariantCoordinates n)
    (a : Fin n → Fin 4) :
    frameTensor E (S - T) a = frameTensor E S a - frameTensor E T a := by
  simp only [frameTensor, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem frameTensor_two_prefix {n : ℕ} (E : Mat4)
    (X : CovariantCoordinates (n + 1 + 1)) (i j : Fin 4) (a : Fin n → Fin 4) :
    frameTensor E X (Fin.cons i (Fin.cons j a)) =
      ∑ p, ∑ q, (E p i * E q j) *
        frameTensor E (fun b => X (Fin.cons p (Fin.cons q b))) a := by
  rw [frameTensor_cons]
  simp only [frameTensor_cons, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- Pull back the two tangent arguments of the curvature endomorphism. -/
def pulledCurvatureEndomorphism (E : Mat4) (C : Fin 4 → Fin 4 → Mat4)
    (i j : Fin 4) : Mat4 :=
  ∑ p, ∑ q, (E p i * E q j) • C p q

/-- This is purely finite tensor algebra; the actual coordinate curvature
commutator supplies `hX` in the geometric specialization. -/
theorem framed_tensor_commutator {n : ℕ} (E : Mat4) (hE : IsUnit E.det)
    (C : Fin 4 → Fin 4 → Mat4) (T : CovariantCoordinates n)
    (X : CovariantCoordinates (n + 1 + 1))
    (hX : ∀ p q a, X (Fin.cons p (Fin.cons q a)) -
      X (Fin.cons q (Fin.cons p a)) = -tensorSlotAction (C p q) T a)
    (i j : Fin 4) (a : Fin n → Fin 4) :
    frameTensor E X (Fin.cons i (Fin.cons j a)) -
      frameTensor E X (Fin.cons j (Fin.cons i a)) =
        -tensorSlotAction
          (E⁻¹ * pulledCurvatureEndomorphism E C i j * E) (frameTensor E T) a := by
  have hswap :
      (∑ p, ∑ q, (E p j * E q i) *
        frameTensor E (fun b => X (Fin.cons p (Fin.cons q b))) a) =
      ∑ p, ∑ q, (E p i * E q j) *
        frameTensor E (fun b => X (Fin.cons q (Fin.cons p b))) a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  have hd (p q : Fin 4) :
      (fun b => X (Fin.cons p (Fin.cons q b))) -
        (fun b => X (Fin.cons q (Fin.cons p b))) = -tensorSlotAction (C p q) T := by
    funext b
    exact hX p q b
  have hsum : tensorSlotAction (pulledCurvatureEndomorphism E C i j) T =
      fun b => ∑ p, ∑ q, (E p i * E q j) * tensorSlotAction (C p q) T b := by
    simp only [pulledCurvatureEndomorphism, tensorSlotAction_sum_matrix,
      tensorSlotAction_smul_matrix]
    rfl
  calc
    _ = ∑ p, ∑ q, (E p i * E q j) *
        frameTensor E ((fun b => X (Fin.cons p (Fin.cons q b))) -
          (fun b => X (Fin.cons q (Fin.cons p b)))) a := by
      rw [frameTensor_two_prefix, frameTensor_two_prefix, hswap]
      simp only [frameTensor_sub, mul_sub, Finset.sum_sub_distrib]
    _ = -(∑ p, ∑ q, (E p i * E q j) *
        frameTensor E (tensorSlotAction (C p q) T) a) := by
      simp only [hd, frameTensor_neg, mul_neg, Finset.sum_neg_distrib]
    _ = -frameTensor E (tensorSlotAction (pulledCurvatureEndomorphism E C i j) T) a := by
      rw [hsum, frameTensor_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      rw [frameTensor_sum]
      apply Finset.sum_congr rfl
      intro q _
      exact (frameTensor_const_mul E (E p i * E q j) (tensorSlotAction (C p q) T) a).symm
    _ = _ := by rw [frameTensor_slotAction E _ hE]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Test both actual scalar Weyl equations against the total derivative
energy. This is the norm-equation half of the cancellation in (16). -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem scalarNormExpression_frameReflection (ε : ℝ) (e : FrameBundle g) :
    scalarNormExpression ε (plusWeyl g (frameReflection e).base (frameReflection e).frame)
      (plusWeylGradient g (frameReflection e).base (frameReflection e).frame) =
    scalarNormExpression ε (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame) := by
  have hZ : plusWeylGradient g (frameReflection e).base (frameReflection e).frame =
      reflectedGradient (minusWeylGradient g e.base e.frame) := by
    funext i
    exact plusWeylGradient_reflect g e.base e.frame i
  change scalarNormExpression ε (plusWeyl g e.base e.frame.reflect) _ = _
  rw [plusWeyl_reflect, hZ, scalarNormExpression_reflected]

namespace FrameReflectionData

variable {d : MetricGreenData g μ} (r : FrameReflectionData d)
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

include r

theorem opposite_scalarNorm_integrable :
    Integrable (fun e => scalarNormExpression 0 (minusWeyl g e.base e.frame)
      (minusWeylGradient g e.base e.frame)) μ := by
  have h := r.preserves.integrable_comp_of_integrable d.scalarNorm_integrable
  exact h.congr (Filter.Eventually.of_forall (scalarNormExpression_frameReflection 0))

theorem opposite_radial_integrable (i : Fin 4) :
    Integrable (fun e => regularizedRadialDerivative 0 (minusWeyl g e.base e.frame)
      (minusWeylGradient g e.base e.frame i)) μ := by
  have h := (r.preserves.integrable_comp_of_integrable (d.radial_integrable i)).const_mul
    (orientationSign i)
  apply h.congr
  filter_upwards [] with e
  change orientationSign i * regularizedRadialDerivative 0
    (plusWeyl g e.base e.frame.reflect) (plusWeylGradient g e.base e.frame.reflect i) = _
  rw [plusWeyl_reflect, plusWeylGradient_reflect, regularizedRadialDerivative_smul,
    ← mul_assoc, ← pow_two, orientationSign_sq, one_mul]

theorem jointNormEnergyEquation :
    (∫ e, d.totalEnergyField e *
      (scalarNormExpression 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) +
       scalarNormExpression 0 (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)) +
      ∑ i, d.totalEnergyDerivativeField i e *
        (regularizedRadialDerivative 0 (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame i) +
         regularizedRadialDerivative 0 (minusWeyl g e.base e.frame)
          (minusWeylGradient g e.base e.frame i)) ∂μ) = 0 := by
  let E := d.totalEnergyField
  let D := d.totalEnergyDerivativeField
  let P : FrameBundle g → ℝ := fun e => E e *
      scalarNormExpression 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) +
    ∑ i, D i e * regularizedRadialDerivative 0 (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i)
  let Q : FrameBundle g → ℝ := fun e => E e *
      scalarNormExpression 0 (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame) +
    ∑ i, D i e * regularizedRadialDerivative 0 (minusWeyl g e.base e.frame)
      (minusWeylGradient g e.base e.frame i)
  have hp : (∫ e, P e ∂μ) = 0 :=
    d.testedNormEquation d.refinedKato E D r.totalEnergy_derivative
  have hq : (∫ e, Q e ∂μ) = 0 := r.opposite_testedNormEquation E D r.totalEnergy_derivative
  have hpi : Integrable P μ :=
    (integrable_continuous_weight d.scalarNorm_integrable E).add
      (integrable_finsetSum _ (fun i _ => integrable_continuous_weight (d.radial_integrable i) (D i)))
  have hqi : Integrable Q μ :=
    (integrable_continuous_weight r.opposite_scalarNorm_integrable E).add
      (integrable_finsetSum _ (fun i _ =>
        integrable_continuous_weight (r.opposite_radial_integrable i) (D i)))
  have hsum : (∫ e, P e + Q e ∂μ) = 0 := by
    rw [integral_add hpi hqi, hp, hq, add_zero]
  convert! hsum using 1
  apply integral_congr_ae
  filter_upwards [] with e
  dsimp only [P, Q, E, D]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

end FrameReflectionData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact scalar separation into quartic, axial quadratic, and potential
terms. No geometric estimate is an assumption in these identities. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry
open Energy QuarticEnergy Quadratic Potential Boundary

noncomputable section

def scalarHessianCorrection (v b σ τ e B radial : ℝ) : ℝ :=
  (17 / 10 : ℝ) *
      ((6 * (σ * v ^ 2 + τ * b ^ 2 - v - b) - 26 * (2 - v - b)) * e +
        40 * (2 - v - b) * B) +
    kappa v b * ((e - radial) / v)

def quarticNormLoss (v b e f : ℝ) (p q : Vec) : ℝ :=
  -(17 / 10 : ℝ) * (e + f) * ((e - ‖p‖ ^ 2) / v + (f - ‖q‖ ^ 2) / b)

def radialQuadraticTerm (v b : ℝ) (p q : Vec) : ℝ :=
  158 * (‖p - q‖ ^ 2 / (4 + v ^ 2 + b ^ 2)) +
    kappaV v b * ‖p‖ ^ 2 + (kappaB v b + kappaB b v) * inner ℝ p q +
    kappaV b v * ‖q‖ ^ 2

theorem scalar_potential_identity (v b σ τ : ℝ) :
    -(17 / 10 : ℝ) * (2 - v - b) *
        (30 * v ^ 2 * (1 - 2 * σ * v + v ^ 2) +
          30 * b ^ 2 * (1 - 2 * τ * b + b ^ 2)) +
      kappa v b * (6 * v * (1 - σ * v)) +
      kappa b v * (6 * b * (1 - τ * b)) -
      158 * (1 - (2 - v - b) ^ 2 / 4) * (v - b) ^ 2 =
    zeroOrderIntegrand v b σ τ := by
  unfold zeroOrderIntegrand zeroOrder spectralCoefficient
  ring

theorem scalarCouplingTerm_spectral_split (v b σ τ e f B C : ℝ) (p q : Vec) :
    scalarCouplingTerm v b e f B C
        ((e - ‖p‖ ^ 2) / v + 6 * v * (1 - σ * v))
        ((f - ‖q‖ ^ 2) / b + 6 * b * (1 - τ * b))
        (30 * v ^ 2 * (1 - 2 * σ * v + v ^ 2))
        (30 * b ^ 2 * (1 - 2 * τ * b + b ^ 2)) p q =
      scalarHessianCorrection v b σ τ e B (‖p‖ ^ 2) +
      scalarHessianCorrection b v τ σ f C (‖q‖ ^ 2) +
      quarticNormLoss v b e f p q + radialQuadraticTerm v b p q +
      zeroOrderIntegrand v b σ τ := by
  rw [← scalar_potential_identity]
  unfold scalarCouplingTerm scalarHessianCorrection quarticNormLoss radialQuadraticTerm
  ring

theorem axial_plus_radial_identity (v b : ℝ) (p q : Vec) :
    (axialCoefficient v b + 2 * kappa v b / (3 * v)) * ‖p‖ ^ 2 +
      (axialCoefficient b v + 2 * kappa b v / (3 * b)) * ‖q‖ ^ 2 +
      radialQuadraticTerm v b p q =
    quadraticCoefficient v b * ‖p‖ ^ 2 +
      2 * mixedCoefficient v b * inner ℝ p q +
      quadraticCoefficient b v * ‖q‖ ^ 2 := by
  unfold radialQuadraticTerm quadraticCoefficient mixedCoefficient denominator
  rw [norm_sub_sq_real]
  have hd : 4 + b ^ 2 + v ^ 2 = 4 + v ^ 2 + b ^ 2 := by ring
  rw [hd]
  ring

/-- The actual invariant Hessian expression and the scalar correction
are bounded together, so the axial reduction uses the same spectral data. -/
theorem invariant_axial_bound (A U : Mat) (Z : Angular.Gradient)
    (S : Shape) (τ : ℝ) (p' k l p : Vec)
    (hv : 0 < normalizedBlockNorm A)
    (hsum : normalizedBlockNorm A + normalizedBlockNorm U ≤ 2) (hτ : τ ≤ 1)
    (he : (parameters S p' k l).squaredNorm / 6 = weylGradientEnergy Z)
    (hp : ‖p'‖ ^ 2 = ‖p‖ ^ 2)
    (hB : weylMatrixEnergy A Z =
      curvatureContraction S (normalizedBlockNorm A) (parameters S p' k l))
    (hH : invariantHessianForm A U Z ≤
      hessianTensorForm S (normalizedBlockNorm A) (normalizedBlockNorm U) p' k l) :
    weight (normalizedBlockNorm A) (normalizedBlockNorm U) * invariantHessianForm A U Z +
      scalarHessianCorrection (normalizedBlockNorm A) (normalizedBlockNorm U)
        S.sigma τ (weylGradientEnergy Z) (weylMatrixEnergy A Z) (‖p‖ ^ 2) ≤
    (axialCoefficient (normalizedBlockNorm A) (normalizedBlockNorm U) +
        2 * kappa (normalizedBlockNorm A) (normalizedBlockNorm U) /
          (3 * normalizedBlockNorm A)) * ‖p‖ ^ 2 := by
  have hh := hessian_quadratic_axial_bound S hv (normalizedBlockNorm_nonneg U) hsum hτ p' k l
  have hm := mul_le_mul_of_nonneg_left hH
    (show 0 ≤ weight (normalizedBlockNorm A) (normalizedBlockNorm U) by unfold weight; positivity)
  unfold hessianQuadraticContribution at hh
  rw [he, ← hB, hp] at hh
  unfold scalarHessianCorrection
  linarith only [hh, hm]

theorem scalarWeight_positive {v b : ℝ} (_hv : 0 ≤ v) (hb : 0 ≤ b)
    (hsum : v + b ≤ 2) : 0 < scalarWeight v b := by
  unfold scalarWeight
  linarith

/-- The two cubic and projection upper bounds have exactly the quartic
energy form used by the scalar relaxation. -/
theorem quartic_bounds_identity (v b r s σ τ ρ χ e f : ℝ) (p q : Vec) :
    (1 / 2 : ℝ) * Real.sqrt (3 / 5) * (‖p‖ + ‖q‖) * scalarWeight v b *
        (e * Real.sqrt e) +
      (1 / 2 : ℝ) * Real.sqrt (3 / 5) * (‖p‖ + ‖q‖) * scalarWeight b v *
        (f * Real.sqrt f) +
      (9 / 64 : ℝ) * (‖p‖ + ‖q‖) ^ 2 * projectionBracket v (b * s) σ ρ e (‖p‖ ^ 2) +
      (9 / 64 : ℝ) * (‖p‖ + ‖q‖) ^ 2 * projectionBracket b (v * r) τ χ f (‖q‖ ^ 2) +
      quarticNormLoss v b e f p q =
    quarticEnergy v b ((5 / 3) * ‖p‖ ^ 2) ((5 / 3) * ‖q‖ ^ 2)
      (projectionCoefficient v (b * s) σ ρ) (projectionCoefficient b (v * r) τ χ)
      (defectCoefficient v (b * s)) (defectCoefficient b (v * r)) e f := by
  unfold quarticEnergy
  rw [gradientSum_radial]
  unfold projectionBracket quarticNormLoss
  ring

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The two actual Weyl Hessian blocks are trace-free because the
Einstein curvature Hessian has zero Ricci contraction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem actual_weylHessian_traceFree (e : OrthonormalFrame g c) (hRic : RicciThree g)
    (i j : Fin 4) :
    TraceHessian.traceFree (plusWeylHessian g c e i j) ∧
      TraceHessian.traceFree (minusWeylHessian g c e i j) := by
  let T := frameTensor e.matrix
    (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))
      (chartAt FourSpace c c))
  have hs := frame_normalizedWeyl_hessian_symmetries g c e i j
  have hb := frame_normalizedWeyl_hessian_firstBianchi g c e i j
  have hR (k : Fin 4) : (∑ r, T ![i, j, r, k, k, r]) = 0 :=
    frame_normalizedWeyl_hessian_trace_zero e hRic i j k k
  exact AlgebraicCurvature.ricci_zero_blocks_traceFree
    (curvatureHessianArray T i j) hs.1 hs.2.1 hb hR

theorem actual_weylHessian_constraints (e : OrthonormalFrame g c) (hRic : RicciThree g)
    (i j : Fin 4) :
    (TraceHessian.symmetric (plusWeylHessian g c e i j) ∧
      TraceHessian.traceFree (plusWeylHessian g c e i j)) ∧
    (TraceHessian.symmetric (minusWeylHessian g c e i j) ∧
      TraceHessian.traceFree (minusWeylHessian g c e i j)) :=
  ⟨⟨(actual_weylHessian_symmetric e i j).1, (actual_weylHessian_traceFree e hRic i j).1⟩,
   ⟨(actual_weylHessian_symmetric e i j).2, (actual_weylHessian_traceFree e hRic i j).2⟩⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual rank-four curvature commutator on the positive Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped BigOperators Manifold ContDiff

noncomputable section

private theorem sumThree_cycle (f : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

private theorem sumFour_pairSwap (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  have h := (Equiv.prodComm (Fin 4 × Fin 4) (Fin 4 × Fin 4)).sum_comp
    (fun p => f p.2.1 p.2.2 p.1.1 p.1.2)
  simpa only [Fintype.sum_prod_type, Equiv.prodComm_apply, Prod.swap_prod_mk] using h

private theorem sumFour_BCAD (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ b, ∑ c, ∑ a, ∑ d, f a b c d := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]

private theorem sumFour_BDAC (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ b, ∑ d, ∑ a, ∑ c, f a b c d := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [sumThree_cycle]

private theorem metric_pairing_apply (E G : Mat4) (i j : Fin 4) :
    (Eᵀ * G * E) i j = ∑ p, ∑ q, E p i * G p q * E q j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem unit_product_first (E G : Mat4) (i j k l : Fin 4) :
    (∑ p, ∑ q, ∑ r, ∑ s,
      E p i * E q j * E r k * E s l * (G q r * G p s)) =
      (Eᵀ * G * E) i l * (Eᵀ * G * E) j k := by
  simp only [metric_pairing_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sumFour_BCAD]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

private theorem unit_product_second (E G : Mat4) (i j k l : Fin 4) :
    (∑ p, ∑ q, ∑ r, ∑ s,
      E p i * E q j * E r k * E s l * (G p r * G q s)) =
      (Eᵀ * G * E) i k * (Eᵀ * G * E) j l := by
  simp only [metric_pairing_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sumFour_BDAC]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

/-- The constant-curvature tensor in an orthonormal frame. -/
def unitFrameTensor : CovariantCoordinates 4 := fun a =>
  (if a 1 = a 2 then (1 : ℝ) else 0) * (if a 0 = a 3 then 1 else 0) -
    (if a 0 = a 2 then 1 else 0) * (if a 1 = a 3 then 1 else 0)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem frameTensor_unitCurvature (e : OrthonormalFrame g c) :
    frameTensor e.matrix
      (unitCurvatureCoordinates g c (chartAt FourSpace c c)) = unitFrameTensor := by
  funext a
  have ha : a = ![a 0, a 1, a 2, a 3] := by
    funext i
    fin_cases i <;> rfl
  rw [ha, frameTensor_four]
  change (∑ p, ∑ q, ∑ r, ∑ s, e.matrix p (a 0) * e.matrix q (a 1) *
      e.matrix r (a 2) * e.matrix s (a 3) *
      (chartMetric g c q r * chartMetric g c p s -
        chartMetric g c p r * chartMetric g c q s)) = _
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [unit_product_first, unit_product_second, e.orthonormal]
  simp only [unitFrameTensor, Matrix.one_apply]
  dsimp
  congr 1
  exact mul_comm _ _

private theorem sumFive_moveLast (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) =
      ∑ e, ∑ a, ∑ b, ∑ c, ∑ d, f a b c d e := by
  calc
    _ = ∑ a, ∑ b, ∑ e, ∑ c, ∑ d, f a b c d e := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [sumThree_cycle]
    _ = ∑ a, ∑ e, ∑ b, ∑ c, ∑ d, f a b c d e := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

private theorem sumFour_moveLast (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := by
  calc
    _ = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      rw [sumThree_cycle]
    _ = _ := by rw [Finset.sum_comm]

theorem frameTensor_curvatureCoordinates (e : OrthonormalFrame g c)
    (i j k l : Fin 4) :
    frameTensor e.matrix (curvatureCoordinates g c (chartAt FourSpace c c)) ![i,j,k,l] =
      frameCurvature g c e i j k l := by
  rw [frameTensor_four]
  change (∑ p, ∑ q, ∑ r, ∑ b, e.matrix p i * e.matrix q j * e.matrix r k *
    e.matrix b l * (∑ a, chartMetric g c a b *
      curvatureComponent g c (chartAt FourSpace c c) a p q r)) = _
  simp only [Finset.mul_sum]
  rw [sumFive_moveLast]
  unfold frameCurvature
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = ∑ b, ∑ p, ∑ q, ∑ r,
        e.matrix p i * e.matrix q j * e.matrix r k * e.matrix b l *
          (chartMetric g c a b * curvatureComponent g c (chartAt FourSpace c c) a p q r) := by
      rw [sumFour_moveLast]
    _ = _ := by
      repeat' (apply Finset.sum_congr rfl; intro _ _)
      ring

private theorem unitFrameTensor_pairing (P Q : Mat4)
    (hQ : Qᵀ = -Q) : twoFormPairing unitFrameTensor P Q =
      (1 / 4 : ℝ) * ∑ a, ∑ b, P a b * Q a b := by
  have hq (a b : Fin 4) : Q b a = -Q a b := congrArg (fun A : Mat4 => A a b) hQ
  change (1 / 8 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d,
    ((if b = d then (1 : ℝ) else 0) * (if a = c then 1 else 0) -
      (if a = d then 1 else 0) * (if b = c then 1 else 0)) * P a b * Q c d) = _
  simp only [sub_mul, mul_ite, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib, ite_self, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const_zero]
  have hcross : (∑ a, ∑ b, P a b * Q b a) = -(∑ a, ∑ b, P a b * Q a b) := by
    calc
      _ = ∑ a, ∑ b, -(P a b * Q a b) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [hq a b]
        ring
      _ = _ := by simp only [Finset.sum_neg_distrib]
  rw [hcross]
  ring

theorem blockCoordinates_unitFrameTensor :
    blockCoordinates unitFrameTensor quaternionMatrix = 1 := by
  ext a b
  rw [blockCoordinates_pairing,
    unitFrameTensor_pairing _ _ (Angular.quaternionMatrix_transpose b),
    CurvatureContraction.plus_twoForm_pairing]
  simp only [Matrix.one_apply]
  split_ifs <;> norm_num

theorem frameWeyl_blockCoordinates (e : OrthonormalFrame g c) :
    blockCoordinates (frameTensor e.matrix
      (normalizedWeylCoordinates g c (chartAt FourSpace c c))) quaternionMatrix =
        plusWeyl g c e := by
  have hT : frameTensor e.matrix (normalizedWeylCoordinates g c (chartAt FourSpace c c)) =
      frameTensor e.matrix (curvatureCoordinates g c (chartAt FourSpace c c)) - unitFrameTensor := by
    funext a
    change frameTensor e.matrix (_ - _) a = _
    rw [frameTensor_sub, frameTensor_unitCurvature]
    rfl
  rw [hT]
  change blockCoordinatesLinear quaternionMatrix (_ - _) = _
  rw [map_sub]
  change blockCoordinates (frameTensor e.matrix
    (curvatureCoordinates g c (chartAt FourSpace c c))) quaternionMatrix -
      blockCoordinates unitFrameTensor quaternionMatrix = _
  rw [blockCoordinates_unitFrameTensor]
  change blockCoordinates (frameTensor e.matrix
    (curvatureCoordinates g c (chartAt FourSpace c c))) quaternionMatrix - 1 =
      curvatureBlock (curvaturePairing g c e) quaternionMatrix - 1
  congr 1
  ext a b
  simp only [blockCoordinates, curvatureBlock, frameTensor_curvatureCoordinates,
    curvaturePairing]

theorem OrthonormalFrame.inverse_eq_transpose_metric (e : OrthonormalFrame g c) :
    e.matrix⁻¹ = e.matrixᵀ * chartMetric g c := by
  have h := congrArg (fun A : Mat4 => A * e.matrix⁻¹) e.orthonormal
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr e.det_ne_zero),
    mul_one, one_mul] at h
  exact h.symm

private theorem sumFive_moveFirst (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) =
      ∑ b, ∑ c, ∑ d, ∑ e, ∑ a, f a b c d e := by
  exact (sumFive_moveLast (fun b c d e a => f a b c d e)).symm

/-- The matrix in the framed covector action is exactly the metric's
curvature endomorphism evaluated on that orthonormal frame. -/
theorem frame_curvatureEndomorphism (e : OrthonormalFrame g c) (i j : Fin 4) :
    e.matrix⁻¹ * pulledCurvatureEndomorphism e.matrix
      (fun p q => coordinateCurvatureMatrix g c p q (chartAt FourSpace c c)) i j * e.matrix =
        curvatureEndomorphism (frameCurvature g c e) i j := by
  rw [e.inverse_eq_transpose_metric]
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, pulledCurvatureEndomorphism,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
    coordinateCurvatureMatrix_apply, curvatureEndomorphism, frameCurvature]
  rw [sumFive_moveFirst, sumFour_pairSwap]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  have hs (v w : Fin 4) : chartMetric g c w v = chartMetric g c v w := by
    exact g.symm _ _ _
  rw [hs]
  ring

/-- The last pointwise commutator input of the Weyl equation is a consequence
of the actual Levi-Civita commutator and Einstein curvature decomposition. -/
theorem actual_plusWeylHessian_commutator (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (i j : Fin 4) (a b : Fin 3) :
    plusWeylHessian g c e i j a b - plusWeylHessian g c e j i a b =
      bundleCurvatureAction (plusWeyl g c e) i j (plusWeyl g c e) a b := by
  let z : FourSpace := chartAt FourSpace c c
  let T : CovariantCoordinates 4 := normalizedWeylCoordinates g c z
  let X : CovariantCoordinates 6 := covariantDerivative g c
    (covariantDerivative g c (normalizedWeylCoordinates g c)) z
  let C : Fin 4 → Fin 4 → Mat4 := fun p q => coordinateCurvatureMatrix g c p q z
  have hz : z ∈ (chartAt FourSpace c).target := (chartAt FourSpace c).map_source
    (mem_chart_source FourSpace c)
  have hdet : (metricInChart g c z).det ≠ 0 :=
    (metricInChart_posDef g c z hz).det_pos.ne'
  have hX (p q : Fin 4) (v : Fin 4 → Fin 4) :
      X (Fin.cons p (Fin.cons q v)) - X (Fin.cons q (Fin.cons p v)) =
        -tensorSlotAction (C p q) T v :=
    normalizedWeyl_commutator g c z hz hdet p q v
  have hc : e.matrix⁻¹ * pulledCurvatureEndomorphism e.matrix C i j * e.matrix =
      curvatureEndomorphism (Angular.einsteinCurvatureTensor
        (plusWeyl g c e) (minusWeyl g c e)) i j := by
    rw [frame_curvatureEndomorphism, actual_einstein_decomposition e hRic]
  have he : (fun v => frameTensor e.matrix X (Fin.cons i (Fin.cons j v))) -
      (fun v => frameTensor e.matrix X (Fin.cons j (Fin.cons i v))) =
        -tensorSlotAction (curvatureEndomorphism (Angular.einsteinCurvatureTensor
          (plusWeyl g c e) (minusWeyl g c e)) i j) (frameTensor e.matrix T) := by
    funext v
    have hh := framed_tensor_commutator e.matrix (isUnit_iff_ne_zero.mpr e.det_ne_zero)
      C T X hX i j v
    rw [hc] at hh
    exact hh
  have hb := congrArg (blockCoordinatesLinear quaternionMatrix) he
  rw [map_sub] at hb
  change blockCoordinates (fun v => frameTensor e.matrix X (Fin.cons i (Fin.cons j v)))
      quaternionMatrix -
    blockCoordinates (fun v => frameTensor e.matrix X (Fin.cons j (Fin.cons i v)))
      quaternionMatrix =
    blockCoordinates (-tensorSlotAction (curvatureEndomorphism
      (Angular.einsteinCurvatureTensor (plusWeyl g c e) (minusWeyl g c e)) i j)
      (frameTensor e.matrix T)) quaternionMatrix at hb
  rw [blockCoordinates_einstein_curvature_action, frameWeyl_blockCoordinates] at hb
  exact congrArg (fun B : Mat3 => B a b) hb

end
end PositiveEinsteinFour.Geometry
end


section

/-! Differentiating the actual cyclic second Bianchi identity preserves
its derivative and curvature slots, before passage to an orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators Topology

noncomputable section

private def differentiatedBianchiCycle : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 0, 3, 4]
  invFun := ![2, 0, 1, 3, 4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem covariantHessian_differentialBianchi (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates 5) (z : FourSpace)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) z)
    (hB : ∀ᶠ w in 𝓝 z, ∀ a i j k l,
      T w ![a, i, j, k, l] + T w ![i, j, a, k, l] + T w ![j, a, i, k, l] = 0)
    (d : Fin 4) :
    AlgebraicCurvature.DifferentialBianchi
      (curvatureDerivativeArray (fun b => covariantDerivative g c T z (Fin.cons d b))) := by
  let P : FourSpace → CovariantCoordinates 5 := fun w b => T w (b ∘ differentiatedBianchiCycle)
  let V : FourSpace → CovariantCoordinates 5 :=
    fun w b => T w (b ∘ (differentiatedBianchiCycle.trans differentiatedBianchiCycle))
  have hP : ∀ b, DifferentiableAt ℝ (fun w => P w b) z := fun b => hT _
  have hV : ∀ b, DifferentiableAt ℝ (fun w => V w b) z := fun b => hT _
  have hfield : (fun w => T w + P w + V w) =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [hB] with w hw
    funext b
    have hb : b = ![b 0, b 1, b 2, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    have hp : b ∘ differentiatedBianchiCycle = ![b 1, b 2, b 0, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    have hv : b ∘ (differentiatedBianchiCycle.trans differentiatedBianchiCycle) =
        ![b 2, b 0, b 1, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    change T w b + T w (b ∘ differentiatedBianchiCycle) +
      T w (b ∘ (differentiatedBianchiCycle.trans differentiatedBianchiCycle)) = 0
    rw [hp, hv, hb]
    exact hw _ _ _ _ _
  have hd : covariantDerivative g c T z + covariantDerivative g c P z +
      covariantDerivative g c V z = 0 := by
    rw [← covariantDerivative_add g c T P z hT hP,
      ← covariantDerivative_add g c (fun w => T w + P w) V z
        (fun b => (hT b).add (hP b)) hV,
      covariantDerivative_congr g c hfield]
    funext b
    simp [covariantDerivative, partialDeriv]
  intro a i j k l
  have h := congrFun hd (Fin.cons d ![a, i, j, k, l])
  change covariantDerivative g c T z (Fin.cons d ![a, i, j, k, l]) +
    covariantDerivative g c (fun w b => T w (b ∘ differentiatedBianchiCycle)) z
      (Fin.cons d ![a, i, j, k, l]) +
    covariantDerivative g c
      (fun w b => T w (b ∘ (differentiatedBianchiCycle.trans differentiatedBianchiCycle))) z
      (Fin.cons d ![a, i, j, k, l]) = 0 at h
  rw [covariantDerivative_permute, covariantDerivative_permute] at h
  have hp : ![a, i, j, k, l] ∘ differentiatedBianchiCycle = ![i, j, a, k, l] := by
    funext b
    fin_cases b <;> rfl
  have hv : ![a, i, j, k, l] ∘ (differentiatedBianchiCycle.trans differentiatedBianchiCycle) =
      ![j, a, i, k, l] := by
    funext b
    fin_cases b <;> rfl
  rw [hp, hv] at h
  exact h


theorem curvatureHessian_differentialBianchi (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (d : Fin 4) :
    AlgebraicCurvature.DifferentialBianchi (curvatureDerivativeArray
      (fun b => covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c))
        z (Fin.cons d b))) := by
  have hdet := (metricInChart_posDef g c z hz).det_pos.ne'
  apply covariantHessian_differentialBianchi
  · intro b
    exact (covariantDerivative_contDiffAt g c z hz hdet (curvatureCoordinates g c)
      (curvatureCoordinates_contDiffAt g c z hz hdet) b).differentiableAt (by simp)
  · filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
    exact curvatureCoordinates_second_bianchi g c w hw
      (metricInChart_posDef g c w hw).det_pos.ne'

theorem frameHessian_differentialBianchi (E : Mat4) (T : CovariantCoordinates 6)
    (h : ∀ d, AlgebraicCurvature.DifferentialBianchi
      (curvatureDerivativeArray (fun b => T (Fin.cons d b)))) (d : Fin 4) :
    AlgebraicCurvature.DifferentialBianchi
      (curvatureDerivativeArray (fun b => frameTensor E T (Fin.cons d b))) := by
  intro a i j k l
  change frameTensor E T (Fin.cons d ![a, i, j, k, l]) +
    frameTensor E T (Fin.cons d ![i, j, a, k, l]) +
    frameTensor E T (Fin.cons d ![j, a, i, k, l]) = 0
  rw [frameTensor_cons E T d ![a, i, j, k, l],
    frameTensor_cons E T d ![i, j, a, k, l], frameTensor_cons E T d ![j, a, i, k, l],
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro b _
  have hb := frameTensor_differentialBianchi E (fun w => T (Fin.cons b w))
    (h b) a i j k l
  simp only [curvatureDerivativeArray] at hb
  linear_combination E b d * hb

theorem frame_normalizedWeyl_hessian_differentialBianchi (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (d : Fin 4) :
    AlgebraicCurvature.DifferentialBianchi (curvatureDerivativeArray
      (fun b => frameTensor e.matrix
        (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))
          (chartAt FourSpace c c)) (Fin.cons d b))) := by
  have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  rw [covariantHessian_normalizedWeyl g c (chartAt FourSpace c c) hz]
  exact frameHessian_differentialBianchi e.matrix
    (covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c))
      (chartAt FourSpace c c))
    (curvatureHessian_differentialBianchi g c (chartAt FourSpace c c) hz) d

end
end PositiveEinsteinFour.Geometry
end


section

/-! The opposite and summed deficit tests, obtained from the same
proved plus-block energy identity by reflection of the actual frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem minusWeylGradient_reflect (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (i : Fin 4) :
    minusWeylGradient g c e.reflect i = orientationSign i • plusWeylGradient g c e i := by
  have h := plusWeylGradient_reflect g c e.reflect i
  rw [e.reflect_reflect] at h
  have h' := congrArg (fun A : Mat => orientationSign i • A) h
  rw [smul_smul, ← pow_two, orientationSign_sq, one_smul] at h'
  exact h'.symm

theorem regularizedDeficit_swap (ε : ℝ) (A B : Mat) :
    regularizedDeficit ε B A = regularizedDeficit ε A B := by
  unfold regularizedDeficit
  ring

theorem deficit_frameReflection (e : FrameBundle g) :
    regularizedDeficit 0 (plusWeyl g (frameReflection e).base (frameReflection e).frame)
      (minusWeyl g (frameReflection e).base (frameReflection e).frame) =
    regularizedDeficit 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) := by
  change regularizedDeficit 0 (plusWeyl g e.base e.frame.reflect)
    (minusWeyl g e.base e.frame.reflect) = _
  rw [plusWeyl_reflect, minusWeyl_reflect, regularizedDeficit_swap]

theorem deficitDerivative_frameReflection (e : FrameBundle g) (i : Fin 4) :
    regularizedDeficitDerivative 0 (plusWeyl g (frameReflection e).base (frameReflection e).frame)
      (minusWeyl g (frameReflection e).base (frameReflection e).frame)
      (plusWeylGradient g (frameReflection e).base (frameReflection e).frame i)
      (minusWeylGradient g (frameReflection e).base (frameReflection e).frame i) =
    orientationSign i * regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame)
      (minusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame i)
      (minusWeylGradient g e.base e.frame i) := by
  change regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame.reflect)
    (minusWeyl g e.base e.frame.reflect) (plusWeylGradient g e.base e.frame.reflect i)
    (minusWeylGradient g e.base e.frame.reflect i) = _
  rw [plusWeyl_reflect, minusWeyl_reflect, plusWeylGradient_reflect, minusWeylGradient_reflect]
  simp only [regularizedDeficitDerivative, regularizedRadialDerivative_smul]
  ring

namespace FrameReflectionData

variable {d : MetricGreenData g μ} (r : FrameReflectionData d)
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

include r

theorem deficitEnergy_integrable (o : OppositeWeylData d)
    (L : C(FrameBundle g, ℝ)) (D : Fin 4 → C(FrameBundle g, ℝ)) :
    Integrable (fun e => regularizedDeficit 0 (plusWeyl g e.base e.frame)
      (minusWeyl g e.base e.frame) * L e +
      ∑ i, regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) * D i e) μ := by
  have hδ : Continuous (fun e : FrameBundle g => regularizedDeficit 0
      (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)) := by
    exact (continuous_const.sub ((continuous_regularizedBlockNorm 0).comp d.continuousWeyl)).sub
      ((continuous_regularizedBlockNorm 0).comp o.continuousWeyl)
  apply Integrable.add ((hδ.mul L.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))
  apply integrable_finsetSum
  intro i _
  have hi := integrable_continuous_weight
    ((d.radial_integrable i).neg.sub (r.opposite_radial_integrable i)) (D i)
  apply hi.congr
  filter_upwards [] with e
  change D i e * (-_ - _) = (-_ - _) * D i e
  ring

theorem opposite_deficitEnergyEquation (o : OppositeWeylData d)
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    (∫ e, regularizedDeficit 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) *
        d.oppositeEnergyLaplacianField e +
      ∑ i, regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
        d.oppositeEnergyDerivativeField i e ∂μ) = 0 := by
  let F : FrameBundle g → ℝ := fun e =>
    regularizedDeficit 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) *
      d.energyLaplacianField e +
    ∑ i, regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
      d.energyDerivativeField i e
  have hF : (∫ e, F e ∂μ) = 0 := d.deficitEnergyEquation o hpinch
  rw [← r.integral_reflection F] at hF
  refine Eq.trans (b := ∫ e, F (frameReflection e) ∂μ) ?_ hF
  apply integral_congr_ae
  filter_upwards [] with e
  change regularizedDeficit 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) *
    d.energyLaplacianField (frameReflection e) +
      (∑ i, regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
        (orientationSign i * d.energyDerivativeField i (frameReflection e))) =
    regularizedDeficit 0 (plusWeyl g (frameReflection e).base (frameReflection e).frame)
    (minusWeyl g (frameReflection e).base (frameReflection e).frame) *
      d.energyLaplacianField (frameReflection e) +
      (∑ i, regularizedDeficitDerivative 0 (plusWeyl g (frameReflection e).base (frameReflection e).frame)
        (minusWeyl g (frameReflection e).base (frameReflection e).frame)
        (plusWeylGradient g (frameReflection e).base (frameReflection e).frame i)
        (minusWeylGradient g (frameReflection e).base (frameReflection e).frame i) *
        d.energyDerivativeField i (frameReflection e))
  rw [deficit_frameReflection]
  simp_rw [deficitDerivative_frameReflection]
  apply congrArg (fun z : ℝ => regularizedDeficit 0 (plusWeyl g e.base e.frame)
    (minusWeyl g e.base e.frame) * d.energyLaplacianField (frameReflection e) + z)
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem jointDeficitEnergyEquation (o : OppositeWeylData d)
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    (∫ e, regularizedDeficit 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) *
        (d.energyLaplacianField e + d.oppositeEnergyLaplacianField e) +
      ∑ i, regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
        d.totalEnergyDerivativeField i e ∂μ) = 0 := by
  let P : FrameBundle g → ℝ := fun e =>
    regularizedDeficit 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) *
      d.energyLaplacianField e +
    ∑ i, regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
      d.energyDerivativeField i e
  let Q : FrameBundle g → ℝ := fun e =>
    regularizedDeficit 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) *
      d.oppositeEnergyLaplacianField e +
    ∑ i, regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
      d.oppositeEnergyDerivativeField i e
  have hp : (∫ e, P e ∂μ) = 0 := d.deficitEnergyEquation o hpinch
  have hq : (∫ e, Q e ∂μ) = 0 := r.opposite_deficitEnergyEquation o hpinch
  have hsum : (∫ e, P e + Q e ∂μ) = 0 := by
    rw [integral_add (r.deficitEnergy_integrable o _ _) (r.deficitEnergy_integrable o _ _),
      hp, hq, add_zero]
  convert! hsum using 1
  apply integral_congr_ae
  filter_upwards [] with e
  dsimp only [P, Q, MetricGreenData.totalEnergyDerivativeField, ContinuousMap.add_apply]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

end FrameReflectionData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The opposite square-root energy inequality on the original measure.
Only parallel-flow compatibility with reflection is used: the plus equation
is applied to the reflected measure and then pulled back. The original
oriented measure is never required to be reflection invariant. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem integral_reflectedMeasure (f : FrameBundle g → ℝ) :
    (∫ e, f e ∂μ.map frameReflection) = ∫ e, f (frameReflection e) ∂μ :=
  (frameReflectionEquiv g).measurableEmbedding.integral_map f

theorem blockNorm_frameReflection (e : FrameBundle g) :
    normalizedBlockNorm (plusWeyl g (frameReflection e).base (frameReflection e).frame) =
      normalizedBlockNorm (minusWeyl g e.base e.frame) := by
  change normalizedBlockNorm (plusWeyl g e.base e.frame.reflect) = _
  rw [plusWeyl_reflect]

theorem blockRadialEnergy_frameReflection (e : FrameBundle g) :
    ‖blockRadialGradient (plusWeyl g (frameReflection e).base (frameReflection e).frame)
      (plusWeylGradient g (frameReflection e).base (frameReflection e).frame)‖ ^ 2 =
    ‖blockRadialGradient (minusWeyl g e.base e.frame)
      (minusWeylGradient g e.base e.frame)‖ ^ 2 := by
  have hz : plusWeylGradient g (frameReflection e).base (frameReflection e).frame =
      reflectedGradient (minusWeylGradient g e.base e.frame) := by
    funext i
    exact plusWeylGradient_reflect g e.base e.frame i
  rw [hz]
  change ‖blockRadialGradient (plusWeyl g e.base e.frame.reflect)
    (reflectedGradient (minusWeylGradient g e.base e.frame))‖ ^ 2 = _
  rw [plusWeyl_reflect, reflectedGradient_radial_norm]

namespace MetricGreenData

def reflectedFlow (d : MetricGreenData g μ) (hparallel : ParallelReflection d) (i : Fin 4) :
    FrameFlow g (μ.map frameReflection) where
  map := (d.flow i).map
  continuous := (d.flow i).continuous
  preserves t := d.flow_preserves_reflected hparallel i t

def onReflectedMeasure (d : MetricGreenData g μ) (hparallel : ParallelReflection d) :
    MetricGreenData g (μ.map frameReflection) where
  flow := d.reflectedFlow hparallel
  weyl := d.weyl
  continuousWeyl := d.continuousWeyl
  continuousGradient := d.continuousGradient
  continuousHessian := d.continuousHessian
  continuousThird := d.continuousThird
  derivativeWeyl := d.derivativeWeyl
  derivativeGradient := d.derivativeGradient
  derivativeHessian := d.derivativeHessian
  gradientBianchi := d.gradientBianchi
  innerCommutator := d.innerCommutator
  outerCommutator := d.outerCommutator
  ricci := d.ricci

variable [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

theorem oppositeWeakNormEquation (d : MetricGreenData g μ) (hparallel : ParallelReflection d) :
    (∫ e, scalarNormExpression 0 (minusWeyl g e.base e.frame)
      (minusWeylGradient g e.base e.frame) ∂μ) = 0 := by
  have h := (d.onReflectedMeasure hparallel).weakNormEquation
  rw [integral_reflectedMeasure] at h
  simpa only [scalarNormExpression_frameReflection] using h

theorem oppositeScalarNorm_integrable (d : MetricGreenData g μ)
    (hparallel : ParallelReflection d) :
    Integrable (fun e => scalarNormExpression 0 (minusWeyl g e.base e.frame)
      (minusWeylGradient g e.base e.frame)) μ := by
  have hi := (d.onReflectedMeasure hparallel).scalarNorm_integrable
  have hc := hi.comp_measurable (frameReflectionEquiv g).measurable
  apply hc.congr
  filter_upwards [] with e
  exact scalarNormExpression_frameReflection 0 e

theorem oppositeRadialEnergyQuotient_integrable (d : MetricGreenData g μ)
    (hparallel : ParallelReflection d) :
    Integrable (fun e =>
      ‖blockRadialGradient (minusWeyl g e.base e.frame)
        (minusWeylGradient g e.base e.frame)‖ ^ 2 /
          normalizedBlockNorm (minusWeyl g e.base e.frame)) μ := by
  have hi := (d.onReflectedMeasure hparallel).radialEnergyQuotient_integrable
  have hc := hi.comp_measurable (frameReflectionEquiv g).measurable
  apply hc.congr
  filter_upwards [] with e
  change _ / normalizedBlockNorm (plusWeyl g (frameReflection e).base
    (frameReflection e).frame) = _
  rw [blockRadialEnergy_frameReflection, blockNorm_frameReflection]

theorem oppositeSqrtNormEnergyGap (d : MetricGreenData g μ)
    (hparallel : ParallelReflection d) :
    (4 / 9 : ℝ) * (∫ e,
      (‖blockRadialGradient (minusWeyl g e.base e.frame)
        (minusWeylGradient g e.base e.frame)‖ ^ 2 /
          normalizedBlockNorm (minusWeyl g e.base e.frame)) / 4 ∂μ) ≤
      (∫ e, normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2 ∂μ) -
        ∫ e, normalizedBlockNorm (minusWeyl g e.base e.frame) ∂μ := by
  have h := (d.onReflectedMeasure hparallel).sqrtNormEnergyGap
  rw [integral_reflectedMeasure, integral_reflectedMeasure, integral_reflectedMeasure] at h
  simpa only [blockRadialEnergy_frameReflection, blockNorm_frameReflection] using h

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! A pointwise spectral witness retains exactly the data used by the
coupled estimate. The witness is constructed from the actual matrices
and Bianchi gradient; it never requires a measurable spectral frame. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry
open Energy QuarticEnergy Quadratic Potential

noncomputable section

structure PointwiseSpectrum (A U : Mat) (Z : Angular.Gradient) (p : Vec) where
  frame : Mat
  orthogonal : frameᵀ * frame = 1
  shape : Shape
  diagonal : conjugateMatrix frame A =
    Matrix.diagonal (fun i => normalizedBlockNorm A * shape.s i)
  minimum : ℝ
  minimum_lower : 1 ≤ minimum
  minimum_upper : minimum ≤ 2
  cubic : shape.sigma = (3 * minimum - minimum ^ 3) / 2
  spectrum_lower : ∀ i, -minimum ≤ shape.s i
  spectrum_minimum : ∃ i, shape.s i = -minimum
  radial : Vec
  second : Vec
  third : Vec
  energy : (parameters shape radial second third).squaredNorm / 6 = weylGradientEnergy Z
  radial_norm : ‖radial‖ ^ 2 = ‖p‖ ^ 2
  original_radial_norm : ‖blockRadialGradient A Z‖ ^ 2 = ‖p‖ ^ 2
  matrix_energy : weylMatrixEnergy A Z =
    curvatureContraction shape (normalizedBlockNorm A) (parameters shape radial second third)
  hessian : invariantHessianForm A U Z ≤
    hessianTensorForm shape (normalizedBlockNorm A) (normalizedBlockNorm U) radial second third

/-- All fields, including the Hessian upper bound, come from the proved
finite-dimensional identities. -/
theorem pointwiseSpectrum_nonempty (A U : Mat) (Z : Angular.Gradient) (p : Vec)
    (hA : symmetric A) (htA : traceFree A) (hv : 0 < normalizedBlockNorm A)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0)
    (hp : ‖p‖ ^ 2 = ‖blockRadialGradient A Z‖ ^ 2) :
    Nonempty (PointwiseSpectrum A U Z p) := by
  obtain ⟨R, hR, ⟨P⟩, S, hdiag⟩ := exists_lifted_spectral_shape A hA htA hv
  obtain ⟨r, hr, hr2, hσ, hlo, hmin⟩ := shape_exists_minimum_parameter S
  obtain ⟨p', k, l, he, hrad, hB, hH⟩ :=
    invariantHessianForm_spectral_upper_of_frame A U Z R hR P S hdiag hv hs ht hb
  exact ⟨{
    frame := R
    orthogonal := hR
    shape := S
    diagonal := hdiag
    minimum := r
    minimum_lower := hr
    minimum_upper := hr2
    cubic := hσ
    spectrum_lower := hlo
    spectrum_minimum := hmin
    radial := p'
    second := k
    third := l
    energy := he
    radial_norm := hrad.trans hp.symm
    original_radial_norm := hp.symm
    matrix_energy := hB
    hessian := hH }⟩

namespace PointwiseSpectrum

variable {A U : Mat} {Z : Angular.Gradient} {p : Vec}

theorem energy_lower (D : PointwiseSpectrum A U Z p) :
    (5 / 3 : ℝ) * ‖p‖ ^ 2 ≤ weylGradientEnergy Z := by
  have h := D.energy
  rw [parameters_energy, D.radial_norm] at h
  nlinarith only [h, sq_nonneg ‖D.second‖, sq_nonneg ‖D.third‖]

theorem shape_sigma_upper (D : PointwiseSpectrum A U Z p) : D.shape.sigma ≤ 1 := by
  nlinarith only [D.shape.sigma_rho_circle, sq_nonneg D.shape.rho]

theorem shape_circle (D : PointwiseSpectrum A U Z p) :
    D.shape.rho ^ 2 = 1 - D.shape.sigma ^ 2 := by
  linarith only [D.shape.sigma_rho_circle]

theorem minimum_shift (D : PointwiseSpectrum A U Z p) :
    (A + (normalizedBlockNorm A * D.minimum) • (1 : Mat)).PosSemidef :=
  shape_minimum_shift_posSemidef A D.frame D.orthogonal D.shape _ D.minimum
    (normalizedBlockNorm_nonneg A) D.diagonal D.spectrum_lower

theorem minimum_le_shift (D : PointwiseSpectrum A U Z p) (x : ℝ)
    (hAx : (A + x • (1 : Mat)).PosSemidef) :
    normalizedBlockNorm A * D.minimum ≤ x :=
  shape_minimum_parameter_bound A D.frame D.orthogonal D.shape _ x D.minimum
    D.diagonal hAx D.spectrum_minimum

theorem scalar_norm (D : PointwiseSpectrum A U Z p) (hv : 0 < normalizedBlockNorm A) :
    scalarNormExpression 0 A Z =
      (weylGradientEnergy Z - ‖p‖ ^ 2) / normalizedBlockNorm A +
        6 * normalizedBlockNorm A * (1 - D.shape.sigma * normalizedBlockNorm A) := by
  rw [scalarNormExpression_spectral A D.frame D.orthogonal D.shape Z hv D.diagonal,
    D.original_radial_norm]

theorem trace_energy (D : PointwiseSpectrum A U Z p) :
    traceEnergy A = 30 * normalizedBlockNorm A ^ 2 *
      (1 - 2 * D.shape.sigma * normalizedBlockNorm A + normalizedBlockNorm A ^ 2) :=
  traceEnergy_spectral A D.frame D.orthogonal D.shape _ D.diagonal

end PointwiseSpectrum

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! Differentiation of a finite covariant tensor pullback. Rank induction
keeps the product rule and connection cancellation small at ranks four
through seven used by the actual Weyl fields. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

/-- First variation in the frame matrix, adding one covariant slot at a time. -/
def frameVariation : {n : ℕ} → Mat4 → Mat4 → CovariantCoordinates n →
    CovariantCoordinates n
  | 0, _, _, _ => 0
  | _n + 1, E, P, T => fun a =>
      (∑ b, P b (a 0) * frameTensor E (fun v => T (Fin.cons b v)) (fun k => a k.succ)) +
      ∑ b, E b (a 0) * frameVariation E P (fun v => T (Fin.cons b v)) (fun k => a k.succ)

theorem frameVariation_cons {n : ℕ} (E P : Mat4)
    (T : CovariantCoordinates (n + 1)) (i : Fin 4) (a : Fin n → Fin 4) :
    frameVariation E P T (Fin.cons i a) =
      (∑ b, P b i * frameTensor E (fun v => T (Fin.cons b v)) a) +
      ∑ b, E b i * frameVariation E P (fun v => T (Fin.cons b v)) a := rfl

private theorem connection_pairing (E P U C : Mat4) (h : E * C = P + U * E)
    (f : Fin 4 → ℝ) (i : Fin 4) :
    (∑ b, P b i * f b) + (∑ b, E b i * ∑ c, U c b * f c) =
      ∑ b, C b i * ∑ c, E c b * f c := by
  have hp : (∑ b, E b i * ∑ c, U c b * f c) =
      ∑ c, (U * E) c i * f c := by
    simp only [Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  have hc : (∑ b, C b i * ∑ c, E c b * f c) =
      ∑ c, (E * C) c i * f c := by
    simp only [Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  rw [hp, hc, h]
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]

/-- The derivative of the frame precisely cancels the difference between
the source and target connection coefficients. -/
theorem frameVariation_connection {n : ℕ} (E P U C : Mat4)
    (h : E * C = P + U * E) (T : CovariantCoordinates n) :
    frameVariation E P T + frameTensor E (tensorSlotAction U T) =
      tensorSlotAction C (frameTensor E T) := by
  induction n with
  | zero =>
    funext a
    simp [frameVariation, tensorSlotAction, frameTensor]
  | succ n ih =>
    funext a
    obtain ⟨i, v, rfl⟩ := Fin.exists_cons a
    let F (b : Fin 4) : CovariantCoordinates n := fun w => T (Fin.cons b w)
    have hU (b : Fin 4) :
        frameTensor E (fun w => tensorSlotAction U T (Fin.cons b w)) v =
          (∑ c, U c b * frameTensor E (F c) v) +
            frameTensor E (tensorSlotAction U (F b)) v := by
      have he : (fun w => tensorSlotAction U T (Fin.cons b w)) =
          (fun w => ∑ c, U c b * F c w) + tensorSlotAction U (F b) := by
        funext w
        exact tensorSlotAction_cons U T b w
      rw [he, frameTensor_add, frameTensor_sum]
      simp only [frameTensor_const_mul]
    have hC : tensorSlotAction C (fun w => frameTensor E T (Fin.cons i w)) v =
        ∑ b, E b i * tensorSlotAction C (frameTensor E (F b)) v := by
      have he : (fun w => frameTensor E T (Fin.cons i w)) =
          fun w => ∑ b, E b i * frameTensor E (F b) w := by
        funext w
        exact frameTensor_cons E T i w
      rw [he, tensorSlotAction_sum]
      simp only [tensorSlotAction_const_mul]
    have hV (b : Fin 4) : frameVariation E P (F b) v +
        frameTensor E (tensorSlotAction U (F b)) v =
          tensorSlotAction C (frameTensor E (F b)) v := congrFun (ih (F b)) v
    change frameVariation E P T (Fin.cons i v) +
      frameTensor E (tensorSlotAction U T) (Fin.cons i v) = _
    rw [frameVariation_cons, frameTensor_cons, tensorSlotAction_cons]
    simp only [hU, mul_add, Finset.sum_add_distrib]
    rw [hC]
    have hsum := connection_pairing E P U C h (fun b => frameTensor E (F b) v) i
    have hrem : (∑ b, E b i * frameVariation E P (F b) v) +
        (∑ b, E b i * frameTensor E (tensorSlotAction U (F b)) v) =
          ∑ b, E b i * tensorSlotAction C (frameTensor E (F b)) v := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      rw [← mul_add, hV b]
    simp only [frameTensor_cons]
    linarith only [hsum, hrem]

theorem frameTensor_differentiableAt {n : ℕ} (E : FourSpace → Mat4)
    (T : FourSpace → CovariantCoordinates n) (z : FourSpace)
    (hE : ∀ i j, DifferentiableAt ℝ (fun w => E w i j) z)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) z)
    (a : Fin n → Fin 4) :
    DifferentiableAt ℝ (fun w => frameTensor (E w) (T w) a) z := by
  unfold frameTensor
  apply DifferentiableAt.fun_sum
  intro b _
  exact (HasFDerivAt.finsetProd (fun k _ => (hE (b k) (a k)).hasFDerivAt)).differentiableAt.mul
    (hT b)

private theorem pullback_partial_sum {ι : Type*} [Fintype ι]
    (F : ι → FourSpace → ℝ) (z : FourSpace)
    (hF : ∀ a, DifferentiableAt ℝ (F a) z) (i : Fin 4) :
    partialDeriv (fun w => ∑ a, F a w) i z = ∑ a, partialDeriv (F a) i z := by
  unfold partialDeriv
  rw [fderiv_fun_sum (u := Finset.univ) (A := F) (fun a _ => hF a), _root_.sum_apply]

private theorem pullback_partial_mul {f h : FourSpace → ℝ} {z : FourSpace}
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) (i : Fin 4) :
    partialDeriv (fun w => f w * h w) i z =
      partialDeriv f i z * h z + f z * partialDeriv h i z := by
  simp only [partialDeriv, fderiv_fun_mul hf hh, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

theorem tensorPartial_frameTensor {n : ℕ} (E : FourSpace → Mat4)
    (T : FourSpace → CovariantCoordinates n) (z : FourSpace)
    (hE : ∀ i j, DifferentiableAt ℝ (fun w => E w i j) z)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) z) (i : Fin 4) :
    tensorPartial (fun w => frameTensor (E w) (T w)) i z =
      frameVariation (E z) (matrixPartial E i z) (T z) +
        frameTensor (E z) (tensorPartial T i z) := by
  induction n with
  | zero =>
    funext a
    simp [tensorPartial, frameTensor, frameVariation]
  | succ n ih =>
    funext a
    obtain ⟨j, v, rfl⟩ := Fin.exists_cons a
    let F (b : Fin 4) (w : FourSpace) : CovariantCoordinates n := fun a => T w (Fin.cons b a)
    have hF (b : Fin 4) (a : Fin n → Fin 4) :
        DifferentiableAt ℝ (fun w => F b w a) z := hT _
    have hprod (b : Fin 4) : DifferentiableAt ℝ
        (fun w => E w b j * frameTensor (E w) (F b w) v) z :=
      (hE b j).mul (frameTensor_differentiableAt E (F b) z hE (hF b) v)
    have hd (b : Fin 4) :
        partialDeriv (fun w => E w b j * frameTensor (E w) (F b w) v) i z =
          matrixPartial E i z b j * frameTensor (E z) (F b z) v +
            E z b j * (frameVariation (E z) (matrixPartial E i z) (F b z) v +
              frameTensor (E z) (tensorPartial (F b) i z) v) := by
      rw [pullback_partial_mul (hE b j)
        (frameTensor_differentiableAt E (F b) z hE (hF b) v)]
      have hv := congrFun (ih (F b) (hF b)) v
      change partialDeriv (fun w => E w b j) i z * _ + E z b j * _ = _
      rw [show partialDeriv (fun w => frameTensor (E w) (F b w) v) i z = _ from hv]
      rfl
    change partialDeriv (fun w => frameTensor (E w) (T w) (Fin.cons j v)) i z = _
    simp only [frameTensor_cons]
    rw [pullback_partial_sum _ z hprod i]
    simp only [hd, frameVariation_cons, Pi.add_apply, mul_add, Finset.sum_add_distrib,
      frameTensor_cons, tensorPartial, F]
    simp only [add_assoc]
    rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The differentiated Bianchi constraint for the actual Weyl Hessian
follows from the tensor identity and its zero Ricci contraction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem actual_plusWeylHessian_bianchi_components (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (d : Fin 4) (r : Fin 3) (i : Fin 4) :
    gradientDivergence (plusWeylHessian g c e d) r i = 0 := by
  let H := frameTensor e.matrix
    (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))
      (chartAt FourSpace c c))
  let T : CovariantCoordinates 5 := fun b => H (Fin.cons d b)
  have hs := frame_normalizedWeyl_hessian_symmetries g c e d
  have hR (a j k : Fin 4) : (∑ l, T ![a, l, j, k, l]) = 0 :=
    frame_normalizedWeyl_hessian_trace_zero e hRic d a j k
  exact gradientBlock_divergence_of_ricci_parallel T
    (fun a => (hs a).1) (fun a => (hs a).2.1) (fun a => (hs a).2.2)
    (frame_normalizedWeyl_hessian_differentialBianchi g c e d) hR r i

theorem actual_minusWeylHessian_bianchi_components (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (d : Fin 4) (r : Fin 3) (i : Fin 4) :
    (∑ s, ∑ j, Angular.oppositeMatrix s i j * minusWeylHessian g c e d j s r) = 0 := by
  let H := frameTensor e.matrix
    (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))
      (chartAt FourSpace c c))
  let T : CovariantCoordinates 5 := fun b => H (Fin.cons d b)
  have hs := frame_normalizedWeyl_hessian_symmetries g c e d
  have hR (a j k : Fin 4) : (∑ l, T ![a, l, j, k, l]) = 0 :=
    frame_normalizedWeyl_hessian_trace_zero e hRic d a j k
  exact opposite_gradientBlock_divergence_of_ricci_parallel T
    (fun a => (hs a).1) (fun a => (hs a).2.1) (fun a => (hs a).2.2)
    (frame_normalizedWeyl_hessian_differentialBianchi g c e d) hR r i

theorem actual_plusWeylHessian_bianchi (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (d : Fin 4) (r : Fin 3) :
    HighestHessian.divergence (plusWeylHessian g c e) d r = 0 := by
  ext i
  have h := actual_plusWeylHessian_bianchi_components e hRic d r i
  change (∑ s, Bianchi.quaternion s
    (WithLp.toLp 2 (fun j => plusWeylHessian g c e d j s r))) i = 0
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  simp_rw [← TraceHessian.quaternionMatrix_apply]
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual rank-five commutator includes the curvature action on the
leading covector slot of the Weyl gradient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem gradientBlock_negative_slotAction (B : Mat4) (T : CovariantCoordinates 5)
    (Q : Fin 3 → Mat4) (j : Fin 4) :
    gradientBlock (-tensorSlotAction B T) Q j =
      blockCoordinates (-tensorSlotAction B (fun a => T (Fin.cons j a))) Q -
        ∑ r, B r j • gradientBlock T Q r := by
  have hT : (fun a => (-tensorSlotAction B T) (Fin.cons j a)) =
      -tensorSlotAction B (fun a => T (Fin.cons j a)) -
        ∑ r, B r j • (fun a => T (Fin.cons r a)) := by
    funext a
    simp only [Pi.neg_apply, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [tensorSlotAction_cons]
    ring
  have hh := congrArg (blockCoordinatesLinear Q) hT
  rw [map_sub, map_sum] at hh
  simp only [map_smul] at hh
  exact hh

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

/-- The outer Ricci commutation formula is derived from the actual
Levi-Civita action on all five slots, including the gradient covector. -/
theorem actual_plusWeylThird_outerCommutator (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (i k j : Fin 4) :
    plusWeylThirdDerivative g c e i k j - plusWeylThirdDerivative g c e k i j =
      bundleCurvatureAction (plusWeyl g c e) i k (plusWeylGradient g c e j) +
        ∑ a, frameCurvature g c e i k a j • plusWeylGradient g c e a := by
  let z : FourSpace := chartAt FourSpace c c
  let T : CovariantCoordinates 5 := covariantDerivative g c (normalizedWeylCoordinates g c) z
  let X : CovariantCoordinates 7 := covariantDerivative g c
    (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))) z
  let C : Fin 4 → Fin 4 → Mat4 := fun p q => coordinateCurvatureMatrix g c p q z
  have hz : z ∈ (chartAt FourSpace c).target := (chartAt FourSpace c).map_source
    (mem_chart_source FourSpace c)
  have hdet : (metricInChart g c z).det ≠ 0 :=
    (metricInChart_posDef g c z hz).det_pos.ne'
  have hX (p q : Fin 4) (v : Fin 5 → Fin 4) :
      X (Fin.cons p (Fin.cons q v)) - X (Fin.cons q (Fin.cons p v)) =
        -tensorSlotAction (C p q) T v :=
    normalizedWeyl_gradient_commutator g c z hz hdet p q v
  have hc : e.matrix⁻¹ * pulledCurvatureEndomorphism e.matrix C i k * e.matrix =
      curvatureEndomorphism (Angular.einsteinCurvatureTensor
        (plusWeyl g c e) (minusWeyl g c e)) i k := by
    rw [frame_curvatureEndomorphism, actual_einstein_decomposition e hRic]
  have he : (fun v => frameTensor e.matrix X (Fin.cons i (Fin.cons k v))) -
      (fun v => frameTensor e.matrix X (Fin.cons k (Fin.cons i v))) =
        -tensorSlotAction (curvatureEndomorphism (Angular.einsteinCurvatureTensor
          (plusWeyl g c e) (minusWeyl g c e)) i k) (frameTensor e.matrix T) := by
    funext v
    have hh := framed_tensor_commutator e.matrix (isUnit_iff_ne_zero.mpr e.det_ne_zero)
      C T X hX i k v
    rw [hc] at hh
    exact hh
  have hb := congrArg (fun S : CovariantCoordinates 5 =>
    blockCoordinatesLinear quaternionMatrix (fun a => S (Fin.cons j a))) he
  change blockCoordinatesLinear quaternionMatrix
    ((fun a => frameTensor e.matrix X (Fin.cons i (Fin.cons k (Fin.cons j a)))) -
      (fun a => frameTensor e.matrix X (Fin.cons k (Fin.cons i (Fin.cons j a))))) =
    gradientBlock (-tensorSlotAction (curvatureEndomorphism (Angular.einsteinCurvatureTensor
      (plusWeyl g c e) (minusWeyl g c e)) i k) (frameTensor e.matrix T)) quaternionMatrix j at hb
  rw [map_sub, gradientBlock_negative_slotAction,
    blockCoordinates_einstein_curvature_action] at hb
  have hr (r : Fin 4) :
      curvatureEndomorphism (Angular.einsteinCurvatureTensor
        (plusWeyl g c e) (minusWeyl g c e)) i k r j =
        -frameCurvature g c e i k r j := by
    change Angular.einsteinCurvatureTensor (plusWeyl g c e) (minusWeyl g c e) i k j r = _
    rw [← actual_einstein_decomposition e hRic]
    exact frameCurvature_last_skew e i k j r
  simp only [hr, neg_smul, Finset.sum_neg_distrib, sub_neg_eq_add] at hb
  exact hb

end
end PositiveEinsteinFour.Geometry
end


section

/-! Normal-frame changes and their exact Frobenius invariants. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped Manifold ContDiff BigOperators

noncomputable section

local instance frameNormalFrobenius : NormedAddCommGroup Mat3 :=
  Matrix.frobeniusNormedAddCommGroup

/-- The normal restriction of a bilinear form written in coordinate components. -/
def normalRestriction (E K : Mat4) : Mat3 :=
  (Eᵀ * K * E).submatrix Fin.succ Fin.succ

/-- Restrict a full frame change to the three normal vectors. -/
def normalChange (P : Mat4) : Mat3 := P.submatrix Fin.succ Fin.succ

theorem normalChange_orthogonal (P : Mat4) (hP : Pᵀ * P = 1)
    (h0 : ∀ i, P i 0 = if i = 0 then 1 else 0) :
    (normalChange P)ᵀ * normalChange P = 1 := by
  have hrow (j : Fin 4) : P 0 j = if (0 : Fin 4) = j then 1 else 0 := by
    have h := congrArg (fun A : Mat4 => A 0 j) hP
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, h0, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Matrix.one_apply] using h
  ext i j
  have hz (k : Fin 3) : ¬(0 : Fin 4) = k.succ := Ne.symm (Fin.succ_ne_zero k)
  have h := congrArg (fun A : Mat4 => A i.succ j.succ) hP
  simpa only [normalChange, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.submatrix_apply, Fin.sum_univ_succ, hrow, hz, ite_false,
    zero_mul, zero_add, Matrix.one_apply, Fin.succ_inj] using h

theorem normalRestriction_conjugate (E K P : Mat4)
    (hrow : ∀ j, P 0 j = if (0 : Fin 4) = j then 1 else 0) :
    normalRestriction (E * P) K =
      (normalChange P)ᵀ * normalRestriction E K * normalChange P := by
  have hfull : (E * P)ᵀ * K * (E * P) = Pᵀ * (Eᵀ * K * E) * P := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  ext i j
  have hz (k : Fin 3) : ¬(0 : Fin 4) = k.succ := Ne.symm (Fin.succ_ne_zero k)
  change ((E * P)ᵀ * K * (E * P)) i.succ j.succ = _
  rw [hfull]
  simp only [normalRestriction, normalChange, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.submatrix_apply, Fin.sum_univ_succ,
    hrow, hz, ite_false, zero_mul, mul_zero, zero_add]

theorem conjugate_frobenius_norm_sq (V A : Mat3) (hV : Vᵀ * V = 1) :
    ‖Vᵀ * A * V‖ ^ 2 = ‖A‖ ^ 2 := by
  have h := QuaternionFrame.conjugateMatrix_pairing V (mul_eq_one_comm.mp hV) A A
  rw [← squareNorm_eq_frobenius_norm_sq, ← squareNorm_eq_frobenius_norm_sq]
  simpa only [QuaternionFrame.conjugateMatrix, matrixPairing, Angular.squareNorm, pow_two]
    using h

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

/-- Coordinates of the second frame in the first. -/
def OrthonormalFrame.changeMatrix (e f : OrthonormalFrame g c) : Mat4 :=
  e.matrix⁻¹ * f.matrix

theorem OrthonormalFrame.mul_changeMatrix (e f : OrthonormalFrame g c) :
    e.matrix * e.changeMatrix f = f.matrix := by
  rw [OrthonormalFrame.changeMatrix, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr e.det_ne_zero), Matrix.one_mul]

theorem OrthonormalFrame.changeMatrix_orthogonal (e f : OrthonormalFrame g c) :
    (e.changeMatrix f)ᵀ * e.changeMatrix f = 1 := by
  calc
    _ = (e.changeMatrix f)ᵀ * (e.matrixᵀ * chartMetric g c * e.matrix) *
        e.changeMatrix f := by rw [e.orthonormal, Matrix.mul_one]
    _ = (e.matrix * e.changeMatrix f)ᵀ * chartMetric g c *
        (e.matrix * e.changeMatrix f) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [e.mul_changeMatrix f]; exact f.orthonormal

theorem OrthonormalFrame.changeMatrix_first (e f : OrthonormalFrame g c)
    (hfirst : e.vector 0 = f.vector 0) (i : Fin 4) :
    e.changeMatrix f i 0 = if i = 0 then 1 else 0 := by
  have hcol (j : Fin 4) : f.matrix j 0 = e.matrix j 0 := by
    exact (congrArg (fun v : FourSpace => v j) hfirst).symm
  have h := congrArg (fun A : Mat4 => A i 0)
    (Matrix.nonsing_inv_mul e.matrix (isUnit_iff_ne_zero.mpr e.det_ne_zero))
  simpa only [OrthonormalFrame.changeMatrix, Matrix.mul_apply, hcol,
    Matrix.one_apply] using h

theorem normalRestriction_same_direction (e f : OrthonormalFrame g c)
    (hfirst : e.vector 0 = f.vector 0) (K : Mat4) :
    normalRestriction f.matrix K =
      (normalChange (e.changeMatrix f))ᵀ * normalRestriction e.matrix K *
        normalChange (e.changeMatrix f) := by
  have hrow (j : Fin 4) : e.changeMatrix f 0 j = if (0 : Fin 4) = j then 1 else 0 := by
    have h := congrArg (fun A : Mat4 => A 0 j) (e.changeMatrix_orthogonal f)
    simpa only [Matrix.mul_apply, Matrix.transpose_apply,
      e.changeMatrix_first f hfirst, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.one_apply] using h
  calc
    _ = normalRestriction (e.matrix * e.changeMatrix f) K := by
      rw [e.mul_changeMatrix f]
    _ = _ := normalRestriction_conjugate _ _ _ hrow

theorem normalRestriction_norm_sq_same_direction (e f : OrthonormalFrame g c)
    (hfirst : e.vector 0 = f.vector 0) (K : Mat4) :
    ‖normalRestriction e.matrix K‖ ^ 2 = ‖normalRestriction f.matrix K‖ ^ 2 := by
  rw [normalRestriction_same_direction e f hfirst]
  exact (conjugate_frobenius_norm_sq _ _
    (normalChange_orthogonal _ (e.changeMatrix_orthogonal f)
      (e.changeMatrix_first f hfirst))).symm

theorem normalRestriction_sub_one_norm_sq_same_direction
    (e f : OrthonormalFrame g c) (hfirst : e.vector 0 = f.vector 0) (K : Mat4) :
    ‖normalRestriction e.matrix K - 1‖ ^ 2 =
      ‖normalRestriction f.matrix K - 1‖ ^ 2 := by
  let V := normalChange (e.changeMatrix f)
  have hV : Vᵀ * V = 1 := normalChange_orthogonal _
    (e.changeMatrix_orthogonal f) (e.changeMatrix_first f hfirst)
  have heq : normalRestriction f.matrix K - 1 =
      Vᵀ * (normalRestriction e.matrix K - 1) * V := by
    rw [normalRestriction_same_direction e f hfirst]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV]
    rfl
  rw [heq]
  exact (conjugate_frobenius_norm_sq _ _ hV).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exchanged polynomial test in (18), obtained from the proved
plus-block test by the actual frame reflection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem regularizedKappaDerivative_smul (ε : ℝ) (A B Z V : Mat) (c : ℝ) :
    regularizedKappaDerivative ε A B (c • Z) (c • V) =
      c * regularizedKappaDerivative ε A B Z V := by
  unfold regularizedKappaDerivative
  rw [regularizedRadialDerivative_smul, regularizedRadialDerivative_smul]
  ring

def kappaNormIntegrand (A B : Mat) (Z V : Angular.Gradient) : ℝ :=
  regularizedKappa 0 A B * scalarNormExpression 0 A Z +
    ∑ i, regularizedKappaDerivative 0 A B (Z i) (V i) * regularizedRadialDerivative 0 A (Z i)

theorem kappaNormIntegrand_reflected (A B : Mat) (Z V : Angular.Gradient) :
    kappaNormIntegrand A B (reflectedGradient Z) (reflectedGradient V) =
      kappaNormIntegrand A B Z V := by
  unfold kappaNormIntegrand
  rw [scalarNormExpression_reflected]
  apply congrArg (fun z : ℝ => regularizedKappa 0 A B * scalarNormExpression 0 A Z + z)
  apply Finset.sum_congr rfl
  intro i _
  simp only [reflectedGradient, regularizedKappaDerivative_smul, regularizedRadialDerivative_smul]
  calc
    _ = orientationSign i ^ 2 * (regularizedKappaDerivative 0 A B (Z i) (V i) *
        regularizedRadialDerivative 0 A (Z i)) := by ring
    _ = _ := by rw [orientationSign_sq, one_mul]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem kappaNormIntegrand_frameReflection (e : FrameBundle g) :
    kappaNormIntegrand (plusWeyl g (frameReflection e).base (frameReflection e).frame)
      (minusWeyl g (frameReflection e).base (frameReflection e).frame)
      (plusWeylGradient g (frameReflection e).base (frameReflection e).frame)
      (minusWeylGradient g (frameReflection e).base (frameReflection e).frame) =
    kappaNormIntegrand (minusWeyl g e.base e.frame) (plusWeyl g e.base e.frame)
      (minusWeylGradient g e.base e.frame) (plusWeylGradient g e.base e.frame) := by
  have hp : plusWeylGradient g e.base e.frame.reflect =
      reflectedGradient (minusWeylGradient g e.base e.frame) := by
    funext i
    exact plusWeylGradient_reflect g e.base e.frame i
  have hm : minusWeylGradient g e.base e.frame.reflect =
      reflectedGradient (plusWeylGradient g e.base e.frame) := by
    funext i
    exact minusWeylGradient_reflect g e.base e.frame i
  change kappaNormIntegrand (plusWeyl g e.base e.frame.reflect)
    (minusWeyl g e.base e.frame.reflect) (plusWeylGradient g e.base e.frame.reflect)
      (minusWeylGradient g e.base e.frame.reflect) = _
  rw [plusWeyl_reflect, minusWeyl_reflect, hp, hm, kappaNormIntegrand_reflected]

theorem FrameReflectionData.opposite_kappaTest {d : MetricGreenData g μ}
    (r : FrameReflectionData d) (o : OppositeWeylData d)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    (∫ e, kappaNormIntegrand (minusWeyl g e.base e.frame) (plusWeyl g e.base e.frame)
      (minusWeylGradient g e.base e.frame) (plusWeylGradient g e.base e.frame) ∂μ) = 0 := by
  let F : FrameBundle g → ℝ := fun e => kappaNormIntegrand (plusWeyl g e.base e.frame)
    (minusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) (minusWeylGradient g e.base e.frame)
  have hF : (∫ e, F e ∂μ) = 0 := d.kappaTest o hpinch
  rw [← r.integral_reflection F] at hF
  refine Eq.trans (b := ∫ e, F (frameReflection e) ∂μ) ?_ hF
  apply integral_congr_ae
  filter_upwards [] with e
  exact (kappaNormIntegrand_frameReflection e).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact cancellation of the two weak norm equations with the
deficit-weighted energy equation. All fields are the actual Weyl fields. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace MetricGreenData

def deficitField (d : MetricGreenData g μ) (o : OppositeWeylData d) : C(FrameBundle g, ℝ) :=
  ⟨fun e => regularizedDeficit 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame),
    (continuous_const.sub ((continuous_regularizedBlockNorm 0).comp d.continuousWeyl)).sub
      ((continuous_regularizedBlockNorm 0).comp o.continuousWeyl)⟩

def jointScalarNorm (_d : MetricGreenData g μ) (e : FrameBundle g) : ℝ :=
  scalarNormExpression 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) +
  scalarNormExpression 0 (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)

def jointEnergyLaplacian (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  d.energyLaplacianField + d.oppositeEnergyLaplacianField

end MetricGreenData

namespace FrameReflectionData

variable {d : MetricGreenData g μ} (r : FrameReflectionData d)
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

include r

theorem jointScalarNorm_integrable : Integrable d.jointScalarNorm μ :=
  d.scalarNorm_integrable.add r.opposite_scalarNorm_integrable

theorem jointEnergyCancellation (o : OppositeWeylData d)
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    (∫ e, d.deficitField o e * d.jointEnergyLaplacian e +
      d.totalEnergyField e * d.jointScalarNorm e ∂μ) = 0 := by
  let N : FrameBundle g → ℝ := fun e => d.totalEnergyField e * d.jointScalarNorm e +
    ∑ i, d.totalEnergyDerivativeField i e *
      (regularizedRadialDerivative 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame i) +
       regularizedRadialDerivative 0 (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame i))
  let Q : FrameBundle g → ℝ := fun e => d.deficitField o e * d.jointEnergyLaplacian e +
    ∑ i, regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
      d.totalEnergyDerivativeField i e
  have hn : (∫ e, N e ∂μ) = 0 := r.jointNormEnergyEquation
  have hq : (∫ e, Q e ∂μ) = 0 := r.jointDeficitEnergyEquation o hpinch
  have hni : Integrable N μ :=
    (integrable_continuous_weight r.jointScalarNorm_integrable d.totalEnergyField).add
      (integrable_finsetSum _ (fun i _ => integrable_continuous_weight
        ((d.radial_integrable i).add (r.opposite_radial_integrable i))
          (d.totalEnergyDerivativeField i)))
  have hqi : Integrable Q μ :=
    r.deficitEnergy_integrable o d.jointEnergyLaplacian d.totalEnergyDerivativeField
  have hsum : (∫ e, N e + Q e ∂μ) = 0 := by
    rw [integral_add hni hqi, hn, hq, add_zero]
  convert! hsum using 1
  apply integral_congr_ae
  filter_upwards [] with e
  dsimp only [N, Q]
  have hc : (∑ i, d.totalEnergyDerivativeField i e *
      (regularizedRadialDerivative 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame i) +
       regularizedRadialDerivative 0 (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame i))) +
      (∑ i, regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
        d.totalEnergyDerivativeField i e) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    unfold regularizedDeficitDerivative
    ring
  linarith only [hc]

end FrameReflectionData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Differentiate the proved Weyl Hessian commutator along parallel frames.
Only the ordinary derivative identities already present in the flow data are used. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance parallelInnerNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance parallelInnerNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance parallelInnerNormedAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

private def matrixActionLinear (s : Fin 3) : Mat →ₗ[ℝ] Mat where
  toFun A := matrixAction s A
  map_add' A B := by
    ext a b
    simp only [matrixAction, Matrix.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    ring
  map_smul' r A := by
    ext a b
    simp only [matrixAction, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring

private def matrixActionCLM (s : Fin 3) : Mat →L[ℝ] Mat :=
  (matrixActionLinear s).toContinuousLinearMap

private def matrixEntryLinear (a b : Fin 3) : Mat →ₗ[ℝ] ℝ where
  toFun A := A a b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def matrixEntryCLM (a b : Fin 3) : Mat →L[ℝ] ℝ :=
  (matrixEntryLinear a b).toContinuousLinearMap

private theorem hasDerivAt_matrixAction {T : ℝ → Mat} {Z : Mat} {t : ℝ}
    (hT : HasDerivAt T Z t) (s : Fin 3) :
    HasDerivAt (fun r => matrixAction s (T r)) (matrixAction s Z) t := by
  exact (matrixActionCLM s).hasFDerivAt.comp_hasDerivAt t hT

private theorem parallel_hasDerivAt_entry {T : ℝ → Mat} {Z : Mat} {t : ℝ}
    (hT : HasDerivAt T Z t) (a b : Fin 3) :
    HasDerivAt (fun r => T r a b) (Z a b) t := by
  exact (matrixEntryCLM a b).hasFDerivAt.comp_hasDerivAt t hT

/-- Product differentiation in the matrix bundle, without an eigenframe. -/
theorem hasDerivAt_bundleCurvatureSelf {T : ℝ → Mat} {Z : Mat} {t : ℝ}
    (hT : HasDerivAt T Z t) (i j : Fin 4) :
    HasDerivAt (fun r => bundleCurvatureAction (T r) i j (T r))
      (bundleCurvatureDerivative Z i j (T t) + bundleCurvatureAction (T t) i j Z) t := by
  have hs (r s : Fin 3) := (parallel_hasDerivAt_entry hT r s).smul
    (hasDerivAt_matrixAction hT s)
  have hr (r : Fin 3) := ((hasDerivAt_matrixAction hT r).add
    (HasDerivAt.fun_sum (u := Finset.univ) (fun s _ => hs r s))).const_smul (quaternionMatrix r i j)
  have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun r _ => hr r)).const_smul (1 / 2 : ℝ)
  let D : Mat := (1 / 2 : ℝ) • ∑ r, quaternionMatrix r i j •
    (matrixAction r Z + ∑ s, (T t r s • matrixAction s Z + Z r s • matrixAction s (T t)))
  change HasDerivAt (fun r => bundleCurvatureAction (T r) i j (T r)) D t at hd
  have hD : D = bundleCurvatureDerivative Z i j (T t) +
      bundleCurvatureAction (T t) i j Z := by
    ext a b
    simp only [D, bundleCurvatureDerivative, bundleCurvatureAction, Matrix.smul_apply,
      Matrix.sum_apply, Matrix.add_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum]
    ring
  rwa [hD] at hd

/-- A pointwise Hessian commutator can be differentiated using only its
parallel derivative fields. -/
theorem inner_commutator_of_derivatives
    (T : ℝ → Mat) (X : ℝ → Hessian) (Z : Mat) (V : Fin 4 → Fin 4 → Mat)
    (t : ℝ) (k j : Fin 4)
    (hcomm : ∀ r, X r k j - X r j k = bundleCurvatureAction (T r) k j (T r))
    (hT : HasDerivAt T Z t)
    (hXkj : HasDerivAt (fun r => X r k j) (V k j) t)
    (hXjk : HasDerivAt (fun r => X r j k) (V j k) t) :
    V k j - V j k =
      bundleCurvatureDerivative Z k j (T t) + bundleCurvatureAction (T t) k j Z := by
  have he : (fun r => X r k j - X r j k) =
      fun r => bundleCurvatureAction (T r) k j (T r) := funext hcomm
  have hd := hXkj.sub hXjk
  change HasDerivAt (fun r => X r k j - X r j k) (V k j - V j k) t at hd
  rw [he] at hd
  exact hd.unique (hasDerivAt_bundleCurvatureSelf hT k j)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The inner commutator in the Green formula is forced by the actual
Hessian identity and the existing ordinary parallel-frame derivatives. -/
theorem actual_plusWeylThird_innerCommutator
    (g : SmoothMetric M) (hRic : RicciThree g) {μ : Measure (FrameBundle g)}
    (φ : Fin 4 → FrameFlow g μ)
    (hT : ∀ i t e, HasDerivAt
      (fun r => plusWeyl g ((φ i).map r e).base ((φ i).map r e).frame)
      (plusWeylGradient g ((φ i).map t e).base ((φ i).map t e).frame i) t)
    (hX : ∀ i k j t e, HasDerivAt
      (fun r => plusWeylHessian g ((φ i).map r e).base ((φ i).map r e).frame k j)
      (plusWeylThirdDerivative g ((φ i).map t e).base ((φ i).map t e).frame i k j) t)
    (e : FrameBundle g) (i k j : Fin 4) :
    plusWeylThirdDerivative g e.base e.frame i k j -
        plusWeylThirdDerivative g e.base e.frame i j k =
      bundleCurvatureDerivative (plusWeylGradient g e.base e.frame i) k j
        (plusWeyl g e.base e.frame) +
      bundleCurvatureAction (plusWeyl g e.base e.frame) k j
        (plusWeylGradient g e.base e.frame i) := by
  obtain ⟨e₀, he⟩ := ((φ i).map 0).surjective e
  change (φ i).map 0 e₀ = e at he
  have hc (r : ℝ) :
      plusWeylHessian g ((φ i).map r e₀).base ((φ i).map r e₀).frame k j -
        plusWeylHessian g ((φ i).map r e₀).base ((φ i).map r e₀).frame j k =
      bundleCurvatureAction (plusWeyl g ((φ i).map r e₀).base ((φ i).map r e₀).frame)
        k j (plusWeyl g ((φ i).map r e₀).base ((φ i).map r e₀).frame) := by
    ext a b
    exact actual_plusWeylHessian_commutator _ hRic k j a b
  have hh := inner_commutator_of_derivatives
    (fun r => plusWeyl g ((φ i).map r e₀).base ((φ i).map r e₀).frame)
    (fun r => plusWeylHessian g ((φ i).map r e₀).base ((φ i).map r e₀).frame)
    (plusWeylGradient g ((φ i).map 0 e₀).base ((φ i).map 0 e₀).frame i)
    (fun k j => plusWeylThirdDerivative g ((φ i).map 0 e₀).base ((φ i).map 0 e₀).frame i k j)
    0 k j hc (hT i 0 e₀) (hX i k j 0 e₀) (hX i j k 0 e₀)
  rw [he] at hh
  exact hh

end
end PositiveEinsteinFour.Geometry
end


section

/-! Zero-axis extensions require the gradient to vanish at the zero
block. This is the almost-everywhere property proved separately from
the actual frame flow; it is not inferred from the block value alone. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry
open Energy QuarticEnergy Quadratic Potential

noncomputable section

theorem zero_gradient_energy : weylGradientEnergy (0 : Angular.Gradient) = 0 := by
  simp [weylGradientEnergy, matrixPairing]

theorem zero_gradient_matrix_energy (A : Mat) :
    weylMatrixEnergy A (0 : Angular.Gradient) = 0 := by
  simp [weylMatrixEnergy, matrixPairing]

theorem zero_gradient_radial (A : Mat) :
    blockRadialGradient A (0 : Angular.Gradient) = 0 := by
  ext i
  simp [blockRadialGradient, regularizedRadialDerivative]

theorem zero_gradient_hessian_nonpos (A U : Mat) :
    invariantHessianForm A U (0 : Angular.Gradient) ≤ 0 := by
  have he : 0 ≤ weylCompressionEnergy A (0 : Angular.Gradient) := by
    unfold weylCompressionEnergy
    exact div_nonneg (rawPairing_self_nonneg _) (by norm_num)
  have hr : weylRadialSquare A (0 : Angular.Gradient) = 0 := by
    simp [weylRadialSquare]
  unfold invariantHessianForm
  rw [zero_gradient_energy, zero_gradient_matrix_energy, zero_gradient_matrix_energy, hr]
  nlinarith only [he]

theorem pointwiseSpectrum_zero (U : Mat) :
    Nonempty (PointwiseSpectrum 0 U (0 : Angular.Gradient) (0 : Vec)) := by
  have hv : normalizedBlockNorm (0 : Mat) = 0 :=
    (normalizedBlockNorm_eq_zero_iff _).mpr rfl
  refine ⟨{
    frame := 1
    orthogonal := by simp
    shape := costShape
    diagonal := by simp [conjugateMatrix, hv]
    minimum := 1
    minimum_lower := le_rfl
    minimum_upper := by norm_num
    cubic := by norm_num [Shape.sigma, costShape, Fin.sum_univ_three]
    spectrum_lower := by intro i; fin_cases i <;> norm_num [costShape]
    spectrum_minimum := ⟨0, by norm_num [costShape]⟩
    radial := 0
    second := 0
    third := 0
    energy := by rw [parameters_energy, zero_gradient_energy]; simp
    radial_norm := rfl
    original_radial_norm := by rw [zero_gradient_radial]
    matrix_energy := by
      rw [zero_gradient_matrix_energy, curvatureContraction_parameters]
      simp
    hessian := ?_ }⟩
  have hh := zero_gradient_hessian_nonpos (0 : Mat) U
  simpa only [hessianTensor_matrix, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    inner_zero_left, inner_zero_right, mul_zero, add_zero, sub_zero] using hh

theorem pointwiseSpectrum_nonempty_closed (A U : Mat) (Z : Angular.Gradient) (p : Vec)
    (hA : symmetric A) (htA : traceFree A)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0)
    (hp : ‖p‖ ^ 2 = ‖blockRadialGradient A Z‖ ^ 2)
    (hzero : normalizedBlockNorm A = 0 → Z = 0) :
    Nonempty (PointwiseSpectrum A U Z p) := by
  by_cases hv : normalizedBlockNorm A = 0
  · have hAz : A = 0 := (normalizedBlockNorm_eq_zero_iff A).mp hv
    have hZz := hzero hv
    have hpz : p = 0 := by
      rw [hZz, zero_gradient_radial, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hp
      exact norm_eq_zero.mp (by nlinarith only [hp, norm_nonneg p])
    subst A
    subst Z
    subst p
    exact pointwiseSpectrum_zero U
  · exact pointwiseSpectrum_nonempty A U Z p hA htA
      (lt_of_le_of_ne (normalizedBlockNorm_nonneg A) (Ne.symm hv)) hs ht hb hp

namespace PointwiseSpectrum

variable {A U : Mat} {Z : Angular.Gradient} {p : Vec}

theorem scalar_norm_closed (D : PointwiseSpectrum A U Z p)
    (hzero : normalizedBlockNorm A = 0 → Z = 0) :
    scalarNormExpression 0 A Z =
      (weylGradientEnergy Z - ‖p‖ ^ 2) / normalizedBlockNorm A +
        6 * normalizedBlockNorm A * (1 - D.shape.sigma * normalizedBlockNorm A) := by
  by_cases hv : normalizedBlockNorm A = 0
  · have hAz : A = 0 := (normalizedBlockNorm_eq_zero_iff A).mp hv
    have hz := hzero hv
    have he : weylGradientEnergy Z = 0 := by rw [hz, zero_gradient_energy]
    have hleft : scalarNormExpression 0 A Z = 0 := by
      rw [hz]
      simp [scalarNormExpression, regularizedRadialDerivative, hAz, zero_gradient_energy]
    rw [hleft, he, hv]
    simp
  · exact D.scalar_norm (lt_of_le_of_ne (normalizedBlockNorm_nonneg A) (Ne.symm hv))

theorem axial_closed (D : PointwiseSpectrum A U Z p)
    (hzero : normalizedBlockNorm A = 0 → Z = 0)
    (hsum : normalizedBlockNorm A + normalizedBlockNorm U ≤ 2)
    {τ : ℝ} (hτ : τ ≤ 1) :
    weight (normalizedBlockNorm A) (normalizedBlockNorm U) * invariantHessianForm A U Z +
      scalarHessianCorrection (normalizedBlockNorm A) (normalizedBlockNorm U)
        D.shape.sigma τ (weylGradientEnergy Z) (weylMatrixEnergy A Z) (‖p‖ ^ 2) ≤
    (axialCoefficient (normalizedBlockNorm A) (normalizedBlockNorm U) +
        2 * kappa (normalizedBlockNorm A) (normalizedBlockNorm U) /
          (3 * normalizedBlockNorm A)) * ‖p‖ ^ 2 := by
  by_cases hv : normalizedBlockNorm A = 0
  · have hz := hzero hv
    have he0 : weylGradientEnergy Z = 0 := by rw [hz, zero_gradient_energy]
    have hB0 : weylMatrixEnergy A Z = 0 := by rw [hz, zero_gradient_matrix_energy]
    have hp : ‖p‖ ^ 2 = 0 := by
      have he := D.energy_lower
      rw [he0] at he
      nlinarith only [he, sq_nonneg ‖p‖]
    have hh : invariantHessianForm A U Z ≤ 0 := by
      rw [hz]
      exact zero_gradient_hessian_nonpos A U
    have hm := mul_le_mul_of_nonneg_left hh
      (show 0 ≤ weight (normalizedBlockNorm A) (normalizedBlockNorm U) by unfold weight; positivity)
    rw [he0, hB0, hp, hv]
    simpa [scalarHessianCorrection, hv] using hm
  · exact invariant_axial_bound A U Z D.shape τ D.radial D.second D.third p
      (lt_of_le_of_ne (normalizedBlockNorm_nonneg A) (Ne.symm hv)) hsum hτ
      D.energy D.radial_norm D.matrix_energy D.hessian

end PointwiseSpectrum

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The normalized Einstein metric supplies all local tensor identities
needed for the Weyl equation. The equation itself is then derived by the
finite Hessian trace calculation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem actual_weylCovariantIdentities (g : SmoothMetric M) (hRic : RicciThree g) :
    WeylCovariantIdentities g where
  symmetric e := (actual_weyl_symmetric e.frame).1
  traceFree e := (actual_weyl_traceFree e.frame hRic).1
  hessianMatrix e i j := (actual_weylHessian_constraints e.frame hRic i j).1
  hessianBianchi e i r := actual_plusWeylHessian_bianchi e.frame hRic i r
  hessianCommutator e i j a b := actual_plusWeylHessian_commutator e.frame hRic i j a b

theorem actual_metric_weyl_trace (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) :
    TraceHessian.hessianTrace (plusWeylHessian g e.base e.frame) =
      TraceHessian.weylLaplacian (plusWeyl g e.base e.frame) :=
  metric_weyl_trace g (actual_weylCovariantIdentities g hRic) e

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal curvature and its covariant derivative depend on the first
frame direction through their Frobenius norms, not on the normal basis. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular
open scoped Manifold ContDiff BigOperators

noncomputable section

local instance curvatureInvariantFrobenius : NormedAddCommGroup Mat3 :=
  Matrix.frobeniusNormedAddCommGroup

private theorem directionalCurvature_sumFour_moveLast (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := by
  calc
    _ = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      calc
        _ = ∑ b, ∑ d, ∑ c, f a b c d := by
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.sum_comm]
        _ = _ := Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Contract the two Jacobi directions before choosing the normal basis. -/
def directionalCurvatureMatrix (T : CovariantCoordinates 4) (w : Fin 4 → ℝ) : Mat4 :=
  fun a b => ∑ p, ∑ q, w p * w q * T ![a, p, q, b]

theorem frameTensor_normal_matrix (E : Mat4) (T : CovariantCoordinates 4)
    (i j : Fin 4) :
    frameTensor E T ![i, 0, 0, j] =
      (Eᵀ * directionalCurvatureMatrix T (fun a => E a 0) * E) i j := by
  rw [frameTensor_four, directionalCurvature_sumFour_moveLast]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, directionalCurvatureMatrix,
    Finset.sum_mul, Finset.mul_sum]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

def directionalDerivativeTensor (T : CovariantCoordinates 5) (w : Fin 4 → ℝ) :
    CovariantCoordinates 4 := fun a => ∑ d, w d * T (Fin.cons d a)

theorem frameTensor_directionalDerivative (E : Mat4) (T : CovariantCoordinates 5)
    (a : Fin 4 → Fin 4) :
    frameTensor E T (Fin.cons 0 a) =
      frameTensor E (directionalDerivativeTensor T (fun d => E d 0)) a := by
  rw [frameTensor_cons]
  simp only [directionalDerivativeTensor, frameTensor, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro d _
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem frameCurvatureField_normalRestriction (e : OrthonormalFrame g c) :
    frameCurvatureField g ⟨c, e⟩ = normalRestriction e.matrix
      (directionalCurvatureMatrix (curvatureCoordinates g c (chartAt FourSpace c c))
        (fun a => e.matrix a 0)) - 1 := by
  ext i j
  rw [frameCurvatureField_apply]
  change frameCurvature g c e i.succ 0 0 j.succ - (if i = j then 1 else 0) = _
  rw [← frameTensor_curvatureCoordinates, frameTensor_normal_matrix]
  rfl

theorem frameCurvatureField_norm_same_direction (e f : OrthonormalFrame g c)
    (hfirst : e.vector 0 = f.vector 0) :
    ‖frameCurvatureField g ⟨c, e⟩‖ ^ 2 = ‖frameCurvatureField g ⟨c, f⟩‖ ^ 2 := by
  have hw : (fun a => e.matrix a 0) = (fun a => f.matrix a 0) := by
    funext a
    exact congrArg (fun v : FourSpace => v a) hfirst
  rw [frameCurvatureField_normalRestriction, frameCurvatureField_normalRestriction, ← hw]
  exact normalRestriction_sub_one_norm_sq_same_direction e f hfirst _

/-- Each actual first derivative of the normalized Weyl tensor has only its
positive and negative Weyl blocks; its Ricci contraction is zero. -/
theorem actual_weyl_derivative_decomposition (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (d : Fin 4) :
    curvatureDerivativeArray (frameTensor e.matrix
      (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c))) d =
      blockTensor (plusWeylGradient g c e d) quaternionMatrix +
        blockTensor (minusWeylGradient g c e d) oppositeMatrix := by
  let T := frameTensor e.matrix
    (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c))
  have hs := frame_normalizedWeyl_derivative_symmetries g c e d
  have hR (j k : Fin 4) : (∑ l, T ![d, l, j, k, l]) = 0 := by
    dsimp only [T]
    have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
    rw [covariantDerivative_normalizedWeyl g c (chartAt FourSpace c c) hz
      (chartMetric_posDef g c).det_pos.ne']
    exact frame_curvature_derivative_trace_zero e
      (actual_ricci_parallel_at_center g hRic c) d j k
  exact AlgebraicCurvature.ricci_zero_decomposition _ hs.1 hs.2.1 hs.2.2 hR

private theorem blockTensor_add (A B : Mat3) (Q : Fin 3 → Mat4) :
    blockTensor (A + B) Q = blockTensor A Q + blockTensor B Q := by
  simp only [blockTensor, Matrix.add_apply, add_smul, Finset.sum_add_distrib, smul_add]

private theorem normalEvaluation_pureBlocks (A B : Mat3) (q : Directions) (i j : Fin 3) :
    normalEvaluation q i j (blockTensor A quaternionMatrix + blockTensor B oppositeMatrix) =
      normalDeviation A B q i j := by
  have hh := normalEvaluation_einstein A B q i j
  have hzero := normalEvaluation_einstein (0 : Mat3) (0 : Mat3) q i j
  rw [einsteinCurvatureTensor, blockTensor_add, blockTensor_add,
    map_add, map_add, map_add] at hh
  simp only [einsteinCurvatureTensor, add_zero, map_add] at hzero
  have hz : normalDeviation (0 : Mat3) (0 : Mat3) q = 0 := by
    simp [normalDeviation, rotated]
  rw [hz, add_zero] at hzero
  simp only [Matrix.add_apply] at hh
  rw [map_add]
  linarith only [hh, hzero]

theorem frameCurvatureDerivative_actual (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (i j : Fin 3) :
    frameCurvatureDerivative g ⟨c, e⟩ i j = frameTensor e.matrix
      (covariantDerivative g c (normalizedWeylCoordinates g c)
        (chartAt FourSpace c c)) ![0, i.succ, 0, 0, j.succ] := by
  have hd := congrArg (fun R : CurvatureArray => normalEvaluation firstDirection i j R)
    (actual_weyl_derivative_decomposition e hRic 0)
  rw [frameCurvatureDerivative_eq]
  rw [← normalEvaluation_pureBlocks]
  rw [← hd]
  simp only [normalEvaluation, firstDirection_normal, firstDirection_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

theorem frameCurvatureDerivative_normalRestriction (e : OrthonormalFrame g c)
    (hRic : RicciThree g) :
    frameCurvatureDerivative g ⟨c, e⟩ = normalRestriction e.matrix
      (directionalCurvatureMatrix
        (directionalDerivativeTensor
          (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c))
          (fun a => e.matrix a 0)) (fun a => e.matrix a 0)) := by
  ext i j
  rw [frameCurvatureDerivative_actual e hRic]
  let E : Mat4 := e.matrix
  let T : CovariantCoordinates 5 :=
    covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c)
  change frameTensor E T (Fin.cons (0 : Fin 4) (![i.succ, 0, 0, j.succ] : Fin 4 → Fin 4)) =
    normalRestriction E (directionalCurvatureMatrix
      (directionalDerivativeTensor T (fun a : Fin 4 => E a 0))
      (fun a : Fin 4 => E a 0)) i j
  rw [frameTensor_directionalDerivative, frameTensor_normal_matrix]
  rfl

theorem frameCurvatureDerivative_norm_same_direction (e f : OrthonormalFrame g c)
    (hRic : RicciThree g) (hfirst : e.vector 0 = f.vector 0) :
    ‖frameCurvatureDerivative g ⟨c, e⟩‖ ^ 2 =
      ‖frameCurvatureDerivative g ⟨c, f⟩‖ ^ 2 := by
  have hw : (fun a => e.matrix a 0) = (fun a => f.matrix a 0) := by
    funext a
    exact congrArg (fun v : FourSpace => v a) hfirst
  rw [frameCurvatureDerivative_normalRestriction e hRic,
    frameCurvatureDerivative_normalRestriction f hRic, ← hw]
  exact normalRestriction_norm_sq_same_direction e f hfirst _

theorem frameCurvatureField_directionInvariant (g : SmoothMetric M) :
    DirectionInvariant (fun e => ‖frameCurvatureField g e‖ ^ 2) := by
  rintro ⟨c, e⟩ ⟨d, f⟩ hbase hfirst
  dsimp only at hbase
  subst d
  exact frameCurvatureField_norm_same_direction e f hfirst

theorem frameCurvatureDerivative_directionInvariant (g : SmoothMetric M)
    (hRic : RicciThree g) :
    DirectionInvariant (fun e => ‖frameCurvatureDerivative g e‖ ^ 2) := by
  rintro ⟨c, e⟩ ⟨d, f⟩ hbase hfirst
  dsimp only at hbase
  subst d
  exact frameCurvatureDerivative_norm_same_direction e f hRic hfirst

end
end PositiveEinsteinFour.Geometry
end


section

/-! Equation (16), before its positive constant factor: the integrated
trace-subtracted energy is nonnegative. The proof combines the actual
weak equations and the full prescribed trace subtraction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace MetricGreenData

def jointMatrixEnergy (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  d.matrixEnergyField + d.matrixEnergyField.comp ⟨frameReflection, continuous_frameReflection g⟩

def jointTraceEnergy (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => traceEnergy (plusWeyl g e.base e.frame) +
    traceEnergy (plusWeyl g (frameReflection e).base (frameReflection e).frame),
    (continuous_traceEnergy.comp d.continuousWeyl).add
      ((continuous_traceEnergy.comp d.continuousWeyl).comp (continuous_frameReflection g))⟩

def jointHessianEnergy (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => d.jointEnergyLaplacian e - 26 * d.totalEnergyField e + 40 * d.jointMatrixEnergy e,
    (d.jointEnergyLaplacian.continuous.sub
      (continuous_const.mul d.totalEnergyField.continuous)).add
        (continuous_const.mul d.jointMatrixEnergy.continuous)⟩

theorem jointTraceEnergy_le_hessian (d : MetricGreenData g μ) (e : FrameBundle g) :
    d.jointTraceEnergy e ≤ d.jointHessianEnergy e := by
  have hp := d.traceEnergy_le_hessian e
  have hm := d.traceEnergy_le_hessian (frameReflection e)
  change traceEnergy (plusWeyl g e.base e.frame) +
    traceEnergy (plusWeyl g (frameReflection e).base (frameReflection e).frame) ≤
    ((hessianNormSq (plusWeylHessian g e.base e.frame) / 3 +
        26 * weylGradientEnergy (plusWeylGradient g e.base e.frame) -
        40 * weylMatrixEnergy (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)) +
      (hessianNormSq (plusWeylHessian g (frameReflection e).base (frameReflection e).frame) / 3 +
        26 * weylGradientEnergy (plusWeylGradient g (frameReflection e).base (frameReflection e).frame) -
        40 * weylMatrixEnergy (plusWeyl g (frameReflection e).base (frameReflection e).frame)
          (plusWeylGradient g (frameReflection e).base (frameReflection e).frame))) -
      26 * (weylGradientEnergy (plusWeylGradient g e.base e.frame) +
        weylGradientEnergy (plusWeylGradient g (frameReflection e).base (frameReflection e).frame)) +
      40 * (weylMatrixEnergy (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) +
        weylMatrixEnergy (plusWeyl g (frameReflection e).base (frameReflection e).frame)
          (plusWeylGradient g (frameReflection e).base (frameReflection e).frame))
  linarith only [hp, hm]

def traceDeficitIntegrand (d : MetricGreenData g μ) (o : OppositeWeylData d)
    (e : FrameBundle g) : ℝ :=
  -(d.totalEnergyField e * d.jointScalarNorm e) -
    26 * d.deficitField o e * d.totalEnergyField e +
    40 * d.deficitField o e * d.jointMatrixEnergy e - d.deficitField o e * d.jointTraceEnergy e

end MetricGreenData

namespace FrameReflectionData

variable {d : MetricGreenData g μ} (r : FrameReflectionData d)
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

include r

theorem traceDeficit_integral_nonneg (o : OppositeWeylData d)
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    0 ≤ ∫ e, d.traceDeficitIntegrand o e ∂μ := by
  let F : C(FrameBundle g, ℝ) := d.deficitField o * (d.jointHessianEnergy - d.jointTraceEnergy)
  let K : FrameBundle g → ℝ := fun e => d.deficitField o e * d.jointEnergyLaplacian e +
    d.totalEnergyField e * d.jointScalarNorm e
  have hF : Integrable F μ := F.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hK : Integrable K μ :=
    (((d.deficitField o).continuous.mul d.jointEnergyLaplacian.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).add
        (integrable_continuous_weight r.jointScalarNorm_integrable d.totalEnergyField)
  have hz : (∫ e, K e ∂μ) = 0 := r.jointEnergyCancellation o hpinch
  have he (e : FrameBundle g) : d.traceDeficitIntegrand o e = F e - K e := by
    change -(d.totalEnergyField e * d.jointScalarNorm e) -
      26 * d.deficitField o e * d.totalEnergyField e +
      40 * d.deficitField o e * d.jointMatrixEnergy e - d.deficitField o e * d.jointTraceEnergy e =
      d.deficitField o e * ((d.jointEnergyLaplacian e - 26 * d.totalEnergyField e +
        40 * d.jointMatrixEnergy e) - d.jointTraceEnergy e) -
        (d.deficitField o e * d.jointEnergyLaplacian e + d.totalEnergyField e * d.jointScalarNorm e)
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall he), integral_sub hF hK, hz, sub_zero]
  apply integral_nonneg
  intro e
  change 0 ≤ d.deficitField o e * (d.jointHessianEnergy e - d.jointTraceEnergy e)
  apply mul_nonneg
  · change 0 ≤ 2 - regularizedBlockNorm 0 (plusWeyl g e.base e.frame) -
      regularizedBlockNorm 0 (minusWeyl g e.base e.frame)
    rw [regularizedBlockNorm_zero, regularizedBlockNorm_zero]
    linarith [hpinch e]
  · exact sub_nonneg.mpr (d.jointTraceEnergy_le_hessian e)

end FrameReflectionData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual two-block finite-array integrand is bounded using the
constructed spectral data. All spectral choices disappear from the final
estimate, including zero axes where the actual gradient vanishes. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian HighestHessian PositiveEinsteinFour.Geometry
open Energy QuarticEnergy Quadratic Potential Boundary

noncomputable section

theorem arrayCoupledIntegrand_le_reduced
    (A U : Mat) (Z V : Angular.Gradient) (a ab p q : Vec)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (hZs : ∀ i, symmetric (Z i)) (hZt : ∀ i, traceFree (Z i))
    (hZb : ∀ r i, gradientDivergence Z r i = 0)
    (hVs : ∀ i, symmetric (V i)) (hVt : ∀ i, traceFree (V i))
    (hVb : ∀ r i, gradientDivergence V r i = 0)
    (hzero : normalizedBlockNorm A = 0 → Z = 0)
    (hzerob : normalizedBlockNorm U = 0 → V = 0)
    (D : PointwiseSpectrum A U Z p) (F : PointwiseSpectrum U A V q)
    (hmin : normalizedBlockNorm A * D.minimum + normalizedBlockNorm U * F.minimum ≤ 2)
    (ha : ‖a‖ ^ 2 = (9 / 16 : ℝ) * scalarWeight (normalizedBlockNorm A) (normalizedBlockNorm U) ^ 2 *
      ‖p - q‖ ^ 2)
    (hab : ‖ab‖ ^ 2 = (9 / 16 : ℝ) * scalarWeight (normalizedBlockNorm U) (normalizedBlockNorm A) ^ 2 *
      ‖p - q‖ ^ 2) :
    arrayCoupledIntegrand A U Z V a ab p q ≤
      reducedIntegrand (normalizedBlockNorm A) (normalizedBlockNorm U) D.minimum F.minimum
        D.shape.sigma F.shape.sigma D.shape.rho F.shape.rho
        (weylGradientEnergy Z) (weylGradientEnergy V) p q := by
  let v := normalizedBlockNorm A
  let b := normalizedBlockNorm U
  have hv0 : 0 ≤ v := normalizedBlockNorm_nonneg A
  have hb0 : 0 ≤ b := normalizedBlockNorm_nonneg U
  have hsum : v + b ≤ 2 := by
    have hr : v ≤ v * D.minimum := by nlinarith only [hv0, D.minimum_lower]
    have hs : b ≤ b * F.minimum := by nlinarith only [hb0, F.minimum_lower]
    linarith only [hmin, hr, hs]
  have hv2 : v ≤ 2 := by linarith only [hsum, hb0]
  have hb2 : b ≤ 2 := by linarith only [hsum, hv0]
  have hM := scalarWeight_positive hv0 hb0 hsum
  have hMb := scalarWeight_positive hb0 hv0 (show b + v ≤ 2 by linarith only [hsum])
  have hab' : ‖ab‖ ^ 2 = (9 / 16 : ℝ) * scalarWeight b v ^ 2 * ‖q - p‖ ^ 2 := by
    rw [norm_sub_rev q p]
    exact hab
  have hc := cubic_bound_of_weight_square (scalarWeight v b) hM.le a p q ha Z hZs hZt hZb
  have hcb := cubic_bound_of_weight_square (scalarWeight b v) hMb.le ab q p hab' V hVs hVt hVb
  have hnormsum : ‖q‖ + ‖p‖ = ‖p‖ + ‖q‖ := add_comm _ _
  rw [hnormsum] at hcb
  have hcost := projection_bound_of_weight_square A U hA hU htA htU
    (v * D.minimum) (b * F.minimum) D.minimum_shift F.minimum_shift hmin
    (scalarWeight v b) (ne_of_gt hM) a p q ha Z hZs hZt hZb
    D.shape D.radial D.second D.third D.energy D.radial_norm D.matrix_energy
  have hcostb := projection_bound_of_weight_square U A hU hA htU htA
    (b * F.minimum) (v * D.minimum) F.minimum_shift D.minimum_shift
    (by linarith only [hmin]) (scalarWeight b v) (ne_of_gt hMb) ab q p hab' V hVs hVt hVb
    F.shape F.radial F.second F.third F.energy F.radial_norm F.matrix_energy
  have hcost' := hcost.trans (projection_bound_norm_sum p q hv0 hv2
    (mul_nonneg hb0 (by linarith only [F.minimum_lower])) D.shape_sigma_upper D.energy_lower)
  have hcostb' := hcostb.trans (projection_bound_norm_sum q p hb0 hb2
    (mul_nonneg hv0 (by linarith only [D.minimum_lower])) F.shape_sigma_upper F.energy_lower)
  rw [hnormsum] at hcostb'
  have hx := D.axial_closed hzero hsum F.shape_sigma_upper
  have hy := F.axial_closed hzerob (by linarith only [hsum]) D.shape_sigma_upper
  have hcostWeight :
      generalCurvaturePairing A U
          (highestProjection (weightTensor a (gradientTensor Z)))
          (highestProjection (weightTensor a (gradientTensor Z))) / (24 * weight v b) ≤
        (9 / 64 : ℝ) * (‖p‖ + ‖q‖) ^ 2 *
          projectionBracket v (b * F.minimum) D.shape.sigma D.shape.rho
            (weylGradientEnergy Z) (‖p‖ ^ 2) := by
    simpa only [weight, scalarWeight] using hcost'
  have hcostWeightb :
      generalCurvaturePairing U A
          (highestProjection (weightTensor ab (gradientTensor V)))
          (highestProjection (weightTensor ab (gradientTensor V))) / (24 * weight b v) ≤
        (9 / 64 : ℝ) * (‖p‖ + ‖q‖) ^ 2 *
          projectionBracket b (v * D.minimum) F.shape.sigma F.shape.rho
            (weylGradientEnergy V) (‖q‖ ^ 2) := by
    simpa only [weight, scalarWeight] using hcostb'
  have hfour :
      (-(5 / 36 : ℝ) * weightedCubicField a Z +
        generalCurvaturePairing A U
          (highestProjection (weightTensor a (gradientTensor Z)))
          (highestProjection (weightTensor a (gradientTensor Z))) / (24 * weight v b)) +
      (-(5 / 36 : ℝ) * weightedCubicField ab V +
        generalCurvaturePairing U A
          (highestProjection (weightTensor ab (gradientTensor V)))
          (highestProjection (weightTensor ab (gradientTensor V))) / (24 * weight b v)) +
      quarticNormLoss v b (weylGradientEnergy Z) (weylGradientEnergy V) p q ≤
      quarticEnergy v b ((5 / 3) * ‖p‖ ^ 2) ((5 / 3) * ‖q‖ ^ 2)
        (projectionCoefficient v (b * F.minimum) D.shape.sigma D.shape.rho)
        (projectionCoefficient b (v * D.minimum) F.shape.sigma F.shape.rho)
        (defectCoefficient v (b * F.minimum)) (defectCoefficient b (v * D.minimum))
        (weylGradientEnergy Z) (weylGradientEnergy V) := by
    rw [← quartic_bounds_identity]
    linarith only [hc, hcb, hcostWeight, hcostWeightb]
  have hsplit : arrayCoupledIntegrand A U Z V a ab p q =
      (weight v b * invariantHessianForm A U Z +
        scalarHessianCorrection v b D.shape.sigma F.shape.sigma
          (weylGradientEnergy Z) (weylMatrixEnergy A Z) (‖p‖ ^ 2)) +
      (weight b v * invariantHessianForm U A V +
        scalarHessianCorrection b v F.shape.sigma D.shape.sigma
          (weylGradientEnergy V) (weylMatrixEnergy U V) (‖q‖ ^ 2)) +
      ((-(5 / 36 : ℝ) * weightedCubicField a Z +
        generalCurvaturePairing A U
          (highestProjection (weightTensor a (gradientTensor Z)))
          (highestProjection (weightTensor a (gradientTensor Z))) / (24 * weight v b)) +
       (-(5 / 36 : ℝ) * weightedCubicField ab V +
        generalCurvaturePairing U A
          (highestProjection (weightTensor ab (gradientTensor V)))
          (highestProjection (weightTensor ab (gradientTensor V))) / (24 * weight b v)) +
        quarticNormLoss v b (weylGradientEnergy Z) (weylGradientEnergy V) p q) +
      radialQuadraticTerm v b p q + zeroOrderIntegrand v b D.shape.sigma F.shape.sigma := by
    unfold arrayCoupledIntegrand arrayHessianTerm
    rw [D.scalar_norm_closed hzero, F.scalar_norm_closed hzerob, D.trace_energy, F.trace_energy,
      scalarCouplingTerm_spectral_split]
    ring
  rw [hsplit]
  unfold reducedIntegrand
  have htwo := axial_plus_radial_identity v b p q
  linarith only [hx, hy, hfour, htwo]

/-- Positive-norm finite-array coupling estimate. Spectral frames and all
three-parameter decompositions are constructed and eliminated internally. -/
theorem pointwise_coupling_bound
    (A U : Mat) (Z V : Angular.Gradient) (a ab p q : Vec)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (hZs : ∀ i, symmetric (Z i)) (hZt : ∀ i, traceFree (Z i))
    (hZb : ∀ r i, gradientDivergence Z r i = 0)
    (hVs : ∀ i, symmetric (V i)) (hVt : ∀ i, traceFree (V i))
    (hVb : ∀ r i, gradientDivergence V r i = 0)
    (hv : 0 < normalizedBlockNorm A) (hb : 0 < normalizedBlockNorm U)
    (x y : ℝ) (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2)
    (hp : ‖p‖ ^ 2 = ‖blockRadialGradient A Z‖ ^ 2)
    (hq : ‖q‖ ^ 2 = ‖blockRadialGradient U V‖ ^ 2)
    (ha : ‖a‖ ^ 2 = (9 / 16 : ℝ) * scalarWeight (normalizedBlockNorm A) (normalizedBlockNorm U) ^ 2 *
      ‖p - q‖ ^ 2)
    (hab : ‖ab‖ ^ 2 = (9 / 16 : ℝ) * scalarWeight (normalizedBlockNorm U) (normalizedBlockNorm A) ^ 2 *
      ‖p - q‖ ^ 2) :
    arrayCoupledIntegrand A U Z V a ab p q ≤
      -couplingCoefficient (normalizedBlockNorm A) (normalizedBlockNorm U) *
        (‖p‖ ^ 2 + ‖q‖ ^ 2) *
          (‖p‖ ^ 2 / normalizedBlockNorm A + ‖q‖ ^ 2 / normalizedBlockNorm U) +
      2 * theta (normalizedBlockNorm A) (normalizedBlockNorm U) *
        (normWeight (normalizedBlockNorm A) * ‖p‖ ^ 2 +
          normWeight (normalizedBlockNorm U) * ‖q‖ ^ 2) -
      theta (normalizedBlockNorm A) (normalizedBlockNorm U) ^ 2 /
        couplingCoefficient (normalizedBlockNorm A) (normalizedBlockNorm U) := by
  obtain ⟨D⟩ := pointwiseSpectrum_nonempty A U Z p hA htA hv hZs hZt hZb hp
  obtain ⟨F⟩ := pointwiseSpectrum_nonempty U A V q hU htU hb hVs hVt hVb hq
  have hmin : normalizedBlockNorm A * D.minimum + normalizedBlockNorm U * F.minimum ≤ 2 := by
    have hd := D.minimum_le_shift x hAx
    have hf := F.minimum_le_shift y hUy
    linarith only [hd, hf, hxy]
  apply (arrayCoupledIntegrand_le_reduced A U Z V a ab p q hA hU htA htU
    hZs hZt hZb hVs hVt hVb
    (by intro h; exact (ne_of_gt hv h).elim) (by intro h; exact (ne_of_gt hb h).elim)
    D F hmin ha hab).trans
  exact reduced_integrand_bound p q hv.le hb.le D.minimum_lower D.minimum_upper
    F.minimum_lower F.minimum_upper hmin D.cubic D.shape_circle F.cubic F.shape_circle
    D.energy_lower F.energy_lower (by intro h; exact (ne_of_gt hv h).elim)
    (by intro h; exact (ne_of_gt hb h).elim)

/-- The same bound includes both zero axes under precisely the
gradient-vanishing hypotheses supplied almost everywhere by the flow. -/
theorem pointwise_coupling_bound_closed
    (A U : Mat) (Z V : Angular.Gradient) (a ab p q : Vec)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (hZs : ∀ i, symmetric (Z i)) (hZt : ∀ i, traceFree (Z i))
    (hZb : ∀ r i, gradientDivergence Z r i = 0)
    (hVs : ∀ i, symmetric (V i)) (hVt : ∀ i, traceFree (V i))
    (hVb : ∀ r i, gradientDivergence V r i = 0)
    (hzero : normalizedBlockNorm A = 0 → Z = 0)
    (hzerob : normalizedBlockNorm U = 0 → V = 0)
    (x y : ℝ) (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2)
    (hp : ‖p‖ ^ 2 = ‖blockRadialGradient A Z‖ ^ 2)
    (hq : ‖q‖ ^ 2 = ‖blockRadialGradient U V‖ ^ 2)
    (ha : ‖a‖ ^ 2 = (9 / 16 : ℝ) * scalarWeight (normalizedBlockNorm A) (normalizedBlockNorm U) ^ 2 *
      ‖p - q‖ ^ 2)
    (hab : ‖ab‖ ^ 2 = (9 / 16 : ℝ) * scalarWeight (normalizedBlockNorm U) (normalizedBlockNorm A) ^ 2 *
      ‖p - q‖ ^ 2) :
    arrayCoupledIntegrand A U Z V a ab p q ≤
      -couplingCoefficient (normalizedBlockNorm A) (normalizedBlockNorm U) *
        (‖p‖ ^ 2 + ‖q‖ ^ 2) *
          (‖p‖ ^ 2 / normalizedBlockNorm A + ‖q‖ ^ 2 / normalizedBlockNorm U) +
      2 * theta (normalizedBlockNorm A) (normalizedBlockNorm U) *
        (normWeight (normalizedBlockNorm A) * ‖p‖ ^ 2 +
          normWeight (normalizedBlockNorm U) * ‖q‖ ^ 2) -
      theta (normalizedBlockNorm A) (normalizedBlockNorm U) ^ 2 /
        couplingCoefficient (normalizedBlockNorm A) (normalizedBlockNorm U) := by
  obtain ⟨D⟩ := pointwiseSpectrum_nonempty_closed A U Z p hA htA hZs hZt hZb hp hzero
  obtain ⟨F⟩ := pointwiseSpectrum_nonempty_closed U A V q hU htU hVs hVt hVb hq hzerob
  have hmin : normalizedBlockNorm A * D.minimum + normalizedBlockNorm U * F.minimum ≤ 2 := by
    have hd := D.minimum_le_shift x hAx
    have hf := F.minimum_le_shift y hUy
    linarith only [hd, hf, hxy]
  apply (arrayCoupledIntegrand_le_reduced A U Z V a ab p q hA hU htA htU
    hZs hZt hZb hVs hVt hVb hzero hzerob D F hmin ha hab).trans
  exact reduced_integrand_bound p q (normalizedBlockNorm_nonneg A) (normalizedBlockNorm_nonneg U)
    D.minimum_lower D.minimum_upper F.minimum_lower F.minimum_upper hmin
    D.cubic D.shape_circle F.cubic F.shape_circle D.energy_lower F.energy_lower
    (by intro h; rw [hzero h, zero_gradient_energy])
    (by intro h; rw [hzerob h, zero_gradient_energy])

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! Rotation of the actual first curvature derivative, including its
covector direction, before either Weyl block is contracted. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular
open scoped Manifold ContDiff BigOperators

noncomputable section

/-- Successive pullbacks act by the product of their frame matrices. -/
theorem frameTensor_mul {n : ℕ} (E P : Mat4) (T : CovariantCoordinates n) :
    frameTensor (E * P) T = frameTensor P (frameTensor E T) := by
  induction n with
  | zero =>
    funext a
    rw [frameTensor_zero, frameTensor_zero, frameTensor_zero]
  | succ n ih =>
    funext a
    obtain ⟨i, v, rfl⟩ := Fin.exists_cons a
    let F (b : Fin 4) : CovariantCoordinates n := fun w => T (Fin.cons b w)
    have hs (d : Fin 4) :
        (fun w => frameTensor E T (Fin.cons d w)) =
          fun w => ∑ b, E b d * frameTensor E (F b) w := by
      funext w
      exact frameTensor_cons E T d w
    rw [frameTensor_cons, frameTensor_cons]
    simp only [hs, frameTensor_sum, frameTensor_const_mul]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [ih (F b)]
    ring

theorem frameTensor_directionFrame_normal (T : CovariantCoordinates 5)
    (q : Directions) (i j : Fin 3) :
    frameTensor (directionFrameMatrix q) T ![0, i.succ, 0, 0, j.succ] =
      ∑ d, q.val d * normalEvaluation q i j (curvatureDerivativeArray T d) := by
  change frameTensor (directionFrameMatrix q) T
    (Fin.cons (0 : Fin 4) (![i.succ, 0, 0, j.succ] : Fin 4 → Fin 4)) = _
  rw [frameTensor_cons]
  simp only [frameTensor_four, directionFrameMatrix_zero, directionFrameMatrix_succ,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  change (∑ a, ∑ b, ∑ c, ∑ f, q.val d *
    (normalVector q i a * q.val b * q.val c * normalVector q j f *
      T (Fin.cons d ![a, b, c, f]))) = q.val d *
    (∑ a, ∑ b, ∑ c, ∑ f, T (Fin.cons d ![a, b, c, f]) *
      normalVector q i a * q.val b * q.val c * normalVector q j f)
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro f _
  ring

private theorem turn_blockTensor_add (A B : Mat3) (Q : Fin 3 → Mat4) :
    blockTensor (A + B) Q = blockTensor A Q + blockTensor B Q := by
  simp only [blockTensor, Matrix.add_apply, add_smul, Finset.sum_add_distrib, smul_add]

private theorem turn_normalEvaluation_pureBlocks (A B : Mat3) (q : Directions) (i j : Fin 3) :
    normalEvaluation q i j (blockTensor A quaternionMatrix + blockTensor B oppositeMatrix) =
      normalDeviation A B q i j := by
  have hh := normalEvaluation_einstein A B q i j
  have hzero := normalEvaluation_einstein (0 : Mat3) (0 : Mat3) q i j
  rw [einsteinCurvatureTensor, turn_blockTensor_add, turn_blockTensor_add,
    map_add, map_add, map_add] at hh
  simp only [einsteinCurvatureTensor, add_zero, map_add] at hzero
  have hz : normalDeviation (0 : Mat3) (0 : Mat3) q = 0 := by
    simp [normalDeviation, rotated]
  rw [hz, add_zero] at hzero
  simp only [Matrix.add_apply] at hh
  rw [map_add]
  linarith only [hh, hzero]

theorem normalDeviation_sum_smul (a : Fin 4 → ℝ) (Z W : Gradient) (q : Directions) :
    normalDeviation (∑ d, a d • Z d) (∑ d, a d • W d) q =
      ∑ d, a d • normalDeviation (Z d) (W d) q := by
  simp only [normalDeviation, rotated, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, ← Finset.sum_add_distrib,
    Finset.smul_sum, smul_add, smul_smul]
  apply Finset.sum_congr rfl
  intro d _
  rw [mul_comm (1 / 2 : ℝ) (a d)]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

/-- The quaternionic completion rotates the derivative direction and all
four curvature slots of the actual tensor at once. -/
theorem frameCurvatureDerivative_turn (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (q : Directions) :
    frameCurvatureDerivative g (frameTurn e q) = normalCurvatureDerivative g c e q := by
  let T : CovariantCoordinates 5 := covariantDerivative g c
    (normalizedWeylCoordinates g c) (chartAt FourSpace c c)
  let Z : Gradient := plusWeylGradient g c e
  let W : Gradient := minusWeylGradient g c e
  have hd (d : Fin 4) : curvatureDerivativeArray (frameTensor e.matrix T) d =
      blockTensor (Z d) quaternionMatrix + blockTensor (W d) oppositeMatrix :=
    actual_weyl_derivative_decomposition e hRic d
  ext i j
  change frameCurvatureDerivative g (⟨c, e.turn q⟩ : FrameBundle g) i j =
    normalCurvatureDerivative g c e q i j
  rw [frameCurvatureDerivative_actual (e.turn q) hRic]
  change frameTensor (e.matrix * directionFrameMatrix q) T
    ![0, i.succ, 0, 0, j.succ] = _
  rw [frameTensor_mul, frameTensor_directionFrame_normal]
  change (∑ d, q.val d * normalEvaluation q i j
    (curvatureDerivativeArray (frameTensor e.matrix T) d)) =
      normalDeviation (directional Z q) (directional W q) q i j
  calc
    _ = ∑ d, q.val d * normalDeviation (Z d) (W d) q i j := by
      apply Finset.sum_congr rfl
      intro d _
      rw [hd, turn_normalEvaluation_pureBlocks]
    _ = _ := by
      rw [directional, directional, normalDeviation_sum_smul]
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrability of the products in the two polynomial norm tests.
The norm derivatives are obtained by their actual regularized limits. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators Topology Manifold ContDiff

noncomputable section

theorem continuous_kappaV_fields {Ω : Type*} [TopologicalSpace Ω]
    (v b : Ω → ℝ) (hv : Continuous v) (hb : Continuous b) :
    Continuous (fun x => Quadratic.kappaV (v x) (b x)) := by
  unfold Quadratic.kappaV
  fun_prop

theorem continuous_kappaB_fields {Ω : Type*} [TopologicalSpace Ω]
    (v b : Ω → ℝ) (hv : Continuous v) (hb : Continuous b) :
    Continuous (fun x => Quadratic.kappaB (v x) (b x)) := by
  unfold Quadratic.kappaB
  fun_prop

theorem abs_radialDerivative_zero_le (A Z : Mat) (hZ : symmetric Z) :
    |regularizedRadialDerivative 0 A Z| ≤ normalizedBlockNorm Z := by
  have ht : Tendsto (fun n : ℕ => regularizedRadialDerivative
      (1 / ((n : ℝ) + 1)) A Z) atTop (𝓝 (regularizedRadialDerivative 0 A Z)) := by
    simpa only [Function.comp_def, regularizedRadialDerivative,
      regularizedBlockNorm_zero] using
      (tendsto_regularizedRadialDerivative A Z).comp
        tendsto_one_div_add_atTop_nhds_zero_nat
  exact le_of_tendsto ht.abs (Eventually.of_forall (fun n =>
    abs_regularizedRadialDerivative_le _ (by positivity) A Z hZ))

section Integral

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

local instance jointIntegrabilityRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance jointIntegrabilitySpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance jointIntegrabilityAlgebra : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

theorem integrable_radialDerivative_product
    (A B Z V : Ω → Mat) (hZ : Continuous Z) (hV : Continuous V)
    (hsZ : ∀ x, symmetric (Z x)) (hsV : ∀ x, symmetric (V x))
    (hp : AEStronglyMeasurable (fun x => regularizedRadialDerivative 0 (A x) (Z x)) μ)
    (hq : AEStronglyMeasurable (fun x => regularizedRadialDerivative 0 (B x) (V x)) μ) :
    Integrable (fun x => regularizedRadialDerivative 0 (A x) (Z x) *
      regularizedRadialDerivative 0 (B x) (V x)) μ := by
  have hc := (continuous_normalizedBlockNorm.comp hZ).mul
    (continuous_normalizedBlockNorm.comp hV)
  apply (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).mono'
    (hp.mul hq)
  filter_upwards [] with x
  change ‖regularizedRadialDerivative 0 (A x) (Z x) *
    regularizedRadialDerivative 0 (B x) (V x)‖ ≤ normalizedBlockNorm (Z x) * normalizedBlockNorm (V x)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (abs_radialDerivative_zero_le _ _ (hsZ x))
    (abs_radialDerivative_zero_le _ _ (hsV x)) (abs_nonneg _)
    (normalizedBlockNorm_nonneg _)

end Integral

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace FrameReflectionData

variable {d : MetricGreenData g μ} (r : FrameReflectionData d)
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

include r

theorem kappaTest_integrable (o : OppositeWeylData d) :
    Integrable (fun e => kappaNormIntegrand (plusWeyl g e.base e.frame)
      (minusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)
      (minusWeylGradient g e.base e.frame)) μ := by
  let k : C(FrameBundle g, ℝ) := ⟨fun e => regularizedKappa 0
    (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame),
    continuous_regularizedKappa 0 _ _ d.continuousWeyl o.continuousWeyl⟩
  let kv : C(FrameBundle g, ℝ) := ⟨fun e => Quadratic.kappaV
    (normalizedBlockNorm (plusWeyl g e.base e.frame))
    (normalizedBlockNorm (minusWeyl g e.base e.frame)),
    continuous_kappaV_fields _ _ d.plusNormField.continuous (d.minusNormField o).continuous⟩
  let kb : C(FrameBundle g, ℝ) := ⟨fun e => Quadratic.kappaB
    (normalizedBlockNorm (plusWeyl g e.base e.frame))
    (normalizedBlockNorm (minusWeyl g e.base e.frame)),
    continuous_kappaB_fields _ _ d.plusNormField.continuous (d.minusNormField o).continuous⟩
  have hpp (i : Fin 4) : Integrable (fun e =>
      regularizedRadialDerivative 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame i) *
      regularizedRadialDerivative 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame i)) μ :=
    integrable_radialDerivative_product _ _ _ _ (d.continuousGradient i) (d.continuousGradient i)
      (fun e => (d.gradientConstraints e).1 i) (fun e => (d.gradientConstraints e).1 i)
      (d.radial_integrable i).aestronglyMeasurable (d.radial_integrable i).aestronglyMeasurable
  have hqp (i : Fin 4) : Integrable (fun e =>
      regularizedRadialDerivative 0 (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame i) *
      regularizedRadialDerivative 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame i)) μ :=
    integrable_radialDerivative_product _ _ _ _ (o.continuousGradient i) (d.continuousGradient i)
      (fun e => (o.gradientConstraints e).1 i) (fun e => (d.gradientConstraints e).1 i)
      (r.opposite_radial_integrable i).aestronglyMeasurable (d.radial_integrable i).aestronglyMeasurable
  have hs := integrable_finsetSum Finset.univ (fun i _ =>
    (integrable_continuous_weight (hpp i) kv).add (integrable_continuous_weight (hqp i) kb))
  have h := (integrable_continuous_weight d.scalarNorm_integrable k).add hs
  apply h.congr
  filter_upwards [] with e
  dsimp only [k, kv, kb, ContinuousMap.coe_mk]
  unfold kappaNormIntegrand regularizedKappaDerivative
  rw [regularizedBlockNorm_zero, regularizedBlockNorm_zero]
  simp only [Pi.add_apply, add_mul, mul_assoc, Finset.sum_add_distrib]

theorem opposite_kappaTest_integrable (o : OppositeWeylData d) :
    Integrable (fun e => kappaNormIntegrand (minusWeyl g e.base e.frame)
      (plusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)
      (plusWeylGradient g e.base e.frame)) μ := by
  exact (r.preserves.integrable_comp_of_integrable (r.kappaTest_integrable o)).congr
    (Eventually.of_forall kappaNormIntegrand_frameReflection)

theorem traceDeficit_integrable (o : OppositeWeylData d) :
    Integrable (d.traceDeficitIntegrand o) μ := by
  have h1 := (integrable_continuous_weight r.jointScalarNorm_integrable d.totalEnergyField).neg
  have h2 := (((d.deficitField o).continuous.mul d.totalEnergyField.continuous).const_mul 26).integrable_of_hasCompactSupport
    (μ := μ) (HasCompactSupport.of_compactSpace _)
  have h3 := (((d.deficitField o).continuous.mul d.jointMatrixEnergy.continuous).const_mul 40).integrable_of_hasCompactSupport
    (μ := μ) (HasCompactSupport.of_compactSpace _)
  have h4 := ((d.deficitField o).continuous.mul d.jointTraceEnergy.continuous).integrable_of_hasCompactSupport
    (μ := μ) (HasCompactSupport.of_compactSpace _)
  apply (((h1.sub h2).add h3).sub h4).congr
  filter_upwards [] with e
  dsimp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.mul_apply,
    MetricGreenData.traceDeficitIntegrand]
  ring

end FrameReflectionData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Express the reflected continuous fields as the actual opposite-block
contractions, so the trace-energy inequality can be used in scalar form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem matrixSlotAction_smul_right (A Z : Mat) (c : ℝ) :
    matrixSlotAction A (c • Z) = c • matrixSlotAction A Z := by
  simpa using QuaternionFrame.matrixSlotAction_sum_smul (ι := Unit) A (fun _ => c) (fun _ => Z)

theorem matrixPairing_same_smul (A B : Mat) (c : ℝ) :
    matrixPairing (c • A) (c • B) = c ^ 2 * matrixPairing A B := by
  simp only [matrixPairing, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weylMatrixEnergy_reflected (A : Mat) (Z : Angular.Gradient) :
    weylMatrixEnergy A (reflectedGradient Z) = weylMatrixEnergy A Z := by
  unfold weylMatrixEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [reflectedGradient, matrixSlotAction_smul_right, matrixPairing_same_smul,
    orientationSign_sq, one_mul]

theorem hessianNormSq_reflected (X : Hessian) :
    hessianNormSq (fun i j => (orientationSign i * orientationSign j) • X i j) =
      hessianNormSq X := by
  simp only [hessianNormSq, Matrix.smul_apply, smul_eq_mul, mul_pow,
    orientationSign_sq, one_mul]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace MetricGreenData

theorem jointMatrixEnergy_apply (d : MetricGreenData g μ) (e : FrameBundle g) :
    d.jointMatrixEnergy e =
      weylMatrixEnergy (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) +
      weylMatrixEnergy (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame) := by
  have hz : plusWeylGradient g e.base e.frame.reflect =
      reflectedGradient (minusWeylGradient g e.base e.frame) := by
    funext i
    exact plusWeylGradient_reflect g e.base e.frame i
  change _ + weylMatrixEnergy (plusWeyl g e.base e.frame.reflect)
    (plusWeylGradient g e.base e.frame.reflect) = _
  rw [plusWeyl_reflect, hz, weylMatrixEnergy_reflected]
  rfl

theorem jointTraceEnergy_apply (d : MetricGreenData g μ) (e : FrameBundle g) :
    d.jointTraceEnergy e = traceEnergy (plusWeyl g e.base e.frame) +
      traceEnergy (minusWeyl g e.base e.frame) := by
  change _ + traceEnergy (plusWeyl g e.base e.frame.reflect) = _
  rw [plusWeyl_reflect]

theorem jointHessianEnergy_apply (d : MetricGreenData g μ) (e : FrameBundle g) :
    d.jointHessianEnergy e = hessianNormSq (plusWeylHessian g e.base e.frame) / 3 +
      hessianNormSq (minusWeylHessian g e.base e.frame) / 3 := by
  have hx : plusWeylHessian g e.base e.frame.reflect =
      (fun i j => (orientationSign i * orientationSign j) • minusWeylHessian g e.base e.frame i j) := by
    funext i j
    exact plusWeylHessian_reflect g e.base e.frame i j
  change ((hessianNormSq (plusWeylHessian g e.base e.frame) / 3 +
      26 * weylGradientEnergy (plusWeylGradient g e.base e.frame) -
      40 * weylMatrixEnergy (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)) +
    (hessianNormSq (plusWeylHessian g e.base e.frame.reflect) / 3 +
      26 * weylGradientEnergy (plusWeylGradient g e.base e.frame.reflect) -
      40 * weylMatrixEnergy (plusWeyl g e.base e.frame.reflect) (plusWeylGradient g e.base e.frame.reflect))) -
    26 * (weylGradientEnergy (plusWeylGradient g e.base e.frame) +
      weylGradientEnergy (plusWeylGradient g e.base e.frame.reflect)) +
    40 * (weylMatrixEnergy (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) +
      weylMatrixEnergy (plusWeyl g e.base e.frame.reflect) (plusWeylGradient g e.base e.frame.reflect)) = _
  rw [hx, hessianNormSq_reflected]
  ring

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Euclidean tensor pairing is unchanged by an orthogonal frame change. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

/-- Pairing of all components of a covariant tensor in an orthonormal frame. -/
def frameTensorPairing {n : ℕ} (T U : CovariantCoordinates n) : ℝ := ∑ a, T a * U a

def frameTensorSquareNorm {n : ℕ} (T : CovariantCoordinates n) : ℝ := frameTensorPairing T T

private def pairingConsEquiv (n : ℕ) :
    (Fin 4 × (Fin n → Fin 4)) ≃ (Fin (n + 1) → Fin 4) where
  toFun p := Fin.cons p.1 p.2
  invFun a := (a 0, fun i => a i.succ)
  left_inv p := by cases p; rfl
  right_inv a := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

theorem sum_tensor_indices_cons {n : ℕ} (f : (Fin (n + 1) → Fin 4) → ℝ) :
    (∑ a, f a) = ∑ d, ∑ a : Fin n → Fin 4, f (Fin.cons d a) := by
  have h := (pairingConsEquiv n).sum_comp f
  have hp : (∑ p : Fin 4 × (Fin n → Fin 4), f (pairingConsEquiv n p)) =
      ∑ d, ∑ a : Fin n → Fin 4, f (Fin.cons d a) := by
    rw [Fintype.sum_prod_type]
    rfl
  exact h.symm.trans hp

private theorem orthogonal_covector_pairing (P : Mat4) (hP : P * Pᵀ = 1)
    (x y : Fin 4 → ℝ) :
    (∑ i, (∑ a, P a i * x a) * (∑ b, P b i * y b)) = ∑ a, x a * y a := by
  have hg (a b : Fin 4) : (∑ i, P a i * P b i) = if a = b then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      congrArg (fun A : Mat4 => A a b) hP
  calc
    _ = ∑ a, ∑ b, (∑ i, P a i * P b i) * (x b * y a) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by simp only [hg, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem frameTensor_pairing_orthogonal {n : ℕ} (P : Mat4) (hP : P * Pᵀ = 1)
    (T U : CovariantCoordinates n) :
    frameTensorPairing (frameTensor P T) (frameTensor P U) = frameTensorPairing T U := by
  induction n with
  | zero =>
    simp only [frameTensorPairing, frameTensor_zero]
  | succ n ih =>
    unfold frameTensorPairing
    rw [sum_tensor_indices_cons, sum_tensor_indices_cons]
    simp only [frameTensor_cons]
    calc
      _ = ∑ a : Fin n → Fin 4, ∑ i,
          (∑ b, P b i * frameTensor P (fun w => T (Fin.cons b w)) a) *
            (∑ b, P b i * frameTensor P (fun w => U (Fin.cons b w)) a) :=
        Finset.sum_comm
      _ = ∑ a : Fin n → Fin 4, ∑ b,
          frameTensor P (fun w => T (Fin.cons b w)) a *
            frameTensor P (fun w => U (Fin.cons b w)) a := by
        apply Finset.sum_congr rfl
        intro a _
        exact orthogonal_covector_pairing P hP _ _
      _ = ∑ b, ∑ a : Fin n → Fin 4,
          frameTensor P (fun w => T (Fin.cons b w)) a *
            frameTensor P (fun w => U (Fin.cons b w)) a := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro b _
        exact ih (fun w => T (Fin.cons b w)) (fun w => U (Fin.cons b w))

theorem frameTensor_norm_orthogonal {n : ℕ} (P : Mat4) (hP : P * Pᵀ = 1)
    (T : CovariantCoordinates n) :
    frameTensorSquareNorm (frameTensor P T) = frameTensorSquareNorm T :=
  frameTensor_pairing_orthogonal P hP T T

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem frameTensor_norm_same_base {n : ℕ} (e f : OrthonormalFrame g c)
    (T : CovariantCoordinates n) :
    frameTensorSquareNorm (frameTensor e.matrix T) =
      frameTensorSquareNorm (frameTensor f.matrix T) := by
  have hf : f.matrix = e.matrix * e.changeMatrix f := (e.mul_changeMatrix f).symm
  rw [hf, frameTensor_mul, frameTensor_norm_orthogonal _
    (mul_eq_one_comm.mp (e.changeMatrix_orthogonal f))]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The sum of the two Hessian inequalities, the trace-deficit inequality,
and both polynomial norm tests. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace MetricGreenData

def preVarianceIntegrand (d : MetricGreenData g μ) (o : OppositeWeylData d)
    (e : FrameBundle g) : ℝ :=
  regularizedHessianIntegrand g 0 e + regularizedHessianIntegrand g 0 (frameReflection e) +
    (17 / 10 : ℝ) * d.traceDeficitIntegrand o e +
    kappaNormIntegrand (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame) (minusWeylGradient g e.base e.frame) +
    kappaNormIntegrand (minusWeyl g e.base e.frame) (plusWeyl g e.base e.frame)
      (minusWeylGradient g e.base e.frame) (plusWeylGradient g e.base e.frame)

end MetricGreenData

namespace FrameReflectionData

variable {d : MetricGreenData g μ} (r : FrameReflectionData d)
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

include r

theorem jointHessianGreen (o : OppositeWeylData d)
    (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    0 ≤ ∫ e, regularizedHessianIntegrand g 0 e +
      regularizedHessianIntegrand g 0 (frameReflection e) ∂μ := by
  have hi := d.hessianIntegrand_integrable o hpinch
  have hsplit := integral_add hi (r.preserves.integrable_comp_of_integrable hi)
  simp only [Function.comp_def] at hsplit
  rw [hsplit, r.integral_reflection]
  have h := d.unregularizedHessianGreen o hp hdecomp hpinch
  linarith only [h]

theorem preVarianceIntegrand_integrable (o : OppositeWeylData d)
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    Integrable (d.preVarianceIntegrand o) μ := by
  have hi := d.hessianIntegrand_integrable o hpinch
  exact ((((hi.add (r.preserves.integrable_comp_of_integrable hi)).add
    ((r.traceDeficit_integrable o).const_mul (17 / 10))).add
      (r.kappaTest_integrable o)).add (r.opposite_kappaTest_integrable o))

theorem preVarianceGreen (o : OppositeWeylData d)
    (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    0 ≤ ∫ e, d.preVarianceIntegrand o e ∂μ := by
  have hi := d.hessianIntegrand_integrable o hpinch
  have hj := hi.add (r.preserves.integrable_comp_of_integrable hi)
  have ht := (r.traceDeficit_integrable o).const_mul (17 / 10)
  have hk := r.kappaTest_integrable o
  have hb := r.opposite_kappaTest_integrable o
  have hs1 := integral_add ((hj.add ht).add hk) hb
  have hs2 := integral_add (hj.add ht) hk
  have hs3 := integral_add hj ht
  simp only [Pi.add_apply, Function.comp_def] at hs1 hs2 hs3
  have hk0 : (∫ e, kappaNormIntegrand (plusWeyl g e.base e.frame)
      (minusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)
      (minusWeylGradient g e.base e.frame) ∂μ) = 0 := d.kappaTest o hpinch
  unfold MetricGreenData.preVarianceIntegrand
  rw [hs1, hs2, hs3, integral_const_mul, hk0,
    r.opposite_kappaTest o hpinch, add_zero, add_zero]
  exact add_nonneg (r.jointHessianGreen o hp hdecomp hpinch)
    (mul_nonneg (by norm_num) (r.traceDeficit_integral_nonneg o hpinch))

end FrameReflectionData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identify the actual metric integral with the finite-array integrand.
Only fixed frame reflection is used for the second Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi QuaternionFrame MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

def weylWeightGradient (A U : Mat) (Z V : Angular.Gradient) : Vec :=
  WithLp.toLp 2 (fun i => regularizedWeylWeightDerivative 0 A U (Z i) (V i))

def reflectedVector (p : Vec) : Vec :=
  WithLp.toLp 2 (fun i => orientationSign i * p i)

theorem reflectedVector_norm (p : Vec) : ‖reflectedVector p‖ = ‖p‖ := by
  have hs : ‖reflectedVector p‖ ^ 2 = ‖p‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, reflectedVector, mul_pow,
      orientationSign_sq, one_mul]
  nlinarith [norm_nonneg (reflectedVector p), norm_nonneg p]

theorem blockRadialGradient_reflected (A : Mat) (Z : Angular.Gradient) :
    blockRadialGradient A (reflectedGradient Z) = reflectedVector (blockRadialGradient A Z) := by
  ext i
  exact regularizedRadialDerivative_smul 0 A (Z i) (orientationSign i)

theorem weylWeightGradient_eq (A U : Mat) (Z V : Angular.Gradient) :
    weylWeightGradient A U Z V =
      (-(3 / 4 : ℝ) * (1 - (3 / 8 : ℝ) * (normalizedBlockNorm A - normalizedBlockNorm U))) •
        (blockRadialGradient A Z - blockRadialGradient U V) := by
  ext i
  simp only [weylWeightGradient, regularizedWeylWeightDerivative,
    regularizedBlockNorm_zero, blockRadialGradient, PiLp.smul_apply, PiLp.sub_apply,
    smul_eq_mul]

theorem weylWeightGradient_reflected (A U : Mat) (Z V : Angular.Gradient) :
    weylWeightGradient A U (reflectedGradient Z) (reflectedGradient V) =
      reflectedVector (weylWeightGradient A U Z V) := by
  ext i
  change regularizedWeylWeightDerivative 0 A U
    (orientationSign i • Z i) (orientationSign i • V i) = _
  unfold regularizedWeylWeightDerivative
  rw [regularizedRadialDerivative_smul, regularizedRadialDerivative_smul]
  change _ = orientationSign i * regularizedWeylWeightDerivative 0 A U (Z i) (V i)
  unfold regularizedWeylWeightDerivative
  ring

theorem kappaNormIntegrand_pair (A U : Mat) (Z V : Angular.Gradient) :
    kappaNormIntegrand A U Z V + kappaNormIntegrand U A V Z =
      Potential.kappa (normalizedBlockNorm A) (normalizedBlockNorm U) * scalarNormExpression 0 A Z +
      Potential.kappa (normalizedBlockNorm U) (normalizedBlockNorm A) * scalarNormExpression 0 U V +
      Quadratic.kappaV (normalizedBlockNorm A) (normalizedBlockNorm U) * ‖blockRadialGradient A Z‖ ^ 2 +
      (Quadratic.kappaB (normalizedBlockNorm A) (normalizedBlockNorm U) +
        Quadratic.kappaB (normalizedBlockNorm U) (normalizedBlockNorm A)) *
          inner ℝ (blockRadialGradient A Z) (blockRadialGradient U V) +
      Quadratic.kappaV (normalizedBlockNorm U) (normalizedBlockNorm A) * ‖blockRadialGradient U V‖ ^ 2 := by
  simp only [kappaNormIntegrand, regularizedKappa, regularizedKappaDerivative,
    regularizedBlockNorm_zero, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, blockRadialGradient]
  simp only [Finset.sum_add_distrib, add_mul, Fin.sum_univ_four]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem regularizedHessianIntegrand_eq_arrayHessianTerm (e : FrameBundle g) :
    regularizedHessianIntegrand g 0 e =
      arrayHessianTerm (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame)
        (weylWeightGradient (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame) (minusWeylGradient g e.base e.frame)) := by
  unfold regularizedHessianIntegrand arrayHessianTerm weylWeightGradient
    regularizedWeylWeight Quadratic.weight weightedCubicField
  simp only [regularizedBlockNorm_zero]
  congr 2 <;> ring

theorem reflectedHessianIntegrand_eq_arrayHessianTerm (e : FrameBundle g) :
    regularizedHessianIntegrand g 0 (frameReflection e) =
      arrayHessianTerm (minusWeyl g e.base e.frame) (plusWeyl g e.base e.frame)
        (reflectedGradient (minusWeylGradient g e.base e.frame))
        (reflectedVector (weylWeightGradient (minusWeyl g e.base e.frame) (plusWeyl g e.base e.frame)
          (minusWeylGradient g e.base e.frame) (plusWeylGradient g e.base e.frame))) := by
  rw [regularizedHessianIntegrand_eq_arrayHessianTerm]
  have hp : plusWeylGradient g e.base e.frame.reflect =
      reflectedGradient (minusWeylGradient g e.base e.frame) := by
    funext i
    exact plusWeylGradient_reflect g e.base e.frame i
  have hm : minusWeylGradient g e.base e.frame.reflect =
      reflectedGradient (plusWeylGradient g e.base e.frame) := by
    funext i
    exact minusWeylGradient_reflect g e.base e.frame i
  dsimp only [frameReflection]
  rw [plusWeyl_reflect, minusWeyl_reflect, hp, hm, weylWeightGradient_reflected]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normalization of the two quaternionic blocks in the full tensor norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular
open scoped BigOperators

noncomputable section

def blockTensorCoordinates (A : Mat3) (Q : Fin 3 → Mat4) : CovariantCoordinates 4 :=
  fun a => blockTensor A Q (a 0) (a 1) (a 2) (a 3)

theorem frameTensorPairing_add_right {n : ℕ} (R S T : CovariantCoordinates n) :
    frameTensorPairing R (S + T) = frameTensorPairing R S + frameTensorPairing R T := by
  simp only [frameTensorPairing, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem frameTensorPairing_const_mul_right {n : ℕ} (R T : CovariantCoordinates n) (c : ℝ) :
    frameTensorPairing R (fun a => c * T a) = c * frameTensorPairing R T := by
  simp only [frameTensorPairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem frameTensorPairing_sum_right {n : ℕ} {ι : Type*} [Fintype ι]
    (R : CovariantCoordinates n) (T : ι → CovariantCoordinates n) :
    frameTensorPairing R (fun a => ∑ i, T i a) = ∑ i, frameTensorPairing R (T i) := by
  simp only [frameTensorPairing, Finset.mul_sum]
  exact Finset.sum_comm

private theorem sum_four_coordinates (f : (Fin 4 → Fin 4) → ℝ) :
    (∑ a, f a) = ∑ i, ∑ j, ∑ k, ∑ l, f ![i, j, k, l] := by
  simp only [sum_tensor_indices_cons, Fintype.sum_unique]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  congr 1

theorem frameTensorPairing_twoFormProduct (R : CovariantCoordinates 4) (P Q : Mat4) :
    frameTensorPairing R (fun a => twoFormProduct P Q (a 0) (a 1) (a 2) (a 3)) =
      8 * twoFormPairing R P Q := by
  rw [frameTensorPairing, sum_four_coordinates]
  change (∑ i, ∑ j, ∑ k, ∑ l, R ![i, j, k, l] * (P i j * Q l k)) =
    8 * ((1 / 8 : ℝ) * ∑ i, ∑ j, ∑ l, ∑ k, R ![i, j, k, l] * P i j * Q l k)
  rw [show ∀ x : ℝ, 8 * ((1 / 8 : ℝ) * x) = x by intro x; ring]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Block assembly is four times the adjoint of the normalized block contraction. -/
theorem frameTensorPairing_blockTensor (R : CovariantCoordinates 4)
    (A : Mat3) (Q : Fin 3 → Mat4) :
    frameTensorPairing R (blockTensorCoordinates A Q) =
      4 * matrixPairing A (blockCoordinates R Q) := by
  have hb : blockTensorCoordinates A Q = fun a =>
      (1 / 2 : ℝ) * ∑ s, ∑ t, A s t *
        twoFormProduct (Q s) (Q t) (a 0) (a 1) (a 2) (a 3) := by
    funext a
    simp only [blockTensorCoordinates, blockTensor, Pi.smul_apply,
      Finset.sum_apply, smul_eq_mul]
  rw [hb, frameTensorPairing_const_mul_right]
  simp only [frameTensorPairing_sum_right, frameTensorPairing_const_mul_right,
    frameTensorPairing_twoFormProduct, ← blockCoordinates_pairing]
  simp only [matrixPairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem frameTensorSquareNorm_of_blocks (R : CovariantCoordinates 4) (A B : Mat3)
    (hR : R = blockTensorCoordinates A quaternionMatrix + blockTensorCoordinates B oppositeMatrix)
    (hA : blockCoordinates R quaternionMatrix = A)
    (hB : blockCoordinates R oppositeMatrix = B) :
    frameTensorSquareNorm R = 4 * (squareNorm A + squareNorm B) := by
  change frameTensorPairing R R = _
  calc
    _ = frameTensorPairing R
        (blockTensorCoordinates A quaternionMatrix + blockTensorCoordinates B oppositeMatrix) :=
      congrArg (frameTensorPairing R) hR
    _ = _ := by
      rw [frameTensorPairing_add_right, frameTensorPairing_blockTensor,
        frameTensorPairing_blockTensor, hA, hB]
      simp only [matrixPairing, squareNorm, pow_two]
      ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two total Weyl energies are base scalars, proved from the actual
orthonormal-frame tensor norm and the quaternionic normalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular
open scoped Manifold ContDiff BigOperators

noncomputable section

private theorem squareNorm_one_add (A : Mat3) (ht : A.trace = 0) :
    squareNorm (1 + A) = 3 + squareNorm A := by
  have h : squareNorm (1 + A) = 3 + 2 * A.trace + squareNorm A := by
    simp only [squareNorm, Matrix.add_apply, Matrix.one_apply, Matrix.trace,
      Matrix.diag, Fin.sum_univ_three]
    norm_num
    ring
  rw [h, ht]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

private theorem curvature_blockCoordinates (e : OrthonormalFrame g c)
    (Q : Fin 3 → Mat4) :
    blockCoordinates (frameTensor e.matrix
      (curvatureCoordinates g c (chartAt FourSpace c c))) Q =
      curvatureBlock (curvaturePairing g c e) Q := by
  ext s t
  simp only [blockCoordinates, curvatureBlock]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [frameTensor_curvatureCoordinates]
  rfl

theorem frame_curvature_norm_energy (e : OrthonormalFrame g c) (hRic : RicciThree g) :
    frameTensorSquareNorm (frameTensor e.matrix
      (curvatureCoordinates g c (chartAt FourSpace c c))) =
      24 + 24 * (normalizedBlockNorm (plusWeyl g c e) ^ 2 +
        normalizedBlockNorm (minusWeyl g c e) ^ 2) := by
  let R := frameTensor e.matrix (curvatureCoordinates g c (chartAt FourSpace c c))
  have hR : R = blockTensorCoordinates (1 + plusWeyl g c e) quaternionMatrix +
      blockTensorCoordinates (1 + minusWeyl g c e) oppositeMatrix := by
    funext a
    have ha : a = ![a 0, a 1, a 2, a 3] := by
      funext i
      fin_cases i <;> rfl
    dsimp only [R]
    rw [ha, frameTensor_curvatureCoordinates, actual_einstein_decomposition e hRic]
    rfl
  have hA : blockCoordinates R quaternionMatrix = 1 + plusWeyl g c e := by
    dsimp only [R]
    rw [curvature_blockCoordinates]
    unfold plusWeyl
    abel
  have hB : blockCoordinates R oppositeMatrix = 1 + minusWeyl g c e := by
    dsimp only [R]
    rw [curvature_blockCoordinates]
    unfold minusWeyl
    abel
  have h := frameTensorSquareNorm_of_blocks R _ _ hR hA hB
  have ht := actual_weyl_traceFree e hRic
  rw [squareNorm_one_add (plusWeyl g c e) ht.1,
    squareNorm_one_add (minusWeyl g c e) ht.2] at h
  have hpa := normalizedBlockNorm_sq (plusWeyl g c e)
  have hpb := normalizedBlockNorm_sq (minusWeyl g c e)
  change normalizedBlockNorm (plusWeyl g c e) ^ 2 = squareNorm (plusWeyl g c e) / 6 at hpa
  change normalizedBlockNorm (minusWeyl g c e) ^ 2 = squareNorm (minusWeyl g c e) / 6 at hpb
  change frameTensorSquareNorm R = _
  linarith only [h, hpa, hpb]

theorem frame_weyl_norm_sum_same_base (e f : OrthonormalFrame g c) (hRic : RicciThree g) :
    normalizedBlockNorm (plusWeyl g c e) ^ 2 + normalizedBlockNorm (minusWeyl g c e) ^ 2 =
      normalizedBlockNorm (plusWeyl g c f) ^ 2 + normalizedBlockNorm (minusWeyl g c f) ^ 2 := by
  have he := frame_curvature_norm_energy e hRic
  have hf := frame_curvature_norm_energy f hRic
  have hnorm := frameTensor_norm_same_base e f
    (curvatureCoordinates g c (chartAt FourSpace c c))
  linarith only [he, hf, hnorm]

theorem frame_weyl_gradient_norm_energy (e : OrthonormalFrame g c) (hRic : RicciThree g) :
    frameTensorSquareNorm (frameTensor e.matrix
      (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c))) =
      4 * (gradientSquareNorm (plusWeylGradient g c e) +
        gradientSquareNorm (minusWeylGradient g c e)) := by
  let T := frameTensor e.matrix
    (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c))
  have hs (d : Fin 4) : frameTensorSquareNorm (fun a => T (Fin.cons d a)) =
      4 * (squareNorm (plusWeylGradient g c e d) + squareNorm (minusWeylGradient g c e d)) := by
    apply frameTensorSquareNorm_of_blocks
    · funext a
      have ha : a = ![a 0, a 1, a 2, a 3] := by
        funext i
        fin_cases i <;> rfl
      rw [ha]
      exact congrFun (congrFun (congrFun (congrFun
        (actual_weyl_derivative_decomposition e hRic d) (a 0)) (a 1)) (a 2)) (a 3)
    · rfl
    · rfl
  change (∑ a, T a * T a) = _
  rw [sum_tensor_indices_cons]
  change (∑ d, frameTensorSquareNorm (fun a => T (Fin.cons d a))) = _
  simp only [hs, Finset.sum_add_distrib, ← Finset.mul_sum, gradientSquareNorm]

theorem frame_weyl_gradient_sum_same_base (e f : OrthonormalFrame g c)
    (hRic : RicciThree g) :
    gradientSquareNorm (plusWeylGradient g c e) + gradientSquareNorm (minusWeylGradient g c e) =
      gradientSquareNorm (plusWeylGradient g c f) + gradientSquareNorm (minusWeylGradient g c f) := by
  have he := frame_weyl_gradient_norm_energy e hRic
  have hf := frame_weyl_gradient_norm_energy f hRic
  have hnorm := frameTensor_norm_same_base e f
    (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c))
  linarith only [he, hf, hnorm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The full finite-array integrand is the actual metric integral from
both Green identities, trace subtraction, variance, and polynomial tests. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi QuaternionFrame MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

def varianceDensity (A U : Mat) (p q : Vec) : ℝ :=
  ‖p - q‖ ^ 2 / (4 + normalizedBlockNorm A ^ 2 + normalizedBlockNorm U ^ 2) -
    (1 - (2 - normalizedBlockNorm A - normalizedBlockNorm U) ^ 2 / 4) *
      (normalizedBlockNorm A - normalizedBlockNorm U) ^ 2

def traceCouplingTerm (A U : Mat) (Z V : Angular.Gradient) : ℝ :=
  -(weylGradientEnergy Z + weylGradientEnergy V) *
      (scalarNormExpression 0 A Z + scalarNormExpression 0 U V) -
    26 * (2 - normalizedBlockNorm A - normalizedBlockNorm U) *
      (weylGradientEnergy Z + weylGradientEnergy V) +
    40 * (2 - normalizedBlockNorm A - normalizedBlockNorm U) *
      (weylMatrixEnergy A Z + weylMatrixEnergy U V) -
    (2 - normalizedBlockNorm A - normalizedBlockNorm U) * (traceEnergy A + traceEnergy U)

theorem scalarCouplingTerm_eq_trace_and_tests (A U : Mat) (Z V : Angular.Gradient) :
    scalarCouplingTerm (normalizedBlockNorm A) (normalizedBlockNorm U)
      (weylGradientEnergy Z) (weylGradientEnergy V)
      (weylMatrixEnergy A Z) (weylMatrixEnergy U V)
      (scalarNormExpression 0 A Z) (scalarNormExpression 0 U V)
      (traceEnergy A) (traceEnergy U) (blockRadialGradient A Z) (blockRadialGradient U V) =
    (17 / 10 : ℝ) * traceCouplingTerm A U Z V +
      158 * varianceDensity A U (blockRadialGradient A Z) (blockRadialGradient U V) +
      (kappaNormIntegrand A U Z V + kappaNormIntegrand U A V Z) := by
  rw [kappaNormIntegrand_pair]
  unfold scalarCouplingTerm traceCouplingTerm varianceDensity
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace MetricGreenData

theorem totalEnergyField_apply (d : MetricGreenData g μ) (e : FrameBundle g) :
    d.totalEnergyField e = weylGradientEnergy (plusWeylGradient g e.base e.frame) +
      weylGradientEnergy (minusWeylGradient g e.base e.frame) := by
  have hz : plusWeylGradient g e.base e.frame.reflect =
      reflectedGradient (minusWeylGradient g e.base e.frame) := by
    funext i
    exact plusWeylGradient_reflect g e.base e.frame i
  change _ + weylGradientEnergy (plusWeylGradient g e.base e.frame.reflect) = _
  rw [hz, reflectedGradient_energy]
  rfl

theorem traceDeficitIntegrand_eq_arrays (d : MetricGreenData g μ)
    (o : OppositeWeylData d) (e : FrameBundle g) :
    d.traceDeficitIntegrand o e = traceCouplingTerm
      (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame) (minusWeylGradient g e.base e.frame) := by
  unfold traceDeficitIntegrand
  rw [d.totalEnergyField_apply, d.jointMatrixEnergy_apply, d.jointTraceEnergy_apply]
  unfold deficitField regularizedDeficit jointScalarNorm
  simp only [ContinuousMap.coe_mk, regularizedBlockNorm_zero]
  unfold traceCouplingTerm
  ring

def coupledIntegrand (d : MetricGreenData g μ) (o : OppositeWeylData d)
    (e : FrameBundle g) : ℝ :=
  d.preVarianceIntegrand o e + 158 * varianceDensity
    (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
    (blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame))
    (blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame))

theorem coupledIntegrand_eq_array (d : MetricGreenData g μ)
    (o : OppositeWeylData d) (e : FrameBundle g) :
    d.coupledIntegrand o e =
      arrayCoupledIntegrand (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) (reflectedGradient (minusWeylGradient g e.base e.frame))
        (weylWeightGradient (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame) (minusWeylGradient g e.base e.frame))
        (reflectedVector (weylWeightGradient (minusWeyl g e.base e.frame) (plusWeyl g e.base e.frame)
          (minusWeylGradient g e.base e.frame) (plusWeylGradient g e.base e.frame)))
        (blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame))
        (blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)) := by
  unfold coupledIntegrand preVarianceIntegrand
  rw [regularizedHessianIntegrand_eq_arrayHessianTerm,
    reflectedHessianIntegrand_eq_arrayHessianTerm, d.traceDeficitIntegrand_eq_arrays]
  unfold arrayCoupledIntegrand
  rw [reflectedGradient_energy, weylMatrixEnergy_reflected, scalarNormExpression_reflected,
    scalarCouplingTerm_eq_trace_and_tests]
  ring

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Apply the finite-array estimate to the actual two Weyl blocks.
The zero faces are supplied by the almost-everywhere derivative theorem. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi QuaternionFrame MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem weylWeightGradient_norm_sq (A U : Mat) (Z V : Angular.Gradient) :
    ‖weylWeightGradient A U Z V‖ ^ 2 =
      (9 / 16 : ℝ) * Energy.scalarWeight (normalizedBlockNorm A) (normalizedBlockNorm U) ^ 2 *
        ‖blockRadialGradient A Z - blockRadialGradient U V‖ ^ 2 := by
  rw [weylWeightGradient_eq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  unfold Energy.scalarWeight
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

def plusRadialEnergy (e : FrameBundle g) : ℝ :=
  ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2

def minusRadialEnergy (e : FrameBundle g) : ℝ :=
  ‖blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)‖ ^ 2

theorem MetricGreenData.coupledIntegrand_bound (d : MetricGreenData g μ)
    (o : OppositeWeylData d) [SFinite μ] (hp : ShiftedCurvaturePositive g) :
    ∀ᵐ e ∂μ, d.coupledIntegrand o e ≤
      -couplingCoefficient (d.plusNormField e) (d.minusNormField o e) *
        ((plusRadialEnergy e + minusRadialEnergy e) *
          (plusRadialEnergy e / d.plusNormField e + minusRadialEnergy e / d.minusNormField o e)) +
      2 * Potential.theta (d.plusNormField e) (d.minusNormField o e) *
        (normWeight (d.plusNormField e) * plusRadialEnergy e +
          normWeight (d.minusNormField o e) * minusRadialEnergy e) -
      Potential.theta (d.plusNormField e) (d.minusNormField o e) ^ 2 /
        couplingCoefficient (d.plusNormField e) (d.minusNormField o e) := by
  filter_upwards [d.gradient_zero_ae_on_zero, o.gradient_zero_ae_on_zero] with e he hoe
  let A := plusWeyl g e.base e.frame
  let U := minusWeyl g e.base e.frame
  let Z := plusWeylGradient g e.base e.frame
  let V := minusWeylGradient g e.base e.frame
  have hVs (i) : symmetric (reflectedGradient V i) := by
    intro a b
    change orientationSign i * V i a b = orientationSign i * V i b a
    exact congrArg (fun t : ℝ => orientationSign i * t) ((o.gradientConstraints e).1 i a b)
  have hVt (i) : traceFree (reflectedGradient V i) := by
    change (∑ a, orientationSign i * V i a a) = 0
    rw [← Finset.mul_sum, (o.gradientConstraints e).2 i, mul_zero]
  have hVb (r i) : gradientDivergence (reflectedGradient V) r i = 0 := by
    rw [reflectedGradient_divergence, o.gradientBianchi e, mul_zero]
  have hzero : normalizedBlockNorm A = 0 → Z = 0 := by
    intro h
    exact funext (he ((normalizedBlockNorm_eq_zero_iff A).mp h))
  have hzerob : normalizedBlockNorm U = 0 → reflectedGradient V = 0 := by
    intro h
    have hv : V = 0 := funext (hoe ((normalizedBlockNorm_eq_zero_iff U).mp h))
    funext i
    change orientationSign i • V i = 0
    rw [hv]
    exact smul_zero _
  obtain ⟨x, y, hx, hy, hxy⟩ := hp e
  have ha := weylWeightGradient_norm_sq A U Z V
  have hab : ‖reflectedVector (weylWeightGradient U A V Z)‖ ^ 2 =
      (9 / 16 : ℝ) * Energy.scalarWeight (normalizedBlockNorm U) (normalizedBlockNorm A) ^ 2 *
        ‖blockRadialGradient A Z - blockRadialGradient U V‖ ^ 2 := by
    rw [reflectedVector_norm, weylWeightGradient_norm_sq, norm_sub_rev]
  have h := pointwise_coupling_bound_closed A U Z (reflectedGradient V)
    (weylWeightGradient A U Z V) (reflectedVector (weylWeightGradient U A V Z))
    (blockRadialGradient A Z) (blockRadialGradient U V)
    (d.weyl.symmetric e) (o.symmetric e) (d.weyl.traceFree e) (o.traceFree e)
    (d.gradientConstraints e).1 (d.gradientConstraints e).2 (d.gradientBianchi e)
    hVs hVt hVb hzero hzerob x y hx hy hxy rfl
    (reflectedGradient_radial_norm U V).symm ha hab
  rw [d.coupledIntegrand_eq_array o e]
  simp only [MetricGreenData.plusNormField, MetricGreenData.minusNormField,
    MetricGreenData.plusMatrixMap, MetricGreenData.minusMatrixMap,
    ContinuousMap.coe_mk, plusRadialEnergy, minusRadialEnergy]
  convert h using 1
  ring

theorem MetricGreenData.radialEnergy_support (d : MetricGreenData g μ)
    (o : OppositeWeylData d) [SFinite μ] :
    ∀ᵐ e ∂μ, (d.plusNormField e = 0 → plusRadialEnergy e = 0) ∧
      (d.minusNormField o e = 0 → minusRadialEnergy e = 0) ∧
      (d.plusNormField e = 1 → plusRadialEnergy e = 0) ∧
      (d.minusNormField o e = 1 → minusRadialEnergy e = 0) := by
  filter_upwards [d.radial_zero_ae_on_level 0, o.radial_zero_ae_on_level 0,
    d.radial_zero_ae_on_level 1, o.radial_zero_ae_on_level 1] with e hp hq hp1 hq1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    simp only [plusRadialEnergy, hp h, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  · intro h
    simp only [minusRadialEnergy, hq h, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  · intro h
    simp only [plusRadialEnergy, hp1 h, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  · intro h
    simp only [minusRadialEnergy, hq1 h, norm_zero, zero_pow (by decide : 2 ≠ 0)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrability of the actual radial difference and the exact variance
correction. The weighted variance inequality remains a separate geometric
obligation; the mean correction is derived from equal second moments. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace FrameReflectionData

variable {d : MetricGreenData g μ} (r : FrameReflectionData d)
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

include r

theorem radialDifferenceSq_integrable (o : OppositeWeylData d) :
    Integrable (fun e => ‖blockRadialGradient (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame) -
        blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)‖ ^ 2) μ := by
  let p : Fin 4 → FrameBundle g → ℝ := fun i e => regularizedRadialDerivative 0
    (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame i)
  let q : Fin 4 → FrameBundle g → ℝ := fun i e => regularizedRadialDerivative 0
    (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame i)
  have hp (i) : AEStronglyMeasurable (p i) μ := (d.radial_integrable i).aestronglyMeasurable
  have hq (i) : AEStronglyMeasurable (q i) μ := (r.opposite_radial_integrable i).aestronglyMeasurable
  have hpp (i) : Integrable (fun e => p i e * p i e) μ :=
    integrable_radialDerivative_product _ _ _ _ (d.continuousGradient i) (d.continuousGradient i)
      (fun e => (d.gradientConstraints e).1 i) (fun e => (d.gradientConstraints e).1 i) (hp i) (hp i)
  have hpq (i) : Integrable (fun e => p i e * q i e) μ :=
    integrable_radialDerivative_product _ _ _ _ (d.continuousGradient i) (o.continuousGradient i)
      (fun e => (d.gradientConstraints e).1 i) (fun e => (o.gradientConstraints e).1 i) (hp i) (hq i)
  have hqq (i) : Integrable (fun e => q i e * q i e) μ :=
    integrable_radialDerivative_product _ _ _ _ (o.continuousGradient i) (o.continuousGradient i)
      (fun e => (o.gradientConstraints e).1 i) (fun e => (o.gradientConstraints e).1 i) (hq i) (hq i)
  have h := integrable_finsetSum Finset.univ (fun i _ =>
    ((hpp i).sub ((hpq i).const_mul 2)).add (hqq i))
  apply h.congr
  filter_upwards [] with e
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Pi.add_apply, Pi.sub_apply, PiLp.sub_apply]
  apply Finset.sum_congr rfl
  intro i _
  change p i e * p i e - 2 * (p i e * q i e) + q i e * q i e = (p i e - q i e) ^ 2
  ring

theorem radialVarianceEnergy_integrable (o : OppositeWeylData d) :
    Integrable (fun e => ‖blockRadialGradient (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame) -
        blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)‖ ^ 2 /
      (4 + normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 +
        normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2)) μ := by
  let K : C(FrameBundle g, ℝ) := ⟨fun e => 1 /
    (4 + d.plusNormField e ^ 2 + d.minusNormField o e ^ 2), by
      apply continuous_const.div
      · fun_prop
      · intro e
        positivity⟩
  have h := integrable_continuous_weight (r.radialDifferenceSq_integrable o) K
  apply h.congr
  filter_upwards [] with e
  simp only [K, MetricGreenData.plusNormField, MetricGreenData.minusNormField,
    MetricGreenData.plusMatrixMap, MetricGreenData.minusMatrixMap, ContinuousMap.coe_mk]
  ring

theorem varianceDensity_integrable (o : OppositeWeylData d) :
    Integrable (fun e => varianceDensity (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame))
      (blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame))) μ := by
  have hc : Continuous (fun e : FrameBundle g =>
      (1 - (2 - d.plusNormField e - d.minusNormField o e) ^ 2 / 4) *
        (d.plusNormField e - d.minusNormField o e) ^ 2) := by fun_prop
  exact (r.radialVarianceEnergy_integrable o).sub
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

theorem coupledIntegrand_integrable (o : OppositeWeylData d)
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    Integrable (d.coupledIntegrand o) μ :=
  (r.preVarianceIntegrand_integrable o hpinch).add ((r.varianceDensity_integrable o).const_mul 158)

omit [IsFiniteMeasure μ] in
/-- This is the integral assembly conditional on the separate weighted
variance statement, not a published-input classification theorem. -/
theorem coupledIntegral_nonneg (o : OppositeWeylData d) [IsProbabilityMeasure μ]
    (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2)
    (hsecond : (∫ e, d.plusNormField e ^ 2 ∂μ) = ∫ e, d.minusNormField o e ^ 2 ∂μ)
    (hvariance : (∫ e, (d.plusNormField e - d.minusNormField o e) ^ 2 ∂μ) -
      (∫ e, d.plusNormField e - d.minusNormField o e ∂μ) ^ 2 ≤
      ∫ e, ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) -
        blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)‖ ^ 2 /
        (4 + d.plusNormField e ^ 2 + d.minusNormField o e ^ 2) ∂μ) :
    0 ≤ ∫ e, d.coupledIntegrand o e ∂μ := by
  have hv := Variance.variance_correction_nonneg d.plusNormField (d.minusNormField o) _
    d.plusNormField.continuous (d.minusNormField o).continuous
    (r.radialVarianceEnergy_integrable o) hsecond hvariance
  have hi := r.preVarianceGreen o hp hdecomp hpinch
  change 0 ≤ ∫ e, d.preVarianceIntegrand o e + 158 * varianceDensity _ _ _ _ ∂μ
  rw [integral_add (r.preVarianceIntegrand_integrable o hpinch)
    ((r.varianceDensity_integrable o).const_mul 158), integral_const_mul]
  exact add_nonneg hi (mul_nonneg (by norm_num) hv)

end FrameReflectionData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Orientation distinguishes the two explicit quaternionic two-form spaces. -/

namespace PositiveEinsteinFour.QuaternionFrame

open Matrix TraceHessian PositiveEinsteinFour.Geometry
open Angular (oppositeMatrix)
open scoped BigOperators

noncomputable section

/-- The Pfaffian with respect to the fixed orientation of four coordinates. -/
def pfaffianFour (A : Mat4) : ℝ :=
  A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2

def upperSquareFour (A : Mat4) : ℝ :=
  A 0 1 ^ 2 + A 0 2 ^ 2 + A 0 3 ^ 2 +
    A 1 2 ^ 2 + A 1 3 ^ 2 + A 2 3 ^ 2

private theorem sandwich_apply (P A : Mat4) (i j : Fin 4) :
    (P * A * Pᵀ) i j = ∑ a, ∑ b, P i a * A a b * P j b := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem pfaffian_quaternion_zero (P : Mat4) :
    pfaffianFour (P * quaternionMatrix 0 * Pᵀ) = P.det := by
  rw [Matrix.det_succ_row_zero P]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp only [pfaffianFour, sandwich_apply]
  norm_num [quaternionMatrix, Fin.sum_univ_four, Fin.succAbove, Fin.lt_def]
  ring

private theorem pfaffian_quaternion_one (P : Mat4) :
    pfaffianFour (P * quaternionMatrix 1 * Pᵀ) = P.det := by
  rw [Matrix.det_succ_row_zero P]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp only [pfaffianFour, sandwich_apply]
  norm_num [quaternionMatrix, Fin.sum_univ_four, Fin.succAbove, Fin.lt_def]
  ring

private theorem pfaffian_quaternion_two (P : Mat4) :
    pfaffianFour (P * quaternionMatrix 2 * Pᵀ) = P.det := by
  rw [Matrix.det_succ_row_zero P]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp only [pfaffianFour, sandwich_apply]
  norm_num [quaternionMatrix, Fin.sum_univ_four, Fin.succAbove, Fin.lt_def]
  ring

theorem pfaffian_quaternion (P : Mat4) (s : Fin 3) :
    pfaffianFour (P * quaternionMatrix s * Pᵀ) = P.det := by
  fin_cases s
  · exact pfaffian_quaternion_zero P
  · exact pfaffian_quaternion_one P
  · exact pfaffian_quaternion_two P

private theorem pfaffian_opposite_zero (P : Mat4) :
    pfaffianFour (P * oppositeMatrix 0 * Pᵀ) = -P.det := by
  rw [Matrix.det_succ_row_zero P]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp only [pfaffianFour, sandwich_apply]
  norm_num [oppositeMatrix, oppositeQuaternion, quaternionMatrix,
    Fin.sum_univ_four, Fin.succAbove, Fin.lt_def]
  ring

private theorem pfaffian_opposite_one (P : Mat4) :
    pfaffianFour (P * oppositeMatrix 1 * Pᵀ) = -P.det := by
  rw [Matrix.det_succ_row_zero P]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp only [pfaffianFour, sandwich_apply]
  norm_num [oppositeMatrix, oppositeQuaternion, quaternionMatrix,
    Fin.sum_univ_four, Fin.succAbove, Fin.lt_def]
  ring

private theorem pfaffian_opposite_two (P : Mat4) :
    pfaffianFour (P * oppositeMatrix 2 * Pᵀ) = -P.det := by
  rw [Matrix.det_succ_row_zero P]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp only [pfaffianFour, sandwich_apply]
  norm_num [oppositeMatrix, oppositeQuaternion, quaternionMatrix,
    Fin.sum_univ_four, Fin.succAbove, Fin.lt_def]
  ring

theorem pfaffian_opposite (P : Mat4) (s : Fin 3) :
    pfaffianFour (P * oppositeMatrix s * Pᵀ) = -P.det := by
  fin_cases s
  · exact pfaffian_opposite_zero P
  · exact pfaffian_opposite_one P
  · exact pfaffian_opposite_two P

private theorem skew_diagonal_zero (A : Mat4)
    (hsk : ∀ i j, A i j = -A j i) (i : Fin 4) : A i i = 0 := by
  linarith [hsk i i]

theorem upperSquareFour_eq_two (A : Mat4)
    (hsk : ∀ i j, A i j = -A j i) (hA : Aᵀ * A = 1) :
    upperSquareFour A = 2 := by
  have hd (i : Fin 4) : ∑ k, A k i ^ 2 = 1 := by
    have h := congrArg (fun B : Mat4 => B i i) hA
    simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using h
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  have h3 := hd 3
  simp only [Fin.sum_univ_four, skew_diagonal_zero A hsk,
    hsk 1 0, hsk 2 0, hsk 3 0, hsk 2 1, hsk 3 1, hsk 3 2,
    neg_sq, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, add_zero] at h0 h1 h2 h3
  dsimp [upperSquareFour]
  linarith

private theorem selfDual_of_pfaffian (A : Mat4)
    (hupper : upperSquareFour A = 2) (hpf : pfaffianFour A = 1) :
    A 2 3 = A 0 1 ∧ A 1 3 = -A 0 2 ∧ A 1 2 = A 0 3 := by
  have hsq : (A 0 1 - A 2 3) ^ 2 + (A 0 2 + A 1 3) ^ 2 +
      (A 0 3 - A 1 2) ^ 2 = 0 := by
    dsimp [upperSquareFour] at hupper
    dsimp [pfaffianFour] at hpf
    nlinarith
  have h1 : (A 0 1 - A 2 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (A 0 2 + A 1 3), sq_nonneg (A 0 3 - A 1 2)]
  have h2 : (A 0 2 + A 1 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (A 0 1 - A 2 3), sq_nonneg (A 0 3 - A 1 2)]
  have h3 : (A 0 3 - A 1 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (A 0 1 - A 2 3), sq_nonneg (A 0 2 + A 1 3)]
  have := sq_eq_zero_iff.mp h1
  have := sq_eq_zero_iff.mp h2
  have := sq_eq_zero_iff.mp h3
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem antiSelfDual_of_pfaffian (A : Mat4)
    (hupper : upperSquareFour A = 2) (hpf : pfaffianFour A = -1) :
    A 2 3 = -A 0 1 ∧ A 1 3 = A 0 2 ∧ A 1 2 = -A 0 3 := by
  have hsq : (A 0 1 + A 2 3) ^ 2 + (A 0 2 - A 1 3) ^ 2 +
      (A 0 3 + A 1 2) ^ 2 = 0 := by
    dsimp [upperSquareFour] at hupper
    dsimp [pfaffianFour] at hpf
    nlinarith
  have h1 : (A 0 1 + A 2 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (A 0 2 - A 1 3), sq_nonneg (A 0 3 + A 1 2)]
  have h2 : (A 0 2 - A 1 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (A 0 1 + A 2 3), sq_nonneg (A 0 3 + A 1 2)]
  have h3 : (A 0 3 + A 1 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (A 0 1 + A 2 3), sq_nonneg (A 0 2 - A 1 3)]
  have := sq_eq_zero_iff.mp h1
  have := sq_eq_zero_iff.mp h2
  have := sq_eq_zero_iff.mp h3
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem selfDual_span (A : Mat4)
    (hsk : ∀ i j, A i j = -A j i)
    (hp : A 2 3 = A 0 1 ∧ A 1 3 = -A 0 2 ∧ A 1 2 = A 0 3) :
    A = imaginaryCombination quaternionMatrix (fun r => A r.succ 0) := by
  have hd := skew_diagonal_zero A hsk
  ext i j
  simp only [imaginaryCombination_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> norm_num [quaternionMatrix]
  all_goals first | exact hd _ | linarith [hsk 0 1, hsk 0 2, hsk 0 3, hsk 1 2, hsk 1 3, hsk 2 3, hp.1, hp.2.1, hp.2.2]

private theorem antiSelfDual_span (A : Mat4)
    (hsk : ∀ i j, A i j = -A j i)
    (hp : A 2 3 = -A 0 1 ∧ A 1 3 = A 0 2 ∧ A 1 2 = -A 0 3) :
    A = imaginaryCombination oppositeMatrix (fun r => -A r.succ 0) := by
  have hd := skew_diagonal_zero A hsk
  ext i j
  simp only [imaginaryCombination_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    norm_num [oppositeMatrix, oppositeQuaternion, quaternionMatrix]
  all_goals first | exact hd _ | linarith [hsk 0 1, hsk 0 2, hsk 0 3, hsk 1 2, hsk 1 3, hsk 2 3, hp.1, hp.2.1, hp.2.2]

private theorem quaternion_orthogonal (s : Fin 3) :
    (quaternionMatrix s)ᵀ * quaternionMatrix s = 1 := by
  ext i j
  change (∑ k, quaternionMatrix s k i * quaternionMatrix s k j) = if i = j then 1 else 0
  fin_cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [quaternionMatrix, Fin.sum_univ_four]

private theorem opposite_orthogonal (s : Fin 3) :
    (oppositeMatrix s)ᵀ * oppositeMatrix s = 1 := by
  ext i j
  change (∑ k, oppositeMatrix s k i * oppositeMatrix s k j) = if i = j then 1 else 0
  fin_cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [oppositeMatrix, oppositeQuaternion, quaternionMatrix, Fin.sum_univ_four]

private theorem conjugate_skew (P A : Mat4) (hsk : Aᵀ = -A) :
    ∀ i j, (P * A * Pᵀ) i j = -(P * A * Pᵀ) j i := by
  have h : (P * A * Pᵀ)ᵀ = -(P * A * Pᵀ) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hsk,
      Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  intro i j
  have hi := congrArg (fun B : Mat4 => B j i) h
  simpa only [Matrix.transpose_apply, Matrix.neg_apply] using hi

private theorem conjugate_orthogonal (P A : Mat4)
    (hP : Pᵀ * P = 1) (hA : Aᵀ * A = 1) :
    (P * A * Pᵀ)ᵀ * (P * A * Pᵀ) = 1 := by
  have hPP : P * Pᵀ = 1 := mul_eq_one_comm.mp hP
  calc
    _ = P * Aᵀ * (Pᵀ * P) * A * Pᵀ := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = P * (Aᵀ * A) * Pᵀ := by rw [hP]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = 1 := by rw [hA, Matrix.mul_one, hPP]

/-- Positive-orientation orthogonal changes preserve the first quaternionic space. -/
theorem oriented_quaternion_span (P : Mat4) (hP : Pᵀ * P = 1) (hdet : P.det = 1)
    (s : Fin 3) :
    P * quaternionMatrix s * Pᵀ = imaginaryCombination quaternionMatrix
      (fun r => (P * quaternionMatrix s * Pᵀ) r.succ 0) := by
  apply selfDual_span
  · exact conjugate_skew P _ (Angular.quaternionMatrix_transpose s)
  · apply selfDual_of_pfaffian
    · exact upperSquareFour_eq_two _ (conjugate_skew P _ (Angular.quaternionMatrix_transpose s))
        (conjugate_orthogonal P _ hP (quaternion_orthogonal s))
    · rw [pfaffian_quaternion, hdet]

/-- The opposite quaternionic space is preserved by the same frame changes. -/
theorem oriented_opposite_span (P : Mat4) (hP : Pᵀ * P = 1) (hdet : P.det = 1)
    (s : Fin 3) :
    P * oppositeMatrix s * Pᵀ = imaginaryCombination oppositeMatrix
      (fun r => -(P * oppositeMatrix s * Pᵀ) r.succ 0) := by
  apply antiSelfDual_span
  · exact conjugate_skew P _ (oppositeMatrix_transpose s)
  · apply antiSelfDual_of_pfaffian
    · exact upperSquareFour_eq_two _ (conjugate_skew P _ (oppositeMatrix_transpose s))
        (conjugate_orthogonal P _ hP (opposite_orthogonal s))
    · rw [pfaffian_opposite, hdet]

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The finite curvature contractions occurring in the four-dimensional
Euler and first Pontryagin densities.  These are pointwise identities for
the actual metric curvature; no characteristic-number or Hodge theorem is
assumed or asserted. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular
open scoped BigOperators Manifold ContDiff

noncomputable section

/-- Hodge star on two-forms in the positively oriented standard basis.
The input is represented by a skew matrix; the formula also defines a
linear map on arbitrary matrices. -/
def hodgeStarFour : Mat4 →ₗ[ℝ] Mat4 where
  toFun A := !![0, A 2 3, -A 1 3, A 1 2;
    -A 2 3, 0, A 0 3, -A 0 2;
    A 1 3, -A 0 3, 0, A 0 1;
    -A 1 2, A 0 2, -A 0 1, 0]
  map_add' A B := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_comm]
  map_smul' r A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- Hodge star in the first alternating pair of a covariant four-tensor. -/
def hodgeFirstTensor : CovariantCoordinates 4 →ₗ[ℝ] CovariantCoordinates 4 where
  toFun R a := hodgeStarFour (fun i j => R ![i, j, a 2, a 3]) (a 0) (a 1)
  map_add' R S := by
    funext a
    let P : Mat4 := fun i j => R ![i, j, a 2, a 3]
    let Q : Mat4 := fun i j => S ![i, j, a 2, a 3]
    exact congrArg (fun A : Mat4 => A (a 0) (a 1)) (hodgeStarFour.map_add P Q)
  map_smul' r R := by
    funext a
    let P : Mat4 := fun i j => R ![i, j, a 2, a 3]
    exact congrArg (fun A : Mat4 => A (a 0) (a 1)) (hodgeStarFour.map_smul r P)

theorem hodgeStarFour_quaternion (s : Fin 3) :
    hodgeStarFour (quaternionMatrix s) = quaternionMatrix s := by
  ext i j
  fin_cases s <;> fin_cases i <;> fin_cases j <;> norm_num [hodgeStarFour, quaternionMatrix]

theorem hodgeStarFour_opposite (s : Fin 3) :
    hodgeStarFour (oppositeMatrix s) = -oppositeMatrix s := by
  ext i j
  change hodgeStarFour (oppositeMatrix s) i j = -(oppositeMatrix s i j)
  fin_cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [hodgeStarFour, oppositeMatrix, oppositeQuaternion, quaternionMatrix]

def twoFormProductCoordinates (P Q : Mat4) : CovariantCoordinates 4 :=
  fun a => twoFormProduct P Q (a 0) (a 1) (a 2) (a 3)

theorem twoFormProductCoordinates_smul_left (c : ℝ) (P Q : Mat4) :
    twoFormProductCoordinates (c • P) Q = c • twoFormProductCoordinates P Q := by
  funext a
  simp only [twoFormProductCoordinates, twoFormProduct, Matrix.smul_apply,
    smul_eq_mul, Pi.smul_apply]
  ring

theorem hodgeFirstTensor_twoFormProduct (P Q : Mat4) :
    hodgeFirstTensor (twoFormProductCoordinates P Q) =
      twoFormProductCoordinates (hodgeStarFour P) Q := by
  funext a
  change hodgeStarFour (fun i j => P i j * Q (a 3) (a 2)) (a 0) (a 1) =
    hodgeStarFour P (a 0) (a 1) * Q (a 3) (a 2)
  have hp : (fun i j => P i j * Q (a 3) (a 2)) = Q (a 3) (a 2) • P := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, mul_comm]
  rw [hp, map_smul]
  simp only [Matrix.smul_apply, smul_eq_mul, mul_comm]

theorem blockTensorCoordinates_sum (A : Mat3) (Q : Fin 3 → Mat4) :
    blockTensorCoordinates A Q = (1 / 2 : ℝ) •
      ∑ s, ∑ t, A s t • twoFormProductCoordinates (Q s) (Q t) := by
  funext a
  simp only [blockTensorCoordinates, blockTensor, twoFormProductCoordinates,
    Pi.smul_apply, Finset.sum_apply]

theorem hodgeFirstTensor_block (A : Mat3) (Q : Fin 3 → Mat4) (r : ℝ)
    (hQ : ∀ s, hodgeStarFour (Q s) = r • Q s) :
    hodgeFirstTensor (blockTensorCoordinates A Q) = r • blockTensorCoordinates A Q := by
  simp only [blockTensorCoordinates_sum, map_sum, map_smul, hodgeFirstTensor_twoFormProduct, hQ,
    twoFormProductCoordinates_smul_left]
  simp only [smul_comm _ r, ← Finset.smul_sum]

theorem hodgeFirstTensor_plus (A : Mat3) :
    hodgeFirstTensor (blockTensorCoordinates A quaternionMatrix) =
      blockTensorCoordinates A quaternionMatrix := by
  simpa only [one_smul] using hodgeFirstTensor_block A quaternionMatrix 1
    (fun s => by simpa only [one_smul] using hodgeStarFour_quaternion s)

theorem hodgeFirstTensor_minus (A : Mat3) :
    hodgeFirstTensor (blockTensorCoordinates A oppositeMatrix) =
      -blockTensorCoordinates A oppositeMatrix := by
  simpa only [neg_one_smul] using hodgeFirstTensor_block A oppositeMatrix (-1)
    (fun s => by simpa only [neg_one_smul] using hodgeStarFour_opposite s)

/-- The signed curvature norm is the difference of the two block norms. -/
theorem frameTensorPairing_hodgeFirst_of_blocks (R : CovariantCoordinates 4)
    (A B : Mat3)
    (hR : R = blockTensorCoordinates A quaternionMatrix +
      blockTensorCoordinates B oppositeMatrix)
    (hA : blockCoordinates R quaternionMatrix = A)
    (hB : blockCoordinates R oppositeMatrix = B) :
    frameTensorPairing R (hodgeFirstTensor R) = 4 * (squareNorm A - squareNorm B) := by
  have hstar : hodgeFirstTensor R = blockTensorCoordinates A quaternionMatrix -
      blockTensorCoordinates B oppositeMatrix := by
    rw [hR, map_add, hodgeFirstTensor_plus, hodgeFirstTensor_minus, sub_eq_add_neg]
  rw [hstar, sub_eq_add_neg, frameTensorPairing_add_right]
  have hneg : frameTensorPairing R (-blockTensorCoordinates B oppositeMatrix) =
      -frameTensorPairing R (blockTensorCoordinates B oppositeMatrix) := by
    simp only [frameTensorPairing, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  rw [hneg, frameTensorPairing_blockTensor, frameTensorPairing_blockTensor, hA, hB]
  simp only [matrixPairing, squareNorm, pow_two]
  ring

private theorem squareNorm_one_add_trace (A : Mat3) (ht : A.trace = 0) :
    squareNorm (1 + A) = 3 + squareNorm A := by
  have h : squareNorm (1 + A) = 3 + 2 * A.trace + squareNorm A := by
    simp only [squareNorm, Matrix.add_apply, Matrix.one_apply, Matrix.trace,
      Matrix.diag, Fin.sum_univ_three]
    norm_num
    ring
  rw [h, ht]
  ring

/-- The curvature polynomial whose integral is the Euler number in the
Chern--Gauss--Bonnet theorem.  That global theorem is not used here. -/
def curvatureEulerDensity (R : CovariantCoordinates 4) : ℝ :=
  (frameTensorSquareNorm R -
    4 * ∑ j, ∑ k, (∑ i : Fin 4, R ![i, j, k, i]) ^ 2 +
    (∑ j, ∑ i : Fin 4, R ![i, j, j, i]) ^ 2) / (32 * Real.pi ^ 2)

/-- The first Pontryagin density; its third is the signature density. -/
def curvaturePontryaginDensity (R : CovariantCoordinates 4) : ℝ :=
  frameTensorPairing R (hodgeFirstTensor R) / (16 * Real.pi ^ 2)

def curvatureSignatureDensity (R : CovariantCoordinates 4) : ℝ :=
  curvaturePontryaginDensity R / 3

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem frame_curvature_hodge_pairing (e : OrthonormalFrame g c) (hRic : RicciThree g) :
    frameTensorPairing
      (frameTensor e.matrix (curvatureCoordinates g c (chartAt FourSpace c c)))
      (hodgeFirstTensor
        (frameTensor e.matrix (curvatureCoordinates g c (chartAt FourSpace c c)))) =
      24 * (normalizedBlockNorm (plusWeyl g c e) ^ 2 -
        normalizedBlockNorm (minusWeyl g c e) ^ 2) := by
  let R := frameTensor e.matrix (curvatureCoordinates g c (chartAt FourSpace c c))
  have hR : R = blockTensorCoordinates (1 + plusWeyl g c e) quaternionMatrix +
      blockTensorCoordinates (1 + minusWeyl g c e) oppositeMatrix := by
    funext a
    have ha : a = ![a 0, a 1, a 2, a 3] := by
      funext i
      fin_cases i <;> rfl
    dsimp only [R]
    rw [ha, frameTensor_curvatureCoordinates, actual_einstein_decomposition e hRic]
    rfl
  have hblock (Q : Fin 3 → Mat4) :
      blockCoordinates R Q = curvatureBlock (curvaturePairing g c e) Q := by
    dsimp only [R]
    ext s t
    simp only [blockCoordinates, curvatureBlock]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    rw [frameTensor_curvatureCoordinates]
    rfl
  have hA : blockCoordinates R quaternionMatrix = 1 + plusWeyl g c e := by
    rw [hblock]
    unfold plusWeyl
    abel
  have hB : blockCoordinates R oppositeMatrix = 1 + minusWeyl g c e := by
    rw [hblock]
    unfold minusWeyl
    abel
  have h := frameTensorPairing_hodgeFirst_of_blocks R _ _ hR hA hB
  have ht := actual_weyl_traceFree e hRic
  rw [squareNorm_one_add_trace (plusWeyl g c e) ht.1,
    squareNorm_one_add_trace (minusWeyl g c e) ht.2] at h
  have hpa := normalizedBlockNorm_sq (plusWeyl g c e)
  have hpb := normalizedBlockNorm_sq (minusWeyl g c e)
  change normalizedBlockNorm (plusWeyl g c e) ^ 2 = squareNorm _ / 6 at hpa
  change normalizedBlockNorm (minusWeyl g c e) ^ 2 = squareNorm _ / 6 at hpb
  change frameTensorPairing R (hodgeFirstTensor R) = _
  linarith only [h, hpa, hpb]

theorem frame_curvature_eulerDensity (e : OrthonormalFrame g c) (hRic : RicciThree g) :
    curvatureEulerDensity
      (frameTensor e.matrix (curvatureCoordinates g c (chartAt FourSpace c c))) =
      (3 / (4 * Real.pi ^ 2)) * (1 + normalizedBlockNorm (plusWeyl g c e) ^ 2 +
        normalizedBlockNorm (minusWeyl g c e) ^ 2) := by
  have hr (j k : Fin 4) :
      (∑ i : Fin 4, (frameTensor e.matrix
        (curvatureCoordinates g c (chartAt FourSpace c c))) ![i, j, k, i]) =
        if j = k then 3 else 0 := by
    simp only [frameTensor_curvatureCoordinates]
    exact frame_algebraic_ricciThree e hRic j k
  rw [curvatureEulerDensity, frame_curvature_norm_energy e hRic]
  simp only [hr, Fin.sum_univ_four]
  norm_num
  ring

theorem frame_curvature_pontryaginDensity (e : OrthonormalFrame g c) (hRic : RicciThree g) :
    curvaturePontryaginDensity
      (frameTensor e.matrix (curvatureCoordinates g c (chartAt FourSpace c c))) =
      (3 / (2 * Real.pi ^ 2)) * (normalizedBlockNorm (plusWeyl g c e) ^ 2 -
        normalizedBlockNorm (minusWeyl g c e) ^ 2) := by
  rw [curvaturePontryaginDensity, frame_curvature_hodge_pairing e hRic]
  ring

theorem frame_curvature_signatureDensity (e : OrthonormalFrame g c) (hRic : RicciThree g) :
    curvatureSignatureDensity
      (frameTensor e.matrix (curvatureCoordinates g c (chartAt FourSpace c c))) =
      (1 / (2 * Real.pi ^ 2)) * (normalizedBlockNorm (plusWeyl g c e) ^ 2 -
        normalizedBlockNorm (minusWeyl g c e) ^ 2) := by
  rw [curvatureSignatureDensity, frame_curvature_pontryaginDensity e hRic]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transfer the reflection-symmetric Green integral to the original
oriented frame measure. The variance correction is then performed on that
original measure, where its scalar means and Weyl gaps have the intended
geometric interpretation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff

noncomputable section

theorem traceCouplingTerm_reflected_swap (A U : Mat) (Z V : Angular.Gradient) :
    traceCouplingTerm U A (reflectedGradient V) (reflectedGradient Z) =
      traceCouplingTerm A U Z V := by
  unfold traceCouplingTerm
  rw [reflectedGradient_energy, reflectedGradient_energy,
    weylMatrixEnergy_reflected, weylMatrixEnergy_reflected,
    scalarNormExpression_reflected, scalarNormExpression_reflected]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem MetricGreenData.traceDeficitIntegrand_reflection (d : MetricGreenData g μ)
    (o : OppositeWeylData d) (e : FrameBundle g) :
    d.traceDeficitIntegrand o (frameReflection e) = d.traceDeficitIntegrand o e := by
  rw [d.traceDeficitIntegrand_eq_arrays o, d.traceDeficitIntegrand_eq_arrays o]
  have hp : plusWeylGradient g e.base e.frame.reflect =
      reflectedGradient (minusWeylGradient g e.base e.frame) := by
    funext i
    exact plusWeylGradient_reflect g e.base e.frame i
  have hm : minusWeylGradient g e.base e.frame.reflect =
      reflectedGradient (plusWeylGradient g e.base e.frame) := by
    funext i
    exact minusWeylGradient_reflect g e.base e.frame i
  dsimp only [frameReflection]
  rw [plusWeyl_reflect, minusWeyl_reflect, hp, hm, traceCouplingTerm_reflected_swap]

theorem MetricGreenData.preVarianceIntegrand_reflection (d : MetricGreenData g μ)
    (o : OppositeWeylData d) (e : FrameBundle g) :
    d.preVarianceIntegrand o (frameReflection e) = d.preVarianceIntegrand o e := by
  unfold preVarianceIntegrand
  rw [frameReflection_involutive, d.traceDeficitIntegrand_reflection,
    kappaNormIntegrand_frameReflection]
  have hk := kappaNormIntegrand_frameReflection (frameReflection e)
  rw [← hk, frameReflection_involutive]
  ring

theorem MetricGreenData.preVarianceGreen_oriented (d : MetricGreenData g μ)
    (o : OppositeWeylData d) [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hparallel : ParallelReflection d) (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    Integrable (d.preVarianceIntegrand o) μ ∧ 0 ≤ ∫ e, d.preVarianceIntegrand o e ∂μ := by
  let dS := d.onSymmetricMeasure hparallel
  let oS := o.onSymmetricMeasure hparallel
  let rS := d.symmetricReflection hparallel
  have hi : Integrable (d.preVarianceIntegrand o) (symmetricFrameMeasure g μ) :=
    rS.preVarianceIntegrand_integrable oS hpinch
  have hn : 0 ≤ ∫ e, d.preVarianceIntegrand o e ∂symmetricFrameMeasure g μ :=
    rS.preVarianceGreen oS hp hdecomp hpinch
  have hs := integral_symmetricFrameMeasure (d.preVarianceIntegrand o) hi
    (d.preVarianceIntegrand_reflection o)
  rw [hs] at hn
  refine ⟨(integrable_add_measure.mp hi).1, ?_⟩
  linarith only [hn]

theorem MetricGreenData.coupledIntegral_oriented (d : MetricGreenData g μ)
    (o : OppositeWeylData d) [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]
    (hparallel : ParallelReflection d) (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2)
    (hsecond : (∫ e, d.plusNormField e ^ 2 ∂μ) = ∫ e, d.minusNormField o e ^ 2 ∂μ)
    (hvariance : (∫ e, (d.plusNormField e - d.minusNormField o e) ^ 2 ∂μ) -
      (∫ e, d.plusNormField e - d.minusNormField o e ∂μ) ^ 2 ≤
      ∫ e, ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) -
        blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)‖ ^ 2 /
        (4 + d.plusNormField e ^ 2 + d.minusNormField o e ^ 2) ∂μ) :
    Integrable (d.coupledIntegrand o) μ ∧ 0 ≤ ∫ e, d.coupledIntegrand o e ∂μ := by
  let oS := o.onSymmetricMeasure hparallel
  let rS := d.symmetricReflection hparallel
  have hF := (integrable_add_measure.mp (rS.radialVarianceEnergy_integrable oS)).1
  have hD := (integrable_add_measure.mp (rS.varianceDensity_integrable oS)).1
  have hpre := d.preVarianceGreen_oriented o hparallel hp hdecomp hpinch
  have hv := Variance.variance_correction_nonneg d.plusNormField (d.minusNormField o) _
    d.plusNormField.continuous (d.minusNormField o).continuous hF hsecond hvariance
  refine ⟨hpre.1.add (hD.const_mul 158), ?_⟩
  change 0 ≤ ∫ e, d.preVarianceIntegrand o e + 158 * varianceDensity _ _ _ _ ∂μ
  rw [integral_add hpre.1 (hD.const_mul 158), integral_const_mul]
  exact add_nonneg hpre.2 (mul_nonneg (by norm_num) hv)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Orthogonal coefficient matrices of orientation-preserving four-frame changes. -/

namespace PositiveEinsteinFour.QuaternionFrame

open Matrix TraceHessian PositiveEinsteinFour.Geometry
open Angular (oppositeMatrix)
open scoped BigOperators

noncomputable section

def fourMatrixPairing (A B : Mat4) : ℝ := ∑ i, ∑ j, A i j * B i j

theorem fourMatrixPairing_eq_trace (A B : Mat4) :
    fourMatrixPairing A B = Matrix.trace (Aᵀ * B) := by
  simp only [fourMatrixPairing, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]
  exact Finset.sum_comm

theorem fourMatrixPairing_add_left (A B C : Mat4) :
    fourMatrixPairing (A + B) C = fourMatrixPairing A C + fourMatrixPairing B C := by
  simp only [fourMatrixPairing, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem fourMatrixPairing_add_right (A B C : Mat4) :
    fourMatrixPairing A (B + C) = fourMatrixPairing A B + fourMatrixPairing A C := by
  simp only [fourMatrixPairing, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem fourMatrixPairing_smul_left (A B : Mat4) (c : ℝ) :
    fourMatrixPairing (c • A) B = c * fourMatrixPairing A B := by
  simp only [fourMatrixPairing, Matrix.smul_apply, smul_eq_mul, mul_assoc,
    Finset.mul_sum]

theorem fourMatrixPairing_smul_right (A B : Mat4) (c : ℝ) :
    fourMatrixPairing A (c • B) = c * fourMatrixPairing A B := by
  simp only [fourMatrixPairing, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

theorem fourMatrixPairing_conjugate (P A B : Mat4) (hP : Pᵀ * P = 1) :
    fourMatrixPairing (P * A * Pᵀ) (P * B * Pᵀ) = fourMatrixPairing A B := by
  rw [fourMatrixPairing_eq_trace, fourMatrixPairing_eq_trace]
  have hm : (P * A * Pᵀ)ᵀ * (P * B * Pᵀ) = P * (Aᵀ * B) * Pᵀ := by
    calc
      _ = P * Aᵀ * (Pᵀ * P) * B * Pᵀ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = _ := by rw [hP]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hm, Matrix.trace_mul_cycle, hP, Matrix.one_mul]

private theorem basis_pairing_combinations (Q : Fin 3 → Mat4)
    (hQ : ∀ r s, fourMatrixPairing (Q r) (Q s) = if r = s then 4 else 0)
    (u v : Fin 3 → ℝ) :
    fourMatrixPairing (imaginaryCombination Q u) (imaginaryCombination Q v) =
      4 * ∑ r, u r * v r := by
  simp only [imaginaryCombination, Fin.sum_univ_three, fourMatrixPairing_add_left,
    fourMatrixPairing_add_right, fourMatrixPairing_smul_left,
    fourMatrixPairing_smul_right, hQ]
  norm_num
  ring

/-- An orthogonal action on an orthogonal three-dimensional two-form basis
has an orthogonal matrix of coefficients. -/
theorem coefficientMatrix_orthogonal (P : Mat4) (Q : Fin 3 → Mat4) (R : Mat3)
    (hP : Pᵀ * P = 1)
    (hQ : ∀ r s, fourMatrixPairing (Q r) (Q s) = if r = s then 4 else 0)
    (hR : ∀ s, P * Q s * Pᵀ = imaginaryCombination Q (fun r => R r s)) :
    Rᵀ * R = 1 := by
  ext s t
  have h := fourMatrixPairing_conjugate P (Q s) (Q t) hP
  rw [hR s, hR t, basis_pairing_combinations Q hQ, hQ] at h
  change (∑ r, R r s * R r t) = if s = t then 1 else 0
  by_cases hst : s = t
  · rw [ite_eq_left hst] at h ⊢
    linarith
  · rw [ite_eq_right hst] at h ⊢
    linarith

/-- Coefficients of the positive two-form action. -/
def positiveOrientationMatrix (P : Mat4) : Mat3 := fun r s =>
  (P * quaternionMatrix s * Pᵀ) r.succ 0

/-- Coefficients of the negative two-form action. -/
def negativeOrientationMatrix (P : Mat4) : Mat3 := fun r s =>
  -(P * oppositeMatrix s * Pᵀ) r.succ 0

theorem positiveOrientationMatrix_span (P : Mat4) (hP : Pᵀ * P = 1)
    (hdet : P.det = 1) (s : Fin 3) :
    P * quaternionMatrix s * Pᵀ =
      imaginaryCombination quaternionMatrix (fun r => positiveOrientationMatrix P r s) :=
  oriented_quaternion_span P hP hdet s

theorem negativeOrientationMatrix_span (P : Mat4) (hP : Pᵀ * P = 1)
    (hdet : P.det = 1) (s : Fin 3) :
    P * oppositeMatrix s * Pᵀ =
      imaginaryCombination oppositeMatrix (fun r => negativeOrientationMatrix P r s) :=
  oriented_opposite_span P hP hdet s

theorem positiveOrientationMatrix_orthogonal (P : Mat4) (hP : Pᵀ * P = 1)
    (hdet : P.det = 1) :
    (positiveOrientationMatrix P)ᵀ * positiveOrientationMatrix P = 1 := by
  apply coefficientMatrix_orthogonal P quaternionMatrix _ hP
  · exact CurvatureContraction.plus_twoForm_pairing
  · exact positiveOrientationMatrix_span P hP hdet

theorem negativeOrientationMatrix_orthogonal (P : Mat4) (hP : Pᵀ * P = 1)
    (hdet : P.det = 1) :
    (negativeOrientationMatrix P)ᵀ * negativeOrientationMatrix P = 1 := by
  apply coefficientMatrix_orthogonal P oppositeMatrix _ hP
  · exact CurvatureContraction.opposite_twoForm_pairing
  · exact negativeOrientationMatrix_span P hP hdet

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The six-dimensional two-form fiber and its actual Hodge involution.
The coordinate order is 01, 02, 03, 12, 13, 23. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

abbrev TwoFormFour := EuclideanSpace ℝ (Fin 6)

def twoFormMatrix (a : TwoFormFour) : Mat4 :=
  !![0, a 0, a 1, a 2;
    -a 0, 0, a 3, a 4;
    -a 1, -a 3, 0, a 5;
    -a 2, -a 4, -a 5, 0]

def twoFormHodgeLinear : TwoFormFour ≃ₗ[ℝ] TwoFormFour where
  toFun a := WithLp.toLp 2 ![a 5, -a 4, a 3, a 2, -a 1, a 0]
  invFun a := WithLp.toLp 2 ![a 5, -a 4, a 3, a 2, -a 1, a 0]
  left_inv a := by ext i; fin_cases i <;> simp
  right_inv a := by ext i; fin_cases i <;> simp
  map_add' a b := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' r a := by ext i; fin_cases i <;> simp

theorem twoFormHodge_norm (a : TwoFormFour) : ‖twoFormHodgeLinear a‖ = ‖a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq]
  simp [twoFormHodgeLinear, Fin.sum_univ_succ, Real.norm_eq_abs]
  ring

def twoFormHodge : TwoFormFour ≃ₗᵢ[ℝ] TwoFormFour where
  toLinearEquiv := twoFormHodgeLinear
  norm_map' := twoFormHodge_norm

@[simp] theorem twoFormHodge_involutive (a : TwoFormFour) :
    twoFormHodge (twoFormHodge a) = a := twoFormHodgeLinear.left_inv a

theorem twoFormMatrix_hodge (a : TwoFormFour) :
    twoFormMatrix (twoFormHodge a) = hodgeStarFour (twoFormMatrix a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoFormMatrix, twoFormHodge, twoFormHodgeLinear,
    hodgeStarFour]

theorem twoFormMatrix_skew (a : TwoFormFour) : (twoFormMatrix a)ᵀ = -twoFormMatrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoFormMatrix]

theorem twoFormMatrix_injective : Function.Injective twoFormMatrix := by
  intro a b hab
  ext i
  fin_cases i
  · exact congrFun (congrFun hab 0) 1
  · exact congrFun (congrFun hab 0) 2
  · exact congrFun (congrFun hab 0) 3
  · exact congrFun (congrFun hab 1) 2
  · exact congrFun (congrFun hab 1) 3
  · exact congrFun (congrFun hab 2) 3

def twoFormSelfDual (a : TwoFormFour) : TwoFormFour := (2 : ℝ)⁻¹ • (a + twoFormHodge a)

def twoFormAntiSelfDual (a : TwoFormFour) : TwoFormFour := (2 : ℝ)⁻¹ • (a - twoFormHodge a)

theorem twoForm_decomposition (a : TwoFormFour) :
    twoFormSelfDual a + twoFormAntiSelfDual a = a := by
  unfold twoFormSelfDual twoFormAntiSelfDual
  module

theorem twoFormSelfDual_hodge (a : TwoFormFour) :
    twoFormHodge (twoFormSelfDual a) = twoFormSelfDual a := by
  simp only [twoFormSelfDual, map_smul, map_add, twoFormHodge_involutive]
  rw [add_comm]

theorem twoFormAntiSelfDual_hodge (a : TwoFormFour) :
    twoFormHodge (twoFormAntiSelfDual a) = -twoFormAntiSelfDual a := by
  simp only [twoFormAntiSelfDual, map_smul, map_sub, twoFormHodge_involutive]
  module

theorem twoForm_eigenspaces_orthogonal (a b : TwoFormFour)
    (ha : twoFormHodge a = a) (hb : twoFormHodge b = -b) : inner ℝ a b = 0 := by
  have h := twoFormHodge.inner_map_map a b
  rw [ha, hb, inner_neg_right] at h
  linarith

theorem twoFormSelfDual_orthogonal (a b : TwoFormFour) :
    inner ℝ (twoFormSelfDual a) (twoFormAntiSelfDual b) = 0 :=
  twoForm_eigenspaces_orthogonal _ _ (twoFormSelfDual_hodge a) (twoFormAntiSelfDual_hodge b)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Measurability and square integrability of both actual radial gradients
on the original oriented measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem blockRadialGradient_aestronglyMeasurable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (A : Ω → Mat) (Z : Ω → Fin 4 → Mat)
    (h : ∀ i, AEStronglyMeasurable (fun x => regularizedRadialDerivative 0 (A x) (Z x i)) μ) :
    AEStronglyMeasurable (fun x => blockRadialGradient (A x) (Z x)) μ := by
  have hm : AEMeasurable (fun x i => regularizedRadialDerivative 0 (A x) (Z x i)) μ :=
    AEMeasurable.of_eval (fun i => (h i).aemeasurable)
  exact ((PiLp.continuous_toLp 2 _).measurable.comp_aemeasurable hm).aestronglyMeasurable

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

namespace MetricGreenData

variable (d : MetricGreenData g μ)

include d

theorem radialVector_measurable :
    AEStronglyMeasurable (fun e => blockRadialGradient (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame)) μ :=
  blockRadialGradient_aestronglyMeasurable _ _ (fun i => (d.radial_integrable i).aestronglyMeasurable)

theorem oppositeRadialVector_measurable (_o : OppositeWeylData d) (hparallel : ParallelReflection d) :
    AEStronglyMeasurable (fun e => blockRadialGradient (minusWeyl g e.base e.frame)
      (minusWeylGradient g e.base e.frame)) μ := by
  let rS := d.symmetricReflection hparallel
  apply blockRadialGradient_aestronglyMeasurable
  intro i
  exact ((integrable_add_measure.mp (rS.opposite_radial_integrable i)).1).aestronglyMeasurable

theorem radialEnergy_integrable : Integrable (fun e : FrameBundle g => plusRadialEnergy e) μ := by
  have hE : Integrable (fun e => weylGradientEnergy (plusWeylGradient g e.base e.frame)) μ :=
    d.gradientEnergyField.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply hE.mono' (d.radialVector_measurable.norm.pow 2)
  filter_upwards [] with e
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2 ≤ _
  have hk := d.refinedKato e
  nlinarith [sq_nonneg ‖blockRadialGradient (plusWeyl g e.base e.frame)
    (plusWeylGradient g e.base e.frame)‖]

theorem oppositeRadialEnergy_integrable (o : OppositeWeylData d)
    (hparallel : ParallelReflection d) :
    Integrable (fun e : FrameBundle g => minusRadialEnergy e) μ := by
  have hc : Continuous (fun e : FrameBundle g =>
      weylGradientEnergy (minusWeylGradient g e.base e.frame)) := by
    have hG := o.continuousGradient
    unfold weylGradientEnergy matrixPairing
    fun_prop
  have hE : Integrable (fun e => weylGradientEnergy (minusWeylGradient g e.base e.frame)) μ :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply hE.mono' ((d.oppositeRadialVector_measurable o hparallel).norm.pow 2)
  filter_upwards [] with e
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change ‖blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)‖ ^ 2 ≤ _
  have hk := o.refinedKato e
  nlinarith [sq_nonneg ‖blockRadialGradient (minusWeyl g e.base e.frame)
    (minusWeylGradient g e.base e.frame)‖]

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! One-block vanishing for the metric under weighted-variance and moment
hypotheses. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]

theorem MetricGreenData.one_block_zero_of_variance (d : MetricGreenData g μ)
    (o : OppositeWeylData d) (orientation : FrameOrientation g) (hparallel : ParallelReflection d)
    (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (hpinch : ∀ e : FrameBundle g, d.plusNormField e + d.minusNormField o e < 2)
    (hsecond : (∫ e, d.plusNormField e ^ 2 ∂μ) = ∫ e, d.minusNormField o e ^ 2 ∂μ)
    (hdifference : (∫ e, (d.plusNormField e - d.minusNormField o e) ^ 2 ∂μ) -
      (∫ e, d.plusNormField e - d.minusNormField o e ∂μ) ^ 2 ≤
      ∫ e, ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) -
        blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)‖ ^ 2 /
        (4 + d.plusNormField e ^ 2 + d.minusNormField o e ^ 2) ∂μ)
    (hplus : (∫ e, (d.plusNormField e - ∫ f, d.plusNormField f ∂μ) ^ 2 ∂μ) ≤
      ∫ e, plusRadialEnergy e ∂μ)
    (hminus : (∫ e, (d.minusNormField o e - ∫ f, d.minusNormField o f ∂μ) ^ 2 ∂μ) ≤
      ∫ e, minusRadialEnergy e ∂μ)
    (hgapPlus : (∃ e ∈ orientation.positive, d.plusNormField e ≠ 0) → 1 ≤ ∫ e, d.plusNormField e ^ 2 ∂μ)
    (hgapMinus : (∃ e ∈ orientation.positive, d.minusNormField o e ≠ 0) → 1 ≤ ∫ e, d.minusNormField o e ^ 2 ∂μ) :
    (∀ e ∈ orientation.positive, d.plusNormField e = 0) ∨
      ∀ e ∈ orientation.positive, d.minusNormField o e = 0 := by
  classical
  by_cases hpzero : ∀ e ∈ orientation.positive, d.plusNormField e = 0
  · exact Or.inl hpzero
  by_cases hmzero : ∀ e ∈ orientation.positive, d.minusNormField o e = 0
  · exact Or.inr hmzero
  push Not at hpzero hmzero
  have hvi : Integrable (fun e => (d.plusNormField e - ∫ f, d.plusNormField f ∂μ) ^ 2) μ :=
    ((d.plusNormField.continuous.sub continuous_const).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hbi : Integrable (fun e => (d.minusNormField o e - ∫ f, d.minusNormField o f ∂μ) ^ 2) μ :=
    (((d.minusNormField o).continuous.sub continuous_const).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hI := d.coupledIntegral_oriented o hparallel hp hdecomp hpinch hsecond hdifference
  have hz := one_block_vanishes_of_coupled_bound
    (I := d.coupledIntegrand o)
    (θ := fun e => Potential.theta (d.plusNormField e) (d.minusNormField o e))
    (v := d.plusNormField) (b := d.minusNormField o)
    (p := plusRadialEnergy) (q := minusRadialEnergy)
    hI.1 hI.2
    (Filter.Eventually.of_forall (fun e => normalizedBlockNorm_nonneg _))
    (Filter.Eventually.of_forall (fun e => normalizedBlockNorm_nonneg _))
    (Filter.Eventually.of_forall hpinch)
    (Filter.Eventually.of_forall (fun e => sq_nonneg _))
    (Filter.Eventually.of_forall (fun e => sq_nonneg _))
    (d.radialEnergy_support o) (d.coupledIntegrand_bound o hp)
    hvi hbi hplus hminus (fun _ => hgapPlus hpzero) (fun _ => hgapMinus hmzero)
  rcases hz with hz | hz
  · exact Or.inl (fun e _ => hz e)
  · exact Or.inr (fun e _ => hz e)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The individual Weyl norms descend to each oriented frame component. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular QuaternionFrame
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem frameTensor_one {n : ℕ} (T : CovariantCoordinates n) :
    frameTensor (1 : Mat4) T = T := by
  induction n with
  | zero =>
    funext a
    exact frameTensor_zero _ T a
  | succ n ih =>
    funext a
    obtain ⟨i, v, rfl⟩ := Fin.exists_cons a
    rw [frameTensor_cons]
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    exact congrFun (ih (fun w => T (Fin.cons i w))) v

/-- The adjoint of tensor pullback by an orthogonal matrix is pullback
by its transpose, on all covariant slots. -/
theorem frameTensorPairing_adjoint {n : ℕ} (P : Mat4) (hP : Pᵀ * P = 1)
    (T S : CovariantCoordinates n) :
    frameTensorPairing (frameTensor P T) S =
      frameTensorPairing T (frameTensor Pᵀ S) := by
  have heq : frameTensor P (frameTensor Pᵀ S) = S := by
    rw [← frameTensor_mul, hP, frameTensor_one]
  calc
    _ = frameTensorPairing (frameTensor P T) (frameTensor P (frameTensor Pᵀ S)) :=
      congrArg (frameTensorPairing (frameTensor P T)) heq.symm
    _ = _ := frameTensor_pairing_orthogonal P (mul_eq_one_comm.mp hP) T (frameTensor Pᵀ S)

private theorem bilinearPullback_apply (P A : Mat4) (i j : Fin 4) :
    (Pᵀ * A * P) i j = ∑ a, ∑ b, P a i * A a b * P b j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem sumPair_product (F G : Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, F a b) * (∑ c, ∑ d, G c d) =
      ∑ a, ∑ b, ∑ c, ∑ d, F a b * G c d := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]

/-- Pullback of the tensor product of two two-forms. -/
theorem frameTensor_twoFormProduct (P A B : Mat4) :
    frameTensor P (fun a : Fin 4 → Fin 4 => twoFormProduct A B (a 0) (a 1) (a 2) (a 3)) =
      fun a => twoFormProduct (Pᵀ * A * P) (Pᵀ * B * P)
        (a 0) (a 1) (a 2) (a 3) := by
  funext a
  have ha : a = ![a 0, a 1, a 2, a 3] := by
    funext i
    fin_cases i <;> rfl
  rw [ha, frameTensor_four]
  change (∑ p, ∑ q, ∑ r, ∑ s,
    P p (a 0) * P q (a 1) * P r (a 2) * P s (a 3) * (A p q * B s r)) =
      (Pᵀ * A * P) (a 0) (a 1) * (Pᵀ * B * P) (a 3) (a 2)
  rw [bilinearPullback_apply, bilinearPullback_apply, sumPair_product]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_comm]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

theorem twoFormPairing_frameTensor (P : Mat4) (hP : Pᵀ * P = 1)
    (T : CovariantCoordinates 4) (A B : Mat4) :
    twoFormPairing (frameTensor P T) A B =
      twoFormPairing T (P * A * Pᵀ) (P * B * Pᵀ) := by
  have h := frameTensorPairing_adjoint P hP T
    (fun a => twoFormProduct A B (a 0) (a 1) (a 2) (a 3))
  rw [frameTensorPairing_twoFormProduct, frameTensor_twoFormProduct,
    Matrix.transpose_transpose, frameTensorPairing_twoFormProduct] at h
  linarith

/-- The block contraction changes by the actual induced three-dimensional
orthogonal coefficient matrix. -/
theorem blockCoordinates_frameTensor (P : Mat4) (hP : Pᵀ * P = 1)
    (Q : Fin 3 → Mat4) (R : Mat3)
    (hR : ∀ s, P * Q s * Pᵀ = imaginaryCombination Q (fun r => R r s))
    (T : CovariantCoordinates 4) :
    blockCoordinates (frameTensor P T) Q =
      conjugateMatrix R (blockCoordinates T Q) := by
  ext s t
  rw [blockCoordinates_pairing, twoFormPairing_frameTensor P hP, hR s, hR t]
  simp only [imaginaryCombination, Fin.sum_univ_three, twoFormPairing_add_left,
    twoFormPairing_add_right, twoFormPairing_smul_left, twoFormPairing_smul_right]
  simp only [conjugateMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_three, blockCoordinates_pairing]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

/-- Two frames in the same oriented component have an orientation-preserving
orthogonal change matrix. -/
theorem OrthonormalFrame.changeMatrix_det_one (e f : OrthonormalFrame g c)
    (hor : 0 < e.matrix.det * f.matrix.det) : (e.changeMatrix f).det = 1 := by
  have hd := congrArg Matrix.det (e.mul_changeMatrix f)
  rw [Matrix.det_mul] at hd
  have hp : 0 < (e.matrix.det) ^ 2 * (e.changeMatrix f).det := by
    calc
      _ = e.matrix.det * f.matrix.det := by rw [← hd]; ring
      _ > 0 := hor
  have hpos : 0 < (e.changeMatrix f).det := by
    rcases mul_pos_iff.mp hp with h | h
    · exact h.2
    · exact False.elim ((not_lt_of_ge (sq_nonneg e.matrix.det)) h.1)
  have ho := congrArg Matrix.det (e.changeMatrix_orthogonal f)
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at ho
  nlinarith

private theorem frameCurvatureBlock_eq (e : OrthonormalFrame g c)
    (Q : Fin 3 → Mat4) :
    curvatureBlock (curvaturePairing g c e) Q =
      blockCoordinates (frameTensor e.matrix
        (curvatureCoordinates g c (chartAt FourSpace c c))) Q := by
  ext a b
  simp only [blockCoordinates, curvatureBlock, frameTensor_curvatureCoordinates,
    curvaturePairing]

private theorem blockNorm_same_oriented_frame (e f : OrthonormalFrame g c)
    (Q : Fin 3 → Mat4) (R : Mat3) (hR : Rᵀ * R = 1)
    (hspan : ∀ s, e.changeMatrix f * Q s * (e.changeMatrix f)ᵀ =
      imaginaryCombination Q (fun r => R r s)) :
    normalizedBlockNorm (curvatureBlock (curvaturePairing g c e) Q - 1) =
      normalizedBlockNorm (curvatureBlock (curvaturePairing g c f) Q - 1) := by
  let T : CovariantCoordinates 4 := curvatureCoordinates g c (chartAt FourSpace c c)
  have heq : blockCoordinates (frameTensor f.matrix T) Q =
      conjugateMatrix R (blockCoordinates (frameTensor e.matrix T) Q) := by
    rw [← e.mul_changeMatrix f, frameTensor_mul]
    exact blockCoordinates_frameTensor _ (e.changeMatrix_orthogonal f) Q R hspan _
  rw [frameCurvatureBlock_eq e Q, frameCurvatureBlock_eq f Q]
  change normalizedBlockNorm (blockCoordinates (frameTensor e.matrix T) Q - 1) =
    normalizedBlockNorm (blockCoordinates (frameTensor f.matrix T) Q - 1)
  rw [heq]
  have hsub (B : Mat3) : conjugateMatrix R (B - 1) = conjugateMatrix R B - 1 := by
    rw [conjugateMatrix_sub, conjugateMatrix_one R hR]
  rw [← hsub]
  exact (conjugateMatrix_norm R (mul_eq_one_comm.mp hR) _).symm

theorem plusWeyl_norm_same_oriented_frame (e f : OrthonormalFrame g c)
    (hor : 0 < e.matrix.det * f.matrix.det) :
    normalizedBlockNorm (plusWeyl g c e) = normalizedBlockNorm (plusWeyl g c f) := by
  exact blockNorm_same_oriented_frame e f quaternionMatrix
    (positiveOrientationMatrix (e.changeMatrix f))
    (positiveOrientationMatrix_orthogonal _ (e.changeMatrix_orthogonal f)
      (e.changeMatrix_det_one f hor))
    (positiveOrientationMatrix_span _ (e.changeMatrix_orthogonal f)
      (e.changeMatrix_det_one f hor))

theorem minusWeyl_norm_same_oriented_frame (e f : OrthonormalFrame g c)
    (hor : 0 < e.matrix.det * f.matrix.det) :
    normalizedBlockNorm (minusWeyl g c e) = normalizedBlockNorm (minusWeyl g c f) := by
  exact blockNorm_same_oriented_frame e f oppositeMatrix
    (negativeOrientationMatrix (e.changeMatrix f))
    (negativeOrientationMatrix_orthogonal _ (e.changeMatrix_orthogonal f)
      (e.changeMatrix_det_one f hor))
    (negativeOrientationMatrix_span _ (e.changeMatrix_orthogonal f)
      (e.changeMatrix_det_one f hor))


theorem actual_plusNorm_frame (o : FrameOrientation g) (e : FrameBundle g)
    (he : e ∈ o.positive) :
    plusNorm o e.base = normalizedBlockNorm (plusWeyl g e.base e.frame) := by
  exact plusWeyl_norm_same_oriented_frame (o.frame e.base) e.frame
    ((o.positive_iff_det e.base e.frame).mp he)

theorem actual_minusNorm_frame (o : FrameOrientation g) (e : FrameBundle g)
    (he : e ∈ o.positive) :
    minusNorm o e.base = normalizedBlockNorm (minusWeyl g e.base e.frame) := by
  exact minusWeyl_norm_same_oriented_frame (o.frame e.base) e.frame
    ((o.positive_iff_det e.base e.frame).mp he)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Lowering the actual chart curvature transformation and pulling back
all four covariant slots. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

def loweredMatrixTensor (G : Mat4) (R : Fin 4 → Fin 4 → Mat4) :
    CovariantCoordinates 4 := fun a => (G * R (a 0) (a 1)) (a 3) (a 2)

private theorem lowered_matrix_transition (G H J : Mat4)
    (R S : Fin 4 → Fin 4 → Mat4) (hJ : IsUnit J.det)
    (hG : G = Jᵀ * H * J)
    (hR : ∀ i j, R i j = J⁻¹ * (∑ a, ∑ b, (J a i * J b j) • S a b) * J)
    (i j : Fin 4) :
    G * R i j = ∑ a, ∑ b, (J a i * J b j) • (Jᵀ * (H * S a b) * J) := by
  calc
    _ = Jᵀ * H * (J * J⁻¹) * (∑ a, ∑ b, (J a i * J b j) • S a b) * J := by
      rw [hG, hR]
      simp only [Matrix.mul_assoc]
    _ = Jᵀ * H * (∑ a, ∑ b, (J a i * J b j) • S a b) * J := by
      rw [Matrix.mul_nonsing_inv _ hJ, Matrix.mul_one]
    _ = _ := by
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_assoc]

theorem loweredMatrixTensor_transition (G H J : Mat4)
    (R S : Fin 4 → Fin 4 → Mat4) (hJ : IsUnit J.det)
    (hG : G = Jᵀ * H * J)
    (hR : ∀ i j, R i j = J⁻¹ * (∑ a, ∑ b, (J a i * J b j) • S a b) * J) :
    loweredMatrixTensor G R = frameTensor J (loweredMatrixTensor H S) := by
  funext v
  have hv : v = ![v 0, v 1, v 2, v 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, frameTensor_four]
  change (G * R (v 0) (v 1)) (v 3) (v 2) = _
  rw [lowered_matrix_transition G H J R S hJ hG hR]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum,
    loweredMatrixTensor]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  dsimp
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

private theorem loweredMatrixTensor_curvature (g : SmoothMetric M) (c : M) (z : FourSpace) :
    loweredMatrixTensor (metricInChart g c z)
      (fun i j => coordinateCurvatureMatrix g c i j z) = curvatureCoordinates g c z := by
  funext a
  simp only [loweredMatrixTensor, Matrix.mul_apply, coordinateCurvatureMatrix_apply,
    curvatureCoordinates]
  apply Finset.sum_congr rfl
  intro b _
  rw [show metricInChart g c z (a 3) b = metricInChart g c z b (a 3) from g.symm _ _ _]

/-- Actual lowered curvature is a covariant four-tensor on chart overlaps. -/
theorem curvatureCoordinates_transition (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    curvatureCoordinates g c z = frameTensor (chartTransitionMatrix c d z)
      (curvatureCoordinates g d (chartTransition c d z)) := by
  rw [← loweredMatrixTensor_curvature g c z,
    ← loweredMatrixTensor_curvature g d (chartTransition c d z)]
  exact loweredMatrixTensor_transition _ _ _ _ _
    (isUnit_iff_ne_zero.mpr (chartTransitionMatrix_det_ne_zero g c d z hz hx))
    (by simpa only [Matrix.mul_assoc] using metricInChart_transition g c d z hz hx)
    (coordinateCurvatureMatrix_transition g c d z hz hx)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The infinitesimal orthonormal-frame action on two-forms preserves the
Hodge splitting and the fiber inner product. This is the local algebra
needed for the induced Levi-Civita connection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

def twoFormSkewAction (b a : TwoFormFour) : TwoFormFour :=
  WithLp.toLp 2 ![
    -b 1 * a 3 + a 1 * b 3 - b 2 * a 4 + a 2 * b 4,
    b 0 * a 3 - a 0 * b 3 - b 2 * a 5 + a 2 * b 5,
    b 0 * a 4 - a 0 * b 4 + b 1 * a 5 - a 1 * b 5,
    -b 0 * a 1 + a 0 * b 1 - b 4 * a 5 + a 4 * b 5,
    -b 0 * a 2 + a 0 * b 2 + b 3 * a 5 - a 3 * b 5,
    -b 1 * a 2 + a 1 * b 2 - b 3 * a 4 + a 3 * b 4]

theorem twoFormSkewAction_matrix (b a : TwoFormFour) :
    twoFormMatrix (twoFormSkewAction b a) =
      twoFormMatrix b * twoFormMatrix a - twoFormMatrix a * twoFormMatrix b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoFormSkewAction, twoFormMatrix] <;> ring

def twoFormSkewActionLinear (b : TwoFormFour) : TwoFormFour →ₗ[ℝ] TwoFormFour where
  toFun := twoFormSkewAction b
  map_add' a c := by
    ext i
    fin_cases i <;> simp [twoFormSkewAction] <;> ring
  map_smul' r a := by
    ext i
    fin_cases i <;> simp [twoFormSkewAction] <;> ring

theorem twoFormSkewAction_hodge (b a : TwoFormFour) :
    twoFormSkewAction b (twoFormHodge a) = twoFormHodge (twoFormSkewAction b a) := by
  ext i
  fin_cases i <;> simp [twoFormSkewAction, twoFormHodge, twoFormHodgeLinear] <;> ring

theorem twoFormSkewAction_skewAdjoint (b a c : TwoFormFour) :
    inner ℝ (twoFormSkewAction b a) c = -inner ℝ a (twoFormSkewAction b c) := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, twoFormSkewAction,
    Fin.sum_univ_succ]
  ring

theorem twoFormSkewAction_selfDual (b a : TwoFormFour) (ha : twoFormHodge a = a) :
    twoFormHodge (twoFormSkewAction b a) = twoFormSkewAction b a := by
  rw [← twoFormSkewAction_hodge, ha]

theorem twoFormSkewAction_antiSelfDual (b a : TwoFormFour) (ha : twoFormHodge a = -a) :
    twoFormHodge (twoFormSkewAction b a) = -twoFormSkewAction b a := by
  rw [← twoFormSkewAction_hodge, ha]
  exact (twoFormSkewActionLinear b).map_neg a

end
end PositiveEinsteinFour.Geometry
end


section

/-! Explicit three-dimensional self-dual and anti-self-dual fibers. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour

noncomputable section

def selfDualTwoForms : Submodule ℝ TwoFormFour where
  carrier := {a | twoFormHodge a = a}
  zero_mem' := map_zero _
  add_mem' {a} {b} ha hb := by
    change twoFormHodge a = a at ha
    change twoFormHodge b = b at hb
    change twoFormHodge (a + b) = a + b
    rw [map_add, ha, hb]
  smul_mem' r a ha := by
    change twoFormHodge a = a at ha
    change twoFormHodge (r • a) = r • a
    rw [map_smul, ha]

def antiSelfDualTwoForms : Submodule ℝ TwoFormFour where
  carrier := {a | twoFormHodge a = -a}
  zero_mem' := by simp
  add_mem' {a} {b} ha hb := by
    change twoFormHodge a = -a at ha
    change twoFormHodge b = -b at hb
    change twoFormHodge (a + b) = -(a + b)
    rw [map_add, ha, hb, neg_add]
  smul_mem' r a ha := by
    change twoFormHodge a = -a at ha
    change twoFormHodge (r • a) = -(r • a)
    rw [map_smul, ha, smul_neg]

def selfDualTwoFormCoordinates (x : EuclideanSpace ℝ (Fin 3)) : TwoFormFour :=
  WithLp.toLp 2 ![x 0, x 1, x 2, x 2, -x 1, x 0]

def antiSelfDualTwoFormCoordinates (x : EuclideanSpace ℝ (Fin 3)) : TwoFormFour :=
  WithLp.toLp 2 ![x 0, x 1, x 2, -x 2, x 1, -x 0]

theorem selfDualTwoFormCoordinates_hodge (x : EuclideanSpace ℝ (Fin 3)) :
    twoFormHodge (selfDualTwoFormCoordinates x) = selfDualTwoFormCoordinates x := by
  ext i
  fin_cases i <;> simp [twoFormHodge, twoFormHodgeLinear, selfDualTwoFormCoordinates]

theorem antiSelfDualTwoFormCoordinates_hodge (x : EuclideanSpace ℝ (Fin 3)) :
    twoFormHodge (antiSelfDualTwoFormCoordinates x) = -antiSelfDualTwoFormCoordinates x := by
  ext i
  fin_cases i <;> simp [twoFormHodge, twoFormHodgeLinear, antiSelfDualTwoFormCoordinates]

def selfDualTwoFormEquiv : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] selfDualTwoForms where
  toFun x := ⟨selfDualTwoFormCoordinates x, selfDualTwoFormCoordinates_hodge x⟩
  invFun a := WithLp.toLp 2 ![a.val 0, a.val 1, a.val 2]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv a := by
    apply Subtype.ext
    have ha : twoFormHodge a.val = a.val := a.property
    have h0 := congrArg (fun x : TwoFormFour => x 0) ha
    have h1 := congrArg (fun x : TwoFormFour => x 1) ha
    have h2 := congrArg (fun x : TwoFormFour => x 2) ha
    change a.val 5 = a.val 0 at h0
    change -a.val 4 = a.val 1 at h1
    change a.val 3 = a.val 2 at h2
    ext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · exact h2.symm
    · change -a.val 1 = a.val 4
      linarith
    · exact h0.symm
  map_add' x y := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [selfDualTwoFormCoordinates, add_comm]
  map_smul' r x := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [selfDualTwoFormCoordinates]

def antiSelfDualTwoFormEquiv : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] antiSelfDualTwoForms where
  toFun x := ⟨antiSelfDualTwoFormCoordinates x, antiSelfDualTwoFormCoordinates_hodge x⟩
  invFun a := WithLp.toLp 2 ![a.val 0, a.val 1, a.val 2]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv a := by
    apply Subtype.ext
    have ha : twoFormHodge a.val = -a.val := a.property
    have h0 := congrArg (fun x : TwoFormFour => x 0) ha
    have h1 := congrArg (fun x : TwoFormFour => x 1) ha
    have h2 := congrArg (fun x : TwoFormFour => x 2) ha
    change a.val 5 = -a.val 0 at h0
    change -a.val 4 = -a.val 1 at h1
    change a.val 3 = -a.val 2 at h2
    ext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · exact h2.symm
    · change a.val 1 = a.val 4
      linarith
    · exact h0.symm
  map_add' x y := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [antiSelfDualTwoFormCoordinates, add_comm]
  map_smul' r x := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [antiSelfDualTwoFormCoordinates]

theorem selfDualTwoForms_finrank : Module.finrank ℝ selfDualTwoForms = 3 := by
  rw [← selfDualTwoFormEquiv.finrank_eq]
  simp

theorem antiSelfDualTwoForms_finrank : Module.finrank ℝ antiSelfDualTwoForms = 3 := by
  rw [← antiSelfDualTwoFormEquiv.finrank_eq]
  simp

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two-form Hodge operator is independent of the chosen positively
oriented orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian QuaternionFrame Angular
open scoped BigOperators

noncomputable section

theorem hodgeStarFour_quaternion_combination (u : Fin 3 → ℝ) :
    hodgeStarFour (imaginaryCombination quaternionMatrix u) =
      imaginaryCombination quaternionMatrix u := by
  simp only [imaginaryCombination, map_sum, map_smul, hodgeStarFour_quaternion]

theorem hodgeStarFour_opposite_combination (u : Fin 3 → ℝ) :
    hodgeStarFour (imaginaryCombination oppositeMatrix u) =
      -imaginaryCombination oppositeMatrix u := by
  simp only [imaginaryCombination, map_sum, map_smul, hodgeStarFour_opposite,
    smul_neg, Finset.sum_neg_distrib]

theorem hodgeStarFour_sandwich_quaternion (P : Mat4) (hP : Pᵀ * P = 1)
    (hdet : P.det = 1) (s : Fin 3) :
    hodgeStarFour (P * quaternionMatrix s * Pᵀ) = P * quaternionMatrix s * Pᵀ := by
  rw [oriented_quaternion_span P hP hdet s]
  exact hodgeStarFour_quaternion_combination _

theorem hodgeStarFour_sandwich_opposite (P : Mat4) (hP : Pᵀ * P = 1)
    (hdet : P.det = 1) (s : Fin 3) :
    hodgeStarFour (P * oppositeMatrix s * Pᵀ) = -(P * oppositeMatrix s * Pᵀ) := by
  rw [oriented_opposite_span P hP hdet s]
  exact hodgeStarFour_opposite_combination _

private theorem sandwich_combination (P : Mat4) (Q : Fin 3 → Mat4) (u : Fin 3 → ℝ) :
    P * imaginaryCombination Q u * Pᵀ = imaginaryCombination (fun s => P * Q s * Pᵀ) u := by
  simp only [imaginaryCombination, Matrix.mul_sum, Matrix.sum_mul,
    mul_smul_comm, smul_mul_assoc]

private theorem twoFormMatrix_quaternion_decomposition (a : TwoFormFour) :
    twoFormMatrix a =
      imaginaryCombination quaternionMatrix
        ![-(a 0 + a 5) / 2, -(a 1 - a 4) / 2, -(a 2 + a 3) / 2] +
      imaginaryCombination oppositeMatrix
        ![(a 0 - a 5) / 2, (a 1 + a 4) / 2, (a 2 - a 3) / 2] := by
  ext i j
  simp only [imaginaryCombination_apply, Matrix.add_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    norm_num [twoFormMatrix, quaternionMatrix, oppositeMatrix, oppositeQuaternion] <;> ring

theorem hodgeStarFour_oriented_frame_change (P : Mat4) (hP : Pᵀ * P = 1)
    (hdet : P.det = 1) (a : TwoFormFour) :
    hodgeStarFour (P * twoFormMatrix a * Pᵀ) =
      P * hodgeStarFour (twoFormMatrix a) * Pᵀ := by
  have hp (u : Fin 3 → ℝ) :
      hodgeStarFour (P * imaginaryCombination quaternionMatrix u * Pᵀ) =
        P * imaginaryCombination quaternionMatrix u * Pᵀ := by
    rw [sandwich_combination]
    simp only [imaginaryCombination, map_sum, map_smul,
      hodgeStarFour_sandwich_quaternion P hP hdet]
  have hm (u : Fin 3 → ℝ) :
      hodgeStarFour (P * imaginaryCombination oppositeMatrix u * Pᵀ) =
        -(P * imaginaryCombination oppositeMatrix u * Pᵀ) := by
    rw [sandwich_combination]
    simp only [imaginaryCombination, map_sum, map_smul,
      hodgeStarFour_sandwich_opposite P hP hdet, smul_neg, Finset.sum_neg_distrib]
  rw [twoFormMatrix_quaternion_decomposition]
  simp only [Matrix.mul_add, Matrix.add_mul, map_add, hp, hm,
    hodgeStarFour_quaternion_combination, hodgeStarFour_opposite_combination,
    Matrix.mul_neg, Matrix.neg_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A four-column Gram--Schmidt normalizer with entrywise smooth dependence
on the positive metric matrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

abbrev CoordinateColumn := Fin 4 → ℝ

def metricPair (G : Mat4) (u v : CoordinateColumn) : ℝ :=
  ∑ i, ∑ j, u i * G i j * v j

def gramRemove (G : Mat4) (u v : CoordinateColumn) : CoordinateColumn :=
  v - (metricPair G u v / metricPair G u u) • u

def gramColumnZero (_G : Mat4) : CoordinateColumn := Pi.single 0 1

def gramColumnOne (G : Mat4) : CoordinateColumn :=
  gramRemove G (gramColumnZero G) (Pi.single 1 1)

def gramColumnTwo (G : Mat4) : CoordinateColumn :=
  gramRemove G (gramColumnOne G) (gramRemove G (gramColumnZero G) (Pi.single 2 1))

def gramColumnThree (G : Mat4) : CoordinateColumn :=
  gramRemove G (gramColumnTwo G)
    (gramRemove G (gramColumnOne G) (gramRemove G (gramColumnZero G) (Pi.single 3 1)))

def gramColumn (G : Mat4) (i : Fin 4) : CoordinateColumn :=
  ![gramColumnZero G, gramColumnOne G, gramColumnTwo G, gramColumnThree G] i

/-- The lower-triangular leading coefficient of every residual is one. -/
theorem gramColumn_diagonal (G : Mat4) (i : Fin 4) : gramColumn G i i = 1 := by
  fin_cases i <;> simp [gramColumn, gramColumnZero, gramColumnOne,
    gramColumnTwo, gramColumnThree, gramRemove]

theorem gramColumn_above (G : Mat4) (i j : Fin 4) (hij : i < j) :
    gramColumn G i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [gramColumn, gramColumnZero,
    gramColumnOne, gramColumnTwo, gramColumnThree, gramRemove]

theorem gramColumn_ne_zero (G : Mat4) (i : Fin 4) : gramColumn G i ≠ 0 := by
  intro h
  have hi := gramColumn_diagonal G i
  rw [h] at hi
  norm_num at hi

theorem metricPair_pos (G : Mat4) (hG : G.PosDef) (u : CoordinateColumn) (hu : u ≠ 0) :
    0 < metricPair G u u := by
  simpa only [metricPair, star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    using hG.dotProduct_mulVec_pos hu

theorem gramColumn_energy_pos (G : Mat4) (hG : G.PosDef) (i : Fin 4) :
    0 < metricPair G (gramColumn G i) (gramColumn G i) :=
  metricPair_pos G hG _ (gramColumn_ne_zero G i)

theorem metricPair_symm (G : Mat4) (hG : G.IsHermitian) (u v : CoordinateColumn) :
    metricPair G u v = metricPair G v u := by
  have hs (i j : Fin 4) : G i j = G j i := by
    have h := congrArg (fun A : Mat4 => A j i) hG.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  unfold metricPair
  rw [Finset.sum_comm]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  rw [hs]
  ring

theorem metricPair_gramRemove (G : Mat4) (w u v : CoordinateColumn) :
    metricPair G w (gramRemove G u v) = metricPair G w v -
      (metricPair G u v / metricPair G u u) * metricPair G w u := by
  simp only [metricPair, gramRemove, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

theorem metricPair_gramRemove_self (G : Mat4) (u v : CoordinateColumn)
    (hu : metricPair G u u ≠ 0) : metricPair G u (gramRemove G u v) = 0 := by
  rw [metricPair_gramRemove, div_mul_cancel₀ _ hu, sub_self]

theorem metricPair_gramRemove_orthogonal (G : Mat4) (w u v : CoordinateColumn)
    (hwu : metricPair G w u = 0) :
    metricPair G w (gramRemove G u v) = metricPair G w v := by
  rw [metricPair_gramRemove, hwu, mul_zero, sub_zero]

/-- Orthogonality is proved before normalization, using only the exact
projection formula and positivity of the residual energies. -/
theorem gramColumn_orthogonal (G : Mat4) (hG : G.PosDef)
    (i j : Fin 4) (hij : i ≠ j) : metricPair G (gramColumn G i) (gramColumn G j) = 0 := by
  have hp (i : Fin 4) : metricPair G (gramColumn G i) (gramColumn G i) ≠ 0 :=
    (gramColumn_energy_pos G hG i).ne'
  have h0 : metricPair G (gramColumnZero G) (gramColumnZero G) ≠ 0 := hp 0
  have h1 : metricPair G (gramColumnOne G) (gramColumnOne G) ≠ 0 := hp 1
  have h2 : metricPair G (gramColumnTwo G) (gramColumnTwo G) ≠ 0 := hp 2
  have h01 : metricPair G (gramColumnZero G) (gramColumnOne G) = 0 :=
    metricPair_gramRemove_self G _ _ h0
  have h02 : metricPair G (gramColumnZero G) (gramColumnTwo G) = 0 := by
    rw [gramColumnTwo, metricPair_gramRemove_orthogonal _ _ _ _ h01]
    exact metricPair_gramRemove_self G _ _ h0
  have h12 : metricPair G (gramColumnOne G) (gramColumnTwo G) = 0 :=
    metricPair_gramRemove_self G _ _ h1
  have h03 : metricPair G (gramColumnZero G) (gramColumnThree G) = 0 := by
    rw [gramColumnThree, metricPair_gramRemove_orthogonal _ _ _ _ h02,
      metricPair_gramRemove_orthogonal _ _ _ _ h01]
    exact metricPair_gramRemove_self G _ _ h0
  have h13 : metricPair G (gramColumnOne G) (gramColumnThree G) = 0 := by
    rw [gramColumnThree, metricPair_gramRemove_orthogonal _ _ _ _ h12]
    exact metricPair_gramRemove_self G _ _ h1
  have h23 : metricPair G (gramColumnTwo G) (gramColumnThree G) = 0 :=
    metricPair_gramRemove_self G _ _ h2
  have hs := metricPair_symm G hG.isHermitian
  fin_cases i <;> fin_cases j <;> dsimp only [gramColumn]
  all_goals first
    | exact False.elim (hij rfl)
    | assumption
    | exact (hs _ _).trans h01
    | exact (hs _ _).trans h02
    | exact (hs _ _).trans h03
    | exact (hs _ _).trans h12
    | exact (hs _ _).trans h13
    | exact (hs _ _).trans h23

/-- The inverse square roots of the four residual energies give an
orthonormal frame, with no eigenvector selection. -/
def gramNormalizer (G : Mat4) : Mat4 := fun k i =>
  (Real.sqrt (metricPair G (gramColumn G i) (gramColumn G i)))⁻¹ * gramColumn G i k

private theorem metricPair_scaled (G : Mat4) (u v : CoordinateColumn) (a b : ℝ) :
    metricPair G (fun i => a * u i) (fun i => b * v i) = a * b * metricPair G u v := by
  simp only [metricPair, Finset.mul_sum]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

theorem gramNormalizer_normalizes (G : Mat4) (hG : G.PosDef) :
    (gramNormalizer G)ᵀ * G * gramNormalizer G = 1 := by
  ext i j
  have hp := gramColumn_energy_pos G hG
  have heq : ((gramNormalizer G)ᵀ * G * gramNormalizer G) i j =
      metricPair G (fun k => gramNormalizer G k i) (fun k => gramNormalizer G k j) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, metricPair, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [heq]
  change metricPair G (fun k => _ * gramColumn G i k)
    (fun k => _ * gramColumn G j k) = if i = j then 1 else 0
  rw [metricPair_scaled]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    have hs : Real.sqrt (metricPair G (gramColumn G i) (gramColumn G i)) ≠ 0 :=
      (Real.sqrt_pos.2 (hp i)).ne'
    have hsq := Real.sq_sqrt (hp i).le
    field_simp
    nlinarith
  · rw [ite_eq_right hij, gramColumn_orthogonal G hG i j hij, mul_zero]

/-- Smoothness of the finite bilinear pairing with varying coefficients. -/
theorem metricPair_contDiffAt {G : FourSpace → Mat4} {u v : FourSpace → CoordinateColumn}
    {z : FourSpace} (hG : ∀ i j, ContDiffAt ℝ ∞ (fun w => G w i j) z)
    (hu : ∀ i, ContDiffAt ℝ ∞ (fun w => u w i) z)
    (hv : ∀ i, ContDiffAt ℝ ∞ (fun w => v w i) z) :
    ContDiffAt ℝ ∞ (fun w => metricPair (G w) (u w) (v w)) z := by
  unfold metricPair
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact ((hu i).mul (hG i j)).mul (hv j)

theorem gramRemove_contDiffAt {G : FourSpace → Mat4} {u v : FourSpace → CoordinateColumn}
    {z : FourSpace} (hG : ∀ i j, ContDiffAt ℝ ∞ (fun w => G w i j) z)
    (hu : ∀ i, ContDiffAt ℝ ∞ (fun w => u w i) z)
    (hv : ∀ i, ContDiffAt ℝ ∞ (fun w => v w i) z)
    (hp : metricPair (G z) (u z) (u z) ≠ 0) (i : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => gramRemove (G w) (u w) (v w) i) z := by
  have hc := (metricPair_contDiffAt hG hu hv).div (metricPair_contDiffAt hG hu hu) hp
  exact (hv i).sub (hc.mul (hu i))

theorem gramColumn_contDiffAt {G : FourSpace → Mat4} {z : FourSpace}
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun w => G w i j) z) (hp : (G z).PosDef)
    (i j : Fin 4) : ContDiffAt ℝ ∞ (fun w => gramColumn (G w) i j) z := by
  have hzero (j : Fin 4) : ContDiffAt ℝ ∞ (fun w => gramColumnZero (G w) j) z :=
    contDiffAt_const
  have hp0 : metricPair (G z) (gramColumnZero (G z)) (gramColumnZero (G z)) ≠ 0 :=
    (gramColumn_energy_pos (G z) hp 0).ne'
  have hone (j : Fin 4) : ContDiffAt ℝ ∞ (fun w => gramColumnOne (G w) j) z :=
    gramRemove_contDiffAt (v := fun _ => Pi.single 1 1) hG hzero
      (fun _ => contDiffAt_const) hp0 j
  have hp1 : metricPair (G z) (gramColumnOne (G z)) (gramColumnOne (G z)) ≠ 0 :=
    (gramColumn_energy_pos (G z) hp 1).ne'
  have htwo (j : Fin 4) : ContDiffAt ℝ ∞ (fun w => gramColumnTwo (G w) j) z := by
    exact gramRemove_contDiffAt hG hone
      (gramRemove_contDiffAt (v := fun _ => Pi.single 2 1) hG hzero
        (fun _ => contDiffAt_const) hp0) hp1 j
  have hp2 : metricPair (G z) (gramColumnTwo (G z)) (gramColumnTwo (G z)) ≠ 0 :=
    (gramColumn_energy_pos (G z) hp 2).ne'
  have hthree (j : Fin 4) : ContDiffAt ℝ ∞ (fun w => gramColumnThree (G w) j) z := by
    exact gramRemove_contDiffAt hG htwo
      (gramRemove_contDiffAt hG hone
        (gramRemove_contDiffAt (v := fun _ => Pi.single 3 1) hG hzero
          (fun _ => contDiffAt_const) hp0) hp1) hp2 j
  fin_cases i
  · exact hzero j
  · exact hone j
  · exact htwo j
  · exact hthree j

theorem gramNormalizer_contDiffAt {G : FourSpace → Mat4} {z : FourSpace}
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun w => G w i j) z) (hp : (G z).PosDef)
    (i j : Fin 4) : ContDiffAt ℝ ∞ (fun w => gramNormalizer (G w) i j) z := by
  have hc := gramColumn_contDiffAt hG hp j
  have he := metricPair_contDiffAt hG hc hc
  have hpos := gramColumn_energy_pos (G z) hp j
  have hs : ContDiffAt ℝ ∞ (fun w => Real.sqrt
      (metricPair (G w) (gramColumn (G w) j) (gramColumn (G w) j))) z :=
    (Real.contDiffAt_sqrt hpos.ne').comp z he
  exact (hs.inv (Real.sqrt_pos.2 hpos).ne').mul (hc i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Weyl-norm difference variance follows by passing the smooth scalar
theorem to the limit using parallel-frame calculus. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped Manifold ContDiff Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ}

/-- Only the precise classical inputs of the smooth scalar argument. -/
structure ScalarVarianceInputs (d : MetricGreenData g μ) (orientation : FrameOrientation g) : Prop where
  norms : PetersenOrientedNormInput orientation
  orientationFlow : OrientationPreservingFlow d orientation
  supported : ∀ᵐ e ∂μ, e ∈ orientation.positive
  calculus : PetersenScalarCalculusInput d
  poisson : PetersenPoissonInput g μ
  positive : ShiftedCurvaturePositive g
  decomposition : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
    Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)

theorem blockRadialGradient_zero_of_norm_zero (A : Mat) (Z : Fin 4 → Mat)
    (h : normalizedBlockNorm A = 0) : blockRadialGradient A Z = 0 := by
  have hA := (normalizedBlockNorm_eq_zero_iff A).mp h
  subst A
  ext i
  simp [blockRadialGradient, regularizedRadialDerivative]

def normRegularizationParameter (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem normRegularizationParameter_mem (n : ℕ) :
    normRegularizationParameter n ∈ Set.Ioc (0 : ℝ) 1 := by
  constructor
  · unfold normRegularizationParameter
    positivity
  · unfold normRegularizationParameter
    exact (div_le_one (by positivity : 0 < (n : ℝ) + 1)).2 (by linarith [Nat.cast_nonneg (α := ℝ) n])

theorem normRegularizationParameter_tendsto :
    Tendsto normRegularizationParameter atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem scalarVarianceWeight_continuous (o : OppositeWeylData d) :
    Continuous (scalarVarianceWeight g) :=
  (continuous_const.add ((continuous_normalizedBlockNorm.comp d.continuousWeyl).pow 2)).add
    ((continuous_normalizedBlockNorm.comp o.continuousWeyl).pow 2)

theorem scalarVarianceWeight_ge_one (e : FrameBundle g) : 1 ≤ scalarVarianceWeight g e := by
  unfold scalarVarianceWeight
  nlinarith [sq_nonneg (normalizedBlockNorm (plusWeyl g e.base e.frame)),
    sq_nonneg (normalizedBlockNorm (minusWeyl g e.base e.frame))]

variable [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]

theorem MetricGreenData.normDifferenceVariance (d : MetricGreenData g μ)
    (o : OppositeWeylData d) {orientation : FrameOrientation g}
    (s : ScalarVarianceInputs d orientation) (hparallel : ParallelReflection d)
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    (∫ e, (normalizedBlockNorm (plusWeyl g e.base e.frame) -
      normalizedBlockNorm (minusWeyl g e.base e.frame)) ^ 2 ∂μ) -
    (∫ e, normalizedBlockNorm (plusWeyl g e.base e.frame) -
      normalizedBlockNorm (minusWeyl g e.base e.frame) ∂μ) ^ 2 ≤
    ∫ e, ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) -
      blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)‖ ^ 2 /
        scalarVarianceWeight g e ∂μ := by
  apply Variance.difference_variance_of_regularized
    (continuous_normalizedBlockNorm.comp d.continuousWeyl).aemeasurable
    (continuous_normalizedBlockNorm.comp o.continuousWeyl).aemeasurable
    (scalarVarianceWeight_continuous o).aemeasurable
    d.radialVector_measurable (d.oppositeRadialVector_measurable o hparallel)
    (Filter.Eventually.of_forall (fun e => ⟨normalizedBlockNorm_nonneg _, by
      change normalizedBlockNorm (plusWeyl g e.base e.frame) ≤ 2
      linarith [hpinch e, normalizedBlockNorm_nonneg (minusWeyl g e.base e.frame)]⟩))
    (Filter.Eventually.of_forall (fun e => ⟨normalizedBlockNorm_nonneg _, by
      change normalizedBlockNorm (minusWeyl g e.base e.frame) ≤ 2
      linarith [hpinch e, normalizedBlockNorm_nonneg (plusWeyl g e.base e.frame)]⟩))
    (Filter.Eventually.of_forall scalarVarianceWeight_ge_one)
    (Filter.Eventually.of_forall (fun e => blockRadialGradient_zero_of_norm_zero _ _))
    (Filter.Eventually.of_forall (fun e => blockRadialGradient_zero_of_norm_zero _ _))
    d.radialEnergy_integrable (d.oppositeRadialEnergy_integrable o hparallel)
    normRegularizationParameter normRegularizationParameter_mem normRegularizationParameter_tendsto
  intro n
  exact regularized_difference_variance o orientation s.norms s.orientationFlow s.supported
    s.calculus s.poisson s.positive s.decomposition (normRegularizationParameter_mem n).1

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact principal symbol needed for the four-dimensional two-form
Hodge operator. The pair consists of contraction with a covector and
contraction after the actual Hodge star. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

def twoFormCodifferentialSymbol (ξ : FourSpace) (a : TwoFormFour) : FourSpace :=
  WithLp.toLp 2 ![ξ 1 * a 0 + ξ 2 * a 1 + ξ 3 * a 2,
    -ξ 0 * a 0 + ξ 2 * a 3 + ξ 3 * a 4,
    -ξ 0 * a 1 - ξ 1 * a 3 + ξ 3 * a 5,
    -ξ 0 * a 2 - ξ 1 * a 4 - ξ 2 * a 5]

theorem twoFormCodifferentialSymbol_matrix (ξ : FourSpace) (a : TwoFormFour) :
    twoFormCodifferentialSymbol ξ a = WithLp.toLp 2 (twoFormMatrix a *ᵥ ξ) := by
  ext i
  fin_cases i <;> simp [twoFormCodifferentialSymbol, twoFormMatrix, mulVec,
    dotProduct, Fin.sum_univ_four] <;> ring

def twoFormCodifferentialSymbolLinear (ξ : FourSpace) : TwoFormFour →ₗ[ℝ] FourSpace where
  toFun := twoFormCodifferentialSymbol ξ
  map_add' a b := by
    ext i
    fin_cases i <;> simp [twoFormCodifferentialSymbol] <;> ring
  map_smul' r a := by
    ext i
    fin_cases i <;> simp [twoFormCodifferentialSymbol] <;> ring

theorem twoFormDeRhamSymbol_norm_sq (ξ : FourSpace) (a : TwoFormFour) :
    ‖twoFormCodifferentialSymbol ξ a‖ ^ 2 +
      ‖twoFormCodifferentialSymbol ξ (twoFormHodge a)‖ ^ 2 = ‖ξ‖ ^ 2 * ‖a‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq]
  simp [twoFormCodifferentialSymbol, twoFormHodge, twoFormHodgeLinear,
    Fin.sum_univ_succ, Real.norm_eq_abs]
  ring

theorem twoFormDeRhamSymbol_inner (ξ : FourSpace) (a b : TwoFormFour) :
    inner ℝ (twoFormCodifferentialSymbol ξ a) (twoFormCodifferentialSymbol ξ b) +
      inner ℝ (twoFormCodifferentialSymbol ξ (twoFormHodge a))
        (twoFormCodifferentialSymbol ξ (twoFormHodge b)) = ‖ξ‖ ^ 2 * inner ℝ a b := by
  have hadd := twoFormDeRhamSymbol_norm_sq ξ (a + b)
  have ha := twoFormDeRhamSymbol_norm_sq ξ a
  have hb := twoFormDeRhamSymbol_norm_sq ξ b
  have hm : ∀ x y, twoFormCodifferentialSymbol ξ (x + y) =
      twoFormCodifferentialSymbol ξ x + twoFormCodifferentialSymbol ξ y :=
    (twoFormCodifferentialSymbolLinear ξ).map_add
  rw [map_add, hm, hm, norm_add_sq_real, norm_add_sq_real, norm_add_sq_real] at hadd
  nlinarith only [hadd, ha, hb]

theorem twoFormDeRhamSymbol_injective (ξ : FourSpace) (hξ : ξ ≠ 0)
    (a : TwoFormFour) (hδ : twoFormCodifferentialSymbol ξ a = 0)
    (hδstar : twoFormCodifferentialSymbol ξ (twoFormHodge a) = 0) : a = 0 := by
  have h := twoFormDeRhamSymbol_norm_sq ξ a
  rw [hδ, hδstar, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at h
  have hξpos : 0 < ‖ξ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hξ)
  have ha : ‖a‖ ^ 2 = 0 := (mul_eq_zero.mp h.symm).resolve_left (ne_of_gt hξpos)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp ha)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Christoffel transformation transports the covariant derivative
of every finite covariant tensor.  This is used only at ranks four to seven. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff Topology

noncomputable section

theorem tensorPartial_comp {n : ℕ} (F : FourSpace → FourSpace)
    (T : FourSpace → CovariantCoordinates n) (z : FourSpace)
    (hF : DifferentiableAt ℝ F z)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) (F z)) (i : Fin 4) :
    tensorPartial (fun w => T (F w)) i z =
      ∑ r, jacobianMatrix F z r i • tensorPartial T r (F z) := by
  funext a
  simpa only [tensorPartial, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    partialDeriv_comp hF (hT a) i

private theorem frameTensor_weighted_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (E : Mat4) (c : ι → ℝ) (T : ι → CovariantCoordinates n)
    (a : Fin n → Fin 4) :
    frameTensor E (∑ r, c r • T r) a = ∑ r, c r * frameTensor E (T r) a := by
  have he : (∑ r, c r • T r) = (fun b => ∑ r, c r * T r b) := by
    funext b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he, frameTensor_sum]
  simp only [frameTensor_const_mul]

/-- Connection cancellation in one direction, before adding the derivative
slot to the tensor pullback. -/
theorem covariantDirection_pullback {n : ℕ}
    (F : FourSpace → FourSpace) (E : FourSpace → Mat4)
    (C D : Fin 4 → FourSpace → Mat4) (T : FourSpace → CovariantCoordinates n)
    (z : FourSpace) (hF : DifferentiableAt ℝ F z)
    (hE : ∀ a b, DifferentiableAt ℝ (fun w => E w a b) z)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) (F z))
    (hJ : E z = jacobianMatrix F z) (i : Fin 4)
    (hC : E z * C i z = matrixPartial E i z +
      (∑ r, E z r i • D r (F z)) * E z) :
    tensorCovariantDirection C (fun w => frameTensor (E w) (T (F w))) i z =
      frameTensor (E z) (∑ r, E z r i • tensorCovariantDirection D T r (F z)) := by
  have hcomp (a : Fin n → Fin 4) :
      DifferentiableAt ℝ (fun w => T (F w) a) z := (hT a).comp z hF
  have hder := tensorPartial_frameTensor E (fun w => T (F w)) z hE hcomp i
  have hchain := tensorPartial_comp F T z hF hT i
  rw [← hJ] at hchain
  have hvar := frameVariation_connection (E z) (matrixPartial E i z)
    (∑ r, E z r i • D r (F z)) (C i z) hC (T (F z))
  have hslot : tensorSlotAction (∑ r, E z r i • D r (F z)) (T (F z)) =
      ∑ r, E z r i • tensorSlotAction (D r (F z)) (T (F z)) := by
    simp only [tensorSlotAction_sum_matrix, tensorSlotAction_smul_matrix]
  funext a
  have hv := congrFun hvar a
  change tensorPartial (fun w => frameTensor (E w) (T (F w))) i z a -
    tensorSlotAction (C i z) (frameTensor (E z) (T (F z))) a = _
  rw [hder, hchain]
  rw [hslot] at hv
  simp only [Pi.add_apply] at hv ⊢
  rw [frameTensor_weighted_sum] at hv
  rw [frameTensor_weighted_sum, frameTensor_weighted_sum]
  simp only [tensorCovariantDirection, frameTensor_sub, mul_sub, Finset.sum_sub_distrib]
  linarith only [hv]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

omit [IsManifold I4 ∞ M] in
theorem chart_overlap_eventually (c d : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    ∀ᶠ w in 𝓝 z, w ∈ (chartAt FourSpace c).target ∧
      (chartAt FourSpace c).symm w ∈ (chartAt FourSpace d).source := by
  have h₁ : ∀ᶠ w in 𝓝 z, w ∈ (chartAt FourSpace c).target :=
    (chartAt FourSpace c).open_target.mem_nhds hz
  have h₂ : ∀ᶠ w in 𝓝 z,
      (chartAt FourSpace c).symm w ∈ (chartAt FourSpace d).source :=
    ((chartAt FourSpace c).continuousAt_symm hz).eventually
      ((chartAt FourSpace d).open_source.mem_nhds hx)
  exact h₁.and h₂

/-- Naturality of the coordinate Levi-Civita derivative. The tensor equality
is local; no choice of a global frame is involved. -/
theorem covariantDerivative_chart_transition (g : SmoothMetric M) (c d : M)
    {n : ℕ} (S T : FourSpace → CovariantCoordinates n) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) (chartTransition c d z))
    (hS : S =ᶠ[𝓝 z] fun w => frameTensor (chartTransitionMatrix c d w)
      (T (chartTransition c d w))) :
    covariantDerivative g c S z = frameTensor (chartTransitionMatrix c d z)
      (covariantDerivative g d T (chartTransition c d z)) := by
  rw [covariantDerivative_congr g c hS]
  funext a
  obtain ⟨i, v, rfl⟩ := Fin.exists_cons a
  rw [covariantDerivative_direction]
  rw [covariantDirection_pullback (chartTransition c d) (chartTransitionMatrix c d)
    (connectionMatrix g c) (connectionMatrix g d) T z
    ((chartTransition_contDiffAt c d z hz hx).differentiableAt (by simp))
    (fun a b => (chartTransitionMatrix_contDiffAt c d z hz hx a b).differentiableAt
      (by simp)) hT rfl i (chart_connection_intertwining g c d z hz hx i)]
  rw [frameTensor_cons, frameTensor_weighted_sum]
  apply Finset.sum_congr rfl
  intro r _
  congr 1

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual local orthonormal frames obtained from smooth coordinate vectors
by the explicit four-column normalizer. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle
open scoped BigOperators Manifold ContDiff Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

abbrev ChartTarget (c : M) := {z : FourSpace // z ∈ (chartAt FourSpace c).target}

def chartGramMatrix (g : SmoothMetric M) (c : M) (S : Mat4) (z : FourSpace) : Mat4 :=
  gramNormalizer (metricInChart g c z) * S

theorem chartGramMatrix_normalizes (g : SmoothMetric M) (c : M)
    (S : Mat4) (hS : Sᵀ * S = 1) (z : ChartTarget c) :
    (chartGramMatrix g c S z)ᵀ * metricInChart g c z * chartGramMatrix g c S z = 1 := by
  have hn := gramNormalizer_normalizes _ (metricInChart_posDef g c z z.property)
  calc
    _ = Sᵀ * ((gramNormalizer (metricInChart g c z))ᵀ * metricInChart g c z *
        gramNormalizer (metricInChart g c z)) * S := by
      simp only [chartGramMatrix, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hn, Matrix.mul_one, hS]

def chartGramFrame (g : SmoothMetric M) (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (z : ChartTarget c) : OrthonormalFrame g ((chartAt FourSpace c).symm z) where
  matrix := chartInverseMatrix c z * chartGramMatrix g c S z
  orthonormal := by
    have hm := metricInChart_eq_center_congruence g c z
    rw [← Matrix.mul_assoc] at hm
    calc
      _ = (chartGramMatrix g c S z)ᵀ *
          ((chartInverseMatrix c z)ᵀ * chartMetric g ((chartAt FourSpace c).symm z) *
            chartInverseMatrix c z) * chartGramMatrix g c S z := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by
        rw [← hm]
        exact chartGramMatrix_normalizes g c S hS z

def chartGramSection (g : SmoothMetric M) (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (z : ChartTarget c) : FrameBundle g :=
  ⟨(chartAt FourSpace c).symm z, chartGramFrame g c S hS z⟩

theorem chartGramMatrix_contDiffAt (g : SmoothMetric M) (c : M) (S : Mat4)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => chartGramMatrix g c S w i j) z := by
  change ContDiffAt ℝ ∞ (fun w => ∑ k, gramNormalizer (metricInChart g c w) i k * S k j) z
  apply ContDiffAt.sum
  intro k _
  exact (gramNormalizer_contDiffAt (metricInChart_contDiffAt g c z hz)
    (metricInChart_posDef g c z hz) i k).mul contDiffAt_const

theorem chart_inverse_moving_vector_smooth (c : M) (v : FourSpace → FourSpace)
    (hv : ContDiffOn ℝ ∞ v (chartAt FourSpace c).target) :
    ContMDiffOn I4 I4.tangent ∞
      (fun z => (⟨(chartAt FourSpace c).symm z,
        mfderiv I4 I4 (chartAt FourSpace c).symm z (v z)⟩ : TangentBundle I4 M))
      (chartAt FourSpace c).target := by
  have hphi : ContMDiffOn I4 I4 ∞ (chartAt FourSpace c).symm
      (chartAt FourSpace c).target := contMDiffOn_chart_symm
  have ht := hphi.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    (chartAt FourSpace c).open_target.uniqueMDiffOn
  have hv' : ContMDiffOn I4 I4.tangent ∞
      (fun z => (⟨z, v z⟩ : TangentBundle I4 FourSpace))
      (chartAt FourSpace c).target :=
    contMDiffOn_vectorSpace_iff_contDiffOn.mpr hv
  have hcomp := ht.comp hv' (fun z hz => hz)
  apply hcomp.congr
  intro z hz
  exact congrArg (fun L : TangentSpace I4 z →L[ℝ]
      TangentSpace I4 ((chartAt FourSpace c).symm z) =>
        (⟨(chartAt FourSpace c).symm z, L (v z)⟩ : TangentBundle I4 M))
    (mfderivWithin_of_isOpen (chartAt FourSpace c).open_target hz).symm

omit [IsManifold I4 ∞ M] in
private theorem chartInverseMatrix_apply (c : M) (z : FourSpace) (u : CoordinateColumn) :
    WithLp.toLp 2 (chartInverseMatrix c z *ᵥ u) =
      mfderiv I4 I4 (chartAt FourSpace c).symm z (WithLp.toLp 2 u) := by
  let L : FourSpace →L[ℝ] FourSpace := mfderiv I4 I4 (chartAt FourSpace c).symm z
  change WithLp.toLp 2 (chartInverseMatrix c z *ᵥ u) = L (WithLp.toLp 2 u)
  change WithLp.toLp 2 (fun i => ∑ j, L (coordinateVector j) i * u j) = _
  rw [← sum_coordinateVector u, map_sum]
  ext i
  simp only [map_smul, WithLp.ofLp_sum, PiLp.smul_apply, smul_eq_mul, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem chartGramFrame_vector (g : SmoothMetric M) (c : M) (S : Mat4)
    (hS : Sᵀ * S = 1) (z : ChartTarget c) (i : Fin 4) :
    (chartGramFrame g c S hS z).vector i =
      mfderiv I4 I4 (chartAt FourSpace c).symm z
        (WithLp.toLp 2 (fun j => chartGramMatrix g c S z j i)) := by
  change WithLp.toLp 2 (fun j => (chartInverseMatrix c z * chartGramMatrix g c S z) j i) = _
  exact chartInverseMatrix_apply c z (fun j => chartGramMatrix g c S z j i)

theorem continuous_chartGramSection (g : SmoothMetric M) (c : M) (S : Mat4)
    (hS : Sᵀ * S = 1) : Continuous (chartGramSection g c S hS) := by
  have hv (i : Fin 4) : ContDiffOn ℝ ∞
      (fun z => WithLp.toLp 2 (fun j => chartGramMatrix g c S z j i))
      (chartAt FourSpace c).target := by
    apply (contDiffOn_piLp (p := (2 : ENNReal))).mpr
    intro j z hz
    exact (chartGramMatrix_contDiffAt g c S z hz j i).contDiffWithinAt
  have ht (i : Fin 4) := (chart_inverse_moving_vector_smooth c _ (hv i)).continuousOn
  apply continuous_induced_rng.mpr
  have hbase : Continuous (fun z : ChartTarget c => (chartAt FourSpace c).symm z) :=
    (chartAt FourSpace c).continuousOn_symm.domRestrict
  have hvec (i : Fin 4) : Continuous (fun z : ChartTarget c =>
      (⟨(chartAt FourSpace c).symm z, (chartGramFrame g c S hS z).vector i⟩ :
        TangentBundle I4 M)) := by
    apply (ht i).domRestrict.congr
    intro z
    exact congrArg (fun v : TangentSpace I4 ((chartAt FourSpace c).symm z) =>
      (⟨(chartAt FourSpace c).symm z, v⟩ : TangentBundle I4 M))
      (chartGramFrame_vector g c S hS z i).symm
  exact hbase.prodMk (continuous_pi hvec)

/-- The framed coordinate curvature, expressed entirely in one fixed chart. -/
def chartGramBlock (g : SmoothMetric M) (c : M) (S : Mat4)
    (Q : Fin 3 → Mat4) (z : FourSpace) : Mat3 :=
  blockCoordinates (frameTensor (chartGramMatrix g c S z)
    (curvatureCoordinates g c z)) Q - 1


theorem chartTransitionMatrix_to_center (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    chartTransitionMatrix c ((chartAt FourSpace c).symm z) z = chartInverseMatrix c z := by
  let x := (chartAt FourSpace c).symm z
  let D : FourSpace →L[ℝ] FourSpace := mfderiv I4 I4 (chartAt FourSpace x) x
  have hid : D = ContinuousLinearMap.id ℝ FourSpace := by
    ext v i
    have h := congrArg (fun K : TangentSpace I4 x →L[ℝ]
        TangentSpace I4 (extChartAt I4 x x) => K (show TangentSpace I4 x from v))
      (mfderiv_extChartAt_self (I := I4) (x := x))
    have hv : D v = v := by
      simp only [I4, extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp] at h
      change D v = v at h
      exact h
    exact congrArg (fun w : FourSpace => w i) hv
  let L : FourSpace →L[ℝ] FourSpace := mfderiv I4 I4 (chartAt FourSpace c).symm z
  have hf : fderiv ℝ (chartTransition c x) z = D.comp L :=
    chartTransition_fderiv c x z hz (mem_chart_source FourSpace x)
  rw [hid, ContinuousLinearMap.id_comp] at hf
  ext i j
  exact congrArg (fun K : FourSpace →L[ℝ] FourSpace => K (coordinateVector j) i) hf

theorem chartGramBlock_eq_frame (g : SmoothMetric M) (c : M) (S : Mat4)
    (hS : Sᵀ * S = 1) (Q : Fin 3 → Mat4) (z : ChartTarget c) :
    chartGramBlock g c S Q z =
      curvatureBlock (curvaturePairing g ((chartAt FourSpace c).symm z)
        (chartGramFrame g c S hS z)) Q - 1 := by
  have hc := curvatureCoordinates_transition g c ((chartAt FourSpace c).symm z) z z.property
    (mem_chart_source FourSpace ((chartAt FourSpace c).symm z))
  rw [chartTransitionMatrix_to_center c z z.property] at hc
  unfold chartGramBlock
  rw [hc, ← frameTensor_mul]
  congr 1
  ext i j
  simp only [blockCoordinates, curvatureBlock, curvaturePairing]
  apply congrArg ((1 / 8 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [show frameTensor (chartInverseMatrix c z * chartGramMatrix g c S z)
      (curvatureCoordinates g ((chartAt FourSpace c).symm z)
        (chartTransition c ((chartAt FourSpace c).symm z) z))
        ![a.1, a.2, b.2, b.1] =
      frameCurvature g ((chartAt FourSpace c).symm z)
        (chartGramFrame g c S hS z) a.1 a.2 b.2 b.1 from
    frameTensor_curvatureCoordinates (chartGramFrame g c S hS z) a.1 a.2 b.2 b.1]

private theorem frameTensor_contDiffAt {E : FourSpace → Mat4}
    {T : FourSpace → CovariantCoordinates 4} {z : FourSpace}
    (hE : ∀ i j, ContDiffAt ℝ ∞ (fun w => E w i j) z)
    (hT : ∀ a, ContDiffAt ℝ ∞ (fun w => T w a) z) (a : Fin 4 → Fin 4) :
    ContDiffAt ℝ ∞ (fun w => frameTensor (E w) (T w) a) z := by
  unfold frameTensor
  apply ContDiffAt.sum
  intro b _
  exact (contDiffAt_prod fun k _ => hE (b k) (a k)).mul (hT b)

private theorem blockCoordinates_contDiffAt {T : FourSpace → CovariantCoordinates 4}
    {z : FourSpace} (hT : ∀ a, ContDiffAt ℝ ∞ (fun w => T w a) z)
    (Q : Fin 3 → Mat4) (i j : Fin 3) :
    ContDiffAt ℝ ∞ (fun w => blockCoordinates (T w) Q i j) z := by
  change ContDiffAt ℝ ∞ (fun w => (1 / 8 : ℝ) * ∑ a : Fin 4 × Fin 4,
    ∑ b : Fin 4 × Fin 4, T w ![a.1, a.2, b.2, b.1] * Q i a.1 a.2 * Q j b.1 b.2) z
  apply ContDiffAt.mul contDiffAt_const
  apply ContDiffAt.sum
  intro a _
  apply ContDiffAt.sum
  intro b _
  exact ((hT _).mul contDiffAt_const).mul contDiffAt_const

theorem chartGramBlock_contDiffAt (g : SmoothMetric M) (c : M) (S : Mat4)
    (Q : Fin 3 → Mat4) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (i j : Fin 3) : ContDiffAt ℝ ∞ (fun w => chartGramBlock g c S Q w i j) z := by
  let E : FourSpace → Mat4 := chartGramMatrix g c S
  let T : FourSpace → CovariantCoordinates 4 := curvatureCoordinates g c
  have hE : ∀ a b, ContDiffAt ℝ ∞ (fun w => E w a b) z :=
    chartGramMatrix_contDiffAt g c S z hz
  have hT : ∀ a, ContDiffAt ℝ ∞ (fun w => T w a) z :=
    curvatureCoordinates_contDiffAt g c z hz (metricInChart_posDef g c z hz).det_pos.ne'
  have hF := frameTensor_contDiffAt hE hT
  have hB := blockCoordinates_contDiffAt hF Q i j
  exact hB.sub contDiffAt_const

theorem chartGramBlock_squareNorm_contDiffAt (g : SmoothMetric M) (c : M) (S : Mat4)
    (Q : Fin 3 → Mat4) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ ∞ (fun w => normalizedBlockNorm (chartGramBlock g c S Q w) ^ 2) z := by
  simp only [normalizedBlockNorm_sq]
  apply ContDiffAt.div_const
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (chartGramBlock_contDiffAt g c S Q z hz i j).pow 2


def localGramSection (g : SmoothMetric M) (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (x : M) : FrameBundle g :=
  open Classical in
  if hx : x ∈ (chartAt FourSpace c).source then
    chartGramSection g c S hS ⟨chartAt FourSpace c x, (chartAt FourSpace c).map_source hx⟩
  else frameAt g x

theorem localGramSection_base (g : SmoothMetric M) (c : M) (S : Mat4)
    (hS : Sᵀ * S = 1) (x : M) : (localGramSection g c S hS x).base = x := by
  classical
  by_cases hx : x ∈ (chartAt FourSpace c).source
  · simp only [localGramSection, dite_eq_left hx, chartGramSection]
    exact (chartAt FourSpace c).left_inv hx
  · simp only [localGramSection, dite_eq_right hx, frameAt]

theorem continuousAt_localGramSection (g : SmoothMetric M) (c : M) (S : Mat4)
    (hS : Sᵀ * S = 1) : ContinuousAt (localGramSection g c S hS) c := by
  classical
  let F : {x : M // x ∈ (chartAt FourSpace c).source} → ChartTarget c := fun x =>
    ⟨chartAt FourSpace c x, (chartAt FourSpace c).map_source x.property⟩
  have hF : Continuous F :=
    ((chartAt FourSpace c).continuousOn.domRestrict).subtype_mk _
  have hcont : ContinuousOn (localGramSection g c S hS) (chartAt FourSpace c).source := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply ((continuous_chartGramSection g c S hS).comp hF).congr
    intro x
    change chartGramSection g c S hS ⟨chartAt FourSpace c x,
      (chartAt FourSpace c).map_source x.property⟩ = localGramSection g c S hS x
    simp only [localGramSection, dite_eq_left x.property]
  exact hcont.continuousAt ((chartAt FourSpace c).open_source.mem_nhds
    (mem_chart_source FourSpace c))

private theorem frame_eq_of_matrix_eq {g : SmoothMetric M} {x : M}
    (e f : OrthonormalFrame g x)
    (h : e.matrix = f.matrix) : e = f := by
  cases e
  cases f
  cases h
  rfl

/-- A constant orthogonal change makes the local smooth frame positive at
its center; openness of the chosen component then makes it positive nearby. -/
theorem exists_positive_localGramSection (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) : ∃ S : Mat4, ∃ hS : Sᵀ * S = 1,
      ∀ᶠ x in 𝓝 c, localGramSection g c S hS x ∈ o.positive := by
  classical
  let z : ChartTarget c := ⟨chartAt FourSpace c c,
    (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)⟩
  let e := chartGramFrame g c 1 (by simp) z
  let f := o.frame ((chartAt FourSpace c).symm z)
  let S := e.changeMatrix f
  have hS : Sᵀ * S = 1 := e.changeMatrix_orthogonal f
  have he : chartGramFrame g c S hS z = f := by
    apply frame_eq_of_matrix_eq
    have hm := e.mul_changeMatrix f
    simpa only [e, S, chartGramFrame, chartGramMatrix, Matrix.mul_one,
      Matrix.mul_assoc] using hm
  have hpos : localGramSection g c S hS c ∈ o.positive := by
    change (if hx : c ∈ (chartAt FourSpace c).source then _ else _) ∈ o.positive
    rw [dite_eq_left (mem_chart_source FourSpace c)]
    change (⟨(chartAt FourSpace c).symm z, chartGramFrame g c S hS z⟩ : FrameBundle g) ∈ o.positive
    rw [he]
    exact o.frame_positive _
  refine ⟨S, hS, ?_⟩
  exact (continuousAt_localGramSection g c S hS).preimage_mem_nhds
    (o.clopen.isOpen.mem_nhds hpos)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The finite-dimensional even Hodge–Dirac symbol in dimension four. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators

noncomputable section

abbrev HodgeEvenFiber := ℝ × TwoFormFour × ℝ
abbrev HodgeOddFiber := FourSpace × FourSpace

def hodgeDiracEvenSymbol (ξ : FourSpace) : HodgeEvenFiber →ₗ[ℝ] HodgeOddFiber :=
  let f : HodgeEvenFiber →ₗ[ℝ] ℝ := LinearMap.fst ℝ _ _
  let a : HodgeEvenFiber →ₗ[ℝ] TwoFormFour :=
    (LinearMap.fst ℝ _ _).comp (LinearMap.snd ℝ _ _)
  let b : HodgeEvenFiber →ₗ[ℝ] ℝ :=
    (LinearMap.snd ℝ _ _).comp (LinearMap.snd ℝ _ _)
  let m : ℝ →ₗ[ℝ] FourSpace := LinearMap.toSpanSingleton ℝ FourSpace ξ
  ((m.comp f) + ((twoFormCodifferentialSymbolLinear ξ).comp a)).prod
    (((twoFormCodifferentialSymbolLinear ξ).comp (twoFormHodge.toLinearMap.comp a)) - (m.comp b))

theorem hodgeDiracEvenSymbol_apply (ξ : FourSpace) (f b : ℝ) (a : TwoFormFour) :
    hodgeDiracEvenSymbol ξ (f, a, b) =
      (f • ξ + twoFormCodifferentialSymbol ξ a,
        twoFormCodifferentialSymbol ξ (twoFormHodge a) - b • ξ) := rfl

theorem hodgeDiracEvenSymbol_norm_sq (ξ : FourSpace) (f b : ℝ) (a : TwoFormFour) :
    ‖(hodgeDiracEvenSymbol ξ (f, a, b)).1‖ ^ 2 +
      ‖(hodgeDiracEvenSymbol ξ (f, a, b)).2‖ ^ 2 =
      ‖ξ‖ ^ 2 * (f ^ 2 + ‖a‖ ^ 2 + b ^ 2) := by
  rw [hodgeDiracEvenSymbol_apply]
  simp only [EuclideanSpace.norm_sq_eq]
  simp [twoFormCodifferentialSymbol, twoFormHodge, twoFormHodgeLinear,
    Fin.sum_univ_succ, Real.norm_eq_abs]
  ring

theorem hodgeDiracEvenSymbol_eq_zero (ξ : FourSpace) (hξ : ξ ≠ 0)
    (z : HodgeEvenFiber) (hz : hodgeDiracEvenSymbol ξ z = 0) : z = 0 := by
  obtain ⟨f, a, b⟩ := z
  have hn := hodgeDiracEvenSymbol_norm_sq ξ f b a
  rw [hz] at hn
  simp only [Prod.fst_zero, Prod.snd_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
    zero_add] at hn
  have hsum : f ^ 2 + ‖a‖ ^ 2 + b ^ 2 = 0 :=
    (mul_eq_zero.mp hn.symm).resolve_left (pow_ne_zero 2 (norm_ne_zero_iff.mpr hξ))
  have hf : f = 0 := by nlinarith only [hsum, sq_nonneg f, sq_nonneg ‖a‖, sq_nonneg b]
  have ha : a = 0 := by
    apply norm_eq_zero.mp
    nlinarith only [hsum, sq_nonneg f, sq_nonneg b, norm_nonneg a]
  have hb : b = 0 := by nlinarith only [hsum, sq_nonneg f, sq_nonneg ‖a‖, sq_nonneg b]
  simp [hf, ha, hb]

theorem hodgeDiracEvenSymbol_injective (ξ : FourSpace) (hξ : ξ ≠ 0) :
    Function.Injective (hodgeDiracEvenSymbol ξ) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply hodgeDiracEvenSymbol_eq_zero ξ hξ
  rw [map_sub, huv, sub_self]

theorem hodgeDiracEvenSymbol_bijective (ξ : FourSpace) (hξ : ξ ≠ 0) :
    Function.Bijective (hodgeDiracEvenSymbol ξ) := by
  have hd : Module.finrank ℝ HodgeEvenFiber = Module.finrank ℝ HodgeOddFiber := by
    simp [HodgeEvenFiber, HodgeOddFiber, TwoFormFour, FourSpace, Module.finrank_prod]
  exact ⟨hodgeDiracEvenSymbol_injective ξ hξ,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp
      (hodgeDiracEvenSymbol_injective ξ hξ)⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual changes of orthonormal frame on the six two-form coefficients. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix

noncomputable section

def twoFormExtract (A : Mat4) : TwoFormFour :=
  WithLp.toLp 2 ![A 0 1, A 0 2, A 0 3, A 1 2, A 1 3, A 2 3]

theorem twoFormExtract_matrix (a : TwoFormFour) : twoFormExtract (twoFormMatrix a) = a := by
  ext i
  fin_cases i <;> rfl

theorem twoFormMatrix_extract (A : Mat4) (hA : Aᵀ = -A) :
    twoFormMatrix (twoFormExtract A) = A := by
  have hs (i j : Fin 4) : A j i = -A i j := congrFun (congrFun hA i) j
  have hd (i : Fin 4) : A i i = 0 := by linarith [hs i i]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoFormMatrix, twoFormExtract]
  all_goals first | exact (hd _).symm | exact (hs _ _).symm

def twoFormFrameAction (P : Mat4) (a : TwoFormFour) : TwoFormFour :=
  twoFormExtract (Pᵀ * twoFormMatrix a * P)

theorem twoFormMatrix_frameAction (P : Mat4) (a : TwoFormFour) :
    twoFormMatrix (twoFormFrameAction P a) = Pᵀ * twoFormMatrix a * P := by
  apply twoFormMatrix_extract
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, twoFormMatrix_skew,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem twoFormFrameAction_one (a : TwoFormFour) : twoFormFrameAction 1 a = a := by
  simp only [twoFormFrameAction, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one,
    twoFormExtract_matrix]

theorem twoFormFrameAction_comp (P Q : Mat4) (a : TwoFormFour) :
    twoFormFrameAction Q (twoFormFrameAction P a) = twoFormFrameAction (P * Q) a := by
  apply twoFormMatrix_injective
  simp only [twoFormMatrix_frameAction, Matrix.transpose_mul, Matrix.mul_assoc]

theorem twoFormMatrix_add (a b : TwoFormFour) :
    twoFormMatrix (a + b) = twoFormMatrix a + twoFormMatrix b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoFormMatrix, add_comm]

theorem twoFormMatrix_smul (r : ℝ) (a : TwoFormFour) :
    twoFormMatrix (r • a) = r • twoFormMatrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoFormMatrix]

def twoFormFrameActionLinear (P : Mat4) : TwoFormFour →ₗ[ℝ] TwoFormFour where
  toFun := twoFormFrameAction P
  map_add' a b := by
    apply twoFormMatrix_injective
    simp only [twoFormMatrix_frameAction, twoFormMatrix_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' r a := by
    apply twoFormMatrix_injective
    simp only [twoFormMatrix_frameAction, twoFormMatrix_smul, mul_smul_comm, smul_mul_assoc,
      RingHom.id_apply]

theorem twoFormFrameAction_hodge (P : Mat4) (hP : Pᵀ * P = 1) (hdet : P.det = 1)
    (a : TwoFormFour) :
    twoFormFrameAction P (twoFormHodge a) = twoFormHodge (twoFormFrameAction P a) := by
  apply twoFormMatrix_injective
  rw [twoFormMatrix_frameAction, twoFormMatrix_hodge, twoFormMatrix_hodge,
    twoFormMatrix_frameAction]
  have hPt : Pᵀᵀ * Pᵀ = 1 := by
    rw [Matrix.transpose_transpose]
    exact mul_eq_one_comm.mp hP
  simpa only [Matrix.transpose_transpose, Matrix.det_transpose] using
    (hodgeStarFour_oriented_frame_change Pᵀ hPt (by simpa using hdet) a).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Weighted variance of each actual Weyl norm and of the square-root
polynomial H. The final H bound combines the proved scalar variance and
weak Weyl norm equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped Manifold ContDiff Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]

theorem MetricGreenData.plusWeightedNormVariance
    (d : MetricGreenData g μ) (o : OppositeWeylData d) {orientation : FrameOrientation g}
    (s : ScalarVarianceInputs d orientation) (_hparallel : ParallelReflection d)
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    (∫ e, (normalizedBlockNorm (plusWeyl g e.base e.frame)) ^ 2 ∂μ) - (∫ e, normalizedBlockNorm (plusWeyl g e.base e.frame) ∂μ) ^ 2 ≤
      ∫ e, ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2 / scalarVarianceWeight g e ∂μ := by
  apply Variance.norm_variance_of_regularized
    (continuous_normalizedBlockNorm.comp d.continuousWeyl).aemeasurable
    (scalarVarianceWeight_continuous o).aemeasurable d.radialVector_measurable
    (Filter.Eventually.of_forall (fun e => ⟨normalizedBlockNorm_nonneg _, by
      change normalizedBlockNorm (plusWeyl g e.base e.frame) ≤ 2
      linarith [hpinch e, normalizedBlockNorm_nonneg (minusWeyl g e.base e.frame)]⟩))
    (Filter.Eventually.of_forall scalarVarianceWeight_ge_one)
    (Filter.Eventually.of_forall (fun e => blockRadialGradient_zero_of_norm_zero _ _))
    d.radialEnergy_integrable
    normRegularizationParameter normRegularizationParameter_mem normRegularizationParameter_tendsto
  intro n
  exact regularized_plus_variance o orientation s.norms s.orientationFlow s.supported
    s.calculus s.poisson s.positive s.decomposition (normRegularizationParameter_mem n).1

theorem MetricGreenData.plusWeightedHVariance
    (d : MetricGreenData g μ) (o : OppositeWeylData d) {orientation : FrameOrientation g}
    (s : ScalarVarianceInputs d orientation) (_hparallel : ParallelReflection d)
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    (∫ e, MomentObstruction.H (normalizedBlockNorm (plusWeyl g e.base e.frame)) ^ 2 ∂μ) -
      (∫ e, MomentObstruction.H (normalizedBlockNorm (plusWeyl g e.base e.frame)) ∂μ) ^ 2 ≤
      ∫ e, Variance.hLimitEnergy (normalizedBlockNorm (plusWeyl g e.base e.frame)) (‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2)
        (scalarVarianceWeight g e) ∂μ := by
  apply Variance.H_variance_of_regularized
    (continuous_normalizedBlockNorm.comp d.continuousWeyl).aemeasurable
    (d.radialVector_measurable.norm.pow 2).aemeasurable
    (scalarVarianceWeight_continuous o).aemeasurable
    (Filter.Eventually.of_forall (fun e => ⟨normalizedBlockNorm_nonneg _, by
      change normalizedBlockNorm (plusWeyl g e.base e.frame) ≤ 2
      linarith [hpinch e, normalizedBlockNorm_nonneg (minusWeyl g e.base e.frame)]⟩))
    (Filter.Eventually.of_forall (fun e => sq_nonneg _))
    (Filter.Eventually.of_forall scalarVarianceWeight_ge_one)
    d.radialEnergyQuotient_integrable
    normRegularizationParameter normRegularizationParameter_mem normRegularizationParameter_tendsto
  intro n
  exact regularized_H_plus_variance o orientation s.norms s.orientationFlow s.supported
    s.calculus s.poisson s.positive s.decomposition (normRegularizationParameter_mem n).1

theorem MetricGreenData.minusWeightedNormVariance
    (d : MetricGreenData g μ) (o : OppositeWeylData d) {orientation : FrameOrientation g}
    (s : ScalarVarianceInputs d orientation) (hparallel : ParallelReflection d)
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    (∫ e, (normalizedBlockNorm (minusWeyl g e.base e.frame)) ^ 2 ∂μ) - (∫ e, normalizedBlockNorm (minusWeyl g e.base e.frame) ∂μ) ^ 2 ≤
      ∫ e, ‖blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)‖ ^ 2 / scalarVarianceWeight g e ∂μ := by
  apply Variance.norm_variance_of_regularized
    (continuous_normalizedBlockNorm.comp o.continuousWeyl).aemeasurable
    (scalarVarianceWeight_continuous o).aemeasurable (d.oppositeRadialVector_measurable o hparallel)
    (Filter.Eventually.of_forall (fun e => ⟨normalizedBlockNorm_nonneg _, by
      change normalizedBlockNorm (minusWeyl g e.base e.frame) ≤ 2
      linarith [hpinch e, normalizedBlockNorm_nonneg (plusWeyl g e.base e.frame)]⟩))
    (Filter.Eventually.of_forall scalarVarianceWeight_ge_one)
    (Filter.Eventually.of_forall (fun e => blockRadialGradient_zero_of_norm_zero _ _))
    (d.oppositeRadialEnergy_integrable o hparallel)
    normRegularizationParameter normRegularizationParameter_mem normRegularizationParameter_tendsto
  intro n
  exact regularized_minus_variance o orientation s.norms s.orientationFlow s.supported
    s.calculus s.poisson s.positive s.decomposition (normRegularizationParameter_mem n).1

theorem MetricGreenData.minusWeightedHVariance
    (d : MetricGreenData g μ) (o : OppositeWeylData d) {orientation : FrameOrientation g}
    (s : ScalarVarianceInputs d orientation) (hparallel : ParallelReflection d)
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    (∫ e, MomentObstruction.H (normalizedBlockNorm (minusWeyl g e.base e.frame)) ^ 2 ∂μ) -
      (∫ e, MomentObstruction.H (normalizedBlockNorm (minusWeyl g e.base e.frame)) ∂μ) ^ 2 ≤
      ∫ e, Variance.hLimitEnergy (normalizedBlockNorm (minusWeyl g e.base e.frame)) (‖blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)‖ ^ 2)
        (scalarVarianceWeight g e) ∂μ := by
  apply Variance.H_variance_of_regularized
    (continuous_normalizedBlockNorm.comp o.continuousWeyl).aemeasurable
    ((d.oppositeRadialVector_measurable o hparallel).norm.pow 2).aemeasurable
    (scalarVarianceWeight_continuous o).aemeasurable
    (Filter.Eventually.of_forall (fun e => ⟨normalizedBlockNorm_nonneg _, by
      change normalizedBlockNorm (minusWeyl g e.base e.frame) ≤ 2
      linarith [hpinch e, normalizedBlockNorm_nonneg (plusWeyl g e.base e.frame)]⟩))
    (Filter.Eventually.of_forall (fun e => sq_nonneg _))
    (Filter.Eventually.of_forall scalarVarianceWeight_ge_one)
    (d.oppositeRadialEnergyQuotient_integrable hparallel)
    normRegularizationParameter normRegularizationParameter_mem normRegularizationParameter_tendsto
  intro n
  exact regularized_H_minus_variance o orientation s.norms s.orientationFlow s.supported
    s.calculus s.poisson s.positive s.decomposition (normRegularizationParameter_mem n).1

end
end PositiveEinsteinFour.Geometry
end

end OAI
