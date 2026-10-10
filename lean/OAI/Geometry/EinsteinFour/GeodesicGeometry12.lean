import OAI.Geometry.EinsteinFour.CurvatureTensors11
import OAI.Geometry.EinsteinFour.FiniteExceptionalMeanValue
import OAI.Geometry.EinsteinFour.FlatJacobiLimit
import OAI.Geometry.EinsteinFour.GeodesicGeometry04
import OAI.Geometry.EinsteinFour.GeodesicGeometry05
import OAI.Geometry.EinsteinFour.GeodesicGeometry06
import OAI.Geometry.EinsteinFour.GeodesicGeometry11
import OAI.Geometry.EinsteinFour.HodgeTheory08
import OAI.Geometry.EinsteinFour.HodgeTheory09
import OAI.Geometry.EinsteinFour.JacobiKernelBound
import OAI.Geometry.EinsteinFour.JacobiKernelLowerCap
import OAI.Geometry.EinsteinFour.LowerVolumeIntegral
import OAI.Geometry.EinsteinFour.ScalarGreenLimit
import OAI.Geometry.EinsteinFour.ScalarRegularity06
import OAI.Geometry.EinsteinFour.ScalarRegularity07
import OAI.Geometry.EinsteinFour.SineLogRemainder
import OAI.Geometry.EinsteinFour.WeylEstimates01
import OAI.Geometry.EinsteinFour.WeylEstimates03
import OAI.Geometry.EinsteinFour.WeylEstimates06
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.IsLocalHomeomorph

namespace OAI


section

/-! Dominated convergence for the actual averaged lower Jacobi comparison. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory Jacobi Filter
open scoped Manifold ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M]

def actualFlatKernelDeterminant (g : SmoothMetric M) (t : ℝ) (N : ℕ)
    (e : FrameBundle g) : ℝ :=
  (1 - curvatureKernel (scaledFlatGreen t N)
    (fun i => actualJacobiCurvature g e (((i.val + 1 : ℕ) : ℝ) * meshStep t N))).det

theorem actualFlatKernelDeterminant_continuous (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (t : ℝ) (N : ℕ) :
    Continuous (actualFlatKernelDeterminant g t N) := by
  have hR (i : Fin N) : Continuous (fun e : FrameBundle g =>
      actualJacobiCurvature g e (((i.val + 1 : ℕ) : ℝ) * meshStep t N)) :=
    actualJacobiCurvature_frame_continuous g o hRic _
  exact (continuous_const.sub (continuous_const.mul
    ((continuous_pi hR).matrix_blockDiagonal))).matrix_det

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] [SecondCountableTopology M] in
theorem actualFlatKernelDeterminant_tendsto (g : SmoothMetric M) (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g) (e : FrameBundle g)
    {t : ℝ} (ht : 0 < t) (htop : t < Real.pi / Real.sqrt 3) :
    Tendsto (fun N => actualFlatKernelDeterminant g t N e) atTop
      (nhds (((actualJacobiSolution g hRic e).J t).det / t ^ 3)) := by
  have hR : ∀ s, ((actualRegularJacobi g hRic e t).R s).PosSemidef ∧
      ((actualRegularJacobi g hRic e t).R s).trace = 3 := by
    intro s
    rw [actualRegularJacobi_R]
    exact ⟨actual_jacobi_posSemidef hpositive _, actualJacobiCurvature_trace g hRic e s⟩
  simpa only [actualFlatKernelDeterminant, actualRegularJacobi_R, actualRegularJacobi_J] using
    (actualRegularJacobi g hRic e t).flat_kernel_determinant_tendsto ht htop hR

theorem actualFlatKernelDeterminant_integral_tendsto (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    {t : ℝ} (ht : 0 < t) (htop : t < Real.pi / Real.sqrt 3) :
    Tendsto (fun N => ∫ e, actualFlatKernelDeterminant g t N e ∂canonicalFrameMeasure g o)
      atTop (nhds (∫ e, ((actualJacobiSolution g hRic e).J t).det / t ^ 3
        ∂canonicalFrameMeasure g o)) := by
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ᵐ e ∂canonicalFrameMeasure g o,
      ‖actualFlatKernelDeterminant g t N e‖ ≤ 1 := by
    filter_upwards [scaledFlatGreen_eventually_below_one ht.le htop] with N hN
    refine Eventually.of_forall fun e => ?_
    have hb := flat_kernel_det_mem_Ioc t
      (fun i : Fin N => actualJacobiCurvature g e (((i.val + 1 : ℕ) : ℝ) * meshStep t N))
      (fun i => ⟨actual_jacobi_posSemidef hpositive _,
        actualJacobiCurvature_trace g hRic e _⟩) hN
    simpa only [actualFlatKernelDeterminant, Real.norm_eq_abs, abs_of_pos hb.1] using hb.2
  exact tendsto_integral_filter_of_dominated_convergence (fun _ : FrameBundle g => (1 : ℝ))
    (Eventually.of_forall fun N => (actualFlatKernelDeterminant_continuous g o hRic t N).aestronglyMeasurable)
    hbound (integrable_const 1)
    (Eventually.of_forall fun e => actualFlatKernelDeterminant_tendsto g hRic hpositive e ht htop)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact classification with only the published half-conformally-flat
model identification left explicit. The Hodge/index, analytic and covering
inputs are all supplied by their actual proofs. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem models_of_actual_normalized_model_input (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g)
    (hmodel : DerdzinskiHitchinInput g o)
    (hEinstein : IsEinstein g) (hpositive : HasPositiveSectionalCurvature g) :
    ∃ a : ℝ, 0 < a ∧ (ScaledIsometricTo g a roundDistance ∨
      ScaledIsometricTo g a fubiniStudyDistance) :=
  hmodel inferInstance inferInstance inferInstance inferInstance hEinstein hpositive
    (actual_one_weyl_block_zero g o hRic hpositive)

theorem models_of_actual_model_inputs (g : SmoothMetric M) (orientation : FrameOrientation g)
    (hmodel : ∀ (h : SmoothMetric M) (o : FrameOrientation h),
      RicciThree h → DerdzinskiHitchinInput h o)
    (hEinstein : IsEinstein g) (hpositive : HasPositiveSectionalCurvature g) :
    ∃ a : ℝ, 0 < a ∧ (ScaledIsometricTo g a roundDistance ∨
      ScaledIsometricTo g a fubiniStudyDistance) := by
  obtain ⟨h, o, c, hc, hRic, hp, hd⟩ := normalized_oriented_metric g orientation
    (positiveRicciInput_of_einstein hEinstein) (petersenScalingInput g) hEinstein hpositive
  obtain ⟨a, ha, hmodels⟩ := models_of_actual_normalized_model_input h o hRic
    (hmodel h o hRic) (einstein_of_ricciThree hRic) hp
  have hscale (x y : M) : scaledEDistance h a x y = scaledEDistance g (a * c) x y := by
    calc
      _ = scaledEDistance h (a * 1) x y := by rw [mul_one]
      _ = ENNReal.ofReal (Real.sqrt a) * scaledEDistance h 1 x y :=
        scaledEDistance_mul h a 1 ha.le x y
      _ = ENNReal.ofReal (Real.sqrt a) * scaledEDistance g c x y := by rw [hd]
      _ = _ := (scaledEDistance_mul g a c ha.le x y).symm
  refine ⟨a * c, mul_pos ha hc, ?_⟩
  rcases hmodels with ⟨f, hf⟩ | ⟨f, hf⟩
  · exact Or.inl ⟨f, fun x y => (hf x y).trans (hscale x y)⟩
  · exact Or.inr ⟨f, fun x y => (hf x y).trans (hscale x y)⟩

end
end PositiveEinsteinFour.Geometry

namespace PositiveEinsteinFour
open EinsteinFour _root_.OAI.PositiveEinsteinFour.Geometry
open scoped Manifold ContDiff
noncomputable section
universe u

/-- The Derdzinski--Hitchin special case applies after establishing
Weyl vanishing. -/
def ModelOrientedInputs (X : ClosedOrientedMetricFour.{u}) : Prop :=
  let : MeasurableSpace X.manifold := borel X.manifold
  let : BorelSpace X.manifold := ⟨rfl⟩
  ∀ (g : SmoothMetric X.manifold) (o : FrameOrientation g),
    RicciThree g → DerdzinskiHitchinInput g o

structure ModelClassificationInputs (_M : Type u) : Prop where
  oriented : ∀ X : ClosedOrientedMetricFour.{u}, ModelOrientedInputs X

variable (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [SecondCountableTopology M]
  [CompactSpace M] [ConnectedSpace M]

theorem classificationOn_of_model_inputs (h : ModelClassificationInputs M) :
    ClassificationOn M := by
  intro g hEinstein hpositive
  apply classified_of_actual_oriented_models g _ hEinstein hpositive
  intro X hE hP
  let : MeasurableSpace X.manifold := borel X.manifold
  let : BorelSpace X.manifold := ⟨rfl⟩
  exact models_of_actual_model_inputs X.metric X.orientation (h.oriented X) hE hP

end
end PositiveEinsteinFour
end


section

/-! Constant-curvature Jacobi fields for the round branch of model
identification. All coefficients are the actual metric curvature. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix Set
open scoped _root_.Topology NNReal Matrix.Norms.L2Operator
noncomputable section

theorem MatrixJacobiSolution.eq_sine_of_curvature_one {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (hR : ∀ t, R t = 1) (t : ℝ) :
    d.J t = Real.sin t • (1 : NormalMatrix) ∧
      d.V t = Real.cos t • (1 : NormalMatrix) := by
  let γ : ℝ → JacobiState := fun s => (d.J s, d.V s)
  let η : ℝ → JacobiState := fun s =>
    (Real.sin s • (1 : NormalMatrix), Real.cos s • (1 : NormalMatrix))
  let a := -(|t| + 1)
  let b := |t| + 1
  have hγ : LinearCurveOn (fun _ => jacobiStateOperator (1 : NormalMatrix)) γ (Ioo a b) := by
    intro s _
    simpa only [γ, hR s, one_mul, jacobiStateOperator_apply] using
      (d.position_derivative s).prodMk (d.velocity_derivative s)
  have hη : LinearCurveOn (fun _ => jacobiStateOperator (1 : NormalMatrix)) η (Ioo a b) := by
    intro s _
    simpa only [η, jacobiStateOperator_apply, one_mul, neg_smul] using
      ((Real.hasDerivAt_sin s).smul_const (1 : NormalMatrix)).prodMk
        ((Real.hasDerivAt_cos s).smul_const (1 : NormalMatrix))
  have hbound (s : ℝ) : ‖jacobiStateOperator (1 : NormalMatrix)‖ ≤
      (‖jacobiStateOperator (1 : NormalMatrix)‖₊ : ℝ) := le_rfl
  have hzero : (0 : ℝ) ∈ Ioo a b :=
    ⟨by dsimp [a]; linarith [abs_nonneg t], by dsimp [b]; positivity⟩
  have hinit : γ 0 = η 0 := by simp [γ, η, d.initial_position, d.initial_velocity]
  have heq := linear_curve_eqOn_interval (fun _ => jacobiStateOperator (1 : NormalMatrix))
    ‖jacobiStateOperator (1 : NormalMatrix)‖₊ hbound hγ hη hzero hinit
  have ht : t ∈ Ioo a b := by
    dsimp [a, b]
    exact abs_lt.mp (lt_add_one |t|)
  exact ⟨congrArg Prod.fst (heq ht), congrArg Prod.snd (heq ht)⟩

end
end PositiveEinsteinFour.Jacobi

namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Jacobi Angular
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.L2Operator
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualJacobiCurvature_eq_one_of_weyl_zero (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (s : ℝ) :
    actualJacobiCurvature g e s = 1 := by
  let f := parallelFrameFlowMap g 0 s e
  have hf : f ∈ o.positive := (canonicalParallelMetricData_orientation o hRic 0 s e).mpr he
  have hP : plusWeyl g f.base f.frame = 0 := by
    apply (normalizedBlockNorm_eq_zero_iff _).mp
    rw [← actual_plusNorm_frame o f hf]
    exact (plusNorm_eq_zero_iff o f.base).mpr (hplus f.base)
  have hM : minusWeyl g f.base f.frame = 0 := by
    apply (normalizedBlockNorm_eq_zero_iff _).mp
    rw [← actual_minusNorm_frame o f hf]
    exact (minusNorm_eq_zero_iff o f.base).mpr (hminus f.base)
  change 1 + normalCurvatureDeviation g f.base f.frame firstDirection = 1
  rw [normalCurvatureDeviation_eq_of_decomposition g f.base f.frame
    (actual_einstein_decomposition f.frame hRic), hP, hM]
  simp [normalDeviation, rotated]

theorem actualJacobi_eq_sine_of_weyl_zero (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) :
    (actualJacobiSolution g hRic e).J t = Real.sin t • (1 : NormalMatrix) ∧
      (actualJacobiSolution g hRic e).V t = Real.cos t • (1 : NormalMatrix) :=
  (actualJacobiSolution g hRic e).eq_sine_of_curvature_one
    (actualJacobiCurvature_eq_one_of_weyl_zero hRic hplus hminus e he) t

theorem actualFirstConjugateTime_eq_pi_of_weyl_zero (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    actualFirstConjugateTime g hRic e = Real.pi := by
  apply le_antisymm (actualFirstConjugateTime_le_pi g hRic e)
  by_contra hnot
  have hlt : actualFirstConjugateTime g hRic e < Real.pi := lt_of_not_ge hnot
  apply actualFirstConjugateTime_singular g hRic e
  rw [(actualJacobi_eq_sine_of_weyl_zero hRic hplus hminus e he _).1]
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero _
    (Real.sin_pos_of_pos_of_lt_pi (actualFirstConjugateTime_pos g hRic e) hlt).ne')

end
end PositiveEinsteinFour.Geometry
end


section

/-! A unit Weyl norm forces parallel Weyl curvature and maximal normalized
determinant. The proof differentiates its actual constant norm twice. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff
noncomputable section

private theorem matrixPairing_swap (A B : Mat) : matrixPairing A B = matrixPairing B A := by
  simp only [matrixPairing, mul_comm]

private theorem hasDerivAt_pairing {A B : ℝ → Mat} {A' B' : Mat} {t : ℝ}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    HasDerivAt (fun s => matrixPairing (A s) (B s))
      (matrixPairing A' (B t) + matrixPairing (A t) B') t := by
  simpa only [inner_matrixVector, add_comm] using
    (hasDerivAt_matrixVector hA).inner ℝ (hasDerivAt_matrixVector hB)

private theorem constant_matrix_norm_pairing {A : ℝ → Mat} {Z : Mat} {t : ℝ}
    (hA : HasDerivAt A Z t) (hnorm : ∀ s, normalizedBlockNorm (A s) = 1) :
    matrixPairing (A t) Z = 0 := by
  have hd := hasDerivAt_pairing hA hA
  have he : (fun s => matrixPairing (A s) (A s)) = fun _ => (6 : ℝ) := by
    funext s
    rw [matrixPairing_self_norm, hnorm s]
    norm_num
  rw [he] at hd
  have hz := hd.unique (hasDerivAt_const t (6 : ℝ))
  rw [matrixPairing_swap Z (A t)] at hz
  linarith

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}
  {μ : Measure (FrameBundle g)}

theorem MetricGreenData.unit_norm_first_pairing (d : MetricGreenData g μ)
    (hflow : OrientationPreservingFlow d o) (hnorm : ∀ x, plusNorm o x = 1)
    (f : FrameBundle g) (hf : f ∈ o.positive) (i : Fin 4) :
    matrixPairing (plusWeyl g f.base f.frame) (plusWeylGradient g f.base f.frame i) = 0 := by
  obtain ⟨f₀,hf₀⟩ := ((d.flow i).map 0).surjective f
  have hp : f₀ ∈ o.positive := (hflow i 0 f₀).mp (hf₀.symm ▸ hf)
  have hn (s : ℝ) : normalizedBlockNorm (plusWeyl g ((d.flow i).map s f₀).base
      ((d.flow i).map s f₀).frame) = 1 := by
    rw [← actual_plusNorm_frame o _ ((hflow i s f₀).mpr hp)]
    exact hnorm _
  have h := constant_matrix_norm_pairing (d.derivativeWeyl i 0 f₀) hn
  change matrixPairing (plusWeyl g ((d.flow i).map 0 f₀).base ((d.flow i).map 0 f₀).frame)
    (plusWeylGradient g ((d.flow i).map 0 f₀).base ((d.flow i).map 0 f₀).frame i) = 0 at h
  rw [hf₀] at h
  exact h

theorem MetricGreenData.unit_norm_second_pairing (d : MetricGreenData g μ)
    (hflow : OrientationPreservingFlow d o) (hnorm : ∀ x, plusNorm o x = 1)
    (e : FrameBundle g) (he : e ∈ o.positive) (i : Fin 4) :
    matrixPairing (plusWeylGradient g e.base e.frame i) (plusWeylGradient g e.base e.frame i) +
      matrixPairing (plusWeyl g e.base e.frame) (plusWeylHessian g e.base e.frame i i) = 0 := by
  obtain ⟨f₀,hf₀⟩ := ((d.flow i).map 0).surjective e
  have hp : f₀ ∈ o.positive := (hflow i 0 f₀).mp (hf₀.symm ▸ he)
  have hd := hasDerivAt_pairing (d.derivativeWeyl i 0 f₀) (d.derivativeGradient i i 0 f₀)
  have hz : (fun s => matrixPairing (plusWeyl g ((d.flow i).map s f₀).base
      ((d.flow i).map s f₀).frame) (plusWeylGradient g ((d.flow i).map s f₀).base
      ((d.flow i).map s f₀).frame i)) = fun _ => (0 : ℝ) := by
    funext s
    exact d.unit_norm_first_pairing hflow hnorm _ ((hflow i s f₀).mpr hp) i
  rw [hz] at hd
  have h := hd.unique (hasDerivAt_const 0 (0 : ℝ))
  change matrixPairing (plusWeylGradient g ((d.flow i).map 0 f₀).base ((d.flow i).map 0 f₀).frame i)
    (plusWeylGradient g ((d.flow i).map 0 f₀).base ((d.flow i).map 0 f₀).frame i) +
    matrixPairing (plusWeyl g ((d.flow i).map 0 f₀).base ((d.flow i).map 0 f₀).frame)
      (plusWeylHessian g ((d.flow i).map 0 f₀).base ((d.flow i).map 0 f₀).frame i i) = 0 at h
  rw [hf₀] at h
  exact h

variable [T3Space M] [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M]

theorem actual_unit_weyl_parallel (hRic : RicciThree g)
    (hnorm : ∀ x, plusNorm o x = 1) (e : FrameBundle g) (he : e ∈ o.positive) :
    (∀ i, plusWeylGradient g e.base e.frame i = 0) ∧
      normalizedDeterminantShape (plusWeyl g e.base e.frame) = 1 := by
  let p := canonicalParallelMetricData g o hRic
  let d := p.toMetricGreenData
  have hflow : OrientationPreservingFlow d o := canonicalParallelMetricData_orientation o hRic
  have hsecond := d.unit_norm_second_pairing hflow hnorm e he
  let A := plusWeyl g e.base e.frame
  let Z := plusWeylGradient g e.base e.frame
  let X := plusWeylHessian g e.base e.frame
  have hlin : (∑ i, matrixPairing A (X i i)) = matrixPairing A (hessianTrace X) := by
    simp only [← inner_matrixVector]
    rw [← inner_sum]
    congr 1
  have hsum : (∑ i, matrixPairing (Z i) (Z i)) + matrixPairing A (weylLaplacian A) = 0 := by
    have h := Finset.sum_eq_zero (s := Finset.univ) (fun i _ => hsecond i)
    rw [Finset.sum_add_distrib] at h
    change (∑ i, matrixPairing (Z i) (Z i)) + (∑ i, matrixPairing A (X i i)) = 0 at h
    rw [hlin, metric_weyl_trace g d.weyl] at h
    exact h
  have hA : normalizedBlockNorm A = 1 := by
    rw [← actual_plusNorm_frame o e he]
    exact hnorm e.base
  have hp := weylLaplacian_pairing A (d.weyl.symmetric e) (d.weyl.traceFree e)
  rw [hA] at hp
  have hs := normalizedDeterminantShape_le_one A (d.weyl.symmetric e) (d.weyl.traceFree e)
  have hnn (i : Fin 4) : 0 ≤ matrixPairing (Z i) (Z i) := by
    rw [matrixPairing_self_norm]
    positivity
  have hnonneg := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hnn i)
  have hzero : (∑ i, matrixPairing (Z i) (Z i)) = 0 := by nlinarith
  constructor
  · intro i
    have hi : matrixPairing (Z i) (Z i) ≤ ∑ j, matrixPairing (Z j) (Z j) :=
      Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
    have hn : normalizedBlockNorm (Z i) = 0 := by
      rw [matrixPairing_self_norm] at hi
      nlinarith [normalizedBlockNorm_nonneg (Z i)]
    exact (normalizedBlockNorm_eq_zero_iff _).mp hn
  · change normalizedDeterminantShape A = 1
    nlinarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! No actual conjugate point occurs below pi/sqrt(3). -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Jacobi Matrix Filter
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem actualJacobi_determinant_lower_cap (g : SmoothMetric M) (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g) (e : FrameBundle g)
    {t : ℝ} (ht : 0 < t) (htop : t < Real.pi / Real.sqrt 3) :
    (Real.sin (Real.sqrt 3 * t) / (Real.sqrt 3 * t)) ^ 3 ≤
      ((actualJacobiSolution g hRic e).J t).det / t ^ 3 := by
  apply le_of_tendsto_of_tendsto ((scalarGreen_determinant_tendsto ht htop).pow 3)
    (actualFlatKernelDeterminant_tendsto g hRic hpositive e ht htop)
  filter_upwards [scaledFlatGreen_eventually_below_one ht.le htop] with N hN
  exact curvatureKernel_determinant_lower_cap _ _ (flatGreenRoot_square t N)
    (flatGreenRoot_transpose t N) _
    (fun i => ⟨actual_jacobi_posSemidef hpositive _, actualJacobiCurvature_trace g hRic e _⟩) hN

theorem actualJacobi_determinant_pos_below_sqrt_three (g : SmoothMetric M)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g) (e : FrameBundle g)
    {t : ℝ} (ht : 0 < t) (htop : t < Real.pi / Real.sqrt 3) :
    0 < ((actualJacobiSolution g hRic e).J t).det := by
  have hθ : 0 < Real.sqrt 3 * t := mul_pos (Real.sqrt_pos.mpr (by norm_num)) ht
  have hθπ : Real.sqrt 3 * t < Real.pi := by
    have h := (lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))).mp htop
    nlinarith
  have hp := pow_pos (div_pos (Real.sin_pos_of_pos_of_lt_pi hθ hθπ) hθ) 3
  have hd := hp.trans_le (actualJacobi_determinant_lower_cap g hRic hpositive e ht htop)
  have h := (lt_div_iff₀ (pow_pos ht 3)).mp hd
  simpa only [zero_mul] using h

theorem actualJacobi_isUnit_below_sqrt_three (g : SmoothMetric M) (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g) (e : FrameBundle g)
    {t : ℝ} (ht : 0 < t) (htop : t < Real.pi / Real.sqrt 3) :
    IsUnit ((actualJacobiSolution g hRic e).J t) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr
    (actualJacobi_determinant_pos_below_sqrt_three g hRic hpositive e ht htop).ne')

theorem actualFirstConjugateTime_lower_sqrt_three (g : SmoothMetric M)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g) (e : FrameBundle g) :
    Real.pi / Real.sqrt 3 ≤ actualFirstConjugateTime g hRic e := by
  by_contra hn
  exact actualFirstConjugateTime_singular g hRic e
    (actualJacobi_isUnit_below_sqrt_three g hRic hpositive e
      (actualFirstConjugateTime_pos g hRic e) (lt_of_not_ge hn))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The continuous lower Jacobi determinant comparison at total Weyl energy three. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory Jacobi Filter
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M]

theorem actual_jacobi_average_lower_normalized (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    (hE : (∫ x, plusNorm o x ^ 2 + minusNorm o x ^ 2 ∂normalizedVolume g) = 3)
    {t : ℝ} (ht : 0 < t) (htop : t < Real.pi / Real.sqrt 3) :
    Real.exp ((5 / 6 : ℝ) * Real.log (Real.sin (Real.sqrt 3 * t) / (Real.sqrt 3 * t)) -
      t ^ 2 / 12) ≤
        ∫ e, ((actualJacobiSolution g hRic e).J t).det / t ^ 3 ∂canonicalFrameMeasure g o := by
  have hθ : 0 < Real.sqrt 3 * t := mul_pos (Real.sqrt_pos.mpr (by norm_num)) ht
  have hθπ : Real.sqrt 3 * t < Real.pi := by
    have h := (lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))).mp htop
    nlinarith
  have hs : 0 < Real.sin (Real.sqrt 3 * t) / (Real.sqrt 3 * t) :=
    div_pos (Real.sin_pos_of_pos_of_lt_pi hθ hθπ) hθ
  have hlog := (scalarGreen_determinant_tendsto ht htop).log hs.ne'
  have htrace := (scaledFlatGreen_trace_tendsto t).div_const 2
  have hleft : Tendsto (fun N : ℕ => Real.exp ((5 / 6 : ℝ) *
      Real.log (1 - (3 : ℝ) • scaledFlatGreen t N).det -
        (scaledFlatGreen t N).trace / 2)) atTop
      (nhds (Real.exp ((5 / 6 : ℝ) *
        Real.log (Real.sin (Real.sqrt 3 * t) / (Real.sqrt 3 * t)) - t ^ 2 / 12))) := by
    have ha := (hlog.const_mul (5 / 6 : ℝ)).sub htrace
    convert (Real.continuous_exp.tendsto _).comp ha using 1
    congr 2
    ring_nf
  apply le_of_tendsto_of_tendsto hleft
    (actualFlatKernelDeterminant_integral_tendsto g o hRic hpositive ht htop)
  filter_upwards [actual_finite_jacobi_determinant_lower g o hRic hpositive hE t ht.le htop]
    with N hN
  exact hN (fun i => ((i.val + 1 : ℕ) : ℝ) * meshStep t N)

theorem actual_jacobi_average_lower (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    (hE : (∫ x, plusNorm o x ^ 2 + minusNorm o x ^ 2 ∂normalizedVolume g) = 3)
    {t : ℝ} (ht : 0 < t) (htop : t < Real.pi / Real.sqrt 3) :
    t ^ 3 * Real.exp ((5 / 6 : ℝ) *
      Real.log (Real.sin (Real.sqrt 3 * t) / (Real.sqrt 3 * t)) - t ^ 2 / 12) ≤
        ∫ e, ((actualJacobiSolution g hRic e).J t).det ∂canonicalFrameMeasure g o := by
  have h := actual_jacobi_average_lower_normalized g o hRic hpositive hE ht htop
  rw [integral_div] at h
  simpa only [mul_comm] using (le_div_iff₀ (pow_pos ht 3)).mp h

end
end PositiveEinsteinFour.Geometry
end


section

/-! All points of the open round normal ball have genuine local exponential
charts, including its center. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_round_localChart (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace)
    (hv : ‖v‖ < Real.pi) :
    ∃ C : OpenPartialHomeomorph FourSpace M,
      v ∈ C.source ∧ EqOn C (frameExponential g o e) C.source := by
  by_cases hz : v = 0
  · subst v
    exact frameExponential_localChart g o e
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  have hf : e.rotate (orientedToOrthogonal (directionOrientedMatrix q)) ∈ o.positive :=
    frameRotate_oriented_positive o e he (directionOrientedMatrix q)
  have hp : (q, ‖v‖) ∈ framePolarDomain g hRic e := by
    refine ⟨norm_pos_iff.mpr hz, ?_⟩
    rw [actualFirstConjugateTime_eq_pi_of_weyl_zero hRic hplus hminus _ hf]
    exact hv
  obtain ⟨C, hC, heq⟩ := frameExponential_polar_localChart g o hRic e he q ‖v‖ hp
  exact ⟨C, hrad ▸ hC, heq⟩

theorem frameExponential_round_isLocalHomeomorphOn (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    IsLocalHomeomorphOn (frameExponential g o e) (Metric.ball 0 Real.pi) := by
  apply IsLocalHomeomorphOn.mk
  intro v hv
  obtain ⟨C, hC, heq⟩ := frameExponential_round_localChart hRic hplus hminus e he v
    (by simpa only [Metric.mem_ball, dist_zero_right] using hv)
  exact ⟨C, hC, heq.symm⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The genuine exponential pullback metric in the round branch. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Jacobi
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

private theorem round_jacobi_gram (a : ℝ) :
    (jacobiBlockMatrix 1 (a • (1 : NormalMatrix)))ᵀ *
      jacobiBlockMatrix 1 (a • (1 : NormalMatrix)) =
      jacobiBlockMatrix 1 (a ^ 2 • (1 : NormalMatrix)) := by
  have hblock (b : ℝ) : jacobiBlockMatrix 1 (b • (1 : NormalMatrix)) =
      Matrix.diagonal (Fin.cons 1 (fun _ : Fin 3 => b)) := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [jacobiBlockMatrix, Matrix.diagonal]
      · simp [jacobiBlockMatrix, Matrix.diagonal, Ne.symm (Fin.succ_ne_zero j)]
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [jacobiBlockMatrix, Matrix.diagonal]
      · simp [jacobiBlockMatrix, Matrix.diagonal, Matrix.one_apply]
  rw [hblock, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, hblock]
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [pow_two]

theorem heatNormalMetric_first_of_weyl_zero (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t) :
    heatNormalMetric g o e (t • coordinateVector 0) =
      jacobiBlockMatrix 1 ((Real.sin t / t) ^ 2 • (1 : NormalMatrix)) := by
  let f := parallelFrameFlowMap g 0 t e
  let c := f.base
  have hf : f.base ∈ (chartAt FourSpace c).source := mem_chart_source FourSpace c
  have hx : frameExponential g o e (t • coordinateVector 0) = f.base :=
    frameExponential_first_ray g o e he t ht
  let E := frameChartMatrix g c f
  let H := metricInChart g c (chartAt FourSpace c f.base)
  let B := jacobiBlockMatrix 1 (t⁻¹ • (actualJacobiSolution g hRic e).J t)
  have hN : Eᵀ * H * E = 1 := frameChartMatrix_normalizes g c f hf
  have hD := (frameExponential_hasFDerivAt g o hRic c e he t ht hf).fderiv
  have hcol (i : Fin 4) :
      WithLp.ofLp (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (E * B)
        (coordinateVector i)) = fun k => (E * B) k i := by
    change (E * B) *ᵥ Pi.single i 1 = _
    exact Matrix.mulVec_single_one _ _
  have hGram : heatNormalMetric g o e (t • coordinateVector 0) = Bᵀ * B := by
    ext i j
    rw [heatNormalMetric_chart_pairing g o e c _ (hx ▸ hf), hD]
    rw [hcol, hcol]
    rw [hx, ← heat_matrix_congruence_pairing]
    change ((E * B)ᵀ * H * (E * B)) i j = (Bᵀ * B) i j
    have hmat : (E * B)ᵀ * H * (E * B) = Bᵀ * B := by
      rw [Matrix.transpose_mul]
      calc
        _ = Bᵀ * (Eᵀ * H * E) * B := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hN, Matrix.mul_one]
    exact congrArg (fun A : Mat4 => A i j) hmat
  rw [hGram]
  have hB : B = jacobiBlockMatrix 1 ((Real.sin t / t) • (1 : NormalMatrix)) := by
    dsimp only [B]
    rw [(actualJacobi_eq_sine_of_weyl_zero hRic hplus hminus e he t).1, smul_smul]
    congr 2
    ring
  rw [hB, round_jacobi_gram]

theorem frameExponential_pi_normal_differential_zero (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (c : M)
    (hc : (parallelFrameFlowMap g 0 Real.pi e).base ∈ (chartAt FourSpace c).source)
    (w : Fin 3 → ℝ) :
    fderiv ℝ (fun v : FourSpace => chartAt FourSpace c
      (frameExponential g o e (Real.pi • v))) (coordinateVector 0)
      (WithLp.toLp 2 (Fin.cons 0 w)) = 0 := by
  rw [frameExponential_rescaled_fderiv g o hRic c e he Real.pi Real.pi_pos hc,
    (actualJacobi_eq_sine_of_weyl_zero hRic hplus hminus e he Real.pi).1,
    Real.sin_pi, zero_smul]
  change WithLp.toLp 2 ((frameChartMatrix g c (parallelFrameFlowMap g 0 Real.pi e) *
    jacobiBlockMatrix Real.pi 0) *ᵥ Fin.cons 0 w) = 0
  rw [← Matrix.mulVec_mulVec]
  have hz : jacobiBlockMatrix Real.pi (0 : NormalMatrix) *ᵥ
      (Fin.cons 0 w : Fin 4 → ℝ) = 0 := by
    rw [jacobiBlockMatrix_mulVec]
    ext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  rw [hz, Matrix.mulVec_zero, WithLp.toLp_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual index identities force equality in the normalized volume
bound when both Weyl blocks vanish. The common chart factor is retained. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem round_normalized_volume_eq_one (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0) :
    volumeRatio g / riemannianChartFactor.toReal = 1 := by
  have hp : ∀ c, plusNorm o c = 0 := fun c => (plusNorm_eq_zero_iff o c).mpr (hplus c)
  have hm : ∀ c, minusNorm o c = 0 := fun c => (minusNorm_eq_zero_iff o c).mpr (hminus c)
  have hu := normalized_volume_ratio_upper g o hRic hpositive
  obtain ⟨n, m, hc, _⟩ := normalized_hodge_counts g o hRic
  simp only [hp, hm, zero_pow (by decide : 2 ≠ 0), add_zero, integral_zero,
    mul_zero, sub_zero, mul_one] at hu hc
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem round_normalized_totalVolume (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0) :
    totalVolume g / riemannianChartFactor.toReal = 8 * Real.pi ^ 2 / 3 := by
  have h := round_normalized_volume_eq_one hRic hpositive hplus hminus
  unfold volumeRatio at h
  rw [div_right_comm] at h
  exact (div_eq_one_iff_eq (by positivity : (8 * Real.pi ^ 2 / 3 : ℝ) ≠ 0)).mp h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Radial projection onto the sphere of radius pi and its tangent
identity, used to descend the round exponential through its boundary. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped _root_.Topology InnerProductSpace
noncomputable section

def roundBoundaryProjection (v : FourSpace) : FourSpace := Real.pi • (‖v‖⁻¹ • v)

theorem roundBoundaryProjection_norm (v : FourSpace) (hv : v ≠ 0) :
    ‖roundBoundaryProjection v‖ = Real.pi := by
  rw [roundBoundaryProjection, norm_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv), mul_one]

theorem roundBoundaryProjection_differentiableAt (v : FourSpace) (hv : v ≠ 0) :
    DifferentiableAt ℝ roundBoundaryProjection v := by
  have hn : DifferentiableAt ℝ (fun x : FourSpace => ‖x‖) v :=
    (contDiffAt_norm ℝ hv : ContDiffAt ℝ 1 (fun x : FourSpace => ‖x‖) v).differentiableAt one_ne_zero
  exact ((hn.inv (norm_ne_zero_iff.mpr hv)).smul differentiableAt_id).const_smul Real.pi

theorem roundBoundaryProjection_derivative_tangent (v : FourSpace) (hv : v ≠ 0)
    (w : FourSpace) :
    inner ℝ (‖v‖⁻¹ • v) (fderiv ℝ roundBoundaryProjection v w) = 0 := by
  have hd := (hasStrictFDerivAt_norm_sq (roundBoundaryProjection v)).hasFDerivAt.comp v
    (roundBoundaryProjection_differentiableAt v hv).hasFDerivAt
  have heq : (fun x : FourSpace => ‖roundBoundaryProjection x‖ ^ 2) =ᶠ[𝓝 v]
      (fun _ => Real.pi ^ 2) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hv] with x hx
    rw [roundBoundaryProjection_norm x hx]
  have hc : HasFDerivAt (fun x : FourSpace => ‖roundBoundaryProjection x‖ ^ 2)
      (0 : FourSpace →L[ℝ] ℝ) v :=
    (hasFDerivAt_const (Real.pi ^ 2) v).congr_of_eventuallyEq heq
  have hzero := hd.unique hc
  have hz := congrArg (fun A : FourSpace →L[ℝ] ℝ => A w) hzero
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
    innerSL_apply_apply, zero_apply] at hz
  rw [roundBoundaryProjection, real_inner_smul_left, two_smul] at hz
  nlinarith [Real.pi_pos]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact radial mass for the round Jacobi determinant. Cutting strictly
before pi strictly decreases this mass. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory Set
open scoped ENNReal
noncomputable section

def roundRadialMass (c : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Ioc (0 : ℝ) c, ENNReal.ofReal (Real.sin r ^ 3)

theorem roundRadialMass_formula (c : ℝ) (hc : c ∈ Icc (0 : ℝ) Real.pi) :
    roundRadialMass c = ENNReal.ofReal
      (2 / 3 - Real.cos c + Real.cos c ^ 3 / 3) := by
  have hi : IntegrableOn (fun r => Real.sin r ^ 3) (Ioc (0 : ℝ) c) :=
    (Real.continuous_sin.pow 3).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hn : ∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) c)), 0 ≤ Real.sin r ^ 3 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact pow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hr.1.le (hr.2.trans hc.2)) 3
  rw [roundRadialMass, ← ofReal_integral_eq_lintegral_ofReal hi hn,
    ← intervalIntegral.integral_of_le hc.1, integral_sin_pow_three, Real.cos_zero]
  congr 1
  ring

theorem roundRadialMass_pi : roundRadialMass Real.pi = ENNReal.ofReal (4 / 3 : ℝ) := by
  rw [roundRadialMass_formula _ ⟨Real.pi_pos.le, le_rfl⟩, Real.cos_pi]
  norm_num

theorem roundRadialMass_le_pi (c : ℝ) (hc : c ≤ Real.pi) :
    roundRadialMass c ≤ roundRadialMass Real.pi :=
  lintegral_mono_set (Ioc_subset_Ioc_right hc)

theorem roundRadialMass_lt_pi (c : ℝ) (hc : c ∈ Ico (0 : ℝ) Real.pi) :
    roundRadialMass c < roundRadialMass Real.pi := by
  rw [roundRadialMass_formula c ⟨hc.1, hc.2.le⟩, roundRadialMass_pi]
  have hlo : -1 < Real.cos c := by
    simpa only [Real.cos_pi] using
      Real.strictAntiOn_cos ⟨hc.1, hc.2.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ hc.2
  have hhi := Real.cos_le_one c
  have hpos : 0 < (Real.cos c + 1) ^ 2 * (2 - Real.cos c) :=
    mul_pos (sq_pos_of_pos (by linarith)) (by linarith)
  apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : 0 < (4 / 3 : ℝ))).mpr
  nlinarith only [hpos]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Explicit polar coordinates on the actual round four-sphere. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped BigOperators
noncomputable section

def roundNorth : RoundSphere4 := ⟨EuclideanSpace.single 0 1, by simp⟩

def roundPolarVector (t : ℝ) (q : Directions) : EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 (Fin.cons (Real.cos t) (fun i => Real.sin t * q.val i))

theorem roundPolarVector_norm (t : ℝ) (q : Directions) : ‖roundPolarVector t q‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  change (Real.cos t) ^ 2 + (∑ i : Fin 4, (Real.sin t * q.val i) ^ 2) = 1 ^ 2
  have hq : (∑ i : Fin 4, (q.val i) ^ 2) = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, q.property]
    norm_num
  simp_rw [mul_pow]
  rw [← Finset.mul_sum, hq, mul_one]
  nlinarith [Real.sin_sq_add_cos_sq t]

def roundPolarPoint (t : ℝ) (q : Directions) : RoundSphere4 :=
  ⟨roundPolarVector t q, roundPolarVector_norm t q⟩

@[simp] theorem roundPolarPoint_first (t : ℝ) (q : Directions) :
    (roundPolarPoint t q).val 0 = Real.cos t := rfl

@[simp] theorem roundPolarPoint_tail (t : ℝ) (q : Directions) (i : Fin 4) :
    (roundPolarPoint t q).val i.succ = Real.sin t * q.val i := rfl

theorem roundPolarPoint_zero (q : Directions) : roundPolarPoint 0 q = roundNorth := by
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [roundNorth, roundPolarPoint, roundPolarVector]
  · simp [roundNorth, roundPolarPoint, roundPolarVector]

theorem roundPolarPoint_pi (q : Directions) :
    roundPolarPoint Real.pi q = antipode roundNorth := by
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [roundNorth, roundPolarPoint, roundPolarVector]
  · simp [roundNorth, roundPolarPoint, roundPolarVector]

theorem roundDistance_polar (t : ℝ) (ht : t ∈ Icc (0 : ℝ) Real.pi) (q : Directions) :
    roundDistance roundNorth (roundPolarPoint t q) = t := by
  unfold roundDistance
  have hinner : inner ℝ roundNorth.val (roundPolarPoint t q).val = Real.cos t := by
    simp [roundNorth, PiLp.inner_apply]
  rw [hinner, Real.arccos_cos ht.1 ht.2]

def roundTail (p : RoundSphere4) : FourSpace :=
  WithLp.toLp 2 (fun i => p.val i.succ)

theorem roundTail_norm_sq (p : RoundSphere4) :
    ‖roundTail p‖ ^ 2 = 1 - (p.val 0) ^ 2 := by
  have hp := congrArg (fun r : ℝ => r ^ 2) p.property
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ] at hp
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i : Fin 4, (p.val i.succ) ^ 2) = _
  nlinarith only [hp]

theorem roundFirst_bounds (p : RoundSphere4) : p.val 0 ∈ Icc (-1 : ℝ) 1 := by
  have hn := sq_nonneg ‖roundTail p‖
  rw [roundTail_norm_sq] at hn
  constructor <;> nlinarith [sq_nonneg (p.val 0 + 1), sq_nonneg (p.val 0 - 1)]

theorem roundTail_norm_arccos (p : RoundSphere4) :
    Real.sin (Real.arccos (p.val 0)) = ‖roundTail p‖ := by
  rw [Real.sin_arccos, ← roundTail_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem exists_roundPolarPoint (p : RoundSphere4) :
    ∃ t ∈ Icc (0 : ℝ) Real.pi, ∃ q : Directions, p = roundPolarPoint t q := by
  let t := Real.arccos (p.val 0)
  have ht : t ∈ Icc (0 : ℝ) Real.pi := ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hcos : Real.cos t = p.val 0 := Real.cos_arccos (roundFirst_bounds p).1 (roundFirst_bounds p).2
  have hsin : Real.sin t = ‖roundTail p‖ := roundTail_norm_arccos p
  by_cases hn : roundTail p = 0
  · refine ⟨t, ht, firstDirection, ?_⟩
    have hs : Real.sin t = 0 := by rw [hsin, hn, norm_zero]
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hcos.symm
    · have hi := congrArg (fun w : FourSpace => w i) hn
      change p.val i.succ = Real.sin t * firstDirection.val i
      rw [hs, zero_mul]
      exact hi
  · let q : Directions := ⟨‖roundTail p‖⁻¹ • roundTail p, by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hn)]⟩
    refine ⟨t, ht, q, ?_⟩
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hcos.symm
    · change p.val i.succ = Real.sin t * (‖roundTail p‖⁻¹ * p.val i.succ)
      rw [hsin, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hn), one_mul]

theorem roundTail_zero_cases (p : RoundSphere4) (hp : roundTail p = 0) :
    p = roundNorth ∨ p = antipode roundNorth := by
  have hsq := roundTail_norm_sq p
  rw [hp, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hsq
  have heq : (p.val 0 - 1) * (p.val 0 + 1) = 0 := by nlinarith only [hsq]
  rcases mul_eq_zero.mp heq with hpos | hneg
  · left
    have hzero : p.val 0 = 1 := by linarith only [hpos]
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [roundNorth] using hzero
    · have hi := congrArg (fun v : FourSpace => v i) hp
      simpa [roundNorth, roundTail] using hi
  · right
    have hzero : p.val 0 = -1 := by linarith only [hneg]
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [roundNorth] using hzero
    · have hi := congrArg (fun v : FourSpace => v i) hp
      simpa [roundNorth, roundTail] using hi

end
end PositiveEinsteinFour.Geometry
end


section

/-! Unit-norm Weyl curvature yields the parallel rank-one orthogonal
projector (W+ + I)/3. The polynomial relation comes from the actual
second derivative and Weyl equation. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour TraceHessian Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff
noncomputable section
local instance projectorNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance projectorNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}
  {μ : Measure (FrameBundle g)}

theorem MetricGreenData.hessian_zero_of_gradient_zero (d : MetricGreenData g μ)
    (hflow : OrientationPreservingFlow d o)
    (hgrad : ∀ f ∈ o.positive, ∀ j, plusWeylGradient g f.base f.frame j = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (i j : Fin 4) :
    plusWeylHessian g e.base e.frame i j = 0 := by
  obtain ⟨f,hf⟩ := ((d.flow i).map 0).surjective e
  have hp : f ∈ o.positive := (hflow i 0 f).mp (hf.symm ▸ he)
  have hd := d.derivativeGradient i j 0 f
  have hz : (fun s => plusWeylGradient g ((d.flow i).map s f).base
      ((d.flow i).map s f).frame j) = fun _ => (0 : Mat) := by
    funext s
    exact hgrad _ ((hflow i s f).mpr hp) j
  rw [hz] at hd
  have h := hd.unique (hasDerivAt_const (0 : ℝ) (0 : Mat))
  change plusWeylHessian g ((d.flow i).map 0 f).base ((d.flow i).map 0 f).frame i j = 0 at h
  rw [hf] at h
  exact h

variable [T3Space M] [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M]

theorem actual_unit_weyl_polynomial (hRic : RicciThree g)
    (hnorm : ∀ x, plusNorm o x = 1) (e : FrameBundle g) (he : e ∈ o.positive) :
    plusWeyl g e.base e.frame * plusWeyl g e.base e.frame =
      plusWeyl g e.base e.frame + (2 : ℝ) • (1 : Mat) := by
  let d := (canonicalParallelMetricData g o hRic).toMetricGreenData
  have hf : OrientationPreservingFlow d o := canonicalParallelMetricData_orientation o hRic
  have hg f hf' := (actual_unit_weyl_parallel hRic hnorm f hf').1
  have hx := d.hessian_zero_of_gradient_zero hf hg e he
  have hL : weylLaplacian (plusWeyl g e.base e.frame) = 0 := by
    rw [← metric_weyl_trace g d.weyl]
    simp only [hessianTrace, hx, Finset.sum_const_zero]
  have hn : normalizedBlockNorm (plusWeyl g e.base e.frame) = 1 := by
    rw [← actual_plusNorm_frame o e he, hnorm]
  have ht : Matrix.trace (plusWeyl g e.base e.frame * plusWeyl g e.base e.frame) = 6 := by
    rw [trace_square_eq_six_norm_sq _ (d.weyl.symmetric e), hn]
    norm_num
  ext i j
  have h := congrFun (congrFun hL i) j
  simp only [weylLaplacian, traceFreeSquare, Matrix.smul_apply, Matrix.sub_apply,
    ht, smul_eq_mul, Matrix.zero_apply] at h
  change (plusWeyl g e.base e.frame * plusWeyl g e.base e.frame) i j = _
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! The explicit positive correction to the continuous lower radial bound. -/
namespace PositiveEinsteinFour.Jacobi
noncomputable section

theorem sine_exponential_lower_refined {x : ℝ} (hx : 0 < x) (hxπ : x < Real.pi) :
    (Real.sin x / x) * (1 + ((x / Real.pi) ^ 4 / 2 + (x / Real.pi) ^ 6 / 3) / 6) ≤
      Real.exp ((5 / 6 : ℝ) * Real.log (Real.sin x / x) - x ^ 2 / 36) := by
  have hs : 0 < Real.sin x / x := div_pos (Real.sin_pos_of_pos_of_lt_pi hx hxπ) hx
  have hr := sine_log_remainder_lower hx hxπ
  have he : (5 / 6 : ℝ) * Real.log (Real.sin x / x) - x ^ 2 / 36 =
      Real.log (Real.sin x / x) + (-Real.log (Real.sin x / x) - x ^ 2 / 6) / 6 := by ring
  rw [he, Real.exp_add, Real.exp_log hs]
  apply mul_le_mul_of_nonneg_left _ hs.le
  have h := Real.add_one_le_exp ((-Real.log (Real.sin x / x) - x ^ 2 / 6) / 6)
  linarith

end
end PositiveEinsteinFour.Jacobi

namespace PositiveEinsteinFour.Geometry
open EinsteinFour Jacobi Matrix MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M]

theorem actual_jacobi_average_lower_refined (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    (hE : (∫ x, plusNorm o x ^ 2 + minusNorm o x ^ 2 ∂normalizedVolume g) = 3)
    {t : ℝ} (ht : 0 < t) (htop : t < Real.pi / Real.sqrt 3) :
    t ^ 3 * (Real.sin (Real.sqrt 3 * t) / (Real.sqrt 3 * t)) *
      (1 + ((Real.sqrt 3 * t / Real.pi) ^ 4 / 2 +
        (Real.sqrt 3 * t / Real.pi) ^ 6 / 3) / 6) ≤
      ∫ e, ((actualJacobiSolution g hRic e).J t).det ∂canonicalFrameMeasure g o := by
  have hθ : 0 < Real.sqrt 3 * t := mul_pos (Real.sqrt_pos.mpr (by norm_num)) ht
  have hθπ : Real.sqrt 3 * t < Real.pi := by
    have h := (lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))).mp htop
    nlinarith
  have h := mul_le_mul_of_nonneg_left (sine_exponential_lower_refined hθ hθπ)
    (pow_nonneg ht.le 3)
  have he : (Real.sqrt 3 * t) ^ 2 / 36 = t ^ 2 / 12 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    ring
  rw [he, ← mul_assoc] at h
  exact h.trans (actual_jacobi_average_lower g o hRic hpositive hE ht htop)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Real-valued lower polar integration with the actual normalization factor. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Matrix MeasureTheory Set Filter Metric
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem actualJacobi_truncated_eq_det_below_sqrt_three (g : SmoothMetric M)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    (e : FrameBundle g) {r : ℝ} (hr : 0 < r) (htop : r < Real.pi / Real.sqrt 3) :
    (actualRegularJacobi g hRic e r).truncatedDensity =
      ((actualJacobiSolution g hRic e).J r).det := by
  rw [← actualJacobi_abs_det_eq_truncatedDensity g hRic e r hr
    (fun s hs hsr => actualJacobi_isUnit_below_sqrt_three g hRic hpositive e hs (hsr.trans_lt htop)),
    abs_of_pos (actualJacobi_determinant_pos_below_sqrt_three g hRic hpositive e hr htop)]

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem canonical_actualBallRadialMass_eq (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    {R : ℝ} (hR : 0 ≤ R) (hRtop : R ≤ Real.pi / Real.sqrt 3) :
    (∫⁻ e, actualBallRadialMass g hRic R e ∂canonicalFrameMeasure g o) =
      ENNReal.ofReal (∫ r in (0 : ℝ)..R, ∫ e,
        (actualRegularJacobi g hRic e r).truncatedDensity ∂canonicalFrameMeasure g o) := by
  have hmeas := ENNReal.measurable_ofReal.comp
    (actualJacobiJ_joint_continuous g hRic).matrix_det.abs.measurable
  have hswap : (∫⁻ e, actualBallRadialMass g hRic R e ∂canonicalFrameMeasure g o) =
      ∫⁻ r in Ioo (0 : ℝ) R, ∫⁻ e, ENNReal.ofReal
        |((actualJacobiSolution g hRic e).J r).det| ∂canonicalFrameMeasure g o :=
    lintegral_lintegral_swap (hmeas.comp measurable_swap).aemeasurable
  rw [hswap, intervalIntegral.integral_of_le hR, integral_Ioc_eq_integral_Ioo]
  have hi := (actualJacobi_average_integrableOn g o hRic 0 R).mono_set Ioo_subset_Icc_self
  have hn : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      0 ≤ ∫ e, (actualRegularJacobi g hRic e r).truncatedDensity ∂canonicalFrameMeasure g o := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact actualJacobi_average_nonneg g o hRic r hr.1.le
  rw [ofReal_integral_eq_lintegral_ofReal hi hn]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  have he (e : FrameBundle g) : |((actualJacobiSolution g hRic e).J r).det| =
      (actualRegularJacobi g hRic e r).truncatedDensity :=
    actualJacobi_abs_det_eq_truncatedDensity g hRic e r hr.1
      (fun s hs hsr => actualJacobi_isUnit_below_sqrt_three g hRic hpositive e hs
        (hsr.trans_lt (hr.2.trans_le hRtop)))
  simp_rw [he]
  exact (ofReal_integral_eq_lintegral_ofReal (actualJacobiDensity_integrable g o hRic r)
    (Eventually.of_forall fun e => (actualRegularJacobi g hRic e r).truncatedDensity_nonneg hr.1.le)).symm

variable [SecondCountableTopology M]

theorem lower_polar_volume_of_injective_ball (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    {R : ℝ} (hR : 0 ≤ R) (hRtop : R ≤ Real.pi / Real.sqrt 3)
    (hinj : ∀ e ∈ o.positive, InjOn (frameExponential g o e) (ball 0 R)) :
    riemannianChartFactor.toReal * (2 * Real.pi ^ 2) *
      (∫ r in (0 : ℝ)..R, ∫ e, (actualRegularJacobi g hRic e r).truncatedDensity
        ∂canonicalFrameMeasure g o) ≤ totalVolume g := by
  have h := lower_canonical_radial_mass_le_volume g o hRic R hinj
  rw [canonical_actualBallRadialMass_eq g o hRic hpositive hR hRtop, polarAngularMass_eq] at h
  have hfin : volumeMeasure g univ ≠ ⊤ := ne_of_lt (actual_finitePositiveVolume g).finite
  have hb := ENNReal.toReal_mono hfin h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * Real.pi ^ 2),
    ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hR (fun r hr =>
      actualJacobi_average_nonneg g o hRic r hr.1)), totalVolume] using hb

end
end PositiveEinsteinFour.Geometry
end


section

/-! A globally shortest cut point below the conjugate radius yields a
closed geodesic, with matching velocity at both joins. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameAntipode_vector (g : SmoothMetric M) (e : FrameBundle g) (i : Fin 4) :
    (frameAntipode g e).frame.vector i = -e.frame.vector i := by
  change (e.frame.rotate (orientedToOrthogonal reverseFrameRotation)).vector i = _
  rw [OrthonormalFrame.rotate_vector,reverseFrameRotation_matrix]
  simp [Matrix.one_apply]

variable [T3Space M] [CompactSpace M] [PreconnectedSpace M]

omit [PreconnectedSpace M] in
theorem frameAntipode_flow_cancel (g : SmoothMetric M) (e : FrameBundle g) (t : ℝ) :
    parallelFrameFlowMap g 0 t (frameAntipode g (parallelFrameFlowMap g 0 t e)) =
      frameAntipode g e := by
  rw [← parallelFrameFlowMap_antipode,← parallelFrameFlowMap_add,neg_add_cancel,
    parallelFrameFlowMap_zero]

theorem minimal_cut_pair_initial_opposite (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (t : ℝ) (ht : 0 < t)
    (hcut : ∀ e ∈ o.positive, t ≤ actualCutTime g e)
    (hconj : ∀ e ∈ o.positive, t < actualFirstConjugateTime g hRic e)
    (e f : FrameBundle g) (he : e ∈ o.positive) (hf : f ∈ o.positive)
    (hbase : e.base = f.base) (hne : e.frame.vector 0 ≠ f.frame.vector 0)
    (hend : frameGeodesic g 0 e t = frameGeodesic g 0 f t) :
    e.frame.vector 0 = -f.frame.vector 0 := by
  have hterminal := minimal_cut_terminal_opposite g o hRic t ht hcut e f he hf
    hbase hne hend (hconj e he) (hconj f hf)
  let E := parallelFrameFlowMap g 0 t e
  let F := parallelFrameFlowMap g 0 t f
  let E' := frameAntipode g E
  let F' := frameAntipode g F
  have hE : E' ∈ o.positive := frameRotate_oriented_positive o E
    (parallelFrameFlowMap_positive g o e he t) _
  have hF : F' ∈ o.positive := frameRotate_oriented_positive o F
    (parallelFrameFlowMap_positive g o f hf t) _
  have hne' : E'.frame.vector 0 ≠ F'.frame.vector 0 := by
    intro h
    have hsame : E.frame.vector 0 = F.frame.vector 0 := by
      simpa only [E',F',frameAntipode_vector,neg_inj] using h
    have hz : E.frame.vector 0 = 0 := by
      have hh : E.frame.vector 0 = -F.frame.vector 0 := hterminal
      rw [← hsame] at hh
      ext i
      have hhi := congrArg (fun v : FourSpace => v i) hh
      change (E.frame.vector 0) i = -(E.frame.vector 0) i at hhi
      change (E.frame.vector 0) i = 0
      linarith
    have hu := E.frame.inner_vector_self 0
    rw [hz] at hu
    have hzinner : g.inner E.base (0 : FourSpace) 0 = 0 := (g.inner E.base 0).map_zero
    exact zero_ne_one (hzinner.symm.trans hu)
  have hends : frameGeodesic g 0 E' t = frameGeodesic g 0 F' t := by
    change (parallelFrameFlowMap g 0 t (frameAntipode g E)).base =
      (parallelFrameFlowMap g 0 t (frameAntipode g F)).base
    rw [frameAntipode_flow_cancel,frameAntipode_flow_cancel]
    exact hbase
  have hh := minimal_cut_terminal_opposite g o hRic t ht hcut E' F' hE hF
    hend hne' hends (hconj E' hE) (hconj F' hF)
  change (parallelFrameFlowMap g 0 t (frameAntipode g E)).frame.vector 0 =
    -(parallelFrameFlowMap g 0 t (frameAntipode g F)).frame.vector 0 at hh
  rw [frameAntipode_flow_cancel,frameAntipode_flow_cancel,frameAntipode_vector,
    frameAntipode_vector,neg_neg] at hh
  exact (neg_eq_iff_eq_neg.mp hh)

theorem exists_closed_geodesic_at_minimal_cut (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hcut : ∀ f ∈ o.positive, actualCutTime g e ≤ actualCutTime g f)
    (hconj : ∀ f ∈ o.positive,
      actualCutTime g e < actualFirstConjugateTime g hRic f) :
    unitTangentOfFrame (parallelFrameFlowMap g 0 (2 * actualCutTime g e) e) =
      unitTangentOfFrame e := by
  let t := actualCutTime g e
  have ht : 0 < t := actualCutTime_pos g o hRic e he
  obtain ⟨w,hw,hend,hwne⟩ := actualCutTime_second_minimizing_vector g o hRic e he (hconj e he)
  have hn : ‖w‖ = t := by
    rw [← hw,hend]
    exact (metricDistance_eq_iff g _ _ ht.le).mpr
      (show t ∈ frameMinimizingTimes g e from by
        rw [frameMinimizingTimes_eq_Icc]; exact ⟨ht.le,le_rfl⟩).2
  let p : Directions := ⟨t⁻¹ • w, by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht),hn,inv_mul_cancel₀ ht.ne']⟩
  have hp : t • p.val = w := by
    change t • (t⁻¹ • w) = w
    rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
  let f := e.rotate (orientedToOrthogonal (directionOrientedMatrix p))
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he _
  have hpoint : frameGeodesic g 0 e t = frameGeodesic g 0 f t := by
    rw [← frameExponential_direction_ray g o e he p t,hp]
    exact hend.symm
  have hne : e.frame.vector 0 ≠ f.frame.vector 0 := by
    intro hh
    have hdir : p.val = coordinateVector 0 := by
      apply e.frame.map_injective
      change e.frame.vector 0 = (e.frame.turn p).vector 0 at hh
      rw [e.frame.turn_first] at hh
      rw [e.frame.map_coordinateVector]
      exact hh.symm
    apply hwne
    rw [← hp,hdir]
  have hi := minimal_cut_pair_initial_opposite g o hRic t ht hcut hconj e f he hf rfl hne hpoint
  have ho := minimal_cut_terminal_opposite g o hRic t ht hcut e f he hf rfl hne hpoint
    (hconj e he) (hconj f hf)
  let F := parallelFrameFlowMap g 0 t f
  have hjoin : unitTangentOfFrame (parallelFrameFlowMap g 0 t e) =
      unitTangentOfFrame (frameAntipode g F) := by
    apply unitTangent_ext (u := unitTangentOfFrame (parallelFrameFlowMap g 0 t e))
      (v := unitTangentOfFrame (frameAntipode g F)) hpoint
    change (parallelFrameFlowMap g 0 t e).frame.vector 0 = (frameAntipode g F).frame.vector 0
    rw [frameAntipode_vector]
    exact ho
  have hfpos : frameAntipode g F ∈ o.positive := frameRotate_oriented_positive o F
    (parallelFrameFlowMap_positive g o f hf t) _
  have hflow := unitTangentOfFrame_flow_eq g o _ _
    (parallelFrameFlowMap_positive g o e he t) hfpos hjoin t
  rw [← parallelFrameFlowMap_add,frameAntipode_flow_cancel] at hflow
  have hstart : unitTangentOfFrame (frameAntipode g f) = unitTangentOfFrame e := by
    apply unitTangent_ext (u := unitTangentOfFrame (frameAntipode g f))
      (v := unitTangentOfFrame e) rfl
    change (frameAntipode g f).frame.vector 0 = e.frame.vector 0
    rw [frameAntipode_vector]
    exact hi.symm
  simpa only [two_mul] using hflow.trans hstart

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local chart argument needed to turn zero boundary derivatives
into a single endpoint of the round exponential. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Metric Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

omit [IsManifold I4 ∞ M] in
theorem zero_chart_derivative_locally_constant (F : FourSpace → M) (U : Set FourSpace)
    (hU : IsOpen U) (hF : ContinuousOn F U)
    (hD : ∀ x ∈ U, ∀ c : M, F x ∈ (chartAt FourSpace c).source →
      HasFDerivAt (fun y => chartAt FourSpace c (F y)) (0 : FourSpace →L[ℝ] FourSpace) x) :
    IsLocallyConstant (fun x : U => F x.val) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  let c := F x.val
  have hc : F x.val ∈ (chartAt FourSpace c).source := mem_chart_source FourSpace c
  have hn : U ∩ F ⁻¹' (chartAt FourSpace c).source ∈ 𝓝 x.val :=
    inter_mem (hU.mem_nhds x.property)
      ((hF x.val x.property).continuousAt (hU.mem_nhds x.property) |>.preimage_mem_nhds
        ((chartAt FourSpace c).open_source.mem_nhds hc))
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hn
  have hzero (y : FourSpace) (hy : y ∈ ball x.val r) :
      HasFDerivAt (fun z => chartAt FourSpace c (F z)) (0 : FourSpace →L[ℝ] FourSpace) y :=
    hD y (hb hy).1 c (hb hy).2
  have hconst (y : FourSpace) (hy : y ∈ ball x.val r) :
      chartAt FourSpace c (F y) = chartAt FourSpace c (F x.val) := by
    apply (convex_ball x.val r).is_const_of_fderivWithin_eq_zero
      (fun z hz => (hzero z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => ?_) hy (mem_ball_self hr)
    rw [fderivWithin_of_isOpen isOpen_ball hz, (hzero z hz).fderiv]
  filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
    (ball_mem_nhds x.val hr)] with y hy
  exact (chartAt FourSpace c).injOn (hb hy).2 hc (hconst y.val hy)

end
end PositiveEinsteinFour.Geometry
end


section

/-! At time pi the round exponential has zero derivative in every
angular direction, including after changing the initial direction. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Jacobi Angular
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_pi_first_tangent_zero (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (c : M)
    (hc : (parallelFrameFlowMap g 0 Real.pi e).base ∈ (chartAt FourSpace c).source)
    (w : FourSpace) (hw : w 0 = 0) :
    fderiv ℝ (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e v))
      (Real.pi • coordinateVector 0) w = 0 := by
  rw [(frameExponential_hasFDerivAt g o hRic c e he Real.pi Real.pi_pos hc).fderiv,
    (actualJacobi_eq_sine_of_weyl_zero hRic hplus hminus e he Real.pi).1,
    Real.sin_pi, zero_smul, smul_zero]
  change WithLp.toLp 2 ((frameChartMatrix g c (parallelFrameFlowMap g 0 Real.pi e) *
    jacobiBlockMatrix 1 0) *ᵥ WithLp.ofLp w) = 0
  rw [← Matrix.mulVec_mulVec]
  have hz : jacobiBlockMatrix 1 (0 : NormalMatrix) *ᵥ WithLp.ofLp w = 0 := by
    rw [jacobiBlockMatrix_mulVec]
    ext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [hw]
  rw [hz, Matrix.mulVec_zero, WithLp.toLp_zero]

theorem frameExponential_pi_angular_derivative_zero (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (q : Directions) (c : M)
    (hc : frameExponential g o e (Real.pi • q.val) ∈ (chartAt FourSpace c).source)
    (w : FourSpace) (hw : inner ℝ q.val w = 0) :
    fderiv ℝ (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e v))
      (Real.pi • q.val) w = 0 := by
  let Q := directionOrientedMatrix q
  let L := (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
    (orientedToOrthogonal Q).property).toContinuousLinearEquiv
  let f := e.rotate (orientedToOrthogonal Q)
  let F := fun v : FourSpace => chartAt FourSpace c (frameExponential g o e v)
  let G := fun v : FourSpace => chartAt FourSpace c (frameExponential g o f v)
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he Q
  have hLfirst : L (coordinateVector 0) = q.val := directionRotation_first q
  have hLpoint : L (Real.pi • coordinateVector 0) = Real.pi • q.val := by
    rw [map_smul, hLfirst]
  have hp : frameExponential g o e (Real.pi • q.val) =
      (parallelFrameFlowMap g 0 Real.pi f).base :=
    frameExponential_direction_ray g o e he q Real.pi
  have hfc : (parallelFrameFlowMap g 0 Real.pi f).base ∈ (chartAt FourSpace c).source := hp ▸ hc
  have hF := (frameExponential_chart_contDiffAt g o c e (Real.pi • q.val) hc).differentiableAt
    one_ne_zero
  rw [← hLpoint] at hF
  have hcomp := hF.hasFDerivAt.comp (Real.pi • coordinateVector 0)
    (L : FourSpace →L[ℝ] FourSpace).hasFDerivAt
  have heq : (fun v : FourSpace => F (L v)) = G := by
    funext v
    exact congrArg (chartAt FourSpace c) (frameExponential_rotate g o e Q v).symm
  change HasFDerivAt (fun v => F (L v))
    ((fderiv ℝ F (L (Real.pi • coordinateVector 0))).comp
      (L : FourSpace →L[ℝ] FourSpace)) (Real.pi • coordinateVector 0) at hcomp
  rw [heq, hLpoint] at hcomp
  have hfirst : (L.symm w) 0 = 0 := by
    have hinner := (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
      (orientedToOrthogonal Q).property).inner_map_map (coordinateVector 0) (L.symm w)
    change inner ℝ (L (coordinateVector 0)) (L (L.symm w)) =
      inner ℝ (coordinateVector 0) (L.symm w) at hinner
    rw [hLfirst, L.apply_symm_apply, hw] at hinner
    simpa [PiLp.inner_apply, coordinateVector] using hinner.symm
  have hz := frameExponential_pi_first_tangent_zero hRic hplus hminus f hf c hfc
    (L.symm w) hfirst
  change fderiv ℝ G (Real.pi • coordinateVector 0) (L.symm w) = 0 at hz
  rw [hcomp.fderiv] at hz
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    L.apply_symm_apply] using hz

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual minimizing-domain integral retains the cut radius exactly
in the constant-curvature branch. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem round_actual_cut_mass (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    (∫⁻ r : Ioi (0 : ℝ),
      (if r.val ≤ actualCutTime g e then
        ENNReal.ofReal |((actualJacobiSolution g hRic e).J r.val).det| else 0)
      ∂((volume : Measure ℝ).comap Subtype.val)) = roundRadialMass (actualCutTime g e) := by
  let F : ℝ → ℝ≥0∞ := fun r => if r ≤ actualCutTime g e then
    ENNReal.ofReal |((actualJacobiSolution g hRic e).J r).det| else 0
  change (∫⁻ r : Ioi (0 : ℝ), F r.val
    ∂((volume : Measure ℝ).comap Subtype.val)) = _
  rw [lintegral_subtype_comap measurableSet_Ioi F,
    ← lintegral_indicator measurableSet_Ioi]
  rw [roundRadialMass, ← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro r
  dsimp only [F]
  by_cases hr : 0 < r
  · rw [Set.indicator_of_mem (show r ∈ Ioi (0 : ℝ) from hr)]
    by_cases hc : r ≤ actualCutTime g e
    · rw [ite_eq_left hc, Set.indicator_of_mem (show r ∈ Ioc (0 : ℝ) (actualCutTime g e) from ⟨hr, hc⟩),
        (actualJacobi_eq_sine_of_weyl_zero hRic hplus hminus e he r).1,
        Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one,
        abs_of_nonneg (pow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hr.le
          (hc.trans (actualCutTime_le_pi g hRic e))) 3)]
    · rw [ite_eq_right hc, Set.indicator_of_notMem (fun h => hc h.2)]
  · rw [Set.indicator_of_notMem (show r ∉ Ioi (0 : ℝ) from hr), Set.indicator_of_notMem (fun h => hr h.1)]

variable [SecondCountableTopology M]

theorem round_volume_le_cut_mass (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    volumeMeasure g univ ≤ riemannianChartFactor *
      (ENNReal.ofReal (2 * Real.pi ^ 2) * ∫⁻ q : Directions,
        roundRadialMass (actualCutTime g
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))) ∂sphereMeasure) := by
  have h := volumeMeasure_le_integral_exponentialJacobian g o hRic e he
  rw [minimizing_exponential_integral_radial g o hRic e he, polarAngularMass_eq] at h
  convert h using 2
  congr 1
  apply lintegral_congr
  intro q
  exact (round_actual_cut_mass hRic hplus hminus _
    (frameRotate_oriented_positive o e he (directionOrientedMatrix q))).symm

theorem round_volumeMeasure (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0) :
    volumeMeasure g univ = riemannianChartFactor * ENNReal.ofReal (8 * Real.pi ^ 2 / 3) := by
  have h := (div_eq_iff riemannianChartFactor_toReal_pos.ne').mp
    (round_normalized_totalVolume hRic hpositive hplus hminus)
  have hk : riemannianChartFactor ≠ ⊤ := by
    unfold riemannianChartFactor
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
  calc
    volumeMeasure g univ = ENNReal.ofReal (totalVolume g) :=
      (ENNReal.ofReal_toReal (ne_of_lt (actual_finitePositiveVolume g).finite)).symm
    _ = ENNReal.ofReal ((8 * Real.pi ^ 2 / 3) * riemannianChartFactor.toReal) := congrArg _ h
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hk, mul_comm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Elementary metric identities for the actual unit sphere. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped RealInnerProductSpace
noncomputable section

theorem roundDistance_eq_angle (p q : RoundSphere4) :
    roundDistance p q = InnerProductGeometry.angle p.val q.val := by
  simp only [roundDistance, InnerProductGeometry.angle, p.property, q.property,
    one_mul, div_one]

theorem roundDistance_nonneg (p q : RoundSphere4) : 0 ≤ roundDistance p q :=
  Real.arccos_nonneg _

theorem roundDistance_le_pi (p q : RoundSphere4) : roundDistance p q ≤ Real.pi :=
  Real.arccos_le_pi _

theorem roundDistance_comm (p q : RoundSphere4) : roundDistance p q = roundDistance q p := by
  simp only [roundDistance, real_inner_comm]

theorem roundDistance_triangle (p q r : RoundSphere4) :
    roundDistance p r ≤ roundDistance p q + roundDistance q r := by
  simpa only [roundDistance_eq_angle] using
    InnerProductGeometry.angle_le_angle_add_angle p.val q.val r.val

theorem roundDistance_self (p : RoundSphere4) : roundDistance p p = 0 := by
  simp [roundDistance, p.property]

theorem roundDistance_eq_zero_iff (p q : RoundSphere4) : roundDistance p q = 0 ↔ p = q := by
  constructor
  · intro h
    apply Subtype.ext
    exact InnerProductGeometry.eq_of_angle_eq_zero_of_norm_eq
      ((roundDistance_eq_angle p q).symm.trans h) (p.property.trans q.property.symm)
  · rintro rfl
    exact roundDistance_self _

theorem roundDistance_continuous :
    Continuous (fun pq : RoundSphere4 × RoundSphere4 => roundDistance pq.1 pq.2) :=
  Real.continuous_arccos.comp
    ((continuous_subtype_val.comp continuous_fst).inner
      (continuous_subtype_val.comp continuous_snd))

theorem round_inner_bounds (p q : RoundSphere4) : inner ℝ p.val q.val ∈ Icc (-1 : ℝ) 1 := by
  have h := abs_real_inner_le_norm p.val q.val
  rw [p.property, q.property, one_mul] at h
  exact abs_le.mp h

theorem cos_roundDistance (p q : RoundSphere4) :
    Real.cos (roundDistance p q) = inner ℝ p.val q.val :=
  Real.cos_arccos (round_inner_bounds p q).1 (round_inner_bounds p q).2

theorem round_chord_sq (p q : RoundSphere4) :
    ‖p.val - q.val‖ ^ 2 = 2 - 2 * Real.cos (roundDistance p q) := by
  rw [norm_sub_pow_two_real, p.property, q.property, cos_roundDistance]
  ring

theorem round_tangent_pairing_bound (p q : RoundSphere4)
    (w : EuclideanSpace ℝ (Fin 5)) (hw : inner ℝ q.val w = 0) :
    |inner ℝ p.val w| ≤ Real.sin (roundDistance p q) * ‖w‖ := by
  let v := p.val - (inner ℝ p.val q.val) • q.val
  have hi : inner ℝ v w = inner ℝ p.val w := by
    simp [v, inner_sub_left, real_inner_smul_left, hw]
  have hn : ‖v‖ = Real.sin (roundDistance p q) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sin_nonneg_of_nonneg_of_le_pi
      (roundDistance_nonneg p q) (roundDistance_le_pi p q))).mp
    rw [Real.sin_sq, cos_roundDistance]
    dsimp [v]
    rw [norm_sub_pow_two_real, norm_smul, Real.norm_eq_abs, q.property,
      mul_one, sq_abs, p.property, real_inner_smul_right]
    ring
  have h := abs_real_inner_le_norm v w
  rwa [hi, hn] at h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two eigenvalues of unit parallel Weyl curvature are expressed by
an actual orthogonal projection, without choosing eigenvectors. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour TraceHessian Matrix
open scoped BigOperators
noncomputable section

def unitWeylProjection (A : Mat) : Mat := (1 / 3 : ℝ) • (A + 1)

theorem unitWeylProjection_idempotent (A : Mat)
    (hA : A * A = A + (2 : ℝ) • (1 : Mat)) :
    IsIdempotentElem (unitWeylProjection A) := by
  change ((1 / 3 : ℝ) • (A + 1)) * ((1 / 3 : ℝ) • (A + 1)) = (1 / 3 : ℝ) • (A + 1)
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul,
    Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hA]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

theorem unitWeylProjection_symmetric (A : Mat) (hA : symmetric A) :
    (unitWeylProjection A).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  have hAs : Aᵀ = A := by ext i j; exact hA j i
  change (unitWeylProjection A)ᵀ = unitWeylProjection A
  simp only [unitWeylProjection, Matrix.transpose_smul, Matrix.transpose_add,
    Matrix.transpose_one, hAs]

theorem unitWeylProjection_trace (A : Mat) (ht : traceFree A) :
    Matrix.trace (unitWeylProjection A) = 1 := by
  have ht' : Matrix.trace A = 0 := ht
  simp only [unitWeylProjection, Matrix.trace_smul, Matrix.trace_add, ht',
    Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  norm_num

theorem unitWeylProjection_posSemidef (A : Mat) (hs : symmetric A)
    (hp : A * A = A + (2 : ℝ) • (1 : Mat)) :
    (unitWeylProjection A).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (unitWeylProjection A)
  rw [(unitWeylProjection_symmetric A hs).eq,
    (unitWeylProjection_idempotent A hp).eq] at h
  exact h

theorem unitWeyl_upper_posSemidef (A : Mat) (hs : symmetric A)
    (hp : A * A = A + (2 : ℝ) • (1 : Mat)) :
    ((2 : ℝ) • (1 : Mat) - A).PosSemidef := by
  let P := unitWeylProjection A
  have hP : P.IsHermitian := unitWeylProjection_symmetric A hs
  have hQ : (1 - P : Mat).IsHermitian := Matrix.isHermitian_one.sub hP
  have hid : IsIdempotentElem (1 - P) := (unitWeylProjection_idempotent A hp).one_sub
  have h := Matrix.posSemidef_conjTranspose_mul_self (1 - P)
  rw [hQ.eq, hid.eq] at h
  have h' := h.smul (show (0 : ℝ) ≤ 3 by norm_num)
  convert h' using 1
  ext i j
  simp only [P, unitWeylProjection, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.add_apply, smul_eq_mul]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual parallel transport around an oriented closed four-dimensional
geodesic fixes a nonzero normal vector. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

omit [PreconnectedSpace M] in
theorem closed_geodesic_fixed_normal (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (T : ℝ)
    (hclosed : unitTangentOfFrame (parallelFrameFlowMap g 0 T e) = unitTangentOfFrame e) :
    ∃ a : Fin 3 → ℝ, a ≠ 0 ∧
      (parallelFrameFlowMap g 0 T e).frame.map (WithLp.toLp 2 (Fin.cons 0 a)) =
        e.frame.map (WithLp.toLp 2 (Fin.cons 0 a)) := by
  let E := parallelFrameFlowMap g 0 T e
  have hbase : e.base = E.base := (congrArg UnitTangentBundle.base hclosed).symm
  have hvec : E.frame.vector 0 = e.frame.vector 0 := congrArg UnitTangentBundle.vector hclosed
  obtain ⟨Q,hQ⟩ := positive_frames_relative_rotation g o e E he
    (parallelFrameFlowMap_positive g o e he T) hbase
  have hfirst : ∀ i, Q.val i 0 = (1 : Mat4) i 0 := by
    have h := hvec
    rw [← hQ,← (e.rotate (orientedToOrthogonal Q)).frame.map_coordinateVector,
      frameRotate_map,← e.frame.map_coordinateVector] at h
    have hh := e.frame.map_injective h
    have hc (i : Fin 4) := congrArg (fun v : FourSpace => v i) hh
    intro i
    have hi := hc i
    change (Q.val *ᵥ WithLp.ofLp (coordinateVector 0)) i = (coordinateVector 0 : FourSpace) i at hi
    simpa [coordinateVector,Matrix.mulVec,dotProduct,Matrix.one_apply,eq_comm] using hi
  obtain ⟨a,ha,hfixed⟩ := oriented_four_fixed_normal Q hfirst
  refine ⟨a,ha,?_⟩
  change E.frame.map (WithLp.toLp 2 (Fin.cons 0 a)) =
    e.frame.map (WithLp.toLp 2 (Fin.cons 0 a))
  rw [← hQ,frameRotate_map]
  apply congrArg e.frame.map
  apply WithLp.ofLp_injective
  exact hfixed

end
end PositiveEinsteinFour.Geometry
end


section

/-! The curvature operator is at most three on self-dual forms when the
remaining Weyl block is bounded above by two. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Matrix TraceHessian
open scoped BigOperators
noncomputable section

theorem halfFlat_curvature_matrix_positive (T : Mat) (a : TwoFormFour)
    (ha : twoFormHodge a = a) :
    twoFormMatrixMul (twoFormCurvatureMatrix (fun v =>
      einsteinCurvatureTensor T 0 (v 0) (v 1) (v 2) (v 3))) a =
      WithLp.toLp 2 ![((1 + T) *ᵥ ![a 0,a 1,a 2]) 0,
        ((1 + T) *ᵥ ![a 0,a 1,a 2]) 1, ((1 + T) *ᵥ ![a 0,a 1,a 2]) 2,
        ((1 + T) *ᵥ ![a 0,a 1,a 2]) 2, -((1 + T) *ᵥ ![a 0,a 1,a 2]) 1,
        ((1 + T) *ᵥ ![a 0,a 1,a 2]) 0] := by
  have h3 : a 3 = a 2 := congrArg (fun v : TwoFormFour => v 2) ha
  have h4 : a 4 = -a 1 := by
    have h := congrArg (fun v : TwoFormFour => v 1) ha
    change -a 4 = a 1 at h
    linarith
  have h5 : a 5 = a 0 := congrArg (fun v : TwoFormFour => v 0) ha
  ext i
  fin_cases i <;>
    simp [twoFormMatrixMul, twoFormCurvatureMatrix, einsteinCurvatureTensor,
      blockTensor, twoFormProduct, quaternionMatrix, oppositeMatrix, oppositeQuaternion,
      AlgebraicCurvature.pair, Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.one_apply,
      Fin.sum_univ_succ, h3, h4, h5] <;> ring

theorem halfFlat_curvature_matrix_bound (T : Mat)
    (hT : ((2 : ℝ) • (1 : Mat) - T).PosSemidef)
    (a : TwoFormFour) (ha : twoFormHodge a = a) :
    inner ℝ a (twoFormMatrixMul (twoFormCurvatureMatrix (fun v =>
      einsteinCurvatureTensor T 0 (v 0) (v 1) (v 2) (v 3))) a) ≤
        3 * inner ℝ a a := by
  rw [halfFlat_curvature_matrix_positive T a ha]
  have h3 : a 3 = a 2 := congrArg (fun v : TwoFormFour => v 2) ha
  have h4 : a 4 = -a 1 := by
    have h := congrArg (fun v : TwoFormFour => v 1) ha
    change -a 4 = a 1 at h
    linarith
  have h5 : a 5 = a 0 := congrArg (fun v : TwoFormFour => v 0) ha
  have h := hT.dotProduct_mulVec_nonneg ![a 0,a 1,a 2]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, star_trivial] at h
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp [Fin.sum_univ_succ, h3, h4, h5, Matrix.mulVec, dotProduct,
    Matrix.add_apply, Matrix.one_apply]
  nlinarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! The refined radial estimate in the manuscript's unit-interval variable. -/
namespace PositiveEinsteinFour.VolumeConstants
noncomputable section

theorem lowerVolumeKernel_rescale {u : ℝ} (hu : u ≠ 0) :
    lowerVolumeKernel u =
      (2 * (Real.pi / Real.sqrt 3)) *
        (((Real.pi / Real.sqrt 3) * u) ^ 3 *
          (Real.sin (Real.pi * u) / (Real.pi * u)) *
          (1 + (u ^ 4 / 2 + u ^ 6 / 3) / 6)) := by
  have hs : Real.sqrt 3 ^ 4 = 9 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, Real.sq_sqrt (by norm_num)]
    norm_num
  unfold lowerVolumeKernel lowerKernel
  field_simp [hu, Real.pi_ne_zero, ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))]
  rw [hs]
  ring

end
end PositiveEinsteinFour.VolumeConstants

namespace PositiveEinsteinFour.Geometry
open EinsteinFour Jacobi Matrix MeasureTheory VolumeConstants
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

theorem actual_scaled_jacobi_lower (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    (hE : (∫ x, plusNorm o x ^ 2 + minusNorm o x ^ 2 ∂normalizedVolume g) = 3)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    lowerVolumeKernel u ≤ (2 * (Real.pi / Real.sqrt 3)) *
      ∫ e, (actualRegularJacobi g hRic e ((Real.pi / Real.sqrt 3) * u)).truncatedDensity
        ∂canonicalFrameMeasure g o := by
  have hR : 0 < Real.pi / Real.sqrt 3 := div_pos Real.pi_pos (Real.sqrt_pos.mpr (by norm_num))
  have ht : 0 < (Real.pi / Real.sqrt 3) * u := mul_pos hR hu
  have htop : (Real.pi / Real.sqrt 3) * u < Real.pi / Real.sqrt 3 := by
    nlinarith
  have heθ : Real.sqrt 3 * ((Real.pi / Real.sqrt 3) * u) = Real.pi * u := by
    field_simp
  have hediv : (Real.pi * u) / Real.pi = u := by field_simp
  have h := mul_le_mul_of_nonneg_left
    (actual_jacobi_average_lower_refined g o hRic hpositive hE ht htop)
    (by positivity : 0 ≤ 2 * (Real.pi / Real.sqrt 3))
  rw [heθ, hediv, ← lowerVolumeKernel_rescale hu.ne'] at h
  convert h using 1
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun e =>
    actualJacobi_truncated_eq_det_below_sqrt_three g hRic hpositive e ht htop

end
end PositiveEinsteinFour.Geometry
end


section

/-! Equality in the actual polar volume formula rules out all early cut
points. Upper semicontinuity upgrades the almost-everywhere conclusion to
all directions, using the full support of the actual sphere measure. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem round_cut_time_all_directions (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (q : Directions) :
    actualCutTime g (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) = Real.pi := by
  let : IsProbabilityMeasure sphereMeasure := actual_sphereMeasure_probability
  let : Measure.IsOpenPosMeasure sphereMeasure := sphereMeasure_openPos
  let R := fun q : Directions => e.rotate (orientedToOrthogonal (directionOrientedMatrix q))
  let F := fun q : Directions => roundRadialMass (actualCutTime g (R q))
  let K := roundRadialMass Real.pi
  have hK : K = ENNReal.ofReal (4 / 3 : ℝ) := roundRadialMass_pi
  have hKfin : K ≠ ⊤ := hK ▸ ENNReal.ofReal_ne_top
  have hle (q : Directions) : F q ≤ K :=
    roundRadialMass_le_pi _ (actualCutTime_le_pi g hRic _)
  have hupper : (∫⁻ q, F q ∂sphereMeasure) ≤ K := by
    calc
      _ ≤ ∫⁻ _q : Directions, K ∂sphereMeasure := lintegral_mono hle
      _ = K := by simp
  have hlower : K ≤ ∫⁻ q, F q ∂sphereMeasure := by
    have h := round_volume_le_cut_mass hRic hplus hminus e he
    rw [round_volumeMeasure hRic hpositive hplus hminus] at h
    have hfactor : ENNReal.ofReal (8 * Real.pi ^ 2 / 3) =
        ENNReal.ofReal (2 * Real.pi ^ 2) * K := by
      rw [hK, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    rw [hfactor] at h
    have hk := ENNReal.toReal_pos_iff.mp riemannianChartFactor_toReal_pos
    have hcancel := (ENNReal.mul_le_mul_iff_right hk.1.ne' hk.2.ne).mp h
    exact (ENNReal.mul_le_mul_iff_right (by positivity : ENNReal.ofReal (2 * Real.pi ^ 2) ≠ 0)
      ENNReal.ofReal_ne_top).mp hcancel
  have hInt : (∫⁻ q, F q ∂sphereMeasure) = K := le_antisymm hupper hlower
  have hae : F =ᵐ[sphereMeasure] (fun _ => K) := by
    apply (lintegral_eq_iff_ae_eq_of_ae_le (hInt ▸ hKfin) aemeasurable_const
      (Filter.Eventually.of_forall hle)).mp
    simpa using hInt
  have haec : ∀ᵐ q : Directions ∂sphereMeasure, Real.pi ≤ actualCutTime g (R q) := by
    filter_upwards [hae] with q hq
    by_contra hn
    have hr : R q ∈ o.positive := frameRotate_oriented_positive o e he (directionOrientedMatrix q)
    exact (roundRadialMass_lt_pi _ ⟨(actualCutTime_pos g o hRic (R q) hr).le,
      lt_of_not_ge hn⟩).ne hq
  have hR : Continuous R := (continuous_frameRotate g).comp
    (continuous_const.prodMk (continuous_orientedToOrthogonal.comp continuous_directionOrientedMatrix))
  have hclosed : IsClosed {q : Directions | Real.pi ≤ actualCutTime g (R q)} :=
    ((actualCutTime_upperSemicontinuous g).isClosed_preimage Real.pi).preimage hR
  have hdense := Measure.dense_of_ae haec
  have hall : {q : Directions | Real.pi ≤ actualCutTime g (R q)} = univ := by
    rw [← hclosed.closure_eq, hdense.closure_eq]
  apply le_antisymm (actualCutTime_le_pi g hRic _)
  have hq : q ∈ {q : Directions | Real.pi ≤ actualCutTime g (R q)} := by rw [hall]; exact mem_univ q
  exact hq

end
end PositiveEinsteinFour.Geometry
end


section

/-! Vanishing angular derivatives imply that every radial geodesic in the
round branch reaches the same point at time pi. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

def roundBoundaryEndpoint (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (v : FourSpace) : M :=
  frameExponential g o e (roundBoundaryProjection v)

theorem roundBoundaryEndpoint_chart_derivative_zero (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace) (hv : v ≠ 0) (c : M)
    (hc : roundBoundaryEndpoint g o e v ∈ (chartAt FourSpace c).source) :
    HasFDerivAt (fun z => chartAt FourSpace c (roundBoundaryEndpoint g o e z))
      (0 : FourSpace →L[ℝ] FourSpace) v := by
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
  have hq : roundBoundaryProjection v = Real.pi • q.val := rfl
  have hF := (frameExponential_chart_contDiffAt g o c e (roundBoundaryProjection v) hc).differentiableAt
    one_ne_zero
  have hcomp := hF.hasFDerivAt.comp v (roundBoundaryProjection_differentiableAt v hv).hasFDerivAt
  have hzero : (fderiv ℝ (fun z : FourSpace => chartAt FourSpace c (frameExponential g o e z))
      (roundBoundaryProjection v)).comp (fderiv ℝ roundBoundaryProjection v) = 0 := by
    apply ContinuousLinearMap.ext
    intro w
    change fderiv ℝ (fun z : FourSpace => chartAt FourSpace c (frameExponential g o e z))
      (roundBoundaryProjection v) (fderiv ℝ roundBoundaryProjection v w) = 0
    rw [hq]
    apply frameExponential_pi_angular_derivative_zero hRic hplus hminus e he q c
      (by rwa [← hq])
    exact roundBoundaryProjection_derivative_tangent v hv w
  rw [hzero] at hcomp
  exact hcomp

theorem frameExponential_pi_independent_direction (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (q p : Directions) :
    frameExponential g o e (Real.pi • q.val) =
      frameExponential g o e (Real.pi • p.val) := by
  let U : Set FourSpace := {0}ᶜ
  have hPr : ContinuousOn roundBoundaryProjection U :=
    fun v hv => (roundBoundaryProjection_differentiableAt v hv).continuousAt.continuousWithinAt
  have hF : ContinuousOn (roundBoundaryEndpoint g o e) U :=
    (frameExponential_continuous g o e).comp_continuousOn hPr
  have hLC := zero_chart_derivative_locally_constant (roundBoundaryEndpoint g o e) U
    isOpen_compl_singleton hF
    (fun v hv c hc => roundBoundaryEndpoint_chart_derivative_zero hRic hplus hminus e he v hv c hc)
  have hrank : 1 < Module.rank ℝ FourSpace := by
    rw [← Module.finrank_eq_rank]
    norm_num [FourSpace]
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp
    (isConnected_compl_singleton_of_one_lt_rank hrank (0 : FourSpace)).isPreconnected
  have hq : q.val ≠ 0 := by
    intro hz
    have h := q.property
    rw [hz, norm_zero] at h
    norm_num at h
  have hp : p.val ≠ 0 := by
    intro hz
    have h := p.property
    rw [hz, norm_zero] at h
    norm_num at h
  have h := hLC.apply_eq_of_preconnectedSpace ⟨q.val, hq⟩ ⟨p.val, hp⟩
  simpa only [roundBoundaryEndpoint, roundBoundaryProjection, q.property, p.property,
    inv_one, one_smul] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The full radial/tangential metric formula of the actual exponential
in the constant-curvature branch. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Jacobi Angular
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem round_block_pairing (a : ℝ) (w z : FourSpace) :
    WithLp.ofLp w ⬝ᵥ (jacobiBlockMatrix 1 (a ^ 2 • (1 : NormalMatrix)) *ᵥ WithLp.ofLp z) =
      a ^ 2 * inner ℝ w z + (1 - a ^ 2) * w 0 * z 0 := by
  rw [jacobiBlockMatrix_mulVec]
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, one_mul]
  simp only [dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Pi.smul_apply, smul_eq_mul, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial]
  simp only [Finset.univ_eq_empty, Finset.sum_empty]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_round_first_pairing (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t) (w z : FourSpace) :
    g.inner (frameExponential g o e (t • coordinateVector 0))
      (mfderiv I4 I4 (frameExponential g o e) (t • coordinateVector 0) w)
      (mfderiv I4 I4 (frameExponential g o e) (t • coordinateVector 0) z) =
        (Real.sin t / t) ^ 2 * inner ℝ w z +
          (1 - (Real.sin t / t) ^ 2) * w 0 * z 0 := by
  have hp := heatNormalMetric_pairing g o e (t • coordinateVector 0)
    (WithLp.ofLp w) (WithLp.ofLp z)
  simp only [WithLp.toLp_ofLp] at hp
  rw [← hp, heatNormalMetric_first_of_weyl_zero hRic hplus hminus e he t ht]
  exact round_block_pairing _ w z

theorem frameExponential_round_pairing (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (q : Directions)
    (t : ℝ) (ht : 0 < t) (w z : FourSpace) :
    g.inner (frameExponential g o e (t • q.val))
      (mfderiv I4 I4 (frameExponential g o e) (t • q.val) w)
      (mfderiv I4 I4 (frameExponential g o e) (t • q.val) z) =
        (Real.sin t / t) ^ 2 * inner ℝ w z +
          (1 - (Real.sin t / t) ^ 2) * inner ℝ q.val w * inner ℝ q.val z := by
  let Q := directionOrientedMatrix q
  let L := orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
    (orientedToOrthogonal Q).property
  let f := e.rotate (orientedToOrthogonal Q)
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he Q
  have hfirst : L (coordinateVector 0) = q.val := directionRotation_first q
  have hpoint : L (t • coordinateVector 0) = t • q.val := by rw [map_smul, hfirst]
  have hbase : frameExponential g o f (t • coordinateVector 0) =
      frameExponential g o e (t • q.val) := by
    rw [frameExponential_rotate]
    exact congrArg (frameExponential g o e) hpoint
  have hD (u : FourSpace) :
      mfderiv I4 I4 (frameExponential g o f) (t • coordinateVector 0) u =
        mfderiv I4 I4 (frameExponential g o e) (t • q.val) (L u) := by
    have h := frameExponential_rotate_mfderiv g o e Q (t • coordinateVector 0) u
    change _ = mfderiv I4 I4 (frameExponential g o e) (L (t • coordinateVector 0)) (L u) at h
    rwa [hpoint] at h
  have hzero (u : FourSpace) : (L.symm u) 0 = inner ℝ q.val u := by
    have h := L.inner_map_map (coordinateVector 0) (L.symm u)
    rw [hfirst, L.apply_symm_apply] at h
    simpa [PiLp.inner_apply, coordinateVector] using h.symm
  have hinner : inner ℝ (L.symm w) (L.symm z) = inner ℝ w z := by
    simpa only [L.apply_symm_apply] using
      (L.inner_map_map (L.symm w) (L.symm z)).symm
  have h := frameExponential_round_first_pairing hRic hplus hminus f hf t ht
    (L.symm w) (L.symm z)
  let B₁ : FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ :=
    g.inner (frameExponential g o f (t • coordinateVector 0))
  let B₂ : FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ :=
    g.inner (frameExponential g o e (t • q.val))
  let D₁ : FourSpace →L[ℝ] FourSpace :=
    mfderiv I4 I4 (frameExponential g o f) (t • coordinateVector 0)
  let D₂ : FourSpace →L[ℝ] FourSpace :=
    mfderiv I4 I4 (frameExponential g o e) (t • q.val)
  have hB : B₁ = B₂ := by
    dsimp only [B₁, B₂]
    rw [hbase]
  have hD' (u : FourSpace) : D₁ u = D₂ (L u) := hD u
  change B₁ (D₁ (L.symm w)) (D₁ (L.symm z)) = _ at h
  change B₂ (D₂ w) (D₂ z) = _
  rw [hB, hD', hD', L.apply_symm_apply, L.apply_symm_apply, hinner,
    hzero, hzero] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The differential bound for angular distance along a genuine sphere
curve. The two singular values are explicit. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped RealInnerProductSpace
noncomputable section

theorem round_inner_ne_endpoints (p q : RoundSphere4) (hpq : q ≠ p)
    (hanti : q ≠ antipode p) :
    inner ℝ p.val q.val ≠ -1 ∧ inner ℝ p.val q.val ≠ 1 := by
  constructor
  · intro h
    have heq := (inner_eq_neg_one_iff_of_norm_eq_one p.property q.property).mp h
    apply hanti
    apply Subtype.ext
    change q.val = -p.val
    simpa using congrArg Neg.neg heq.symm
  · intro h
    have heq := (inner_eq_one_iff_of_norm_eq_one p.property q.property).mp h
    exact hpq (Subtype.ext heq.symm)

theorem round_curve_tangent {u : ℝ → RoundSphere4} {t : ℝ}
    {w : EuclideanSpace ℝ (Fin 5)}
    (hu : HasDerivAt (fun s => (u s).val) w t) :
    inner ℝ (u t).val w = 0 := by
  have h := hu.inner ℝ hu
  have heq : (fun s => inner ℝ (u s).val (u s).val) = fun _ : ℝ => (1 : ℝ) := by
    funext s
    simp [(u s).property]
  rw [heq] at h
  have hz := h.unique (hasDerivAt_const t (1 : ℝ))
  rw [real_inner_comm (u t).val w] at hz
  linarith

theorem roundDistance_derivative_bound (p : RoundSphere4) {u : ℝ → RoundSphere4}
    {t : ℝ} {w : EuclideanSpace ℝ (Fin 5)}
    (hu : HasDerivAt (fun s => (u s).val) w t)
    (hpq : u t ≠ p) (hanti : u t ≠ antipode p) :
    DifferentiableAt ℝ (fun s => roundDistance p (u s)) t ∧
      |deriv (fun s => roundDistance p (u s)) t| ≤ ‖w‖ := by
  obtain ⟨hm, hp⟩ := round_inner_ne_endpoints p (u t) hpq hanti
  have hd := (Real.hasDerivAt_arccos hm hp).comp t
    ((hasDerivAt_const t p.val).inner ℝ hu)
  have hsin : 0 < Real.sin (roundDistance p (u t)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact lt_of_le_of_ne (roundDistance_nonneg _ _)
        (fun h => hpq ((roundDistance_eq_zero_iff _ _).mp h.symm).symm)
    · apply lt_of_le_of_ne (roundDistance_le_pi _ _)
      intro h
      have hc := cos_roundDistance p (u t)
      rw [h, Real.cos_pi] at hc
      exact hm hc.symm
  have hsqrt : Real.sqrt (1 - inner ℝ p.val (u t).val ^ 2) =
      Real.sin (roundDistance p (u t)) := by
    rw [roundDistance, Real.sin_arccos]
  have hform : deriv (fun s => roundDistance p (u s)) t =
      -(inner ℝ p.val w / Real.sin (roundDistance p (u t))) := by
    change deriv (fun s => Real.arccos (inner ℝ p.val (u s).val)) t = _
    change deriv (Real.arccos ∘ fun s => inner ℝ p.val (u s).val) t = _
    rw [hd.deriv]
    simp only [inner_zero_left, hsqrt]
    ring
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hform, abs_neg, abs_div, abs_of_pos hsin]
  exact (div_le_iff₀ hsin).mpr (by
    simpa only [mul_comm] using round_tangent_pairing_bound p (u t) w (round_curve_tangent hu))

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous manifold curve with zero derivative in each chart is
constant. Only the one-dimensional statement needed for boundary circles. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Metric Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem zero_chart_curve_constant (F : ℝ → M) (hF : Continuous F)
    (hD : ∀ t (c : M), F t ∈ (chartAt FourSpace c).source →
      HasDerivAt (fun s => chartAt FourSpace c (F s)) (0 : FourSpace) t)
    (s t : ℝ) : F s = F t := by
  have hLC : IsLocallyConstant F := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro x
    let c := F x
    have hc : F x ∈ (chartAt FourSpace c).source := mem_chart_source FourSpace c
    have hn : F ⁻¹' (chartAt FourSpace c).source ∈ 𝓝 x :=
      hF.continuousAt.preimage_mem_nhds ((chartAt FourSpace c).open_source.mem_nhds hc)
    obtain ⟨r,hr,hb⟩ := Metric.mem_nhds_iff.mp hn
    have heq (y : ℝ) (hy : y ∈ ball x r) : chartAt FourSpace c (F y) = chartAt FourSpace c (F x) := by
      exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball x r).isPreconnected
        (fun z hz => (hD z c (hb hz)).differentiableAt.differentiableWithinAt)
        (fun z hz => (hD z c (hb hz)).deriv) hy (mem_ball_self hr)
    filter_upwards [ball_mem_nhds x hr] with y hy
    exact (chartAt FourSpace c).injOn (hb hy) hc (heq y hy)
  exact hLC.apply_eq_of_preconnectedSpace s t

end
end PositiveEinsteinFour.Geometry
end


section

/-! In the unit-Weyl branch, actual self-dual harmonic forms are parallel.
The conclusion is derived from the global Bochner identity. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Matrix TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance parallelHarmonicAddGroup : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _
local instance parallelPositiveAddGroup (hRic : RicciThree g) :
    AddCommGroup (smoothHarmonicPositive (o := o) hRic) := Submodule.addCommGroup _

theorem halfFlat_unit_curvature_bound (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1) (x : M)
    (a : TwoFormFour) (ha : twoFormHodge a = a) :
    inner ℝ a (twoFormCurvatureAction (twoFormMetricCurvatureTensor g ⟨x,o.frame x⟩) a) ≤
      3 * inner ℝ a a := by
  let e : FrameBundle g := ⟨x,o.frame x⟩
  have hlast : ∀ i j k l, twoFormMetricCurvatureTensor g e ![i,j,l,k] =
      -twoFormMetricCurvatureTensor g e ![i,j,k,l] := by
    intro i j k l
    simp only [twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    exact frame_algebraic_lastSkew e.frame i j k l
  have heq : twoFormMetricCurvatureTensor g e = fun v =>
      einsteinCurvatureTensor (plusWeyl g x (o.frame x)) 0 (v 0) (v 1) (v 2) (v 3) := by
    funext v
    have hv : v = ![v 0,v 1,v 2,v 3] := by ext i; fin_cases i <;> rfl
    rw [hv]
    simp only [twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    rw [actual_einstein_decomposition e.frame hRic]
    rw [show minusWeyl g e.base e.frame = 0 from hminus x]
    rfl
  rw [← twoFormCurvatureMatrix_apply _ hlast, heq]
  exact halfFlat_curvature_matrix_bound _
    (unitWeyl_upper_posSemidef _ (actual_weyl_symmetric (o.frame x)).1
      (actual_unit_weyl_polynomial hRic hnorm e (o.frame_positive x))) a ha

theorem halfFlat_positive_harmonic_covariantEnergy_zero (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1) (u : smoothHarmonicPositive (o := o) hRic) :
    smoothTwoFormCovariantEnergy u.val.val u.val.val = 0 := by
  have hstar (x : M) : twoFormHodge (u.val.val.val x) = u.val.val.val x :=
    congrArg (fun v : smoothHarmonicTwoForms (o := o) => v.val.val x)
      (smoothHarmonicPositive_star hRic u)
  have hC : smoothTwoFormL2Inner (smoothTwoFormCurvature u.val.val) u.val.val ≤
      3 * smoothTwoFormL2Inner u.val.val u.val.val := by
    rw [smoothTwoFormL2Inner, smoothTwoFormL2Inner, ← integral_const_mul]
    apply integral_mono (smoothTwoForm_pairing_integrable _ _)
      ((smoothTwoForm_pairing_integrable u.val.val u.val.val).const_mul 3)
    intro x
    change inner ℝ (twoFormCurvatureAction (twoFormMetricCurvatureTensor g ⟨x,o.frame x⟩)
      (u.val.val.val x)) (u.val.val.val x) ≤ 3 * inner ℝ (u.val.val.val x) (u.val.val.val x)
    rw [real_inner_comm]
    exact halfFlat_unit_curvature_bound hRic hminus hnorm x _ (hstar x)
  have hE := smoothTwoForm_Weitzenbock hRic u.val.val
  rw [smoothHarmonicTwoForm_energy_zero u.val.val u.val.property] at hE
  have hnonneg := smoothTwoFormCovariantEnergy_nonneg u.val.val
  linarith

theorem smoothTwoForm_covariantDerivative_zero_of_energy_zero (u : smoothTwoForms o)
    (hzero : smoothTwoFormCovariantEnergy u u = 0) (x : M) :
    twoFormFramedCovariantDerivative o u.val ⟨x,o.frame x⟩ = 0 := by
  let := normalizedVolume_isOpenPosMeasure g
  have hc := u.property.covariantPairing_continuous u.property
  have hi := smoothTwoFormCovariantPairing_integrable u u
  have hae : twoFormCovariantPairing o u.val u.val =ᵐ[normalizedVolume g] 0 :=
    (integral_eq_zero_iff_of_nonneg (twoFormCovariantPairing_self_nonneg o u.val) hi).mp hzero
  have heq : twoFormCovariantPairing o u.val u.val = 0 :=
    Measure.eq_of_ae_eq hae hc continuous_const
  have hx := congrFun heq x
  change (1 / 2 : ℝ) * ∑ a, (twoFormFramedCovariantDerivative o u.val ⟨x,o.frame x⟩ a) *
    (twoFormFramedCovariantDerivative o u.val ⟨x,o.frame x⟩ a) = 0 at hx
  ext a
  have hle : (twoFormFramedCovariantDerivative o u.val ⟨x,o.frame x⟩ a) *
      (twoFormFramedCovariantDerivative o u.val ⟨x,o.frame x⟩ a) ≤
      ∑ b, (twoFormFramedCovariantDerivative o u.val ⟨x,o.frame x⟩ b) *
        (twoFormFramedCovariantDerivative o u.val ⟨x,o.frame x⟩ b) :=
    Finset.single_le_sum (fun b _ => mul_self_nonneg _) (Finset.mem_univ a)
  change twoFormFramedCovariantDerivative o u.val ⟨x,o.frame x⟩ a = 0
  nlinarith

theorem halfFlat_positive_harmonic_parallel (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1) (u : smoothHarmonicPositive (o := o) hRic) (x : M) :
    twoFormFramedCovariantDerivative o u.val.val.val ⟨x,o.frame x⟩ = 0 :=
  smoothTwoForm_covariantDerivative_zero_of_energy_zero u.val.val
    (halfFlat_positive_harmonic_covariantEnergy_zero hRic hminus hnorm u) x

end
end PositiveEinsteinFour.Geometry
end


section

/-! The round-sphere covering map, with its polar values
and surjectivity supplied by global exponential coverage. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped BigOperators Manifold ContDiff _root_.Topology
noncomputable section

def roundLog (p : RoundSphere4) : FourSpace :=
  if roundTail p = 0 then Real.arccos (p.val 0) • coordinateVector 0
  else (Real.arccos (p.val 0) / ‖roundTail p‖) • roundTail p

theorem roundTail_polar (t : ℝ) (q : Directions) :
    roundTail (roundPolarPoint t q) = Real.sin t • q.val := by
  ext i
  rfl

theorem roundLog_polar_interior (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) Real.pi) (q : Directions) :
    roundLog (roundPolarPoint t q) = t • q.val := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have hn : roundTail (roundPolarPoint t q) ≠ 0 := by
    rw [roundTail_polar]
    exact smul_ne_zero hs.ne' (unitSphere_ne_zero q)
  rw [roundLog, ite_eq_right hn, roundPolarPoint_first, Real.arccos_cos ht.1.le ht.2.le,
    roundTail_polar, norm_smul, Real.norm_eq_abs, abs_of_pos hs, q.property, mul_one,
    smul_smul, div_mul_cancel₀ _ hs.ne']

theorem roundLog_polar_zero (q : Directions) : roundLog (roundPolarPoint 0 q) = 0 := by
  rw [roundLog, roundTail_polar, Real.sin_zero, zero_smul, ite_eq_left rfl,
    roundPolarPoint_first, Real.cos_zero, Real.arccos_one, zero_smul]

theorem roundLog_polar_pi (q : Directions) :
    roundLog (roundPolarPoint Real.pi q) = Real.pi • coordinateVector 0 := by
  rw [roundLog, roundTail_polar, Real.sin_pi, zero_smul, ite_eq_left rfl,
    roundPolarPoint_first, Real.cos_pi, Real.arccos_neg_one]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

def roundSphereMap (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (p : RoundSphere4) : M := frameExponential g o e (roundLog p)

theorem roundSphereMap_polar (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) Real.pi) (q : Directions) :
    roundSphereMap g o e (roundPolarPoint t q) = frameExponential g o e (t • q.val) := by
  unfold roundSphereMap
  by_cases h0 : t = 0
  · subst t
    rw [roundLog_polar_zero, zero_smul]
  by_cases hπ : t = Real.pi
  · subst t
    rw [roundLog_polar_pi]
    exact frameExponential_pi_independent_direction hRic hplus hminus e he firstDirection q
  · rw [roundLog_polar_interior t ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 hπ⟩]

variable [PreconnectedSpace M]

theorem roundSphereMap_surjective (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    Function.Surjective (roundSphereMap g o e) := by
  intro x
  obtain ⟨v, hv, hlen⟩ := frameExponential_global_minimizing g o hRic e he x
  by_cases hz : v = 0
  · refine ⟨roundPolarPoint 0 firstDirection, ?_⟩
    rw [roundSphereMap_polar hRic hplus hminus e he 0 ⟨le_rfl, Real.pi_pos.le⟩,
      zero_smul, ← hz, hv]
  · let q : Directions := ⟨‖v‖⁻¹ • v, by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
    have hvq : ‖v‖ • q.val = v := by
      change ‖v‖ • (‖v‖⁻¹ • v) = v
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
    have hmin : ‖v‖ • q.val ∈ actualMinimizingTangentDomain g o e := by
      rw [hvq]
      change metricDistance g e.base (frameExponential g o e v) = ‖v‖
      rw [hv, hlen]
    have hc := (actualMinimizingTangentDomain_ray_iff g o e he q ‖v‖ (norm_nonneg v)).mp hmin
    have hπ : ‖v‖ ≤ Real.pi := hc.trans
      (actualCutTime_le_pi g hRic (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))))
    refine ⟨roundPolarPoint ‖v‖ q, ?_⟩
    rw [roundSphereMap_polar hRic hplus hminus e he ‖v‖ ⟨(norm_nonneg v), hπ⟩, hvq, hv]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Equal vectors transported along the same actual oriented geodesic
remain equal, even when represented in different parallel frames. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem parallelFrameFlow_vector_eq (g : SmoothMetric M) (o : FrameOrientation g)
    (e f : FrameBundle g) (he : e ∈ o.positive) (hf : f ∈ o.positive)
    (hstate : unitTangentOfFrame e = unitTangentOfFrame f)
    (a b : FourSpace) (hab : e.frame.map a = f.frame.map b) (t : ℝ) :
    (parallelFrameFlowMap g 0 t e).frame.map a =
      (parallelFrameFlowMap g 0 t f).frame.map b := by
  have hbase : e.base = f.base := congrArg UnitTangentBundle.base hstate
  have hvec : e.frame.vector 0 = f.frame.vector 0 := congrArg UnitTangentBundle.vector hstate
  obtain ⟨Q,hQ⟩ := positive_frames_relative_rotation g o e f he hf hbase
  have hfirst : ∀ i, Q.val i 0 = (1 : Mat4) i 0 := by
    have h := hvec.symm
    rw [← hQ,← (e.rotate (orientedToOrthogonal Q)).frame.map_coordinateVector,
      frameRotate_map,← e.frame.map_coordinateVector] at h
    have hh := e.frame.map_injective h
    intro i
    have hi := congrArg (fun v : FourSpace => v i) hh
    change (Q.val *ᵥ WithLp.ofLp (coordinateVector 0)) i = (coordinateVector 0 : FourSpace) i at hi
    simpa [coordinateVector,Matrix.mulVec,dotProduct,Matrix.one_apply,eq_comm] using hi
  have hc : a = orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
      (orientedToOrthogonal Q).property b := by
    apply e.frame.map_injective
    rw [← hQ,frameRotate_map] at hab
    exact hab
  have hflow : parallelFrameFlowMap g 0 t f =
      (parallelFrameFlowMap g 0 t e).rotate (orientedToOrthogonal Q) := by
    rw [← hQ]
    exact (parallelFrameFlowMap_rotate g 0 (orientedToOrthogonal Q) hfirst t e).symm
  rw [hflow,frameRotate_map,← hc]

omit [T3Space M] [CompactSpace M] in
theorem frameAntipode_map (g : SmoothMetric M) (e : FrameBundle g) (v : FourSpace) :
    (frameAntipode g e).frame.map v = -e.frame.map v := by
  rw [frameAntipode,frameRotate_map]
  have hv : orthogonalEuclideanIsometry (orientedToOrthogonal reverseFrameRotation).val
      (orientedToOrthogonal reverseFrameRotation).property v = -v := by
    apply WithLp.ofLp_injective
    change (orientedToOrthogonal reverseFrameRotation).val *ᵥ WithLp.ofLp v = WithLp.ofLp (-v)
    rw [reverseFrameRotation_matrix,Matrix.neg_mulVec,Matrix.one_mulVec]
    rfl
  rw [hv,map_neg]

theorem closed_geodesic_normal_midpoint (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (a : FourSpace)
    (hclosed : unitTangentOfFrame (parallelFrameFlowMap g 0 (2*t) e) = unitTangentOfFrame e)
    (hfixed : (parallelFrameFlowMap g 0 (2*t) e).frame.map a = e.frame.map a) :
    (parallelFrameFlowMap g 0 t (frameAntipode g e)).frame.map (-a) =
      (parallelFrameFlowMap g 0 t e).frame.map a := by
  have hh := parallelFrameFlow_vector_eq g o (parallelFrameFlowMap g 0 (2*t) e) e
    (parallelFrameFlowMap_positive g o e he (2*t)) he hclosed a a hfixed (-t)
  rw [← parallelFrameFlowMap_add,show -t + 2*t = t by ring] at hh
  rw [← parallelFrameFlowMap_antipode,frameAntipode_map,map_neg,neg_neg]
  exact hh.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Angular distance is bounded by the parameter length of a unit-speed
sphere curve, allowing finitely many exceptional parameters. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
noncomputable section

private theorem roundDistance_curve_continuous (p : RoundSphere4) (u : ℝ → RoundSphere4)
    {a b : ℝ} (hu : ContinuousOn u (Icc a b)) :
    ContinuousOn (fun t => roundDistance p (u t)) (Icc a b) := by
  have hv : ContinuousOn (fun t => (u t).val) (Icc a b) :=
    continuous_subtype_val.comp_continuousOn hu
  have hi : ContinuousOn (fun t => inner ℝ p.val (u t).val) (Icc a b) :=
    continuousOn_const.inner hv
  change ContinuousOn (fun t => Real.arccos (inner ℝ p.val (u t).val)) (Icc a b)
  exact Real.continuous_arccos.comp_continuousOn hi

private theorem roundDistance_curve_deriv_bound (p : RoundSphere4) (u : ℝ → RoundSphere4)
    (t : ℝ) (hd : ∃ w : EuclideanSpace ℝ (Fin 5),
      HasDerivAt (fun s => (u s).val) w t ∧ ‖w‖ ≤ 1)
    (hregular : u t ≠ p ∧ u t ≠ antipode p) :
    DifferentiableAt ℝ (fun s => roundDistance p (u s)) t ∧
      deriv (fun s => roundDistance p (u s)) t ≤ 1 := by
  obtain ⟨w, hw, hn⟩ := hd
  obtain ⟨hD, hbound⟩ := roundDistance_derivative_bound p hw hregular.1 hregular.2
  exact ⟨hD, (le_abs_self _).trans (hbound.trans hn)⟩

theorem roundDistance_curve_sub_le (p : RoundSphere4) (u : ℝ → RoundSphere4)
    (a b : ℝ) (hab : a ≤ b) (E : Finset ℝ)
    (hu : ContinuousOn u (Icc a b))
    (hd : ∀ t ∈ Ioo a b, t ∉ E → ∃ w : EuclideanSpace ℝ (Fin 5),
      HasDerivAt (fun s => (u s).val) w t ∧ ‖w‖ ≤ 1)
    (hregular : ∀ t ∈ Ioo a b, t ∉ E → u t ≠ p ∧ u t ≠ antipode p) :
    roundDistance p (u b) - roundDistance p (u a) ≤ b - a := by
  have hc := roundDistance_curve_continuous p u hu
  have hD := fun t ht he => roundDistance_curve_deriv_bound p u t (hd t ht he)
    (hregular t ht he)
  have h := image_sub_le_mul_sub_of_deriv_le_off_finite E hab hc
    (fun t ht he => (hD t ht he).1) (fun t ht he => (hD t ht he).2)
  rwa [one_mul] at h

theorem roundDistance_curve_le (u : ℝ → RoundSphere4)
    (a b : ℝ) (hab : a ≤ b) (E : Finset ℝ)
    (hu : ContinuousOn u (Icc a b))
    (hd : ∀ t ∈ Ioo a b, t ∉ E → ∃ w : EuclideanSpace ℝ (Fin 5),
      HasDerivAt (fun s => (u s).val) w t ∧ ‖w‖ ≤ 1)
    (hregular : ∀ t ∈ Ioo a b, t ∉ E → u t ≠ u a ∧ u t ≠ antipode (u a)) :
    roundDistance (u a) (u b) ≤ b - a := by
  simpa only [roundDistance_self, sub_zero] using
    roundDistance_curve_sub_le (u a) u a b hab E hu hd hregular

end
end PositiveEinsteinFour.Geometry
end


section

/-! The energy-three strict volume refinement, with only the geometric
injectivity bound still explicit. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Jacobi Matrix MeasureTheory VolumeConstants Set Metric Filter
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

theorem strict_lower_volume_of_injective_ball (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    (hE : (∫ x, plusNorm o x ^ 2 + minusNorm o x ^ 2 ∂normalizedVolume g) = 3)
    (hinj : ∀ e ∈ o.positive,
      InjOn (frameExponential g o e) (ball 0 (Real.pi / Real.sqrt 3))) :
    (1 / 2 : ℝ) < volumeRatio g / riemannianChartFactor.toReal := by
  let R : ℝ := Real.pi / Real.sqrt 3
  let F : ℝ → ℝ := fun r => ∫ e, (actualRegularJacobi g hRic e r).truncatedDensity
    ∂canonicalFrameMeasure g o
  have hR : 0 < R := div_pos Real.pi_pos (Real.sqrt_pos.mpr (by norm_num))
  have hFi : IntervalIntegrable F volume 0 R :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hR.le).mpr
      (actualJacobi_average_integrableOn g o hRic 0 R)
  have hFscaled : IntervalIntegrable (fun u => F (R * u)) volume 0 1 := by
    convert hFi.comp_mul_left (c := R) using 1 <;> simp [hR.ne']
  have hkernel : IntervalIntegrable lowerVolumeKernel volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold lowerVolumeKernel lowerKernel
    fun_prop
  have hae : ∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) 1),
      lowerVolumeKernel u ≤ (2 * R) * F (R * u) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne 0), ae_restrict_of_ae (volume.ae_ne 1)] with u hu h0 h1
    exact actual_scaled_jacobi_lower g o hRic hpositive hE
      (lt_of_le_of_ne hu.1 (Ne.symm h0)) (lt_of_le_of_ne hu.2 h1)
  have hi := intervalIntegral.integral_mono_ae_restrict (by norm_num : (0 : ℝ) ≤ 1)
    hkernel (hFscaled.const_mul (2 * R)) hae
  rw [intervalIntegral.integral_const_mul] at hi
  have hchange : (∫ r in (0 : ℝ)..R, F r) = R * ∫ u in (0 : ℝ)..1, F (R * u) := by
    simpa only [smul_eq_mul, mul_zero, mul_one] using
      (intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1) F R).symm
  have hstrict : (4 / 3 : ℝ) < 2 * ∫ r in (0 : ℝ)..R, F r := by
    rw [hchange]
    nlinarith [integral_lowerVolumeKernel_gt]
  have hvol := lower_polar_volume_of_injective_ball g o hRic hpositive hR.le le_rfl hinj
  have hk := riemannianChartFactor_toReal_pos
  have hpi := Real.pi_pos
  have hp2 : 0 < Real.pi ^ 2 := sq_pos_of_pos hpi
  have hnorm : (3 / 4 : ℝ) * (∫ r in (0 : ℝ)..R, F r) ≤
      volumeRatio g / riemannianChartFactor.toReal := by
    rw [volumeRatio, div_div]
    apply (le_div_iff₀ (mul_pos (by positivity : 0 < 8 * Real.pi ^ 2 / 3) hk)).mpr
    convert hvol using 1
    ring
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! A shortest nonconjugate cut loop contradicts the actual two-sided
parallel normal shortening in positive curvature. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

omit [T3Space M] [CompactSpace M] [PreconnectedSpace M] in
theorem normalCoordinates_neg (a : Fin 3 → ℝ) :
    (WithLp.toLp 2 (Fin.cons 0 (-a)) : FourSpace) =
      -(WithLp.toLp 2 (Fin.cons 0 a) : FourSpace) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

omit [PreconnectedSpace M] in
theorem closed_geodesic_antipode_midpoint_base (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ)
    (hclosed : unitTangentOfFrame (parallelFrameFlowMap g 0 (2*t) e) = unitTangentOfFrame e) :
    (parallelFrameFlowMap g 0 t e).base =
      (parallelFrameFlowMap g 0 t (frameAntipode g e)).base := by
  have hh := unitTangentOfFrame_flow_eq g o (parallelFrameFlowMap g 0 (2*t) e) e
    (parallelFrameFlowMap_positive g o e he (2*t)) he hclosed (-t)
  rw [← parallelFrameFlowMap_add,show -t + 2*t = t by ring] at hh
  have hb := congrArg UnitTangentBundle.base hh
  rw [← parallelFrameFlowMap_antipode]
  exact hb

theorem closed_geodesic_impossible_below_uniform_cut (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g) (e : FrameBundle g) (he : e ∈ o.positive)
    (t : ℝ) (ht : 0 < t) (hcut : ∀ f ∈ o.positive, t ≤ actualCutTime g f)
    (hconj : ∀ f ∈ o.positive, t < actualFirstConjugateTime g hRic f)
    (hclosed : unitTangentOfFrame (parallelFrameFlowMap g 0 (2*t) e) = unitTangentOfFrame e) :
    False := by
  obtain ⟨a,ha,hfixed⟩ := closed_geodesic_fixed_normal g o e he (2*t) hclosed
  let f := frameAntipode g e
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he reverseFrameRotation
  have hstart : normalQuadraticEndpointCurve g e a = normalQuadraticEndpointCurve g f (-a) := by
    apply normalQuadraticEndpointCurve_eq g e f a (-a) rfl
    dsimp [f]
    rw [normalCoordinates_neg,frameAntipode_map,map_neg,neg_neg]
  have hend : normalQuadraticEndpointCurve g (parallelFrameFlowMap g 0 t e) a =
      normalQuadraticEndpointCurve g (parallelFrameFlowMap g 0 t f) (-a) := by
    apply normalQuadraticEndpointCurve_eq g _ _ a (-a)
      (closed_geodesic_antipode_midpoint_base g o e he t hclosed)
    rw [normalCoordinates_neg]
    exact (closed_geodesic_normal_midpoint g o e he t _ hclosed hfixed).symm
  obtain ⟨α,u,hα,hu,hα0,hu0,hαbase,hαshort⟩ :=
    exists_parallel_short_branch g o hRic hpositive e he t ht (hconj e he) hcut a ha
  obtain ⟨β,v,hβ,hv,hβ0,hv0,hβbase,hβshort⟩ :=
    exists_parallel_short_branch g o hRic hpositive f hf t ht (hconj f hf) hcut (-a)
      (neg_ne_zero.mpr ha)
  have hcommon : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      α s ∈ o.positive ∧ β s ∈ o.positive ∧ (α s).base = (β s).base ∧
      ‖u s‖ < t ∧ ‖v s‖ < t ∧
      frameExponential g o (α s) (u s) = frameExponential g o (β s) (v s) := by
    filter_upwards [hαshort,hβshort] with s hs ht'
    refine ⟨hs.1,ht'.1,?_,hs.2.1,ht'.2.1,?_⟩
    · rw [hαbase,hβbase,hstart]
    · rw [hs.2.2,ht'.2.2,hend]
  have hh := short_inverse_branches_limit g o t hcut e f rfl α β u v
    hα hβ hu hv hα0 hβ0 hcommon
  rw [hu0,hv0] at hh
  dsimp [f] at hh
  rw [frameAntipode_map,← map_neg] at hh
  have hz := e.frame.map_injective hh
  have hz0 := congrArg (fun w : FourSpace => w 0) hz
  simp [coordinateVector] at hz0
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! The dimension-two branch reduces to the geometric injectivity bound. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory Set Metric
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem halfFlat_dimension_two_impossible_of_injective_ball (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hinj : ∀ e ∈ o.positive,
      InjOn (frameExponential g o e) (ball 0 (Real.pi / Real.sqrt 3))) :
    Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) ≠ 2 := by
  intro hdim
  obtain ⟨hV,hE⟩ := halfFlat_volume_energy_counts hRic hminus
  rw [hdim] at hV hE
  norm_num at hV hE
  have hplus : (∫ x, plusNorm o x ^ 2 ∂normalizedVolume g) = 3 := by
    rw [hV] at hE
    linarith
  have htotal : (∫ x, plusNorm o x ^ 2 + minusNorm o x ^ 2 ∂normalizedVolume g) = 3 := by
    have hz : ∀ x, minusNorm o x = 0 := fun x => (minusNorm_eq_zero_iff o x).mpr (hminus x)
    simpa only [hz, zero_pow (by decide : 2 ≠ 0), add_zero] using hplus
  have hstrict := strict_lower_volume_of_injective_ball g o hRic hpositive htotal hinj
  rw [hV] at hstrict
  norm_num at hstrict

theorem halfFlat_positive_harmonic_dimension_one_of_injective_ball (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hplus : ∃ x, plusWeyl g x (o.frame x) ≠ 0)
    (hinj : ∀ e ∈ o.positive,
      InjOn (frameExponential g o e) (ball 0 (Real.pi / Real.sqrt 3))) :
    Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1 :=
  (halfFlat_positive_harmonic_dimension_cases hRic hpositive hminus hplus).resolve_right
    (halfFlat_dimension_two_impossible_of_injective_ball hRic hpositive hminus hinj)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Endpoint distance estimates for the actual sphere map. These also
control its continuity at both polar-coordinate singularities. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section

theorem roundLog_norm (p : RoundSphere4) : ‖roundLog p‖ = Real.arccos (p.val 0) := by
  unfold roundLog
  split_ifs with hp
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.arccos_nonneg _)]
    simp [coordinateVector]
  · rw [norm_smul, Real.norm_eq_abs, abs_div,
      abs_of_nonneg (Real.arccos_nonneg _), abs_of_nonneg (norm_nonneg _),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hp)]

theorem roundLog_north : roundLog roundNorth = 0 := by
  rw [← roundPolarPoint_zero firstDirection]
  exact roundLog_polar_zero firstDirection

theorem roundLog_south : roundLog (antipode roundNorth) = Real.pi • coordinateVector 0 := by
  rw [← roundPolarPoint_pi firstDirection]
  exact roundLog_polar_pi firstDirection

def roundAntipodalPoint {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
    (g : SmoothMetric M) (o : FrameOrientation g) (e : FrameBundle g) : M :=
  frameExponential g o e (Real.pi • coordinateVector 0)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem roundSphereMap_north (e : FrameBundle g) :
    roundSphereMap g o e roundNorth = e.base := by
  rw [roundSphereMap, roundLog_north, frameExponential_zero]

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem roundSphereMap_south (e : FrameBundle g) :
    roundSphereMap g o e (antipode roundNorth) = roundAntipodalPoint g o e := by
  rw [roundSphereMap, roundLog_south]
  rfl

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem roundSphereMap_distance_north (e : FrameBundle g) (p : RoundSphere4) :
    metricEDistance g e.base (roundSphereMap g o e p) ≤
      ENNReal.ofReal (Real.arccos (p.val 0)) := by
  simpa only [roundLog_norm, roundSphereMap] using frameExponential_distance g o e (roundLog p)

theorem roundSphereMap_distance_south (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (p : RoundSphere4) :
    metricEDistance g (roundAntipodalPoint g o e) (roundSphereMap g o e p) ≤
      ENNReal.ofReal (Real.pi - Real.arccos (p.val 0)) := by
  obtain ⟨t, ht, q, rfl⟩ := exists_roundPolarPoint p
  rw [roundSphereMap_polar hRic hplus hminus e he t ht q, roundPolarPoint_first,
    Real.arccos_cos ht.1 ht.2]
  have hA : roundAntipodalPoint g o e = frameExponential g o e (Real.pi • q.val) :=
    frameExponential_pi_independent_direction hRic hplus hminus e he firstDirection q
  rw [hA, frameExponential_direction_ray g o e he q Real.pi,
    frameExponential_direction_ray g o e he q t]
  have hd := frameGeodesic_distance_le g 0
    (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) Real.pi t
  simpa only [abs_of_nonpos (sub_nonpos.mpr ht.2), neg_sub] using hd

end
end PositiveEinsteinFour.Geometry
end


section

/-! A parallel two-form has constant norm on the actual compact connected
manifold. This uses the existing global geodesics, not a holonomy premise. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoForm_allFrames_covariant_zero (u : smoothTwoForms o)
    (hzero : smoothTwoFormCovariantEnergy u u = 0) (e : FrameBundle g) :
    twoFormFramedCovariantDerivative o u.val e = 0 := by
  have hz := smoothTwoForm_covariantDerivative_zero_of_energy_zero u hzero e.base
  have hpair : twoFormCovariantPairing o u.val u.val e.base = 0 := by
    unfold twoFormCovariantPairing
    rw [hz]
    simp only [frameTensorPairing, Pi.zero_apply, Finset.sum_const_zero, mul_zero]
  rw [twoFormCovariantPairing_eq_frame o u.val u.val e] at hpair
  change (1 / 2 : ℝ) * ∑ a, (twoFormFramedCovariantDerivative o u.val e a) *
    (twoFormFramedCovariantDerivative o u.val e a) = 0 at hpair
  ext a
  have hle : (twoFormFramedCovariantDerivative o u.val e a) *
      (twoFormFramedCovariantDerivative o u.val e a) ≤
      ∑ b, (twoFormFramedCovariantDerivative o u.val e b) *
        (twoFormFramedCovariantDerivative o u.val e b) :=
    Finset.single_le_sum (fun b _ => mul_self_nonneg _) (Finset.mem_univ a)
  change twoFormFramedCovariantDerivative o u.val e a = 0
  nlinarith

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem parallel_twoForm_along_flow (u : smoothTwoForms o)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o u.val e = 0)
    (e : FrameBundle g) (i : Fin 4) (t : ℝ) :
    twoFormFramedValue o u.val (parallelFrameFlowMap g i t e) = twoFormFramedValue o u.val e := by
  ext a
  have hd (r : ℝ) : HasDerivAt (fun s =>
      twoFormFramedValue o u.val (parallelFrameFlowMap g i s e) a) 0 r := by
    have h := u.property.framedValue_parallel_derivative
      (fun s => parallelFrameFlowMap g i s e) r i
      (parallelFrameFlowMap_curve_continuous g i e).continuousAt
      (parallelFrameFlowMap_primitive g i e r) a
    rw [hz] at h
    exact h
  have h := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) t 0
  simpa only [parallelFrameFlowMap_zero] using h

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem parallel_twoForm_norm_along_flow (u : smoothTwoForms o)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o u.val e = 0)
    (e : FrameBundle g) (i : Fin 4) (t : ℝ) :
    ‖u.val (parallelFrameFlowMap g i t e).base‖ = ‖u.val e.base‖ := by
  have h := congrArg frameTensorSquareNorm (parallel_twoForm_along_flow u hz e i t)
  rw [twoFormFramedValue_norm, twoFormFramedValue_norm] at h
  nlinarith [norm_nonneg (u.val (parallelFrameFlowMap g i t e).base), norm_nonneg (u.val e.base)]

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem parallel_twoForm_norm_on_exponential (u : smoothTwoForms o)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o u.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace) :
    ‖u.val (frameExponential g o e v)‖ = ‖u.val e.base‖ := by
  by_cases hv : v = 0
  · subst v
    rw [frameExponential_zero]
  have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : FourSpace := ‖v‖⁻¹ • v
  have hwn : ‖w‖ = 1 := by
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
  let Q := directionOrientedMatrix ⟨w,hwn⟩
  let f := e.rotate (orientedToOrthogonal Q)
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he Q
  have hdir : orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
      (orientedToOrthogonal Q).property (coordinateVector 0) = w := directionRotation_first ⟨w,hwn⟩
  have hexp : frameExponential g o e v = (parallelFrameFlowMap g 0 ‖v‖ f).base := by
    rw [← frameExponential_first_ray g o f hf ‖v‖ hr,
      frameExponential_rotate, map_smul, hdir]
    congr 1
    dsimp [w]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  rw [hexp, parallel_twoForm_norm_along_flow u hz]
  rfl

variable [PreconnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
theorem parallel_twoForm_norm_constant (hRic : RicciThree g) (u : smoothTwoForms o)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o u.val e = 0) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x, ‖u.val x‖ = c := by
  let x : M := Classical.arbitrary M
  let e : FrameBundle g := ⟨x,o.frame x⟩
  refine ⟨‖u.val x‖, norm_nonneg _, fun y => ?_⟩
  obtain ⟨v,hv⟩ := frameExponential_surjective g o hRic e (o.frame_positive x) y
  rw [← hv]
  exact parallel_twoForm_norm_on_exponential u hz e (o.frame_positive x) v

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual global injectivity bound in the oriented positively curved
Ricci-normalized four-dimensional case. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Metric
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem actualCutTime_lower_sqrt_three (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    Real.pi / Real.sqrt 3 ≤ actualCutTime g e := by
  let : Nonempty M := ⟨e.base⟩
  obtain ⟨f,hf,hpos,hmin⟩ := exists_minimal_actualCutTime g o hRic
  have hbound : Real.pi / Real.sqrt 3 ≤ actualCutTime g f := by
    by_contra hh
    have hlt := lt_of_not_ge hh
    have hconj (q : FrameBundle g) (_ : q ∈ o.positive) :
        actualCutTime g f < actualFirstConjugateTime g hRic q :=
      hlt.trans_le (actualFirstConjugateTime_lower_sqrt_three g hRic hpositive q)
    exact closed_geodesic_impossible_below_uniform_cut g o hRic hpositive f hf
      (actualCutTime g f) hpos hmin hconj
      (exists_closed_geodesic_at_minimal_cut g o hRic f hf hmin hconj)
  exact hbound.trans (hmin e he)

theorem actual_frameExponential_injOn_sqrt_three (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g) (e : FrameBundle g) (he : e ∈ o.positive) :
    InjOn (frameExponential g o e) (ball 0 (Real.pi / Real.sqrt 3)) :=
  frameExponential_injOn_ball_of_cut_lower (Real.pi / Real.sqrt 3)
    (actualCutTime_lower_sqrt_three g o hRic hpositive) e he

end
end PositiveEinsteinFour.Geometry
end


section

/-! The dimension-one half-flat branch has an actual global parallel
self-dual two-form of norm sqrt(2), constructed from its harmonic space. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance unitFormHarmonicAddGroup : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _
local instance unitFormPositiveAddGroup (hRic : RicciThree g) :
    AddCommGroup (smoothHarmonicPositive (o := o) hRic) := Submodule.addCommGroup _

theorem halfFlat_dimension_one_parallel_unit_form (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1) :
    ∃ w : smoothTwoForms o,
      (∀ x, twoFormHodge (w.val x) = w.val x) ∧
      (∀ x, ‖w.val x‖ ^ 2 = 2) ∧
      ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0 := by
  obtain ⟨u,hu⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ)
    (M := smoothHarmonicPositive (o := o) hRic)).mp (by rw [hdim]; norm_num)
  have hn := halfFlat_dimension_one_norm hRic hminus hdim
  have he := halfFlat_positive_harmonic_covariantEnergy_zero hRic hminus hn u
  have hz := smoothTwoForm_allFrames_covariant_zero u.val.val he
  obtain ⟨c,hc,hconst⟩ := parallel_twoForm_norm_constant hRic u.val.val hz
  have hcpos : 0 < c := by
    by_contra h
    have hc0 : c = 0 := le_antisymm (le_of_not_gt h) hc
    apply hu
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact norm_eq_zero.mp (hc0 ▸ hconst x)
  let r := Real.sqrt 2 / c
  have hr : 0 < r := div_pos (Real.sqrt_pos.mpr (by norm_num)) hcpos
  refine ⟨r • u.val.val, ?_, ?_, ?_⟩
  · intro x
    change twoFormHodge (r • u.val.val.val x) = r • u.val.val.val x
    rw [map_smul]
    congr 1
    exact congrArg (fun v : smoothHarmonicTwoForms (o := o) => v.val.val x)
      (smoothHarmonicPositive_star hRic u)
  · intro x
    change ‖r • u.val.val.val x‖ ^ 2 = 2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hconst]
    dsimp only [r]
    rw [div_mul_cancel₀ _ hcpos.ne', Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  · intro e
    change twoFormFramedCovariantDerivative o (r • u.val.val.val) e = 0
    rw [twoFormFramedCovariantDerivative_smul, hz, smul_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The sphere map is continuous at both poles as well as in the ordinary
polar chart; the south-pole bound uses the proved common endpoint. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Bundle Set Filter
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem roundTail_continuous : Continuous roundTail := by
  unfold roundTail
  fun_prop

theorem roundPolarAngle_continuous :
    Continuous (fun p : RoundSphere4 => Real.arccos (p.val 0)) := by
  fun_prop

theorem roundLog_continuousAt {p : RoundSphere4} (hp : roundTail p ≠ 0) :
    ContinuousAt roundLog p := by
  have h := (roundPolarAngle_continuous.continuousAt.div
    roundTail_continuous.norm.continuousAt (norm_ne_zero_iff.mpr hp)).smul
      roundTail_continuous.continuousAt
  apply h.congr_of_eventuallyEq
  filter_upwards [roundTail_continuous.continuousAt.preimage_mem_nhds
    (isOpen_compl_singleton.mem_nhds hp)] with q hq
  exact ite_eq_right hq

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem roundSphereMap_continuous (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) : Continuous (roundSphereMap g o e) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : roundTail p = 0
  · rcases roundTail_zero_cases p hp with rfl | rfl
    · apply (tendsto_iff_edist_tendsto_0).mpr
      have hb : Tendsto (fun q : RoundSphere4 => ENNReal.ofReal (Real.arccos (q.val 0)))
          (𝓝 roundNorth) (𝓝 0) := by
        have hc : Continuous (fun q : RoundSphere4 =>
            ENNReal.ofReal (Real.arccos (q.val 0))) :=
          ENNReal.continuous_ofReal.comp roundPolarAngle_continuous
        simpa [roundNorth] using hc.tendsto roundNorth
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
        (fun _ => bot_le) (fun q => ?_)
      rw [roundSphereMap_north, edist_comm]
      exact roundSphereMap_distance_north e q
    · apply (tendsto_iff_edist_tendsto_0).mpr
      have hb : Tendsto (fun q : RoundSphere4 =>
          ENNReal.ofReal (Real.pi - Real.arccos (q.val 0)))
          (𝓝 (antipode roundNorth)) (𝓝 0) := by
        have hc : Continuous (fun q : RoundSphere4 =>
            ENNReal.ofReal (Real.pi - Real.arccos (q.val 0))) :=
          ENNReal.continuous_ofReal.comp (continuous_const.sub roundPolarAngle_continuous)
        simpa [roundNorth, antipode] using hc.tendsto (antipode roundNorth)
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
        (fun _ => bot_le) (fun q => ?_)
      rw [roundSphereMap_south, edist_comm]
      exact roundSphereMap_distance_south hRic hplus hminus e he q
  · exact (frameExponential_continuous g o e).continuousAt.comp (roundLog_continuousAt hp)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual sphere exponential and its continuous ambient formula.
This fixes the topology at the center of polar coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped _root_.Topology
noncomputable section

def roundSphereExponential (v : FourSpace) : RoundSphere4 :=
  if hv : v = 0 then roundNorth else
    roundPolarPoint ‖v‖ ⟨‖v‖⁻¹ • v, by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩

theorem roundSphereExponential_zero : roundSphereExponential 0 = roundNorth := by
  simp [roundSphereExponential]

theorem roundSphereExponential_radial (t : ℝ) (ht : 0 ≤ t) (q : Directions) :
    roundSphereExponential (t • q.val) = roundPolarPoint t q := by
  by_cases hz : t = 0
  · subst t
    simp [roundSphereExponential_zero, roundPolarPoint_zero]
  have hn : ‖t • q.val‖ = t := by
    rw [norm_smul, q.property, mul_one, Real.norm_eq_abs, abs_of_nonneg ht]
  have hv : t • q.val ≠ 0 := smul_ne_zero hz (unitSphere_ne_zero q)
  rw [roundSphereExponential, dite_eq_right hv]
  congr 1
  apply Subtype.ext
  change ‖t • q.val‖⁻¹ • (t • q.val) = q.val
  rw [hn, smul_smul, inv_mul_cancel₀ hz, one_smul]

theorem roundSphereExponential_vector (v : FourSpace) :
    (roundSphereExponential v).val =
      WithLp.toLp 2 (Fin.cons (Real.cos ‖v‖) (fun i => Real.sinc ‖v‖ * v i)) := by
  by_cases hz : v = 0
  · subst v
    rw [roundSphereExponential_zero]
    ext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [roundNorth]
  · rw [roundSphereExponential, dite_eq_right hz]
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · change Real.sin ‖v‖ * (‖v‖⁻¹ * v i) = Real.sinc ‖v‖ * v i
      rw [Real.sinc_of_ne_zero (norm_ne_zero_iff.mpr hz)]
      ring

theorem roundSphereExponential_continuous : Continuous roundSphereExponential := by
  apply continuous_induced_rng.mpr
  change Continuous (fun v : FourSpace => (roundSphereExponential v).val)
  simp_rw [roundSphereExponential_vector]
  fun_prop

end
end PositiveEinsteinFour.Geometry
end


section

/-! A self-dual two-form of norm sqrt(2) is an orthogonal complex structure
in each positively oriented orthonormal frame. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped BigOperators
noncomputable section

theorem selfDual_twoFormMatrix_square (a : TwoFormFour)
    (ha : twoFormHodge a = a) (hn : ‖a‖ ^ 2 = 2) :
    twoFormMatrix a * twoFormMatrix a = -(1 : Mat4) := by
  have h3 : a 3 = a 2 := congrArg (fun v : TwoFormFour => v 2) ha
  have h4 : a 4 = -a 1 := by
    have h := congrArg (fun v : TwoFormFour => v 1) ha
    change -a 4 = a 1 at h
    linarith
  have h5 : a 5 = a 0 := congrArg (fun v : TwoFormFour => v 0) ha
  have hs : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 = 1 := by
    have he := EuclideanSpace.real_norm_sq_eq a
    simp [Fin.sum_univ_succ, h3, h4, h5] at he
    nlinarith only [he, hn]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoFormMatrix, Matrix.mul_apply, Fin.sum_univ_succ, h3, h4, h5] <;>
    nlinarith only [hs]

theorem selfDual_twoFormMatrix_orthogonal (a : TwoFormFour)
    (ha : twoFormHodge a = a) (hn : ‖a‖ ^ 2 = 2) :
    (twoFormMatrix a)ᵀ * twoFormMatrix a = 1 := by
  rw [twoFormMatrix_skew, Matrix.neg_mul, selfDual_twoFormMatrix_square a ha hn, neg_neg]

open scoped Manifold ContDiff
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem unit_selfDual_frame_complex (w : smoothTwoForms o)
    (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hnorm : ∀ x, ‖w.val x‖ ^ 2 = 2) (e : FrameBundle g) (he : e ∈ o.positive) :
    twoFormMatrix (twoFormFrameValue o w.val e) * twoFormMatrix (twoFormFrameValue o w.val e) =
      -(1 : Mat4) ∧
    (twoFormMatrix (twoFormFrameValue o w.val e))ᵀ *
      twoFormMatrix (twoFormFrameValue o w.val e) = 1 := by
  have hs : twoFormHodge (twoFormFrameValue o w.val e) = twoFormFrameValue o w.val e := by
    rw [← twoFormFrameValue_hodge o w.val e he]
    congr 1
    funext x
    exact hstar x
  have hn : ‖twoFormFrameValue o w.val e‖ ^ 2 = 2 := by
    rw [twoFormFrameValue_norm, hnorm]
  exact ⟨selfDual_twoFormMatrix_square _ hs hn, selfDual_twoFormMatrix_orthogonal _ hs hn⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The curvature eigenvalue of an actual parallel two-form. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem parallel_twoForm_secondDerivative_zero (u : smoothTwoForms o)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o u.val e = 0)
    (e : FrameBundle g) : twoFormFramedSecondDerivative o u.val e = 0 := by
  ext a
  let i := a 0
  let b : Fin 3 → Fin 4 := fun j => a j.succ
  have ha : Fin.cons i b = a := by
    ext j
    fin_cases j <;> rfl
  have hd := u.property.framedCovariant_parallel_derivative
    (fun t => parallelFrameFlowMap g i t e) 0 i
    (parallelFrameFlowMap_curve_continuous g i e).continuousAt
    (parallelFrameFlowMap_primitive g i e 0) b
  have hf : (fun t => twoFormFramedCovariantDerivative o u.val
      (parallelFrameFlowMap g i t e) b) = fun _ : ℝ => (0 : ℝ) := by
    funext t
    rw [hz]
    rfl
  rw [hf, parallelFrameFlowMap_zero, ha] at hd
  exact hd.unique (hasDerivAt_const 0 (0 : ℝ))

theorem parallel_twoForm_roughTrace_zero (u : smoothTwoForms o)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o u.val e = 0)
    (e : FrameBundle g) : twoFormFramedRoughTrace o u.val e = 0 := by
  unfold twoFormFramedRoughTrace
  rw [parallel_twoForm_secondDerivative_zero u hz e]
  simp only [Pi.zero_apply, Finset.sum_const_zero]
  rfl

omit [T3Space M] [CompactSpace M] in
theorem parallel_twoForm_harmonic (u : smoothTwoForms o)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o u.val e = 0) :
    u ∈ smoothHarmonicTwoForms := by
  apply (mem_smoothHarmonicTwoForms u).mpr
  constructor
  · intro e i j k
    change twoFormExteriorComponent
      (fun p q r => twoFormFramedCovariantDerivative o u.val e ![p,q,r]) i j k = 0
    rw [hz]
    simp only [Pi.zero_apply, twoFormExteriorComponent, sub_self, add_zero]
  · intro e k
    change twoFormCodiffComponent
      (fun p q r => twoFormFramedCovariantDerivative o u.val e ![p,q,r]) k = 0
    rw [hz]
    simp only [Pi.zero_apply, twoFormCodiffComponent, Finset.sum_const_zero, neg_zero]

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem parallel_twoForm_curvature_eigenvalue (hRic : RicciThree g)
    (u : smoothTwoForms o)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o u.val e = 0)
    (e : FrameBundle g) :
    twoFormCurvatureAction (twoFormMetricCurvatureTensor g e)
      (twoFormFrameValue o u.val e) = (3 : ℝ) • twoFormFrameValue o u.val e := by
  have hzero := (smoothHodgeLaplacian_eq_zero_iff hRic u).mpr
    (parallel_twoForm_harmonic u hz)
  have h := smoothHodgeLaplacian_framed hRic u e
  rw [hzero, parallel_twoForm_roughTrace_zero u hz e, sub_zero] at h
  have hv : twoFormFramedValue o (0 : smoothTwoForms o).val e = 0 := by
    rw [twoFormFramedValue_eq]
    change twoFormTensorLinear (twoFormFrameActionLinear _ 0) = 0
    rw [map_zero, map_zero]
  have hc := twoFormCurvatureField_frame (o := o) u.val e
  change twoFormFrameValue o (smoothTwoFormCurvature u).val e = _ at hc
  rw [hv, twoFormFramedValue_eq, twoFormFramedValue_eq, hc] at h
  apply twoFormTensor_injective
  change twoFormTensorLinear _ = twoFormTensorLinear ((3 : ℝ) • _)
  rw [map_smul]
  ext a
  have ha := congrFun h a
  simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at ha
  change twoFormTensor (twoFormCurvatureAction (twoFormMetricCurvatureTensor g e)
      (twoFormFrameValue o u.val e)) a = 3 * twoFormTensor (twoFormFrameValue o u.val e) a
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! An explicit open polar chart on the standard sphere, including the
north pole and excluding precisely the south pole. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set Filter
open scoped _root_.Topology
noncomputable section

theorem roundSphereExponential_log (p : RoundSphere4) :
    roundSphereExponential (roundLog p) = p := by
  obtain ⟨t, ht, q, rfl⟩ := exists_roundPolarPoint p
  by_cases h0 : t = 0
  · subst t
    rw [roundLog_polar_zero, roundSphereExponential_zero, roundPolarPoint_zero]
  by_cases hπ : t = Real.pi
  · subst t
    rw [roundLog_polar_pi]
    change roundSphereExponential (Real.pi • firstDirection.val) = _
    rw [roundSphereExponential_radial _ Real.pi_pos.le,
      roundPolarPoint_pi, roundPolarPoint_pi]
  · rw [roundLog_polar_interior t
      ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 hπ⟩,
      roundSphereExponential_radial t ht.1]

theorem roundLog_sphereExponential {v : FourSpace} (hv : ‖v‖ < Real.pi) :
    roundLog (roundSphereExponential v) = v := by
  by_cases hz : v = 0
  · subst v
    rw [roundSphereExponential_zero, roundLog_north]
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  rw [← hrad, roundSphereExponential_radial _ (norm_nonneg _),
    roundLog_polar_interior _ ⟨norm_pos_iff.mpr hz, hv⟩]

theorem roundLog_norm_lt_pi {p : RoundSphere4} (hp : p ≠ antipode roundNorth) :
    ‖roundLog p‖ < Real.pi := by
  obtain ⟨t, ht, q, rfl⟩ := exists_roundPolarPoint p
  rw [roundLog_norm, roundPolarPoint_first, Real.arccos_cos ht.1 ht.2]
  apply lt_of_le_of_ne ht.2
  intro heq
  exact hp (heq ▸ roundPolarPoint_pi q)

theorem roundSphereExponential_ne_south {v : FourSpace} (hv : ‖v‖ < Real.pi) :
    roundSphereExponential v ≠ antipode roundNorth := by
  intro h
  have hn := congrArg norm (roundLog_sphereExponential hv)
  rw [h, roundLog_norm] at hn
  have ha : (antipode roundNorth).val 0 = -1 := by simp [antipode, roundNorth]
  rw [ha, Real.arccos_neg_one] at hn
  exact (ne_of_lt hv) hn.symm

theorem roundLog_continuousAt_north : ContinuousAt roundLog roundNorth := by
  rw [ContinuousAt, roundLog_north]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp_rw [roundLog_norm]
  simpa [roundNorth] using roundPolarAngle_continuous.tendsto roundNorth

theorem roundLog_continuousOn : ContinuousOn roundLog {antipode roundNorth}ᶜ := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  by_cases hz : roundTail p = 0
  · rcases roundTail_zero_cases p hz with rfl | h
    · exact roundLog_continuousAt_north
    · exact False.elim (hp h)
  · exact roundLog_continuousAt hz

def roundSpherePolarChart : OpenPartialHomeomorph FourSpace RoundSphere4 where
  toFun := roundSphereExponential
  invFun := roundLog
  source := Metric.ball 0 Real.pi
  target := {antipode roundNorth}ᶜ
  map_source' := by
    intro v hv
    exact roundSphereExponential_ne_south (by simpa only [Metric.mem_ball, dist_zero_right] using hv)
  map_target' := by
    intro p hp
    simpa only [Metric.mem_ball, dist_zero_right] using roundLog_norm_lt_pi hp
  left_inv' := by
    intro v hv
    exact roundLog_sphereExponential (by simpa only [Metric.mem_ball, dist_zero_right] using hv)
  right_inv' := fun {_} _ => roundSphereExponential_log _
  open_source := Metric.isOpen_ball
  open_target := isOpen_compl_singleton
  continuousOn_toFun := roundSphereExponential_continuous.continuousOn
  continuousOn_invFun := roundLog_continuousOn

end
end PositiveEinsteinFour.Geometry
end


section

/-! The differential of the standard sphere exponential away from zero,
with the radial norm derivative justified from its squared norm. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Filter Set
open scoped _root_.Topology InnerProductSpace
noncomputable section

theorem round_norm_fderiv (v : FourSpace) (hv : v ≠ 0) (w : FourSpace) :
    fderiv ℝ (fun x : FourSpace => ‖x‖) v w = inner ℝ (‖v‖⁻¹ • v) w := by
  have hd : DifferentiableAt ℝ (fun x : FourSpace => ‖x‖) v :=
    (contDiffAt_norm ℝ hv : ContDiffAt ℝ 1 (fun x : FourSpace => ‖x‖) v).differentiableAt one_ne_zero
  have h := congrArg (fun D : FourSpace →L[ℝ] ℝ => D w)
    ((hd.hasFDerivAt.pow 2).unique (hasStrictFDerivAt_norm_sq v).hasFDerivAt)
  simp only [Nat.reduceSub, pow_one, _root_.smul_apply, smul_eq_mul,
    two_smul, add_apply, innerSL_apply_apply] at h
  rw [real_inner_smul_left]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  apply (mul_left_cancel₀ hn)
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  linarith

def roundSphereLinearInclusion : (ℝ × FourSpace) →L[ℝ] EuclideanSpace ℝ (Fin 5) where
  toFun p := WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2))
  map_add' p q := by
    ext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  map_smul' a p := by
    ext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  cont := by fun_prop

@[simp] theorem roundSphereLinearInclusion_first (p : ℝ × FourSpace) :
    roundSphereLinearInclusion p 0 = p.1 := rfl

@[simp] theorem roundSphereLinearInclusion_tail (p : ℝ × FourSpace) (i : Fin 4) :
    roundSphereLinearInclusion p i.succ = p.2 i := rfl

theorem roundSphereExponential_differentiableAt (v : FourSpace) (hv : v ≠ 0) :
    DifferentiableAt ℝ (fun x : FourSpace => (roundSphereExponential x).val) v := by
  have hn : DifferentiableAt ℝ (fun x : FourSpace => ‖x‖) v :=
    (contDiffAt_norm ℝ hv : ContDiffAt ℝ 1 (fun x : FourSpace => ‖x‖) v).differentiableAt one_ne_zero
  have hs : DifferentiableAt ℝ (fun x : FourSpace => Real.sin ‖x‖ / ‖x‖) v := by
    simpa only [div_eq_mul_inv] using! hn.sin.mul (hn.inv (norm_ne_zero_iff.mpr hv))
  have htail : DifferentiableAt ℝ (fun x : FourSpace => (Real.sin ‖x‖ / ‖x‖) • x) v :=
    hs.smul differentiableAt_id
  have hF := roundSphereLinearInclusion.differentiableAt.comp v (hn.cos.prodMk htail)
  apply hF.congr_of_eventuallyEq
  filter_upwards [isOpen_compl_singleton.mem_nhds hv] with x hx
  rw [roundSphereExponential_vector, Real.sinc_of_ne_zero (norm_ne_zero_iff.mpr hx)]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The real circle action generated by an orthogonal complex structure. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
noncomputable section

def complexCircleMatrix (J : Mat4) (t : ℝ) : Mat4 :=
  Real.cos t • (1 : Mat4) + Real.sin t • J

theorem complexCircleMatrix_orthogonal (J : Mat4) (hsk : Jᵀ = -J)
    (hsq : J * J = -(1 : Mat4)) (t : ℝ) :
    (complexCircleMatrix J t)ᵀ * complexCircleMatrix J t = 1 := by
  simp only [complexCircleMatrix, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_one, hsk, smul_neg, Matrix.add_mul, Matrix.mul_add,
    Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, hsq]
  ext i j
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination ((1 : Mat4) i j) * Real.sin_sq_add_cos_sq t

def complexCircleVector (J : Mat4) (q : FourSpace) (t : ℝ) : FourSpace :=
  Real.cos t • q + Real.sin t • (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) J q)

theorem complexCircleVector_eq_matrix (J : Mat4) (q : FourSpace) (t : ℝ) :
    complexCircleVector J q t =
      Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (complexCircleMatrix J t) q := by
  rw [complexCircleMatrix, map_add, map_smul, map_smul, map_one]
  rfl

theorem complexCircleVector_norm (J : Mat4) (hsk : Jᵀ = -J)
    (hsq : J * J = -(1 : Mat4)) (q : FourSpace) (t : ℝ) :
    ‖complexCircleVector J q t‖ = ‖q‖ := by
  rw [complexCircleVector_eq_matrix]
  exact (orthogonalEuclideanIsometry (complexCircleMatrix J t)
    (complexCircleMatrix_orthogonal J hsk hsq t)).norm_map q

theorem complexCircleVector_hasDerivAt (J : Mat4) (hsq : J * J = -(1 : Mat4))
    (q : FourSpace) (t : ℝ) :
    HasDerivAt (complexCircleVector J q)
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) J (complexCircleVector J q t)) t := by
  have hJJ : Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) J
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) J q) = -q := by
    change ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) J) *
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) J)) q = -q
    rw [← map_mul, hsq, map_neg, map_one]
    rfl
  convert ((Real.hasDerivAt_cos t).smul_const q).add
    ((Real.hasDerivAt_sin t).smul_const
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) J q)) using 1
  · rfl
  · rw [complexCircleVector, map_add, map_smul, map_smul, hJJ]
    module

theorem complexCircleVector_zero (J : Mat4) (q : FourSpace) : complexCircleVector J q 0 = q := by
  simp [complexCircleVector]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual sphere map is locally a homeomorphism away from its south
pole, by composing the two genuine normal-coordinate charts. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem roundSphereMap_localChart (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (p : RoundSphere4)
    (hp : p ≠ antipode roundNorth) :
    ∃ D : OpenPartialHomeomorph RoundSphere4 M,
      p ∈ D.source ∧ EqOn D (roundSphereMap g o e) D.source := by
  obtain ⟨C, hv, hC⟩ := frameExponential_round_localChart hRic hplus hminus e he
    (roundLog p) (roundLog_norm_lt_pi hp)
  let D := roundSpherePolarChart.symm.trans C
  refine ⟨D, ?_, ?_⟩
  · exact ⟨hp, hv⟩
  · intro q hq
    change C (roundLog q) = frameExponential g o e (roundLog q)
    exact hC hq.2

theorem roundSphereMap_isLocalHomeomorphOn (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    IsLocalHomeomorphOn (roundSphereMap g o e) {antipode roundNorth}ᶜ := by
  apply IsLocalHomeomorphOn.mk
  intro p hp
  obtain ⟨D, hD, heq⟩ := roundSphereMap_localChart hRic hplus hminus e he p hp
  exact ⟨D, hD, heq.symm⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! A symmetric projection of trace one is determined by a unit vector
in its image. This will identify the actual parallel Weyl block. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour TraceHessian Matrix
open scoped BigOperators
noncomputable section

theorem symmetric_projection_trace_one (P : Mat) (hs : symmetric P)
    (hp : P * P = P) (ht : Matrix.trace P = 1)
    (v : Fin 3 → ℝ) (hv : dotProduct v v = 1) (hPv : P *ᵥ v = v) :
    P = Matrix.vecMulVec v v := by
  let Q := Matrix.vecMulVec v v
  have hPt : Pᵀ = P := by ext i j; exact hs j i
  have hQt : Qᵀ = Q := by
    ext i j
    exact mul_comm _ _
  have hPQ : P * Q = Q := by
    dsimp only [Q]
    rw [Matrix.mul_vecMulVec, hPv]
  have hQP : Q * P = Q := by
    have h := congrArg Matrix.transpose hPQ
    simpa only [Matrix.transpose_mul, hPt, hQt] using h
  have hQQ : Q * Q = Q := by
    dsimp only [Q]
    rw [Matrix.vecMulVec_mul_vecMulVec, hv, one_smul]
  have hD : (P - Q) * (P - Q) = P - Q := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hp, hPQ, hQP, hQQ, sub_self,
      sub_zero]
  have hsD : symmetric (P - Q) := by
    intro i j
    change P i j - v i * v j = P j i - v j * v i
    rw [hs i j, mul_comm (v i)]
  have htD : Matrix.trace (P - Q) = 0 := by
    rw [Matrix.trace_sub, ht]
    dsimp only [Q]
    rw [Matrix.trace_vecMulVec, hv, sub_self]
  have hnorm := trace_square_eq_six_norm_sq (P - Q) hsD
  rw [hD, htD] at hnorm
  have hzero : P - Q = 0 := (normalizedBlockNorm_eq_zero_iff _).mp (by nlinarith)
  exact sub_eq_zero.mp hzero

theorem unitWeylProjection_eq_vector (A : Mat) (hs : symmetric A)
    (ht : traceFree A) (hp : A * A = A + (2 : ℝ) • (1 : Mat))
    (v : Fin 3 → ℝ) (hv : dotProduct v v = 1) (hAv : A *ᵥ v = (2 : ℝ) • v) :
    A = (3 : ℝ) • Matrix.vecMulVec v v - 1 := by
  have hPv : unitWeylProjection A *ᵥ v = v := by
    rw [unitWeylProjection, Matrix.smul_mulVec, Matrix.add_mulVec, hAv, Matrix.one_mulVec]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  have hP := symmetric_projection_trace_one (unitWeylProjection A)
    (fun i j => by
      have h := Matrix.isHermitian_iff_isSymm.mp (unitWeylProjection_symmetric A hs)
      exact congrFun (congrFun h j) i)
    (unitWeylProjection_idempotent A hp).eq (unitWeylProjection_trace A ht) v hv hPv
  ext i j
  have h := congrFun (congrFun hP i) j
  change (1 / 3 : ℝ) * (A i j + (1 : Mat) i j) = v i * v j at h
  change A i j = 3 * (v i * v j) - (1 : Mat) i j
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! The polar differential of the standard round exponential. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Filter Set
open scoped _root_.Topology InnerProductSpace
noncomputable section

theorem roundSphereExponential_fderiv (v : FourSpace) (hv : v ≠ 0) (w : FourSpace) :
    fderiv ℝ (fun x : FourSpace => (roundSphereExponential x).val) v w =
      roundSphereLinearInclusion
        (-Real.sin ‖v‖ * inner ℝ (‖v‖⁻¹ • v) w,
          ((Real.cos ‖v‖ - Real.sin ‖v‖ / ‖v‖) * inner ℝ (‖v‖⁻¹ • v) w) • (‖v‖⁻¹ • v) +
            (Real.sin ‖v‖ / ‖v‖) • w) := by
  have hn : HasFDerivAt (fun x : FourSpace => ‖x‖)
      (fderiv ℝ (fun x : FourSpace => ‖x‖) v) v :=
    ((contDiffAt_norm ℝ hv : ContDiffAt ℝ 1 (fun x : FourSpace => ‖x‖) v).differentiableAt one_ne_zero).hasFDerivAt
  have hi := (hasDerivAt_inv (norm_ne_zero_iff.mpr hv)).comp_hasFDerivAt v hn
  have hs := (hn.sin.mul hi).smul (hasFDerivAt_id v)
  have hF := roundSphereLinearInclusion.hasFDerivAt.comp v (hn.cos.prodMk hs)
  have heq : (fun x : FourSpace => (roundSphereExponential x).val) =ᶠ[𝓝 v]
      (fun x : FourSpace => roundSphereLinearInclusion
        (Real.cos ‖x‖, (Real.sin ‖x‖ * ‖x‖⁻¹) • x)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hv] with x hx
    rw [roundSphereExponential_vector, Real.sinc_of_ne_zero (norm_ne_zero_iff.mpr hx)]
    simp only [roundSphereLinearInclusion, div_eq_mul_inv]
    rfl
  have hA := hF.congr_of_eventuallyEq heq
  rw [hA.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    add_apply, Function.comp_apply, Pi.mul_apply, id_eq,
    ContinuousLinearMap.smulRight_apply, _root_.smul_apply,
    smul_eq_mul, ContinuousLinearMap.id_apply]
  rw [round_norm_fderiv v hv w]
  congr 1
  apply Prod.ext
  · rfl
  · ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp [norm_ne_zero_iff.mpr hv]
    ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The standard sphere's radial differential has exactly the metric
pairing supplied by the round Jacobi equation. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular
open scoped BigOperators InnerProductSpace
noncomputable section

theorem roundSphereLinearInclusion_inner (p r : ℝ × FourSpace) :
    inner ℝ (roundSphereLinearInclusion p) (roundSphereLinearInclusion r) =
      p.1 * r.1 + inner ℝ p.2 r.2 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Fin.sum_univ_succ]
  change r.1 * p.1 + (∑ i : Fin 4, r.2 i * p.2 i) =
    p.1 * r.1 + (∑ i : Fin 4, r.2 i * p.2 i)
  ring

theorem roundSphere_radial_pairing (q : Directions) (t : ℝ) (w z : FourSpace) :
    inner ℝ
      (roundSphereLinearInclusion
        (-Real.sin t * inner ℝ q.val w,
          ((Real.cos t - Real.sin t / t) * inner ℝ q.val w) • q.val +
            (Real.sin t / t) • w))
      (roundSphereLinearInclusion
        (-Real.sin t * inner ℝ q.val z,
          ((Real.cos t - Real.sin t / t) * inner ℝ q.val z) • q.val +
            (Real.sin t / t) • z)) =
      (Real.sin t / t) ^ 2 * inner ℝ w z +
        (1 - (Real.sin t / t) ^ 2) * inner ℝ q.val w * inner ℝ q.val z := by
  rw [roundSphereLinearInclusion_inner]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  have hq : inner ℝ q.val q.val = 1 := by
    rw [real_inner_self_eq_norm_sq, q.property, one_pow]
  rw [hq, real_inner_comm w q.val]
  have htrig := Real.sin_sq_add_cos_sq t
  linear_combination (inner ℝ w q.val * inner ℝ q.val z) * htrig

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactness upgrades the local sphere map to a genuine covering away
from the common antipodal value. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section

theorem roundSphere_compact : IsCompact {v : EuclideanSpace ℝ (Fin 5) | ‖v‖ = 1} := by
  simpa only [Metric.sphere, dist_zero_right] using
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 5)) 1)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem roundSphereMap_isCoveringMapOn (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    IsCoveringMapOn (roundSphereMap g o e) {roundAntipodalPoint g o e}ᶜ := by
  let : CompactSpace RoundSphere4 := isCompact_iff_compactSpace.mp roundSphere_compact
  apply IsCoveringMapOn.of_isLocalHomeomorphOn
    (roundSphereMap_continuous hRic hplus hminus e he)
  apply (roundSphereMap_isLocalHomeomorphOn hRic hplus hminus e he).mono
  intro p hp hps
  apply hp
  change roundSphereMap g o e p = roundAntipodalPoint g o e
  rw [hps, roundSphereMap_south]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Equality of the genuine manifold and standard sphere metrics in
normal coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology InnerProductSpace
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem roundSphereMap_exponential (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace)
    (hv : ‖v‖ ≤ Real.pi) :
    roundSphereMap g o e (roundSphereExponential v) = frameExponential g o e v := by
  by_cases hz : v = 0
  · subst v
    rw [roundSphereExponential_zero, roundSphereMap_north, frameExponential_zero]
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  rw [← hrad, roundSphereExponential_radial _ (norm_nonneg _),
    roundSphereMap_polar hRic hplus hminus e he _ ⟨norm_nonneg _, hv⟩]

theorem frameExponential_round_metric_eq_sphere (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace) (hv : v ≠ 0)
    (w z : FourSpace) :
    g.inner (frameExponential g o e v)
      (mfderiv I4 I4 (frameExponential g o e) v w)
      (mfderiv I4 I4 (frameExponential g o e) v z) =
      inner ℝ (fderiv ℝ (fun x : FourSpace => (roundSphereExponential x).val) v w)
        (fderiv ℝ (fun x : FourSpace => (roundSphereExponential x).val) v z) := by
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
  rw [roundSphereExponential_fderiv v hv w, roundSphereExponential_fderiv v hv z]
  change _ = inner ℝ
    (roundSphereLinearInclusion (-Real.sin ‖v‖ * inner ℝ q.val w,
      ((Real.cos ‖v‖ - Real.sin ‖v‖ / ‖v‖) * inner ℝ q.val w) • q.val +
        (Real.sin ‖v‖ / ‖v‖) • w))
    (roundSphereLinearInclusion (-Real.sin ‖v‖ * inner ℝ q.val z,
      ((Real.cos ‖v‖ - Real.sin ‖v‖ / ‖v‖) * inner ℝ q.val z) • q.val +
        (Real.sin ‖v‖ / ‖v‖) • z))
  rw [roundSphere_radial_pairing]
  have h := frameExponential_round_pairing hRic hplus hminus e he q ‖v‖
    (norm_pos_iff.mpr hv) w z
  rw [hrad] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The unit parallel form determines the actual remaining Weyl block. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular TraceHessian Matrix
open scoped BigOperators Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem halfFlat_parallel_form_weyl (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    let a := twoFormFrameValue o w.val e
    plusWeyl g e.base e.frame =
      (3 : ℝ) • Matrix.vecMulVec ![a 0,a 1,a 2] ![a 0,a 1,a 2] - 1 := by
  let a := twoFormFrameValue o w.val e
  let T := plusWeyl g e.base e.frame
  let v : Fin 3 → ℝ := ![a 0,a 1,a 2]
  have hs : twoFormHodge a = a := by
    dsimp only [a]
    rw [← twoFormFrameValue_hodge o w.val e he]
    congr 1
    exact funext hstar
  have ha : ‖a‖ ^ 2 = 2 := by rw [twoFormFrameValue_norm, hw]
  have h3 : a 3 = a 2 := congrArg (fun b : TwoFormFour => b 2) hs
  have h4 : a 4 = -a 1 := by
    have h := congrArg (fun b : TwoFormFour => b 1) hs
    change -a 4 = a 1 at h
    linarith
  have h5 : a 5 = a 0 := congrArg (fun b : TwoFormFour => b 0) hs
  have hv : dotProduct v v = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq a
    simp [Fin.sum_univ_succ, h3, h4, h5] at h
    simp [v, dotProduct, Fin.sum_univ_succ]
    nlinarith only [h,ha]
  have hlast : ∀ i j k l, twoFormMetricCurvatureTensor g e ![i,j,l,k] =
      -twoFormMetricCurvatureTensor g e ![i,j,k,l] := by
    intro i j k l
    simp only [twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    exact frame_algebraic_lastSkew e.frame i j k l
  have hm : minusWeyl g e.base e.frame = 0 := by
    apply (normalizedBlockNorm_eq_zero_iff _).mp
    rw [← actual_minusNorm_frame o e he]
    exact (minusNorm_eq_zero_iff o e.base).mpr (hminus e.base)
  have hR : twoFormMetricCurvatureTensor g e = fun b =>
      einsteinCurvatureTensor T 0 (b 0) (b 1) (b 2) (b 3) := by
    funext b
    have hb : b = ![b 0,b 1,b 2,b 3] := by ext i; fin_cases i <;> rfl
    rw [hb]
    simp only [twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    rw [actual_einstein_decomposition e.frame hRic, hm]
    rfl
  have hEig := parallel_twoForm_curvature_eigenvalue hRic w hz e
  change twoFormCurvatureAction (twoFormMetricCurvatureTensor g e) a = (3 : ℝ) • a at hEig
  rw [← twoFormCurvatureMatrix_apply _ hlast, hR] at hEig
  change twoFormMatrixMul (twoFormCurvatureMatrix (fun b =>
    einsteinCurvatureTensor T 0 (b 0) (b 1) (b 2) (b 3))) a = (3 : ℝ) • a at hEig
  rw [halfFlat_curvature_matrix_positive T a hs] at hEig
  have hIv : (1 + T) *ᵥ v = (3 : ℝ) • v := by
    ext i
    fin_cases i
    · exact congrArg (fun b : TwoFormFour => b 0) hEig
    · exact congrArg (fun b : TwoFormFour => b 1) hEig
    · exact congrArg (fun b : TwoFormFour => b 2) hEig
  have hTv : T *ᵥ v = (2 : ℝ) • v := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec] at hIv
    ext i
    have h := congrFun hIv i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
    linarith
  exact unitWeylProjection_eq_vector T (actual_weyl_symmetric e.frame).1
    (actual_weyl_traceFree e.frame hRic).1 (actual_unit_weyl_polynomial hRic hnorm e he) v hv hTv

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normalized complex-space-form curvature tensor in real coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular TraceHessian Matrix AlgebraicCurvature
open scoped BigOperators
noncomputable section

def complexSpaceCurvature (a : TwoFormFour) : CurvatureArray := fun i j k l =>
  (1 / 2 : ℝ) * ((1 : Mat4) i l * (1 : Mat4) j k -
    (1 : Mat4) i k * (1 : Mat4) j l +
    twoFormMatrix a i l * twoFormMatrix a j k -
    twoFormMatrix a i k * twoFormMatrix a j l -
    2 * twoFormMatrix a i j * twoFormMatrix a k l)

theorem complexSpaceCurvature_firstSkew (a : TwoFormFour) :
    FirstSkew (complexSpaceCurvature a) := by
  intro i j k l
  have h : twoFormMatrix a j i = -twoFormMatrix a i j :=
    congrArg (fun B : Mat4 => B i j) (twoFormMatrix_skew a)
  simp only [complexSpaceCurvature, h]
  ring

theorem complexSpaceCurvature_lastSkew (a : TwoFormFour) :
    LastSkew (complexSpaceCurvature a) := by
  intro i j k l
  have h : twoFormMatrix a l k = -twoFormMatrix a k l :=
    congrArg (fun B : Mat4 => B k l) (twoFormMatrix_skew a)
  simp only [complexSpaceCurvature, h]
  ring

private theorem complexSpace_matrix_row0 (a : TwoFormFour)
    (h3 : a 3 = a 2) (h4 : a 4 = -a 1) (h5 : a 5 = a 0)
    (hs : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 = 1) (j : Fin 6) :
    matrixOf (einsteinCurvatureTensor
      ((3 : ℝ) • Matrix.vecMulVec ![a 0,a 1,a 2] ![a 0,a 1,a 2] - 1) 0) 0 j =
      matrixOf (complexSpaceCurvature a) 0 j := by
  fin_cases j <;>
    simp [matrixOf, pair, einsteinCurvatureTensor, blockTensor, twoFormProduct,
      quaternionMatrix, oppositeMatrix, oppositeQuaternion,
      Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
      Fin.sum_univ_succ, complexSpaceCurvature,
      twoFormMatrix, h3, h4, h5] <;> nlinarith only [hs]

private theorem complexSpace_matrix_row1 (a : TwoFormFour)
    (h3 : a 3 = a 2) (h4 : a 4 = -a 1) (h5 : a 5 = a 0)
    (hs : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 = 1) (j : Fin 6) :
    matrixOf (einsteinCurvatureTensor
      ((3 : ℝ) • Matrix.vecMulVec ![a 0,a 1,a 2] ![a 0,a 1,a 2] - 1) 0) 1 j =
      matrixOf (complexSpaceCurvature a) 1 j := by
  fin_cases j <;>
    simp [matrixOf, pair, einsteinCurvatureTensor, blockTensor, twoFormProduct,
      quaternionMatrix, oppositeMatrix, oppositeQuaternion,
      Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
      Fin.sum_univ_succ, complexSpaceCurvature,
      twoFormMatrix, h3, h4, h5] <;> nlinarith only [hs]

private theorem complexSpace_matrix_row2 (a : TwoFormFour)
    (h3 : a 3 = a 2) (h4 : a 4 = -a 1) (h5 : a 5 = a 0)
    (hs : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 = 1) (j : Fin 6) :
    matrixOf (einsteinCurvatureTensor
      ((3 : ℝ) • Matrix.vecMulVec ![a 0,a 1,a 2] ![a 0,a 1,a 2] - 1) 0) 2 j =
      matrixOf (complexSpaceCurvature a) 2 j := by
  fin_cases j <;>
    simp [matrixOf, pair, einsteinCurvatureTensor, blockTensor, twoFormProduct,
      quaternionMatrix, oppositeMatrix, oppositeQuaternion,
      Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
      Fin.sum_univ_succ, complexSpaceCurvature,
      twoFormMatrix, h3, h4, h5] <;> nlinarith only [hs]

private theorem complexSpace_matrix_row3 (a : TwoFormFour)
    (h3 : a 3 = a 2) (h4 : a 4 = -a 1) (h5 : a 5 = a 0)
    (hs : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 = 1) (j : Fin 6) :
    matrixOf (einsteinCurvatureTensor
      ((3 : ℝ) • Matrix.vecMulVec ![a 0,a 1,a 2] ![a 0,a 1,a 2] - 1) 0) 3 j =
      matrixOf (complexSpaceCurvature a) 3 j := by
  fin_cases j <;>
    simp [matrixOf, pair, einsteinCurvatureTensor, blockTensor, twoFormProduct,
      quaternionMatrix, oppositeMatrix, oppositeQuaternion,
      Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
      Fin.sum_univ_succ, complexSpaceCurvature,
      twoFormMatrix, h3, h4, h5] <;> nlinarith only [hs]

private theorem complexSpace_matrix_row4 (a : TwoFormFour)
    (h3 : a 3 = a 2) (h4 : a 4 = -a 1) (h5 : a 5 = a 0)
    (hs : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 = 1) (j : Fin 6) :
    matrixOf (einsteinCurvatureTensor
      ((3 : ℝ) • Matrix.vecMulVec ![a 0,a 1,a 2] ![a 0,a 1,a 2] - 1) 0) 4 j =
      matrixOf (complexSpaceCurvature a) 4 j := by
  fin_cases j <;>
    simp [matrixOf, pair, einsteinCurvatureTensor, blockTensor, twoFormProduct,
      quaternionMatrix, oppositeMatrix, oppositeQuaternion,
      Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
      Fin.sum_univ_succ, complexSpaceCurvature,
      twoFormMatrix, h3, h4, h5] <;> nlinarith only [hs]

private theorem complexSpace_matrix_row5 (a : TwoFormFour)
    (h3 : a 3 = a 2) (h4 : a 4 = -a 1) (h5 : a 5 = a 0)
    (hs : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 = 1) (j : Fin 6) :
    matrixOf (einsteinCurvatureTensor
      ((3 : ℝ) • Matrix.vecMulVec ![a 0,a 1,a 2] ![a 0,a 1,a 2] - 1) 0) 5 j =
      matrixOf (complexSpaceCurvature a) 5 j := by
  fin_cases j <;>
    simp [matrixOf, pair, einsteinCurvatureTensor, blockTensor, twoFormProduct,
      quaternionMatrix, oppositeMatrix, oppositeQuaternion,
      Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
      Fin.sum_univ_succ, complexSpaceCurvature,
      twoFormMatrix, h3, h4, h5] <;> nlinarith only [hs]

theorem selfDual_complexSpaceCurvature (a : TwoFormFour)
    (ha : twoFormHodge a = a) (hn : ‖a‖ ^ 2 = 2) :
    einsteinCurvatureTensor
      ((3 : ℝ) • Matrix.vecMulVec ![a 0,a 1,a 2] ![a 0,a 1,a 2] - 1) 0 =
      complexSpaceCurvature a := by
  have h3 : a 3 = a 2 := congrArg (fun v : TwoFormFour => v 2) ha
  have h4 : a 4 = -a 1 := by
    have h := congrArg (fun v : TwoFormFour => v 1) ha
    change -a 4 = a 1 at h
    linarith
  have h5 : a 5 = a 0 := congrArg (fun v : TwoFormFour => v 0) ha
  have hs : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq a
    simp [Fin.sum_univ_succ, h3, h4, h5] at h
    nlinarith only [h,hn]
  apply tensor_eq_of_matrixOf_eq
  · intro i j k l
    exact congrArg₂ (· + ·)
      (blockTensor_firstSkew _ _ quaternionMatrix_transpose i j k l)
      (blockTensor_firstSkew _ _ QuaternionFrame.oppositeMatrix_transpose i j k l) |>.trans
        (neg_add _ _).symm
  · intro i j k l
    exact congrArg₂ (· + ·)
      (blockTensor_lastSkew _ _ quaternionMatrix_transpose i j k l)
      (blockTensor_lastSkew _ _ QuaternionFrame.oppositeMatrix_transpose i j k l) |>.trans
        (neg_add _ _).symm
  · exact complexSpaceCurvature_firstSkew a
  · exact complexSpaceCurvature_lastSkew a
  · ext i j
    fin_cases i
    · exact complexSpace_matrix_row0 a h3 h4 h5 hs j
    · exact complexSpace_matrix_row1 a h3 h4 h5 hs j
    · exact complexSpace_matrix_row2 a h3 h4 h5 hs j
    · exact complexSpace_matrix_row3 a h3 h4 h5 hs j
    · exact complexSpace_matrix_row4 a h3 h4 h5 hs j
    · exact complexSpace_matrix_row5 a h3 h4 h5 hs j

end
end PositiveEinsteinFour.Geometry
end


section

/-! The pointwise speed identity in the actual round exponential chart. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem metric_curve_speed_congr {γ η : ℝ → M} {t : ℝ}
    (h : γ =ᶠ[𝓝 t] η) :
    metricTangentNorm g (γ t) (mfderiv 𝓘(ℝ, ℝ) I4 γ t 1) =
      metricTangentNorm g (η t) (mfderiv 𝓘(ℝ, ℝ) I4 η t 1) := by
  have hD : (show ℝ →L[ℝ] FourSpace from mfderiv 𝓘(ℝ, ℝ) I4 γ t) =
      (show ℝ →L[ℝ] FourSpace from mfderiv 𝓘(ℝ, ℝ) I4 η t) := by
    simpa only [tangentSpaceCast, ContinuousLinearMap.id_comp] using! h.mfderiv_eq
  let v : FourSpace := mfderiv 𝓘(ℝ, ℝ) I4 γ t 1
  let w : FourSpace := mfderiv 𝓘(ℝ, ℝ) I4 η t 1
  have hv : v = w := congrArg (fun D : ℝ →L[ℝ] FourSpace => D 1) hD
  change metricTangentNorm g (γ t) v = metricTangentNorm g (η t) w
  rw [hv, h.self_of_nhds]

theorem frameExponential_round_curve_speed (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    {α : ℝ → FourSpace} {t : ℝ} (ha : DifferentiableAt ℝ α t)
    (hz : α t ≠ 0) :
    ‖deriv (fun s => (roundSphereExponential (α s)).val) t‖ =
      metricTangentNorm g (frameExponential g o e (α t))
        (mfderiv 𝓘(ℝ, ℝ) I4 (fun s => frameExponential g o e (α s)) t 1) := by
  have hsp := (roundSphereExponential_differentiableAt (α t) hz).hasFDerivAt.comp_hasDerivAt t
    ha.hasDerivAt
  dsimp only [Function.comp_def] at hsp
  have hm := mfderiv_comp t
    ((frameExponential_contMDiff g o e).mdifferentiable one_ne_zero (α t))
    ha.mdifferentiableAt
  have hDa : mfderiv 𝓘(ℝ, ℝ) I4 α t 1 = deriv α t := by
    have h : (fderiv ℝ α t) (1 : ℝ) = deriv α t := fderiv_apply_one_eq_deriv
    simpa only [mfderiv_eq_fderiv] using! h
  have hD : mfderiv 𝓘(ℝ, ℝ) I4 (fun s => frameExponential g o e (α s)) t 1 =
      mfderiv I4 I4 (frameExponential g o e) (α t) (deriv α t) := by
    have h := congrArg (fun D : ℝ →L[ℝ] FourSpace => D 1) hm
    exact h.trans (congrArg (mfderiv I4 I4 (frameExponential g o e) (α t)) hDa)
  let w : FourSpace := deriv α t
  have hh := frameExponential_round_metric_eq_sphere hRic hplus hminus e he (α t) hz w w
  have hn : ‖fderiv ℝ (fun x : FourSpace => (roundSphereExponential x).val) (α t) w‖ =
      metricTangentNorm g (frameExponential g o e (α t))
        (mfderiv I4 I4 (frameExponential g o e) (α t) w) := by
    rw [metricTangentNorm_eq_sqrt, hh]
    exact norm_eq_sqrt_real_inner _
  exact (congrArg norm hsp.deriv).trans (hn.trans
    (congrArg (metricTangentNorm g (frameExponential g o e (α t))) hD).symm)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every radial segment through length pi is minimizing in the round
branch. The conclusion follows from the actual cut-time equality. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_round_minimizing (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace)
    (hv : ‖v‖ ≤ Real.pi) :
    metricDistance g e.base (frameExponential g o e v) = ‖v‖ := by
  by_cases hz : v = 0
  · subst v
    rw [frameExponential_zero, norm_zero]
    exact (metricDistance_eq_zero_iff g _ _).mpr rfl
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  have hm : ‖v‖ • q.val ∈ actualMinimizingTangentDomain g o e := by
    apply (actualMinimizingTangentDomain_ray_iff g o e he q ‖v‖ (norm_nonneg _)).mpr
    rw [round_cut_time_all_directions hRic hpositive hplus hminus e he q]
    exact hv
  rwa [hrad] at hm

theorem roundSphereMap_radial_distance (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (p : RoundSphere4) :
    metricDistance g e.base (roundSphereMap g o e p) = Real.arccos (p.val 0) := by
  change metricDistance g e.base (frameExponential g o e (roundLog p)) = _
  rw [frameExponential_round_minimizing hRic hpositive hplus hminus e he _
    (by rw [roundLog_norm]; exact Real.arccos_le_pi _), roundLog_norm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normal Jacobi curvature is constant along each geodesic
in the unit parallel-form branch. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Matrix Jacobi
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem parallel_twoForm_frameValue_along_flow (w : smoothTwoForms o)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (i : Fin 4) (t : ℝ) :
    twoFormFrameValue o w.val (parallelFrameFlowMap g i t e) =
      twoFormFrameValue o w.val e := by
  apply twoFormTensor_injective
  simpa only [twoFormFramedValue_eq] using parallel_twoForm_along_flow w hz e i t

theorem actualJacobiCurvature_parallel_form (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) :
    let a := twoFormFrameValue o w.val e
    actualJacobiCurvature g e t = (1 / 2 : ℝ) • (1 : NormalMatrix) +
      (3 / 2 : ℝ) • Matrix.vecMulVec ![a 0,a 1,a 2] ![a 0,a 1,a 2] := by
  let f := parallelFrameFlowMap g 0 t e
  have hf : f ∈ o.positive := (canonicalParallelMetricData_orientation o hRic 0 t e).mpr he
  have hP := halfFlat_parallel_form_weyl hRic hminus hnorm w hstar hw hz f hf
  dsimp only at hP
  rw [parallel_twoForm_frameValue_along_flow w hz e 0 t] at hP
  have hM : minusWeyl g f.base f.frame = 0 := by
    apply (normalizedBlockNorm_eq_zero_iff _).mp
    rw [← actual_minusNorm_frame o f hf]
    exact (minusNorm_eq_zero_iff o f.base).mpr (hminus f.base)
  change 1 + normalCurvatureDeviation g f.base f.frame firstDirection = _
  rw [normalCurvatureDeviation_eq_of_decomposition g f.base f.frame
    (actual_einstein_decomposition f.frame hRic), hP, hM]
  simp only [normalDeviation, rotated, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two scalar Jacobi factors for Ricci-normalized complex curvature. -/
namespace PositiveEinsteinFour.Jacobi
open EinsteinFour
noncomputable section

def complexJacobiSlow (t : ℝ) : ℝ := Real.sqrt 2 * Real.sin (t / Real.sqrt 2)
def complexJacobiFast (t : ℝ) : ℝ := Real.sin (Real.sqrt 2 * t) / Real.sqrt 2

private theorem sqrt_two_inverse : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
  apply (div_eq_div_iff (by positivity : Real.sqrt 2 ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)).mpr
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem complexJacobiSlow_hasDerivAt (t : ℝ) :
    HasDerivAt complexJacobiSlow (Real.cos (t / Real.sqrt 2)) t := by
  convert (((hasDerivAt_id t).div_const (Real.sqrt 2)).sin.const_mul (Real.sqrt 2)) using 1
  · rfl
  · dsimp only [id_eq]
    field_simp

theorem complexJacobiFast_hasDerivAt (t : ℝ) :
    HasDerivAt complexJacobiFast (Real.cos (Real.sqrt 2 * t)) t := by
  convert (((hasDerivAt_id t).const_mul (Real.sqrt 2)).sin.div_const (Real.sqrt 2)) using 1
  · rfl
  · dsimp only [id_eq]
    field_simp

theorem complexJacobiSlow_velocity_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => Real.cos (s / Real.sqrt 2))
      (-(1 / 2 : ℝ) * complexJacobiSlow t) t := by
  convert ((hasDerivAt_id t).div_const (Real.sqrt 2)).cos using 1 <;> dsimp only [id_eq]
  rw [sqrt_two_inverse]
  unfold complexJacobiSlow
  ring

theorem complexJacobiFast_velocity_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => Real.cos (Real.sqrt 2 * s))
      (-2 * complexJacobiFast t) t := by
  convert ((hasDerivAt_id t).const_mul (Real.sqrt 2)).cos using 1 <;> dsimp only [id_eq]
  unfold complexJacobiFast
  rw [div_eq_mul_one_div, sqrt_two_inverse]
  ring

end
end PositiveEinsteinFour.Jacobi
end


section

/-! Actual complex-space-form curvature in the dimension-one branch. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular TraceHessian Matrix
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem halfFlat_parallel_form_curvature (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    (fun i j k l => twoFormMetricCurvatureTensor g e ![i,j,k,l]) =
      complexSpaceCurvature (twoFormFrameValue o w.val e) := by
  have hm : minusWeyl g e.base e.frame = 0 := by
    apply (normalizedBlockNorm_eq_zero_iff _).mp
    rw [← actual_minusNorm_frame o e he]
    exact (minusNorm_eq_zero_iff o e.base).mpr (hminus e.base)
  have hp := halfFlat_parallel_form_weyl hRic hminus hnorm w hstar hw hz e he
  have hs : twoFormHodge (twoFormFrameValue o w.val e) = twoFormFrameValue o w.val e := by
    rw [← twoFormFrameValue_hodge o w.val e he]
    congr 1
    exact funext hstar
  have hn : ‖twoFormFrameValue o w.val e‖ ^ 2 = 2 := by
    rw [twoFormFrameValue_norm, hw]
  have hC := selfDual_complexSpaceCurvature _ hs hn
  funext i j k l
  simp only [twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
  rw [actual_einstein_decomposition e.frame hRic, hm, hp]
  exact congrFun (congrFun (congrFun (congrFun hC i) j) k) l

variable [PreconnectedSpace M] [SecondCountableTopology M]

theorem actual_dimension_one_complex_curvature (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1) :
    ∃ w : smoothTwoForms o,
      (∀ x, twoFormHodge (w.val x) = w.val x) ∧
      (∀ x, ‖w.val x‖ ^ 2 = 2) ∧
      (∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0) ∧
      ∀ e ∈ o.positive,
        (fun i j k l => twoFormMetricCurvatureTensor g e ![i,j,k,l]) =
          complexSpaceCurvature (twoFormFrameValue o w.val e) := by
  obtain ⟨w,hs,hn,hp⟩ := halfFlat_dimension_one_parallel_unit_form hRic hminus hdim
  refine ⟨w,hs,hn,hp,fun e he => ?_⟩
  exact halfFlat_parallel_form_curvature hRic hminus
    (halfFlat_dimension_one_norm hRic hminus hdim) w hs hn hp e he

end
end PositiveEinsteinFour.Geometry
end


section

/-! Once every geodesic minimizes up to pi, the no-corner lemma rules out
multiple radial directions meeting before pi. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem round_direction_injective (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (q p : Directions)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) Real.pi)
    (hqp : frameExponential g o e (t • q.val) = frameExponential g o e (t • p.val)) : q = p := by
  let s := (Real.pi - t) / 2
  have hs : 0 < s := by dsimp [s]; linarith [ht.2]
  have hsum : t + s < Real.pi := by dsimp [s]; linarith [ht.2]
  let f := e.rotate (orientedToOrthogonal (directionOrientedMatrix q))
  let F := parallelFrameFlowMap g 0 (-s) f
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he _
  have hF : F ∈ o.positive := parallelFrameFlowMap_positive g o f hf (-s)
  have hbase : F.base = frameExponential g o e ((-s) • q.val) :=
    (frameExponential_direction_ray g o e he q (-s)).symm
  have hend : frameExponential g o F ((t + s) • coordinateVector 0) =
      frameExponential g o e (t • p.val) := by
    rw [frameExponential_shift_first g o f hf (t + s) (-s),
      show t + s + -s = t by ring]
    exact (frameExponential_direction_ray g o e he q t).symm.trans hqp
  have hnorm : ‖(t + s) • (coordinateVector 0 : FourSpace)‖ = t + s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (add_pos ht.1 hs)]
    simp [coordinateVector]
  have hmin := frameExponential_round_minimizing hRic hpositive hplus hminus F hF
    ((t + s) • coordinateVector 0) (by rw [hnorm]; exact hsum.le)
  rw [hbase, hend, hnorm] at hmin
  have hd := (metricDistance_eq_iff g _ _ (add_pos ht.1 hs).le).mp hmin
  rw [add_comm t s] at hd
  exact Subtype.ext (frameExponential_no_minimizing_corner g o e q.val p.val
    q.property p.property s t hs ht.1 hd)

theorem frameExponential_round_injOn_ball (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    InjOn (frameExponential g o e) (Metric.ball 0 Real.pi) := by
  intro v hv w hw heq
  have hvπ : ‖v‖ < Real.pi := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  have hwπ : ‖w‖ < Real.pi := by simpa only [Metric.mem_ball, dist_zero_right] using hw
  have hn : ‖v‖ = ‖w‖ := by
    rw [← frameExponential_round_minimizing hRic hpositive hplus hminus e he v hvπ.le,
      ← frameExponential_round_minimizing hRic hpositive hplus hminus e he w hwπ.le, heq]
  by_cases hz : v = 0
  · subst v
    have hwzero : w = 0 := norm_eq_zero.mp (by simpa only [norm_zero] using hn.symm)
    exact hwzero.symm
  have hwz : w ≠ 0 := fun h => hz (norm_eq_zero.mp (by simpa only [h, norm_zero] using hn))
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
  let p : Directions := ⟨‖w‖⁻¹ • w, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hwz)]⟩
  have hq : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  have hp : ‖v‖ • p.val = w := by
    change ‖v‖ • (‖w‖⁻¹ • w) = w
    rw [hn, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hwz), one_smul]
  have hqp : q = p := round_direction_injective hRic hpositive hplus hminus e he q p
    ‖v‖ ⟨norm_pos_iff.mpr hz, hvπ⟩ (by rwa [hq, hp])
  rw [← hq, hqp, hp]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact matrix Jacobi solution for the two eigenspaces of the
Ricci-normalized complex-space-form curvature. -/
namespace PositiveEinsteinFour.Jacobi
open EinsteinFour Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section

def complexJacobiCurvature (P : NormalMatrix) : NormalMatrix :=
  (1 / 2 : ℝ) • (1 : NormalMatrix) + (3 / 2 : ℝ) • P

def complexJacobiPosition (P : NormalMatrix) (t : ℝ) : NormalMatrix :=
  complexJacobiSlow t • (1 - P) + complexJacobiFast t • P

def complexJacobiVelocity (P : NormalMatrix) (t : ℝ) : NormalMatrix :=
  Real.cos (t / Real.sqrt 2) • (1 - P) + Real.cos (Real.sqrt 2 * t) • P

theorem complexJacobiCurvature_mul_projection (P : NormalMatrix) (hP : P * P = P) :
    complexJacobiCurvature P * P = (2 : ℝ) • P := by
  rw [complexJacobiCurvature, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.one_mul, hP]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem complexJacobiCurvature_mul_complement (P : NormalMatrix) (hP : P * P = P) :
    complexJacobiCurvature P * (1 - P) = (1 / 2 : ℝ) • (1 - P) := by
  rw [Matrix.mul_sub, Matrix.mul_one, complexJacobiCurvature_mul_projection P hP]
  ext i j
  simp only [complexJacobiCurvature, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

def complexModelJacobi (P : NormalMatrix) (hP : P * P = P) :
    MatrixJacobiSolution (fun _ => complexJacobiCurvature P) where
  J := complexJacobiPosition P
  V := complexJacobiVelocity P
  initial_position := by
    simp [complexJacobiPosition, complexJacobiSlow, complexJacobiFast]
  initial_velocity := by
    simp [complexJacobiVelocity]
  position_derivative t :=
    ((complexJacobiSlow_hasDerivAt t).smul_const (1 - P)).add
      ((complexJacobiFast_hasDerivAt t).smul_const P)
  velocity_derivative t := by
    have h := ((complexJacobiSlow_velocity_hasDerivAt t).smul_const (1 - P)).add
      ((complexJacobiFast_velocity_hasDerivAt t).smul_const P)
    convert h using 1
    · rfl
    · rw [complexJacobiPosition, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
        complexJacobiCurvature_mul_complement P hP, complexJacobiCurvature_mul_projection P hP]
      ext i j
      simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
        smul_eq_mul]
      ring

theorem MatrixJacobiSolution.eq_complex_projection {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (P : NormalMatrix) (hP : P * P = P)
    (hR : ∀ s, R s = complexJacobiCurvature P) :
    d.J = complexJacobiPosition P ∧ d.V = complexJacobiVelocity P := by
  let m := complexModelJacobi P hP
  let e : MatrixJacobiSolution R :=
    { J := m.J
      V := m.V
      initial_position := m.initial_position
      initial_velocity := m.initial_velocity
      position_derivative := m.position_derivative
      velocity_derivative := fun t => by
        simpa only [hR t] using m.velocity_derivative t }
  exact d.unique e ‖complexJacobiCurvature P‖₊ (fun s => by rw [hR]; rfl)

end
end PositiveEinsteinFour.Jacobi
end


section

/-! The exact trigonometric coefficients in the Fubini--Study polar metric. -/
namespace PositiveEinsteinFour.Jacobi
noncomputable section

theorem complexJacobiSlow_sq (t : ℝ) :
    complexJacobiSlow t ^ 2 = 2 * Real.sin (t / Real.sqrt 2) ^ 2 := by
  rw [complexJacobiSlow,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem complexJacobiFast_sq (t : ℝ) :
    complexJacobiFast t ^ 2 =
      2 * Real.sin (t / Real.sqrt 2) ^ 2 * Real.cos (t / Real.sqrt 2) ^ 2 := by
  have htime : Real.sqrt 2 * t = 2 * (t / Real.sqrt 2) := by
    calc
      _ = (Real.sqrt 2 * Real.sqrt 2) * (t / Real.sqrt 2) := by
        field_simp
      _ = _ := by rw [← pow_two,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [complexJacobiFast,htime,Real.sin_two_mul,div_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem complexJacobiFast_sq_sub_slow_sq (t : ℝ) :
    complexJacobiFast t ^ 2 - complexJacobiSlow t ^ 2 =
      -2 * Real.sin (t / Real.sqrt 2) ^ 4 := by
  rw [complexJacobiFast_sq,complexJacobiSlow_sq]
  have h := Real.sin_sq_add_cos_sq (t / Real.sqrt 2)
  nlinarith [sq_nonneg (Real.sin (t / Real.sqrt 2)),
    congrArg (fun x : ℝ => Real.sin (t / Real.sqrt 2) ^ 2 * x) h]

end
end PositiveEinsteinFour.Jacobi
end


section

/-! The round sphere map is globally bijective, hence a homeomorphism. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem roundSphereMap_injective (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    Function.Injective (roundSphereMap g o e) := by
  intro p q hpq
  have hn : ‖roundLog p‖ = ‖roundLog q‖ := by
    rw [roundLog_norm, roundLog_norm,
      ← roundSphereMap_radial_distance hRic hpositive hplus hminus e he p,
      ← roundSphereMap_radial_distance hRic hpositive hplus hminus e he q, hpq]
  have hsouth : ‖roundLog (antipode roundNorth)‖ = Real.pi := by
    rw [roundLog_norm]
    simp [antipode, roundNorth]
  by_cases hp : p = antipode roundNorth
  · subst p
    by_cases hq : q = antipode roundNorth
    · exact hq.symm
    · have hlt := roundLog_norm_lt_pi hq
      rw [← hn, hsouth] at hlt
      exact False.elim ((lt_irrefl _) hlt)
  by_cases hq : q = antipode roundNorth
  · subst q
    have hlt := roundLog_norm_lt_pi hp
    rw [hn, hsouth] at hlt
    exact False.elim ((lt_irrefl _) hlt)
  have hlog : roundLog p = roundLog q :=
    frameExponential_round_injOn_ball hRic hpositive hplus hminus e he
      (by simpa only [Metric.mem_ball, dist_zero_right] using roundLog_norm_lt_pi hp)
      (by simpa only [Metric.mem_ball, dist_zero_right] using roundLog_norm_lt_pi hq) hpq
  have h := congrArg roundSphereExponential hlog
  simpa only [roundSphereExponential_log] using h

def actualRoundHomeomorph (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) : RoundSphere4 ≃ₜ M := by
  let : CompactSpace RoundSphere4 := isCompact_iff_compactSpace.mp roundSphere_compact
  let E := Equiv.ofBijective (roundSphereMap g o e)
    ⟨roundSphereMap_injective hRic hpositive hplus hminus e he,
      roundSphereMap_surjective hRic hplus hminus e he⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := E)
    (roundSphereMap_continuous hRic hplus hminus e he)

theorem actualRoundHomeomorph_apply (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (p : RoundSphere4) :
    actualRoundHomeomorph hRic hpositive hplus hminus e he p = roundSphereMap g o e p := rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The determinant and first zero of the complex-space-form Jacobi matrix. -/
namespace PositiveEinsteinFour.Jacobi
open EinsteinFour Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section

theorem rankOne_two_eigenvalue_determinant (v : Fin 3 → ℝ)
    (hv : dotProduct v v = 1) (a b : ℝ) :
    Matrix.det (a • ((1 : NormalMatrix) - Matrix.vecMulVec v v) +
      b • Matrix.vecMulVec v v) = a ^ 2 * b := by
  have hn : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_succ, pow_two, add_assoc] using hv
  have he : Matrix.det (a • ((1 : NormalMatrix) - Matrix.vecMulVec v v) +
      b • Matrix.vecMulVec v v) =
      a ^ 3 + a ^ 2 * (b - a) * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) := by
    simp [Matrix.det_fin_three, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.vecMulVec_apply]
    ring
  rw [he, hn]
  ring

theorem complexJacobiPosition_det (v : Fin 3 → ℝ) (hv : dotProduct v v = 1) (t : ℝ) :
    Matrix.det (complexJacobiPosition (Matrix.vecMulVec v v) t) =
      complexJacobiSlow t ^ 2 * complexJacobiFast t :=
  rankOne_two_eigenvalue_determinant v hv _ _

def complexJacobiRadius : ℝ := Real.pi / Real.sqrt 2

theorem complexJacobiRadius_pos : 0 < complexJacobiRadius := by
  exact div_pos Real.pi_pos (by positivity)

theorem complexJacobiFast_radius : complexJacobiFast complexJacobiRadius = 0 := by
  unfold complexJacobiFast complexJacobiRadius
  have h : Real.sqrt 2 * (Real.pi / Real.sqrt 2) = Real.pi := by field_simp
  rw [h, Real.sin_pi, zero_div]

theorem complexJacobiFast_pos {t : ℝ} (ht : 0 < t) (hr : t < complexJacobiRadius) :
    0 < complexJacobiFast t := by
  have hs : 0 < Real.sqrt 2 := by positivity
  apply div_pos _ hs
  apply Real.sin_pos_of_pos_of_lt_pi (mul_pos hs ht)
  have h := mul_lt_mul_of_pos_left hr hs
  dsimp only [complexJacobiRadius] at h
  have he : Real.sqrt 2 * (Real.pi / Real.sqrt 2) = Real.pi := by field_simp
  rwa [he] at h

theorem complexJacobiSlow_pos {t : ℝ} (ht : 0 < t) (hr : t < complexJacobiRadius) :
    0 < complexJacobiSlow t := by
  have hs : 0 < Real.sqrt 2 := by positivity
  apply mul_pos hs
  apply Real.sin_pos_of_pos_of_lt_pi (div_pos ht hs)
  have h := div_lt_div_of_pos_right hr hs
  dsimp only [complexJacobiRadius] at h
  rw [div_div, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h
  linarith [Real.pi_pos]

theorem complexJacobiPosition_det_pos (v : Fin 3 → ℝ) (hv : dotProduct v v = 1)
    {t : ℝ} (ht : 0 < t) (hr : t < complexJacobiRadius) :
    0 < Matrix.det (complexJacobiPosition (Matrix.vecMulVec v v) t) := by
  rw [complexJacobiPosition_det v hv]
  exact mul_pos (sq_pos_of_pos (complexJacobiSlow_pos ht hr)) (complexJacobiFast_pos ht hr)

theorem complexJacobiPosition_det_radius (v : Fin 3 → ℝ) (hv : dotProduct v v = 1) :
    Matrix.det (complexJacobiPosition (Matrix.vecMulVec v v) complexJacobiRadius) = 0 := by
  rw [complexJacobiPosition_det v hv, complexJacobiFast_radius, mul_zero]

end
end PositiveEinsteinFour.Jacobi
end


section

/-! Every point in the round branch lies on a minimizing segment from a
point to its unique antipodal endpoint. The resulting distance sum turns
one distance inequality for the sphere homeomorphism into equality. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

omit [T3Space M] [PreconnectedSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]
    [SecondCountableTopology M] in
theorem metricDistance_symm (g : SmoothMetric M) (x y : M) :
    metricDistance g x y = metricDistance g y x := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  change (Manifold.riemannianEDist I4 x y).toReal = (Manifold.riemannianEDist I4 y x).toReal
  rw [Manifold.riemannianEDist_comm]

theorem round_antipodal_distance (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    metricDistance g e.base (roundAntipodalPoint g o e) = Real.pi := by
  have h := roundSphereMap_radial_distance hRic hpositive hplus hminus e he
    (antipode roundNorth)
  rw [roundSphereMap_south] at h
  simpa [antipode, roundNorth] using h

theorem round_antipodal_distance_sum (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (x : M) :
    metricDistance g e.base x + metricDistance g (roundAntipodalPoint g o e) x = Real.pi := by
  obtain ⟨p, rfl⟩ := roundSphereMap_surjective hRic hplus hminus e he x
  have hbase := roundSphereMap_radial_distance hRic hpositive hplus hminus e he p
  have hu := roundSphereMap_distance_south hRic hplus hminus e he p
  have hr : metricDistance g (roundAntipodalPoint g o e) (roundSphereMap g o e p) ≤
      Real.pi - Real.arccos (p.val 0) := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
    simpa only [metricDistance, ENNReal.toReal_ofReal
      (sub_nonneg.mpr (Real.arccos_le_pi _))] using hh
  have hl := metricDistance_triangle g e.base (roundSphereMap g o e p)
    (roundAntipodalPoint g o e)
  rw [round_antipodal_distance hRic hpositive hplus hminus e he,
    metricDistance_symm g (roundSphereMap g o e p) (roundAntipodalPoint g o e)] at hl
  linarith

omit [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]
    [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]
    [SecondCountableTopology M] [PreconnectedSpace M] in
theorem roundDistance_antipode_left (p q : RoundSphere4) :
    roundDistance (antipode p) q = Real.pi - roundDistance p q := by
  simp only [roundDistance, antipode, inner_neg_left, Real.arccos_neg]

omit [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]
    [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]
    [SecondCountableTopology M] [PreconnectedSpace M] in
theorem roundDistance_antipodal (p : RoundSphere4) :
    roundDistance p (antipode p) = Real.pi := by
  rw [roundDistance_comm, roundDistance_antipode_left, roundDistance_self, sub_zero]

theorem roundSphereMap_distance_eq_of_le (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hle : ∀ p q : RoundSphere4, roundDistance p q ≤
      metricDistance g (roundSphereMap g o e p) (roundSphereMap g o e q)) :
    ∀ p q : RoundSphere4, metricDistance g (roundSphereMap g o e p)
      (roundSphereMap g o e q) = roundDistance p q := by
  intro p q
  let H := actualRoundHomeomorph hRic hpositive hplus hminus e he
  let f : FrameBundle g := ⟨H p, o.frame (H p)⟩
  have hf : f ∈ o.positive := o.frame_positive (H p)
  let r := H.symm (roundAntipodalPoint g o f)
  have hHr : H r = roundAntipodalPoint g o f := H.apply_symm_apply _
  have hs (x : RoundSphere4) : metricDistance g (H p) (H x) +
      metricDistance g (H r) (H x) = Real.pi := by
    rw [hHr]
    exact round_antipodal_distance_sum hRic hpositive hplus hminus f hf (H x)
  have hranti : r = antipode p := by
    have hsum := hs (antipode p)
    have hp := hle p (antipode p)
    have hr := hle r (antipode p)
    rw [roundDistance_antipodal] at hp
    have hz : roundDistance r (antipode p) = 0 := by
      have hn := roundDistance_nonneg r (antipode p)
      change Real.pi ≤ metricDistance g (H p) (H (antipode p)) at hp
      change roundDistance r (antipode p) ≤ metricDistance g (H r) (H (antipode p)) at hr
      linarith
    exact (roundDistance_eq_zero_iff _ _).mp hz
  have hsum := hs q
  rw [hranti] at hsum
  have hq := hle (antipode p) q
  rw [roundDistance_antipode_left] at hq
  have hl := hle p q
  change metricDistance g (H p) (H q) = roundDistance p q
  change Real.pi - roundDistance p q ≤ metricDistance g (H (antipode p)) (H q) at hq
  change roundDistance p q ≤ metricDistance g (H p) (H q) at hl
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! The genuine exponential inverse in the open round normal ball is C1.
The invertible derivative is derived from the actual Jacobi solution. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_round_mfderiv_isUnit (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace)
    (hv : v ≠ 0) (hpi : ‖v‖ < Real.pi) :
    IsUnit (show FourSpace →L[ℝ] FourSpace from mfderiv I4 I4 (frameExponential g o e) v) := by
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
  let Q := directionOrientedMatrix q
  let L := (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
    (orientedToOrthogonal Q).property).toContinuousLinearEquiv
  let f := e.rotate (orientedToOrthogonal Q)
  let x := ‖v‖ • coordinateVector 0
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he Q
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
  have hpoint : L x = v := by
    change L (‖v‖ • coordinateVector 0) = v
    rw [map_smul]
    exact (congrArg (fun z => ‖v‖ • z) (directionRotation_first q)).trans hrad
  let d := (parallelFrameFlowMap g 0 ‖v‖ f).base
  have hd : d ∈ (chartAt FourSpace d).source := mem_chart_source FourSpace d
  have hexp : frameExponential g o f x = d :=
    frameExponential_first_ray g o f hf ‖v‖ (norm_pos_iff.mpr hv)
  have hunit : IsUnit (show FourSpace →L[ℝ] FourSpace from mfderiv I4 I4 (frameExponential g o f) x) := by
    rw [← frameExponential_center_fderiv, hexp,
      (frameExponential_hasFDerivAt g o hRic d f hf ‖v‖ (norm_pos_iff.mpr hv) hd).fderiv]
    apply frameExponential_preconjugate_isUnit g hRic d f ‖v‖ (norm_pos_iff.mpr hv)
    · rw [actualFirstConjugateTime_eq_pi_of_weyl_zero hRic hplus hminus f hf]
      exact hpi
    · exact hd
  have hD : (show FourSpace →L[ℝ] FourSpace from mfderiv I4 I4 (frameExponential g o e) v) =
      (show FourSpace →L[ℝ] FourSpace from mfderiv I4 I4 (frameExponential g o f) x) *
        (L.symm : FourSpace →L[ℝ] FourSpace) := by
    apply ContinuousLinearMap.ext
    intro w
    have h := frameExponential_rotate_mfderiv g o e Q x (L.symm w)
    change _ = mfderiv I4 I4 (frameExponential g o e) (L x) (L (L.symm w)) at h
    rw [hpoint, L.apply_symm_apply] at h
    exact h.symm
  rw [hD]
  exact hunit.mul L.symm.toUnit.isUnit

theorem frameExponential_round_inverse_contMDiffAt (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace)
    (hv : v ≠ 0) (hpi : ‖v‖ < Real.pi)
    (C : OpenPartialHomeomorph FourSpace M) (hCv : v ∈ C.source)
    (hC : EqOn C (frameExponential g o e) C.source) :
    ContMDiffAt I4 I4 1 C.symm (frameExponential g o e v) := by
  apply frameExponential_local_inverse_contMDiffAt g o e v C hCv hC
  rw [frameExponential_center_fderiv]
  exact frameExponential_round_mfderiv_isUnit hRic hplus hminus e he v hv hpi

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Jacobi fields and first conjugate radius in the parallel
complex-curvature branch. No model identification is used. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Matrix Jacobi
open scoped BigOperators Manifold ContDiff Matrix.Norms.L2Operator
noncomputable section

theorem selfDual_firstThree_unit (a : TwoFormFour)
    (ha : twoFormHodge a = a) (hn : ‖a‖ ^ 2 = 2) :
    dotProduct ![a 0,a 1,a 2] ![a 0,a 1,a 2] = 1 := by
  have h3 : a 3 = a 2 := congrArg (fun b : TwoFormFour => b 2) ha
  have h4 : a 4 = -a 1 := by
    have h := congrArg (fun b : TwoFormFour => b 1) ha
    change -a 4 = a 1 at h
    linarith
  have h5 : a 5 = a 0 := congrArg (fun b : TwoFormFour => b 0) ha
  have h := EuclideanSpace.real_norm_sq_eq a
  simp [Fin.sum_univ_succ, h3, h4, h5] at h
  simp [dotProduct, Fin.sum_univ_succ]
  nlinarith only [h,hn]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem unitSelfDual_frame_firstThree (w : smoothTwoForms o)
    (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    let a := twoFormFrameValue o w.val e
    dotProduct ![a 0,a 1,a 2] ![a 0,a 1,a 2] = 1 := by
  apply selfDual_firstThree_unit
  · rw [← twoFormFrameValue_hodge o w.val e he]
    congr 1
    exact funext hstar
  · rw [twoFormFrameValue_norm, hw]

theorem actualJacobi_parallel_form (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    let a := twoFormFrameValue o w.val e
    let P := Matrix.vecMulVec ![a 0,a 1,a 2] ![a 0,a 1,a 2]
    (actualJacobiSolution g hRic e).J = complexJacobiPosition P ∧
      (actualJacobiSolution g hRic e).V = complexJacobiVelocity P := by
  let a := twoFormFrameValue o w.val e
  let v : Fin 3 → ℝ := ![a 0,a 1,a 2]
  have hv : dotProduct v v = 1 := unitSelfDual_frame_firstThree w hstar hw e he
  have hP : Matrix.vecMulVec v v * Matrix.vecMulVec v v = Matrix.vecMulVec v v := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hv, one_smul]
  exact (actualJacobiSolution g hRic e).eq_complex_projection _ hP
    (fun t => actualJacobiCurvature_parallel_form hRic hminus hnorm w hstar hw hz e he t)

theorem actualFirstConjugateTime_parallel_form (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    actualFirstConjugateTime g hRic e = complexJacobiRadius := by
  let a := twoFormFrameValue o w.val e
  let v : Fin 3 → ℝ := ![a 0,a 1,a 2]
  have hv : dotProduct v v = 1 := unitSelfDual_frame_firstThree w hstar hw e he
  have hJ : (actualJacobiSolution g hRic e).J =
      complexJacobiPosition (Matrix.vecMulVec v v) :=
    (actualJacobi_parallel_form hRic hminus hnorm w hstar hw hz e he).1
  apply le_antisymm
  · by_contra hnot
    have hc : complexJacobiRadius < actualFirstConjugateTime g hRic e := lt_of_not_ge hnot
    have hu := actualJacobi_isUnit_before_firstConjugate g hRic e _ complexJacobiRadius_pos hc
    rw [hJ] at hu
    have hn := (Matrix.isUnit_iff_isUnit_det _).mp hu
    exact hn.ne_zero (complexJacobiPosition_det_radius v hv)
  · by_contra hnot
    have hc : actualFirstConjugateTime g hRic e < complexJacobiRadius := lt_of_not_ge hnot
    apply actualFirstConjugateTime_singular g hRic e
    rw [hJ]
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    exact isUnit_iff_ne_zero.mpr
      (complexJacobiPosition_det_pos v hv (actualFirstConjugateTime_pos g hRic e) hc).ne'

end
end PositiveEinsteinFour.Geometry
end


section

/-! A smooth manifold curve lifts through the actual sphere homeomorphism
with the same speed away from the two polar values. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem round_inverse_curve_speed (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    {γ : ℝ → M} {t : ℝ} (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I4 1 γ t)
    (hnorth : (actualRoundHomeomorph hRic hpositive hplus hminus e he).symm (γ t) ≠ roundNorth)
    (hsouth : (actualRoundHomeomorph hRic hpositive hplus hminus e he).symm (γ t) ≠
      antipode roundNorth) :
    ∃ w : EuclideanSpace ℝ (Fin 5),
      HasDerivAt (fun s => ((actualRoundHomeomorph hRic hpositive hplus hminus e he).symm
        (γ s)).val) w t ∧
      ‖w‖ = metricTangentNorm g (γ t) (mfderiv 𝓘(ℝ, ℝ) I4 γ t 1) := by
  let H := actualRoundHomeomorph hRic hpositive hplus hminus e he
  let p := H.symm (γ t)
  let v := roundLog p
  have hp : roundSphereExponential v = p := roundSphereExponential_log p
  have hv : v ≠ 0 := by
    intro hz
    have hpn : p = roundNorth := by rw [← hp, hz, roundSphereExponential_zero]
    exact hnorth hpn
  have hvpi : ‖v‖ < Real.pi := roundLog_norm_lt_pi hsouth
  have hpoint : frameExponential g o e v = γ t := by
    change H p = γ t
    exact H.apply_symm_apply (γ t)
  obtain ⟨C, hCv, hC⟩ := frameExponential_round_localChart hRic hplus hminus e he v hvpi
  have hCt : C v = γ t := (hC hCv).trans hpoint
  have hy : γ t ∈ C.target := hCt ▸ C.map_source hCv
  let α : ℝ → FourSpace := fun s => C.symm (γ s)
  have hαt : α t = v := by
    change C.symm (γ t) = v
    rw [← hCt]
    exact C.left_inv hCv
  have hα : ContDiffAt ℝ 1 α t := by
    have hi := frameExponential_round_inverse_contMDiffAt hRic hplus hminus e he v hv hvpi C hCv hC
    rw [hpoint] at hi
    exact (hi.comp t hγ).contDiffAt
  have hn : ∀ᶠ s in 𝓝 t, γ s ∈ C.target :=
    hγ.continuousAt.preimage_mem_nhds (C.open_target.mem_nhds hy)
  have hEq : (fun s => frameExponential g o e (α s)) =ᶠ[𝓝 t] γ := by
    filter_upwards [hn] with s hs
    exact (hC (C.map_target hs)).symm.trans (C.right_inv hs)
  have hnorm : ∀ᶠ s in 𝓝 t, ‖α s‖ < Real.pi :=
    hα.continuousAt.norm.eventually_lt continuousAt_const (by rw [hαt]; exact hvpi)
  have hLift : (fun s => H.symm (γ s)) =ᶠ[𝓝 t]
      (fun s => roundSphereExponential (α s)) := by
    filter_upwards [hEq, hnorm] with s hs hsn
    apply H.injective
    rw [H.apply_symm_apply]
    change γ s = roundSphereMap g o e (roundSphereExponential (α s))
    rw [roundSphereMap_exponential hRic hplus hminus e he _ hsn.le, hs]
  have hdα := hα.differentiableAt one_ne_zero
  have hzα : α t ≠ 0 := by rwa [hαt]
  have hdsp := (roundSphereExponential_differentiableAt (α t) hzα).comp t hdα
  refine ⟨deriv (fun s => (roundSphereExponential (α s)).val) t,
    hdsp.hasDerivAt.congr_of_eventuallyEq ?_, ?_⟩
  · exact hLift.mono (fun _ h => congrArg Subtype.val h)
  · rw [frameExponential_round_curve_speed hRic hplus hminus e he hdα hzα]
    exact metric_curve_speed_congr hEq

end
end PositiveEinsteinFour.Geometry
end


section

/-! The complex line tangent is in the actual exponential kernel at the
first conjugate radius. -/
namespace PositiveEinsteinFour.Jacobi
open EinsteinFour Matrix
noncomputable section

theorem complexJacobiPosition_radius_mulVec (v : Fin 3 → ℝ)
    (hv : dotProduct v v = 1) :
    complexJacobiPosition (Matrix.vecMulVec v v) complexJacobiRadius *ᵥ v = 0 := by
  have hp : Matrix.vecMulVec v v *ᵥ v = v := by
    rw [Matrix.vecMulVec_mulVec, hv]
    simp
  rw [complexJacobiPosition, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.sub_mulVec, Matrix.one_mulVec, hp, sub_self, smul_zero,
    complexJacobiFast_radius, zero_smul, add_zero]

end
end PositiveEinsteinFour.Jacobi

namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Jacobi Angular
open scoped BigOperators Manifold ContDiff Matrix.Norms.L2Operator
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_complex_normal_kernel (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (c : M)
    (hc : (parallelFrameFlowMap g 0 complexJacobiRadius e).base ∈ (chartAt FourSpace c).source) :
    let a := twoFormFrameValue o w.val e
    fderiv ℝ (fun z : FourSpace => chartAt FourSpace c (frameExponential g o e z))
      (complexJacobiRadius • coordinateVector 0)
      (WithLp.toLp 2 (Fin.cons 0 ![a 0,a 1,a 2])) = 0 := by
  let a := twoFormFrameValue o w.val e
  let v : Fin 3 → ℝ := ![a 0,a 1,a 2]
  have hv : dotProduct v v = 1 := unitSelfDual_frame_firstThree w hstar hw e he
  have hJ := (actualJacobi_parallel_form hRic hminus hnorm w hstar hw hz e he).1
  rw [(frameExponential_hasFDerivAt g o hRic c e he complexJacobiRadius
    complexJacobiRadius_pos hc).fderiv, hJ]
  change WithLp.toLp 2 ((frameChartMatrix g c (parallelFrameFlowMap g 0 complexJacobiRadius e) *
    jacobiBlockMatrix 1 (complexJacobiRadius⁻¹ •
      complexJacobiPosition (Matrix.vecMulVec v v) complexJacobiRadius)) *ᵥ Fin.cons 0 v) = 0
  rw [← Matrix.mulVec_mulVec, jacobiBlockMatrix_mulVec]
  simp only [Fin.cons_zero, Fin.cons_succ, mul_zero]
  rw [Matrix.smul_mulVec, complexJacobiPosition_radius_mulVec v hv, smul_zero]
  have hzvec : (Fin.cons 0 (0 : Fin 3 → ℝ) : Fin 4 → ℝ) = 0 := by
    ext i
    fin_cases i <;> rfl
  rw [hzvec, Matrix.mulVec_zero, WithLp.toLp_zero]

theorem frameExponential_complex_first_kernel (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (c : M)
    (hc : (parallelFrameFlowMap g 0 complexJacobiRadius e).base ∈ (chartAt FourSpace c).source) :
    fderiv ℝ (fun z : FourSpace => chartAt FourSpace c (frameExponential g o e z))
      (complexJacobiRadius • coordinateVector 0)
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
        (twoFormMatrix (twoFormFrameValue o w.val e)) (coordinateVector 0)) = 0 := by
  let a := twoFormFrameValue o w.val e
  have hvec : Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (twoFormMatrix a) (coordinateVector 0) =
      -(WithLp.toLp 2 (Fin.cons 0 ![a 0,a 1,a 2])) := by
    ext i
    change ((twoFormMatrix a) *ᵥ Pi.single 0 1) i = _
    rw [Matrix.mulVec_single_one]
    fin_cases i <;> simp [Matrix.col, twoFormMatrix]
  rw [hvec, map_neg, frameExponential_complex_normal_kernel hRic hminus hnorm w hstar hw hz e he c hc,
    neg_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Squaring the actual complex Jacobi solution retains its two orthogonal
eigenspaces. This is the pullback metric, rather than merely its determinant. -/
namespace PositiveEinsteinFour.Jacobi
open EinsteinFour Matrix PositiveEinsteinFour.Geometry
noncomputable section

def complexJacobiGram (P : NormalMatrix) (t : ℝ) : NormalMatrix :=
  complexJacobiSlow t ^ 2 • (1 - P) + complexJacobiFast t ^ 2 • P

theorem complexJacobiPosition_transpose_mul (P : NormalMatrix)
    (hs : Pᵀ = P) (hp : P * P = P) (t : ℝ) :
    (complexJacobiPosition P t)ᵀ * complexJacobiPosition P t = complexJacobiGram P t := by
  have hPQ : P * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hp, sub_self]
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPQ, sub_zero]
  have hQP : (1 - P) * P = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hp, sub_self]
  rw [complexJacobiPosition, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_one, hs,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.smul_mul, Matrix.mul_smul, hQ, hPQ, hQP, hp, smul_zero,
    add_zero, zero_add, smul_smul, complexJacobiGram, pow_two]

theorem jacobiBlockMatrix_transpose_mul (a : ℝ) (A : NormalMatrix) :
    (jacobiBlockMatrix a A)ᵀ * jacobiBlockMatrix a A =
      jacobiBlockMatrix (a ^ 2) (Aᵀ * A) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [jacobiBlockMatrix, Fin.sum_univ_succ, pow_two]
    · simp [jacobiBlockMatrix, Fin.sum_univ_succ]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [jacobiBlockMatrix, Fin.sum_univ_succ]
    · simp [jacobiBlockMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

end
end PositiveEinsteinFour.Jacobi
end


section

/-! Exact radial volume of the Ricci-normalized complex Jacobi solution. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Jacobi MeasureTheory Set
open scoped ENNReal
noncomputable section

def complexRadialDensity (t : ℝ) : ℝ := complexJacobiSlow t ^ 2 * complexJacobiFast t

theorem complexRadialDensity_eq (t : ℝ) :
    complexRadialDensity t =
      2 * Real.sqrt 2 * Real.sin (t / Real.sqrt 2) ^ 3 * Real.cos (t / Real.sqrt 2) := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have harg : Real.sqrt 2 * t = 2 * (t / Real.sqrt 2) := by
    calc
      _ = (Real.sqrt 2 * Real.sqrt 2) * (t / Real.sqrt 2) := by field_simp
      _ = _ := by rw [hs]
  unfold complexRadialDensity complexJacobiSlow complexJacobiFast
  rw [harg, Real.sin_two_mul]
  field_simp

theorem complexRadialPrimitive_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => Real.sin (s / Real.sqrt 2) ^ 4) (complexRadialDensity t) t := by
  convert (((hasDerivAt_id t).div_const (Real.sqrt 2)).sin.pow 4) using 1
  · rfl
  · rw [complexRadialDensity_eq]
    simp only [id_eq, Nat.reduceSub, Nat.cast_ofNat]
    field_simp
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring

theorem complexRadialDensity_continuous : Continuous complexRadialDensity := by
  unfold complexRadialDensity complexJacobiSlow complexJacobiFast
  fun_prop

theorem complexRadial_integral (c : ℝ) :
    (∫ r in (0 : ℝ)..c, complexRadialDensity r) = Real.sin (c / Real.sqrt 2) ^ 4 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => complexRadialPrimitive_hasDerivAt r)
    (complexRadialDensity_continuous.intervalIntegrable 0 c)]
  simp

def complexRadialMass (c : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Ioc (0 : ℝ) c, ENNReal.ofReal (complexRadialDensity r)

theorem complexRadialDensity_nonneg {r : ℝ} (hr : r ∈ Icc (0 : ℝ) complexJacobiRadius) :
    0 ≤ complexRadialDensity r := by
  rcases eq_or_lt_of_le hr.1 with h0 | h0
  · rw [← h0]
    simp [complexRadialDensity, complexJacobiSlow]
  rcases eq_or_lt_of_le hr.2 with hc | hc
  · rw [hc, complexRadialDensity, complexJacobiFast_radius, mul_zero]
  exact mul_nonneg (sq_nonneg _) (complexJacobiFast_pos h0 hc).le

theorem complexRadialMass_formula (c : ℝ) (hc : c ∈ Icc (0 : ℝ) complexJacobiRadius) :
    complexRadialMass c = ENNReal.ofReal (Real.sin (c / Real.sqrt 2) ^ 4) := by
  have hi : IntegrableOn complexRadialDensity (Ioc (0 : ℝ) c) :=
    complexRadialDensity_continuous.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hn : ∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) c)), 0 ≤ complexRadialDensity r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact complexRadialDensity_nonneg ⟨hr.1.le, hr.2.trans hc.2⟩
  rw [complexRadialMass, ← ofReal_integral_eq_lintegral_ofReal hi hn,
    ← intervalIntegral.integral_of_le hc.1, complexRadial_integral]

theorem complexRadialMass_radius : complexRadialMass complexJacobiRadius = 1 := by
  rw [complexRadialMass_formula _ ⟨complexJacobiRadius_pos.le, le_rfl⟩]
  have h : complexJacobiRadius / Real.sqrt 2 = Real.pi / 2 := by
    rw [complexJacobiRadius, div_div, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp [h, Real.sin_pi_div_two]

theorem complexRadialMass_le_one (c : ℝ) (hc : c ≤ complexJacobiRadius) :
    complexRadialMass c ≤ 1 := by
  rw [← complexRadialMass_radius]
  exact lintegral_mono_set (Ioc_subset_Ioc_right hc)

theorem complexRadialMass_lt_one (c : ℝ) (hc : c ∈ Ico (0 : ℝ) complexJacobiRadius) :
    complexRadialMass c < 1 := by
  rw [complexRadialMass_formula c ⟨hc.1,hc.2.le⟩]
  have hs : 0 < Real.sqrt 2 := by positivity
  have h0 : 0 ≤ c / Real.sqrt 2 := div_nonneg hc.1 hs.le
  have hlt : c / Real.sqrt 2 < Real.pi / 2 := by
    have h := div_lt_div_of_pos_right hc.2 hs
    dsimp only [complexJacobiRadius] at h
    rwa [div_div, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hn := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have hp : Real.sin (c / Real.sqrt 2) < 1 := by
    have h := Real.strictMonoOn_sin (show c / Real.sqrt 2 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)
      from ⟨by linarith [Real.pi_pos], hlt.le⟩)
      (show Real.pi / 2 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) from ⟨by linarith [Real.pi_pos], le_rfl⟩) hlt
    simpa only [Real.sin_pi_div_two] using h
  exact (ENNReal.ofReal_lt_one).mpr (pow_lt_one₀ hn hp (by decide : 4 ≠ 0))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual exponential charts throughout the open complex normal ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_complex_localChart (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace)
    (hv : ‖v‖ < complexJacobiRadius) :
    ∃ C : OpenPartialHomeomorph FourSpace M,
      v ∈ C.source ∧ EqOn C (frameExponential g o e) C.source := by
  by_cases hzero : v = 0
  · subst v
    exact frameExponential_localChart g o e
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hzero)]⟩
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hzero),one_smul]
  have hf : e.rotate (orientedToOrthogonal (directionOrientedMatrix q)) ∈ o.positive :=
    frameRotate_oriented_positive o e he (directionOrientedMatrix q)
  have hp : (q, ‖v‖) ∈ framePolarDomain g hRic e := by
    refine ⟨norm_pos_iff.mpr hzero, ?_⟩
    rw [actualFirstConjugateTime_parallel_form hRic hminus hnorm W hstar hw hz _ hf]
    exact hv
  obtain ⟨C,hC,heq⟩ := frameExponential_polar_localChart g o hRic e he q ‖v‖ hp
  exact ⟨C,hrad ▸ hC,heq⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The inverse sphere homeomorphism does not increase the distance
between the endpoints of an actual unit geodesic of length at most pi. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem round_frameGeodesic_radial_distance (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (f : FrameBundle g) (hf : f ∈ o.positive) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) Real.pi) :
    metricDistance g f.base (frameGeodesic g 0 f t) = t := by
  have hn : ‖t • (coordinateVector 0 : FourSpace)‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    simp [coordinateVector]
  have hm := frameExponential_round_minimizing hRic hpositive hplus hminus f hf
    (t • coordinateVector 0) (by rw [hn]; exact ht.2)
  rwa [frameExponential_first_ray_all g o f hf t, hn] at hm

theorem round_frameGeodesic_injOn (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (f : FrameBundle g) (hf : f ∈ o.positive) :
    InjOn (frameGeodesic g 0 f) (Icc (0 : ℝ) Real.pi) := by
  intro s hs t ht heq
  have h := congrArg (metricDistance g f.base) heq
  rwa [round_frameGeodesic_radial_distance hRic hpositive hplus hminus f hf s hs,
    round_frameGeodesic_radial_distance hRic hpositive hplus hminus f hf t ht] at h

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] [PreconnectedSpace M] in
theorem round_frameGeodesic_real_speed (f : FrameBundle g) (t : ℝ) :
    metricTangentNorm g (frameGeodesic g 0 f t)
      (mfderiv 𝓘(ℝ, ℝ) I4 (frameGeodesic g 0 f) t 1) = 1 := by
  have h := frameGeodesic_metric_speed g 0 f t
  rw [metricTangentENorm_eq_ofReal] at h
  have hn : 0 ≤ metricTangentNorm g (frameGeodesic g 0 f t)
      (mfderiv 𝓘(ℝ, ℝ) I4 (frameGeodesic g 0 f) t 1) := by
    rw [metricTangentNorm_eq_sqrt]
    exact Real.sqrt_nonneg _
  have hh := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal hn, ENNReal.toReal_one] using hh

theorem round_inverse_geodesic_distance_le (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (f : FrameBundle g) (hf : f ∈ o.positive) (d : ℝ) (hd : d ∈ Icc (0 : ℝ) Real.pi) :
    roundDistance
      ((actualRoundHomeomorph hRic hpositive hplus hminus e he).symm (frameGeodesic g 0 f 0))
      ((actualRoundHomeomorph hRic hpositive hplus hminus e he).symm (frameGeodesic g 0 f d)) ≤ d := by
  classical
  let H := actualRoundHomeomorph hRic hpositive hplus hminus e he
  let u : ℝ → RoundSphere4 := fun t => H.symm (frameGeodesic g 0 f t)
  have hu : Continuous u := H.symm.continuous.comp (frameGeodesic_contMDiff g 0 f).continuous
  have hi : InjOn u (Icc (0 : ℝ) Real.pi) := by
    intro s hs t ht heq
    exact round_frameGeodesic_injOn hRic hpositive hplus hminus f hf hs ht
      (H.symm.injective heq)
  let S : Set RoundSphere4 := {roundNorth, antipode roundNorth, u 0, antipode (u 0)}
  let B : Set ℝ := Ioo 0 d ∩ u ⁻¹' S
  have hS : S.Finite := by
    simp only [S, Set.finite_insert, Set.finite_singleton]
  have hmap : MapsTo u B S := fun _ ht => ht.2
  have hbi : InjOn u B := hi.mono (show B ⊆ Icc 0 Real.pi from
    fun _ ht => ⟨ht.1.1.le, ht.1.2.le.trans hd.2⟩)
  have hB : B.Finite := hS.of_injOn hmap hbi
  have hgood (t : ℝ) (ht : t ∈ Ioo 0 d) (hexc : t ∉ hB.toFinset) : u t ∉ S := by
    intro hs
    exact hexc (hB.mem_toFinset.mpr ⟨ht, hs⟩)
  have hder (t : ℝ) (ht : t ∈ Ioo 0 d) (hexc : t ∉ hB.toFinset) :
      ∃ w : EuclideanSpace ℝ (Fin 5), HasDerivAt (fun s => (u s).val) w t ∧ ‖w‖ ≤ 1 := by
    have hg := hgood t ht hexc
    have hn : u t ≠ roundNorth := fun h => hg (by simp [S, h])
    have hs : u t ≠ antipode roundNorth := fun h => hg (by simp [S, h])
    obtain ⟨w, hw, hnorm⟩ := round_inverse_curve_speed hRic hpositive hplus hminus e he
      ((frameGeodesic_contMDiff g 0 f).contMDiffAt) hn hs
    exact ⟨w, hw, (hnorm.trans (round_frameGeodesic_real_speed f t)).le⟩
  have hr (t : ℝ) (ht : t ∈ Ioo 0 d) (hexc : t ∉ hB.toFinset) :
      u t ≠ u 0 ∧ u t ≠ antipode (u 0) := by
    have hg := hgood t ht hexc
    exact ⟨fun h => hg (by simp [S, h]), fun h => hg (by simp [S, h])⟩
  have hh := roundDistance_curve_le u 0 d hd.1 hB.toFinset hu.continuousOn hder hr
  simpa only [sub_zero] using hh

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact minimizing-domain radial mass in the complex-curvature branch. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Matrix MeasureTheory Set
open scoped Manifold ContDiff ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}
variable (hRic : RicciThree g) (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
  (hnorm : ∀ x, plusNorm o x = 1)
  (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
  (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
  (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)

include hRic hminus hnorm w hstar hw hz

omit [PreconnectedSpace M] in
theorem actualJacobi_det_parallel_form (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) :
    ((actualJacobiSolution g hRic e).J t).det = complexRadialDensity t := by
  let a := twoFormFrameValue o w.val e
  let v : Fin 3 → ℝ := ![a 0,a 1,a 2]
  have hv : dotProduct v v = 1 := unitSelfDual_frame_firstThree w hstar hw e he
  have hJ : (actualJacobiSolution g hRic e).J =
      complexJacobiPosition (Matrix.vecMulVec v v) :=
    (actualJacobi_parallel_form hRic hminus hnorm w hstar hw hz e he).1
  rw [hJ, complexJacobiPosition_det v hv]
  rfl

theorem parallel_form_cut_le_radius (e : FrameBundle g) (he : e ∈ o.positive) :
    actualCutTime g e ≤ complexJacobiRadius := by
  rw [← actualFirstConjugateTime_parallel_form hRic hminus hnorm w hstar hw hz e he]
  exact actualCutTime_le_firstConjugateTime g hRic e

theorem complex_actual_cut_mass (e : FrameBundle g) (he : e ∈ o.positive) :
    (∫⁻ r : Ioi (0 : ℝ),
      (if r.val ≤ actualCutTime g e then
        ENNReal.ofReal |((actualJacobiSolution g hRic e).J r.val).det| else 0)
      ∂((volume : Measure ℝ).comap Subtype.val)) = complexRadialMass (actualCutTime g e) := by
  let F : ℝ → ℝ≥0∞ := fun r => if r ≤ actualCutTime g e then
    ENNReal.ofReal |((actualJacobiSolution g hRic e).J r).det| else 0
  change (∫⁻ r : Ioi (0 : ℝ), F r.val
    ∂((volume : Measure ℝ).comap Subtype.val)) = _
  rw [lintegral_subtype_comap measurableSet_Ioi F,
    ← lintegral_indicator measurableSet_Ioi]
  rw [complexRadialMass, ← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro r
  dsimp only [F]
  by_cases hr : 0 < r
  · rw [Set.indicator_of_mem (show r ∈ Ioi (0 : ℝ) from hr)]
    by_cases hc : r ≤ actualCutTime g e
    · rw [ite_eq_left hc,
        Set.indicator_of_mem (show r ∈ Ioc (0 : ℝ) (actualCutTime g e) from ⟨hr,hc⟩),
        actualJacobi_det_parallel_form hRic hminus hnorm w hstar hw hz e he r,
        abs_of_nonneg (complexRadialDensity_nonneg
          ⟨hr.le,hc.trans (parallel_form_cut_le_radius hRic hminus hnorm w hstar hw hz e he)⟩)]
    · rw [ite_eq_right hc, Set.indicator_of_notMem (fun h => hc h.2)]
  · rw [Set.indicator_of_notMem (show r ∉ Ioi (0 : ℝ) from hr),
      Set.indicator_of_notMem (fun h => hr h.1)]

variable [SecondCountableTopology M]

theorem complex_volume_le_cut_mass (e : FrameBundle g) (he : e ∈ o.positive) :
    volumeMeasure g univ ≤ riemannianChartFactor *
      (ENNReal.ofReal (2 * Real.pi ^ 2) * ∫⁻ q : Directions,
        complexRadialMass (actualCutTime g
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))) ∂sphereMeasure) := by
  have h := volumeMeasure_le_integral_exponentialJacobian g o hRic e he
  rw [minimizing_exponential_integral_radial g o hRic e he, polarAngularMass_eq] at h
  convert h using 2
  congr 1
  apply lintegral_congr
  intro q
  exact (complex_actual_cut_mass hRic hminus hnorm w hstar hw hz _
    (frameRotate_oriented_positive o e he (directionOrientedMatrix q))).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The complex operator reconstructed from a two-form is equivariant
under genuine orthonormal frame changes. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormFrameValue_rotate (u : M → TwoFormFour) (e : FrameBundle g)
    (Q : OrthogonalFour) :
    twoFormFrameValue o u (e.rotate Q) = twoFormFrameAction Q.val (twoFormFrameValue o u e) := by
  have hQ : e.frame.changeMatrix (e.frame.rotate Q) = Q.val := by
    change e.frame.matrix⁻¹ * (e.frame.matrix * Q.val) = Q.val
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr e.frame.det_ne_zero), Matrix.one_mul]
  exact (twoFormFrameValue_change o u e.frame (e.frame.rotate Q)).trans (by rw [hQ])

theorem twoForm_operator_rotate (u : M → TwoFormFour) (e : FrameBundle g)
    (Q : OrthogonalFour) (v : FourSpace) :
    Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) Q.val
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
        (twoFormMatrix (twoFormFrameValue o u (e.rotate Q))) v) =
      Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
        (twoFormMatrix (twoFormFrameValue o u e))
          (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) Q.val v) := by
  have hmat : Q.val * twoFormMatrix (twoFormFrameValue o u (e.rotate Q)) =
      twoFormMatrix (twoFormFrameValue o u e) * Q.val := by
    rw [twoFormFrameValue_rotate, twoFormMatrix_frameAction]
    calc
      _ = (Q.val * Q.valᵀ) * twoFormMatrix (twoFormFrameValue o u e) * Q.val := by
        noncomm_ring
      _ = _ := by rw [mul_eq_one_comm.mp Q.property, Matrix.one_mul]
  change ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) Q.val) *
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
        (twoFormMatrix (twoFormFrameValue o u (e.rotate Q))))) v =
    ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
      (twoFormMatrix (twoFormFrameValue o u e))) *
        (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) Q.val)) v
  rw [← map_mul, ← map_mul, hmat]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The full actual pullback metric in the parallel complex-curvature branch. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Jacobi
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem heatNormalMetric_first_parallel_form (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t) :
    let a := twoFormFrameValue o w.val e
    let P := Matrix.vecMulVec ![a 0,a 1,a 2] ![a 0,a 1,a 2]
    heatNormalMetric g o e (t • coordinateVector 0) =
      jacobiBlockMatrix 1 ((t⁻¹ * t⁻¹) • complexJacobiGram P t) := by
  let f := parallelFrameFlowMap g 0 t e
  let c := f.base
  have hf : f.base ∈ (chartAt FourSpace c).source := mem_chart_source FourSpace c
  have hx : frameExponential g o e (t • coordinateVector 0) = f.base :=
    frameExponential_first_ray g o e he t ht
  let E := frameChartMatrix g c f
  let H := metricInChart g c (chartAt FourSpace c f.base)
  let B := jacobiBlockMatrix 1 (t⁻¹ • (actualJacobiSolution g hRic e).J t)
  have hN : Eᵀ * H * E = 1 := frameChartMatrix_normalizes g c f hf
  have hD := (frameExponential_hasFDerivAt g o hRic c e he t ht hf).fderiv
  have hcol (i : Fin 4) :
      WithLp.ofLp (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (E * B)
        (coordinateVector i)) = fun k => (E * B) k i := by
    change (E * B) *ᵥ Pi.single i 1 = _
    exact Matrix.mulVec_single_one _ _
  have hGram : heatNormalMetric g o e (t • coordinateVector 0) = Bᵀ * B := by
    ext i j
    rw [heatNormalMetric_chart_pairing g o e c _ (hx ▸ hf), hD]
    rw [hcol, hcol]
    rw [hx, ← heat_matrix_congruence_pairing]
    change ((E * B)ᵀ * H * (E * B)) i j = (Bᵀ * B) i j
    have hmat : (E * B)ᵀ * H * (E * B) = Bᵀ * B := by
      rw [Matrix.transpose_mul]
      calc
        _ = Bᵀ * (Eᵀ * H * E) * B := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hN, Matrix.mul_one]
    exact congrArg (fun A : Mat4 => A i j) hmat
  rw [hGram, jacobiBlockMatrix_transpose_mul]
  simp only [one_pow]
  rw [(actualJacobi_parallel_form hRic hminus hnorm w hstar hw hz e he).1]
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 2
  apply complexJacobiPosition_transpose_mul
  · ext i j
    let v : Fin 3 → ℝ := ![(twoFormFrameValue o w.val e) 0,
      (twoFormFrameValue o w.val e) 1,(twoFormFrameValue o w.val e) 2]
    change v j * v i = v i * v j
    exact mul_comm _ _
  · rw [Matrix.vecMulVec_mul_vecMulVec,
      unitSelfDual_frame_firstThree w hstar hw e he, one_smul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual unit-speed frame geodesic is globally distance nonincreasing in time. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M}

theorem frameGeodesic_metricDistance_le (f : FrameBundle g) (s t : ℝ) :
    metricDistance g (frameGeodesic g 0 f s) (frameGeodesic g 0 f t) ≤ |t-s| := by
  have hordered (a b : ℝ) (hab : a ≤ b) :
      metricDistance g (frameGeodesic g 0 f a) (frameGeodesic g 0 f b) ≤ b-a := by
    have hh := metricDistance_le_of_interior_speed_bound g hab zero_le_one
      (frameGeodesic_contMDiff g 0 f).continuous
      (fun _ _ => (frameGeodesic_contMDiff g 0 f).contMDiffAt)
      (fun x _ => (round_frameGeodesic_real_speed f x).le)
    simpa only [one_mul] using hh
  rcases le_total s t with hst | hts
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using hordered s t hst
  · rw [metricDistance_symm,abs_of_nonpos (sub_nonpos.mpr hts),neg_sub]
    exact hordered t s hts

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual inverse of the complex normal exponential is C1 before the first conjugate radius. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_complex_mfderiv_isUnit (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace)
    (hv : v ≠ 0) (hR : ‖v‖ < complexJacobiRadius) :
    IsUnit (show FourSpace →L[ℝ] FourSpace from mfderiv I4 I4 (frameExponential g o e) v) := by
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
  let Q := directionOrientedMatrix q
  let L := (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
    (orientedToOrthogonal Q).property).toContinuousLinearEquiv
  let f := e.rotate (orientedToOrthogonal Q)
  let x := ‖v‖ • coordinateVector 0
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he Q
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
  have hpoint : L x = v := by
    change L (‖v‖ • coordinateVector 0) = v
    rw [map_smul]
    exact (congrArg (fun z => ‖v‖ • z) (directionRotation_first q)).trans hrad
  let d := (parallelFrameFlowMap g 0 ‖v‖ f).base
  have hd : d ∈ (chartAt FourSpace d).source := mem_chart_source FourSpace d
  have hexp : frameExponential g o f x = d :=
    frameExponential_first_ray g o f hf ‖v‖ (norm_pos_iff.mpr hv)
  have hunit : IsUnit (show FourSpace →L[ℝ] FourSpace from mfderiv I4 I4 (frameExponential g o f) x) := by
    rw [← frameExponential_center_fderiv, hexp,
      (frameExponential_hasFDerivAt g o hRic d f hf ‖v‖ (norm_pos_iff.mpr hv) hd).fderiv]
    apply frameExponential_preconjugate_isUnit g hRic d f ‖v‖ (norm_pos_iff.mpr hv)
    · rw [actualFirstConjugateTime_parallel_form hRic hminus hnorm W hstar hw hz f hf]
      exact hR
    · exact hd
  have hD : (show FourSpace →L[ℝ] FourSpace from mfderiv I4 I4 (frameExponential g o e) v) =
      (show FourSpace →L[ℝ] FourSpace from mfderiv I4 I4 (frameExponential g o f) x) *
        (L.symm : FourSpace →L[ℝ] FourSpace) := by
    apply ContinuousLinearMap.ext
    intro w
    have h := frameExponential_rotate_mfderiv g o e Q x (L.symm w)
    change _ = mfderiv I4 I4 (frameExponential g o e) (L x) (L (L.symm w)) at h
    rw [hpoint, L.apply_symm_apply] at h
    exact h.symm
  rw [hD]
  exact hunit.mul L.symm.toUnit.isUnit

theorem frameExponential_complex_inverse_contMDiffAt (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace)
    (hv : v ≠ 0) (hR : ‖v‖ < complexJacobiRadius)
    (C : OpenPartialHomeomorph FourSpace M) (hCv : v ∈ C.source)
    (hC : EqOn C (frameExponential g o e) C.source) :
    ContMDiffAt I4 I4 1 C.symm (frameExponential g o e v) := by
  apply frameExponential_local_inverse_contMDiffAt g o e v C hCv hC
  rw [frameExponential_center_fderiv]
  exact frameExponential_complex_mfderiv_isUnit hRic hminus hnorm W hstar hw hz e he v hv hR

end
end PositiveEinsteinFour.Geometry
end


section

/-! The global distance comparison for the actual round sphere map. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem roundSphereMap_distance_ge (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (p q : RoundSphere4) :
    roundDistance p q ≤ metricDistance g (roundSphereMap g o e p) (roundSphereMap g o e q) := by
  let H := actualRoundHomeomorph hRic hpositive hplus hminus e he
  let f : FrameBundle g := ⟨H p, o.frame (H p)⟩
  have hf : f ∈ o.positive := o.frame_positive (H p)
  let F := actualRoundHomeomorph hRic hpositive hplus hminus f hf
  let r := F.symm (H q)
  let v := roundLog r
  have hend : frameExponential g o f v = H q := F.apply_symm_apply (H q)
  have hd : ‖v‖ = metricDistance g (H p) (H q) := by
    have hh := roundSphereMap_radial_distance hRic hpositive hplus hminus f hf r
    change metricDistance g (H p) (F r) = Real.arccos (r.val 0) at hh
    rw [F.apply_symm_apply] at hh
    rw [show ‖v‖ = Real.arccos (r.val 0) from roundLog_norm r]
    exact hh.symm
  have hpi : ‖v‖ ≤ Real.pi := by
    change ‖roundLog r‖ ≤ Real.pi
    rw [roundLog_norm]
    exact Real.arccos_le_pi _
  by_cases hz : v = 0
  · have hpq : p = q := by
      apply H.injective
      have hh := hend
      rw [hz, frameExponential_zero] at hh
      exact hh
    subst q
    rw [roundDistance_self]
    exact metricDistance_nonneg _ _ _
  let w : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
  let f' := f.rotate (orientedToOrthogonal (directionOrientedMatrix w))
  have hf' : f' ∈ o.positive := frameRotate_oriented_positive o f hf _
  have hrad : ‖v‖ • w.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  have hstart : frameGeodesic g 0 f' 0 = H p := by
    simp only [frameGeodesic, parallelFrameFlowMap_zero]
    rfl
  have hfinish : frameGeodesic g 0 f' ‖v‖ = H q := by
    rw [← frameExponential_direction_ray g o f hf w ‖v‖, hrad, hend]
  have hh := round_inverse_geodesic_distance_le hRic hpositive hplus hminus e he f' hf'
    ‖v‖ ⟨norm_nonneg _, hpi⟩
  change roundDistance (H.symm (frameGeodesic g 0 f' 0))
    (H.symm (frameGeodesic g 0 f' ‖v‖)) ≤ ‖v‖ at hh
  rw [hstart, hfinish, H.symm_apply_apply, H.symm_apply_apply, hd] at hh
  exact hh

theorem roundSphereMap_distance_eq (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (p q : RoundSphere4) :
    metricDistance g (roundSphereMap g o e p) (roundSphereMap g o e q) = roundDistance p q :=
  roundSphereMap_distance_eq_of_le hRic hpositive hplus hminus e he
    (roundSphereMap_distance_ge hRic hpositive hplus hminus e he) p q

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exponential kernel in the complex-circle direction at an
arbitrary initial unit vector. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Jacobi Angular
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_complex_angular_kernel (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (q : Directions) (c : M)
    (hc : frameExponential g o e (complexJacobiRadius • q.val) ∈ (chartAt FourSpace c).source) :
    fderiv ℝ (fun z : FourSpace => chartAt FourSpace c (frameExponential g o e z))
      (complexJacobiRadius • q.val)
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
        (twoFormMatrix (twoFormFrameValue o w.val e)) q.val) = 0 := by
  let Q := directionOrientedMatrix q
  let L := (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
    (orientedToOrthogonal Q).property).toContinuousLinearEquiv
  let f := e.rotate (orientedToOrthogonal Q)
  let F := fun z : FourSpace => chartAt FourSpace c (frameExponential g o e z)
  let G := fun z : FourSpace => chartAt FourSpace c (frameExponential g o f z)
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he Q
  have hLfirst : L (coordinateVector 0) = q.val := directionRotation_first q
  have hLpoint : L (complexJacobiRadius • coordinateVector 0) = complexJacobiRadius • q.val := by
    rw [map_smul, hLfirst]
  have hp : frameExponential g o e (complexJacobiRadius • q.val) =
      (parallelFrameFlowMap g 0 complexJacobiRadius f).base :=
    frameExponential_direction_ray g o e he q complexJacobiRadius
  have hfc : (parallelFrameFlowMap g 0 complexJacobiRadius f).base ∈ (chartAt FourSpace c).source := hp ▸ hc
  have hF := (frameExponential_chart_contDiffAt g o c e (complexJacobiRadius • q.val) hc).differentiableAt
    one_ne_zero
  rw [← hLpoint] at hF
  have hcomp := hF.hasFDerivAt.comp (complexJacobiRadius • coordinateVector 0)
    (L : FourSpace →L[ℝ] FourSpace).hasFDerivAt
  have heq : (fun z : FourSpace => F (L z)) = G := by
    funext z
    exact congrArg (chartAt FourSpace c) (frameExponential_rotate g o e Q z).symm
  change HasFDerivAt (fun z => F (L z))
    ((fderiv ℝ F (L (complexJacobiRadius • coordinateVector 0))).comp
      (L : FourSpace →L[ℝ] FourSpace)) (complexJacobiRadius • coordinateVector 0) at hcomp
  rw [heq, hLpoint] at hcomp
  have hvel : L (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
      (twoFormMatrix (twoFormFrameValue o w.val f)) (coordinateVector 0)) =
      Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
        (twoFormMatrix (twoFormFrameValue o w.val e)) q.val := by
    have h := twoForm_operator_rotate (o := o) w.val e (orientedToOrthogonal Q) (coordinateVector 0)
    change L (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
      (twoFormMatrix (twoFormFrameValue o w.val f)) (coordinateVector 0)) =
      Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
        (twoFormMatrix (twoFormFrameValue o w.val e)) (L (coordinateVector 0)) at h
    rwa [hLfirst] at h
  have hk := frameExponential_complex_first_kernel hRic hminus hnorm w hstar hw hz f hf c hfc
  change fderiv ℝ G (complexJacobiRadius • coordinateVector 0) _ = 0 at hk
  rw [hcomp.fderiv] at hk
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hvel] using hk

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual index formula fixes the volume in the dimension-one case. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem complex_normalized_totalVolume (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1) :
    totalVolume g / riemannianChartFactor.toReal = 2 * Real.pi ^ 2 := by
  have h := (halfFlat_volume_energy_counts hRic hminus).1
  rw [hdim] at h
  norm_num at h
  unfold volumeRatio at h
  rw [div_right_comm] at h
  have he := (div_eq_iff (by positivity : (8 * Real.pi ^ 2 / 3 : ℝ) ≠ 0)).mp h
  calc
    _ = (3 / 4 : ℝ) * (8 * Real.pi ^ 2 / 3) := he
    _ = _ := by ring

theorem complex_volumeMeasure (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1) :
    volumeMeasure g Set.univ = riemannianChartFactor * ENNReal.ofReal (2 * Real.pi ^ 2) := by
  have h := (div_eq_iff riemannianChartFactor_toReal_pos.ne').mp
    (complex_normalized_totalVolume hRic hminus hdim)
  have hk : riemannianChartFactor ≠ ⊤ := by
    unfold riemannianChartFactor
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
  calc
    volumeMeasure g Set.univ = ENNReal.ofReal (totalVolume g) :=
      (ENNReal.ofReal_toReal (ne_of_lt (actual_finitePositiveVolume g).finite)).symm
    _ = ENNReal.ofReal ((2 * Real.pi ^ 2) * riemannianChartFactor.toReal) := congrArg _ h
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hk, mul_comm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The metric round-model identification in the vanishing-Weyl branch. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actual_round_model (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0) :
    ScaledIsometricTo g 1 roundDistance := by
  let x : M := Classical.choice inferInstance
  let e : FrameBundle g := ⟨x, o.frame x⟩
  have he : e ∈ o.positive := o.frame_positive x
  let H := actualRoundHomeomorph hRic hpositive hplus hminus e he
  refine ⟨H.symm.toEquiv, ?_⟩
  intro p q
  have h := roundSphereMap_distance_eq hRic hpositive hplus hminus e he (H.symm p) (H.symm q)
  change metricDistance g (H (H.symm p)) (H (H.symm q)) =
    roundDistance (H.symm p) (H.symm q) at h
  rw [H.apply_symm_apply, H.apply_symm_apply] at h
  change ENNReal.ofReal (roundDistance (H.symm p) (H.symm q)) = scaledEDistance g 1 p q
  rw [← h, ofReal_metricDistance]
  simp only [scaledEDistance, Real.sqrt_one, ENNReal.ofReal_one, one_mul]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! A unit self-dual form admits a positively oriented standard frame,
constructed with the existing quaternion lifts. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix TraceHessian QuaternionFrame
open scoped BigOperators
noncomputable section

def standardSelfDualForm : TwoFormFour := WithLp.toLp 2 ![1,0,0,0,0,1]

theorem selfDual_matrix_eq_imaginary (a : TwoFormFour) (ha : twoFormHodge a = a) :
    twoFormMatrix a = -imaginaryCombination quaternionMatrix ![a 0,a 1,a 2] := by
  have h3 : a 3 = a 2 := congrArg (fun b : TwoFormFour => b 2) ha
  have h4 : a 4 = -a 1 := by
    have h := congrArg (fun b : TwoFormFour => b 1) ha
    change -a 4 = a 1 at h
    linarith
  have h5 : a 5 = a 0 := congrArg (fun b : TwoFormFour => b 0) ha
  ext i j
  simp only [imaginaryCombination, Matrix.neg_apply, Matrix.sum_apply, Matrix.smul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [twoFormMatrix, quaternionMatrix, Fin.sum_univ_succ, h3,h4,h5]

theorem standardSelfDualForm_matrix : twoFormMatrix standardSelfDualForm = -quaternionMatrix 0 := by
  ext i j
  simp only [Matrix.neg_apply]
  fin_cases i <;> fin_cases j <;>
    simp [standardSelfDualForm, twoFormMatrix, quaternionMatrix]

theorem unitSelfDual_exists_oriented_frame (a : TwoFormFour)
    (ha : twoFormHodge a = a) (hn : ‖a‖ ^ 2 = 2) :
    ∃ c : ℝ, c ^ 2 = 1 ∧ ∃ Q : OrientedOrthogonalFour,
      twoFormFrameAction Q.val a = c • standardSelfDualForm := by
  let v : ThreeSpace := WithLp.toLp 2 ![a 0,a 1,a 2]
  let e0 : ThreeSpace := EuclideanSpace.basisFun (Fin 3) ℝ 0
  have hv : ‖v‖ = 1 := by
    have h := selfDual_firstThree_unit a ha hn
    have hs : ‖v‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simpa only [v, pow_two, dotProduct] using h
    nlinarith [norm_nonneg v]
  have he0 : ‖e0‖ = 1 := (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one 0
  let φ : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace := Submodule.reflection (ℝ ∙ (e0 - v))ᗮ
  have hφ : φ e0 = v := Submodule.reflection_sub (he0.trans hv.symm)
  obtain ⟨c,hc,⟨P⟩⟩ := exists_signed_left_lift φ
  have hAv : (c • frameMatrix φ) *ᵥ (Pi.single 0 1 : Fin 3 → ℝ) = c • (v : Fin 3 → ℝ) := by
    rw [Matrix.smul_mulVec, Matrix.mulVec_single_one]
    ext i
    change c * frameMatrix φ i 0 = c * v i
    rw [frameMatrix_apply]
    exact congrArg (fun x : ThreeSpace => c * x i) hφ
  have hbasic : imaginaryCombination quaternionMatrix (Pi.single 0 1) = quaternionMatrix 0 := by
    simp [imaginaryCombination, Pi.single_apply]
  have hsmul : imaginaryCombination quaternionMatrix (c • (v : Fin 3 → ℝ)) =
      c • imaginaryCombination quaternionMatrix v := by
    simp only [imaginaryCombination, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  have hi := intertwines_combination quaternionMatrix (c • frameMatrix φ) P.matrix
    P.intertwines (Pi.single 0 1)
  rw [hAv,hbasic,hsmul] at hi
  have hj := congrArg (fun B : Mat4 => P.matrixᵀ * B) hi
  have hj' : quaternionMatrix 0 = c •
      (P.matrixᵀ * imaginaryCombination quaternionMatrix v * P.matrix) := by
    simpa only [← Matrix.mul_assoc, P.orthogonal, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul] using hj
  have hjc := congrArg (fun B : Mat4 => c • B) hj'
  rw [smul_smul, ← pow_two, hc, one_smul] at hjc
  refine ⟨c,hc,⟨P.matrix,Matrix.mem_specialOrthogonalGroup_iff.mpr
    ⟨by rw [Matrix.mem_orthogonalGroup_iff']; exact P.orthogonal, P.orientation⟩⟩,?_⟩
  apply twoFormMatrix_injective
  rw [twoFormMatrix_frameAction, selfDual_matrix_eq_imaginary a ha,
    Matrix.mul_neg, Matrix.neg_mul, ← hjc, twoFormMatrix_smul,
    standardSelfDualForm_matrix, smul_neg]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exponential identifies each complex circle at the boundary
of the minimizing ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Jacobi Angular
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_complex_boundary_circle (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (q : Directions) (t : ℝ) :
    frameExponential g o e (complexJacobiRadius • complexCircleVector
      (twoFormMatrix (twoFormFrameValue o w.val e)) q.val t) =
        frameExponential g o e (complexJacobiRadius • q.val) := by
  let J := twoFormMatrix (twoFormFrameValue o w.val e)
  have hs : J * J = -(1 : Mat4) := (unit_selfDual_frame_complex w hstar hw e he).1
  have hsk : Jᵀ = -J := twoFormMatrix_skew _
  let F := fun s : ℝ => frameExponential g o e (complexJacobiRadius • complexCircleVector J q.val s)
  have hcircle : Continuous (complexCircleVector J q.val) :=
    continuous_iff_continuousAt.mpr (fun s => (complexCircleVector_hasDerivAt J hs q.val s).continuousAt)
  have hF : Continuous F := (frameExponential_continuous g o e).comp
    (hcircle.const_smul complexJacobiRadius)
  have hD (s : ℝ) (c : M) (hc : F s ∈ (chartAt FourSpace c).source) :
      HasDerivAt (fun r => chartAt FourSpace c (F r)) (0 : FourSpace) s := by
    let p : Directions := ⟨complexCircleVector J q.val s,
      (complexCircleVector_norm J hsk hs q.val s).trans q.property⟩
    have hd := (complexCircleVector_hasDerivAt J hs q.val s).const_smul complexJacobiRadius
    have hE := (frameExponential_chart_contDiffAt g o c e
      (complexJacobiRadius • p.val) hc).differentiableAt one_ne_zero
    have h := hE.hasFDerivAt.comp_hasDerivAt s hd
    change HasDerivAt (fun r => chartAt FourSpace c (F r))
      (fderiv ℝ (fun z : FourSpace => chartAt FourSpace c (frameExponential g o e z))
        (complexJacobiRadius • p.val)
        (complexJacobiRadius • Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) J p.val)) s at h
    rw [map_smul, frameExponential_complex_angular_kernel hRic hminus hnorm w hstar hw hz e he p c hc,
      smul_zero] at h
    exact h
  have h := zero_chart_curve_constant F hF hD t 0
  simpa only [F, complexCircleVector_zero] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The real orthonormal coordinates adapted to a parallel self-dual form
are the usual two complex coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped BigOperators
noncomputable section

def complexCoordinatesLinear : FourSpace ≃ₗ[ℝ] EuclideanSpace ℂ (Fin 2) where
  toFun x := WithLp.toLp 2 ![⟨x 0,x 1⟩, ⟨x 2,x 3⟩]
  invFun z := WithLp.toLp 2 ![(z 0).re,(z 0).im,(z 1).re,(z 1).im]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv z := by ext i; fin_cases i <;> rfl
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' r x := by
    ext i
    fin_cases i <;> apply Complex.ext <;> simp

theorem complexCoordinatesLinear_norm (x : FourSpace) :
    ‖complexCoordinatesLinear x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [complexCoordinatesLinear, Fin.sum_univ_succ, Complex.sq_norm, Complex.normSq_apply]
  ring

def complexCoordinates : FourSpace ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin 2) :=
  { complexCoordinatesLinear with norm_map' := complexCoordinatesLinear_norm }

theorem complexCoordinates_standard_complex (x : FourSpace) :
    complexCoordinates (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
      (twoFormMatrix standardSelfDualForm) x) = (-Complex.I) • complexCoordinates x := by
  change complexCoordinatesLinear (WithLp.toLp 2
    ((twoFormMatrix standardSelfDualForm) *ᵥ (x : Fin 4 → ℝ))) = _
  ext i
  fin_cases i <;> apply Complex.ext <;>
    simp [complexCoordinates, complexCoordinatesLinear,
      dotProduct, standardSelfDualForm, twoFormMatrix, Fin.sum_univ_succ]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The full radial mass forces the actual cut time to equal the complex
conjugate radius in every direction. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Matrix MeasureTheory Set
open scoped Manifold ContDiff ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem complex_cut_time_all_directions (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (e : FrameBundle g) (he : e ∈ o.positive) (q : Directions) :
    actualCutTime g (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) =
      complexJacobiRadius := by
  obtain ⟨w,hs,hn,hp⟩ := halfFlat_dimension_one_parallel_unit_form hRic hminus hdim
  have hnorm := halfFlat_dimension_one_norm hRic hminus hdim
  let : IsProbabilityMeasure sphereMeasure := actual_sphereMeasure_probability
  let : Measure.IsOpenPosMeasure sphereMeasure := sphereMeasure_openPos
  let R := fun q : Directions => e.rotate (orientedToOrthogonal (directionOrientedMatrix q))
  let F := fun q : Directions => complexRadialMass (actualCutTime g (R q))
  have hRpos (q : Directions) : R q ∈ o.positive :=
    frameRotate_oriented_positive o e he (directionOrientedMatrix q)
  have hcut (q : Directions) : actualCutTime g (R q) ≤ complexJacobiRadius :=
    parallel_form_cut_le_radius hRic hminus hnorm w hs hn hp _ (hRpos q)
  have hle (q : Directions) : F q ≤ 1 := complexRadialMass_le_one _ (hcut q)
  have hupper : (∫⁻ q, F q ∂sphereMeasure) ≤ 1 := by
    calc
      _ ≤ ∫⁻ _q : Directions, (1 : ℝ≥0∞) ∂sphereMeasure := lintegral_mono hle
      _ = 1 := by simp
  have hlower : 1 ≤ ∫⁻ q, F q ∂sphereMeasure := by
    have h := complex_volume_le_cut_mass hRic hminus hnorm w hs hn hp e he
    rw [complex_volumeMeasure hRic hminus hdim] at h
    have hk := ENNReal.toReal_pos_iff.mp riemannianChartFactor_toReal_pos
    have hc := (ENNReal.mul_le_mul_iff_right hk.1.ne' hk.2.ne).mp h
    have hc' : ENNReal.ofReal (2 * Real.pi ^ 2) * 1 ≤
        ENNReal.ofReal (2 * Real.pi ^ 2) * ∫⁻ q, F q ∂sphereMeasure := by
      simpa only [mul_one] using hc
    exact (ENNReal.mul_le_mul_iff_right (by positivity : ENNReal.ofReal (2 * Real.pi ^ 2) ≠ 0)
      ENNReal.ofReal_ne_top).mp hc'
  have hInt : (∫⁻ q, F q ∂sphereMeasure) = 1 := le_antisymm hupper hlower
  have hae : F =ᵐ[sphereMeasure] (fun _ => 1) := by
    apply (lintegral_eq_iff_ae_eq_of_ae_le (hInt ▸ ENNReal.one_ne_top) aemeasurable_const
      (Filter.Eventually.of_forall hle)).mp
    simpa using hInt
  have haec : ∀ᵐ q : Directions ∂sphereMeasure,
      complexJacobiRadius ≤ actualCutTime g (R q) := by
    filter_upwards [hae] with q hq
    by_contra hnot
    exact (complexRadialMass_lt_one _
      ⟨(actualCutTime_pos g o hRic (R q) (hRpos q)).le,lt_of_not_ge hnot⟩).ne hq
  have hR : Continuous R := (continuous_frameRotate g).comp
    (continuous_const.prodMk (continuous_orientedToOrthogonal.comp continuous_directionOrientedMatrix))
  have hclosed : IsClosed {q : Directions | complexJacobiRadius ≤ actualCutTime g (R q)} :=
    ((actualCutTime_upperSemicontinuous g).isClosed_preimage complexJacobiRadius).preimage hR
  have hdense := Measure.dense_of_ae haec
  have hall : {q : Directions | complexJacobiRadius ≤ actualCutTime g (R q)} = univ := by
    rw [← hclosed.closure_eq, hdense.closure_eq]
  apply le_antisymm (hcut q)
  have hq : q ∈ {q : Directions | complexJacobiRadius ≤ actualCutTime g (R q)} := by
    rw [hall]
    exact mem_univ q
  exact hq

end
end PositiveEinsteinFour.Geometry
end


section

/-! An actual positive frame and a global parallel form with the standard
complex matrix, with no choice of complex structure assumed as input. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Matrix
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem halfFlat_dimension_one_standard_frame (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1) (x : M) :
    ∃ w : smoothTwoForms o,
      (∀ y, twoFormHodge (w.val y) = w.val y) ∧
      (∀ y, ‖w.val y‖ ^ 2 = 2) ∧
      (∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0) ∧
      ∃ e : FrameBundle g, e.base = x ∧ e ∈ o.positive ∧
        twoFormFrameValue o w.val e = standardSelfDualForm := by
  obtain ⟨w,hs,hn,hz⟩ := halfFlat_dimension_one_parallel_unit_form hRic hminus hdim
  let f : FrameBundle g := ⟨x,o.frame x⟩
  have hf : f ∈ o.positive := o.frame_positive x
  have hfs : twoFormHodge (twoFormFrameValue o w.val f) = twoFormFrameValue o w.val f := by
    rw [← twoFormFrameValue_hodge o w.val f hf]
    congr 1
    exact funext hs
  have hfn : ‖twoFormFrameValue o w.val f‖ ^ 2 = 2 := by
    rw [twoFormFrameValue_norm, hn]
  obtain ⟨c,hc,Q,hQ⟩ := unitSelfDual_exists_oriented_frame _ hfs hfn
  let e := f.rotate (orientedToOrthogonal Q)
  refine ⟨c • w, ?_, ?_, ?_, e, rfl, frameRotate_oriented_positive o f hf Q, ?_⟩
  · intro y
    change twoFormHodge (c • w.val y) = c • w.val y
    rw [map_smul,hs]
  · intro y
    change ‖c • w.val y‖ ^ 2 = 2
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hc,hn,one_mul]
  · intro E
    change twoFormFramedCovariantDerivative o (c • w.val) E = 0
    rw [twoFormFramedCovariantDerivative_smul,hz,smul_zero]
  · change twoFormFrameValue o (c • w.val) e = standardSelfDualForm
    rw [twoFormFrameValue_smul, twoFormFrameValue_rotate]
    change c • twoFormFrameAction Q.val (twoFormFrameValue o w.val f) = _
    rw [hQ,smul_smul,← pow_two,hc,one_smul]

end
end PositiveEinsteinFour.Geometry
end

end OAI
