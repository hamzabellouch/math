import OAI.Geometry.EinsteinFour.CurvatureTensors02
import OAI.Geometry.EinsteinFour.GeodesicGeometry05
import OAI.Geometry.EinsteinFour.HeatForcedScalar
import OAI.Geometry.EinsteinFour.HeatKernels10
import OAI.Geometry.EinsteinFour.HodgeTheory08
import OAI.Geometry.EinsteinFour.HodgeTheory09
import OAI.Geometry.EinsteinFour.ScalarRegularity07
import OAI.Geometry.EinsteinFour.WeylEstimates03
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI


section

/-! The finite alternating Gram polynomial for degrees zero, one and two. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped BigOperators Matrix.Norms.Elementwise
noncomputable section

abbrev HeatEulerFiber := ℝ × Mat4 × HeatMat6

def heatEulerUnit : HeatEulerFiber := (1, 1, 1)

def heatEulerTrace (A : HeatEulerFiber) : ℝ := 2 * A.1 - 2 * A.2.1.trace + A.2.2.trace

def heatEulerGram (A B : HeatEulerFiber) : ℝ :=
  2 * A.1 * B.1 - 2 * (A.2.1ᵀ * B.2.1).trace + (A.2.2ᵀ * B.2.2).trace

theorem heatEulerGram_add_left (A B C : HeatEulerFiber) :
    heatEulerGram (A + B) C = heatEulerGram A C + heatEulerGram B C := by
  simp only [heatEulerGram, Prod.fst_add, Prod.snd_add, Matrix.transpose_add,
    Matrix.add_mul, Matrix.trace_add]
  ring

theorem heatEulerGram_add_right (A B C : HeatEulerFiber) :
    heatEulerGram A (B + C) = heatEulerGram A B + heatEulerGram A C := by
  simp only [heatEulerGram, Prod.fst_add, Prod.snd_add, Matrix.mul_add, Matrix.trace_add]
  ring

theorem heatEulerGram_smul_left (r : ℝ) (A B : HeatEulerFiber) :
    heatEulerGram (r • A) B = r * heatEulerGram A B := by
  change 2 * (r * A.1) * B.1 - 2 * ((r • A.2.1)ᵀ * B.2.1).trace +
    ((r • A.2.2)ᵀ * B.2.2).trace = r *
      (2 * A.1 * B.1 - 2 * (A.2.1ᵀ * B.2.1).trace + (A.2.2ᵀ * B.2.2).trace)
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  ring

theorem heatEulerGram_smul_right (r : ℝ) (A B : HeatEulerFiber) :
    heatEulerGram A (r • B) = r * heatEulerGram A B := by
  change 2 * A.1 * (r * B.1) - 2 * (A.2.1ᵀ * (r • B.2.1)).trace +
    (A.2.2ᵀ * (r • B.2.2)).trace = r *
      (2 * A.1 * B.1 - 2 * (A.2.1ᵀ * B.2.1).trace + (A.2.2ᵀ * B.2.2).trace)
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  ring

theorem heatEulerGram_comm (A B : HeatEulerFiber) : heatEulerGram A B = heatEulerGram B A := by
  have ht₁ : (A.2.1ᵀ * B.2.1).trace = (B.2.1ᵀ * A.2.1).trace := by
    rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  have ht₂ : (A.2.2ᵀ * B.2.2).trace = (B.2.2ᵀ * A.2.2).trace := by
    rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [heatEulerGram, ht₁, ht₂]
  ring

theorem heatEulerGram_unit_left (A : HeatEulerFiber) :
    heatEulerGram heatEulerUnit A = heatEulerTrace A := by
  simp [heatEulerGram, heatEulerUnit, heatEulerTrace]

theorem heatEulerGram_unit_self : heatEulerGram heatEulerUnit heatEulerUnit = 0 := by
  norm_num [heatEulerGram, heatEulerUnit]

theorem heatEulerTrace_unit : heatEulerTrace heatEulerUnit = 0 := by
  norm_num [heatEulerTrace, heatEulerUnit]

theorem heatEulerGram_polynomial (U t : ℝ) (A B C : HeatEulerFiber) :
    heatEulerGram (U • heatEulerUnit + t • A + t ^ 2 • B + t ^ 3 • C)
      (U • heatEulerUnit + t • A + t ^ 2 • B + t ^ 3 • C) =
    2 * t * (U * heatEulerTrace A) + t ^ 2 *
      (2 * U * heatEulerTrace B + heatEulerGram A A +
        t * (2 * U * heatEulerTrace C + 2 * heatEulerGram A B) +
        t ^ 2 * (2 * heatEulerGram A C + heatEulerGram B B) +
        t ^ 3 * (2 * heatEulerGram B C) + t ^ 4 * heatEulerGram C C) := by
  simp only [heatEulerGram_add_left, heatEulerGram_add_right,
    heatEulerGram_smul_left, heatEulerGram_smul_right]
  rw [heatEulerGram_comm A heatEulerUnit, heatEulerGram_comm B heatEulerUnit,
    heatEulerGram_comm C heatEulerUnit, heatEulerGram_comm B A,
    heatEulerGram_comm C A, heatEulerGram_comm C B]
  simp only [heatEulerGram_unit_left, heatEulerTrace_unit]
  ring

theorem heatEulerGram_scalar_potential (a : ℝ) (V : HeatMat6)
    (hV : Vᵀ = V) (htr : V.trace = 24) :
    heatEulerGram (a, a • (1 : Mat4) - (3 : ℝ) • 1, a • (1 : HeatMat6) - V)
      (a, a • (1 : Mat4) - (3 : ℝ) • 1, a • (1 : HeatMat6) - V) =
        (V * V).trace - 72 := by
  simp only [heatEulerGram, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, hV, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.trace_sub,
    Matrix.trace_smul, htr, smul_eq_mul]
  norm_num
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Each actual smooth Hodge eigenmode satisfies the scalar forced heat
equation for the constructed normal parametrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.eigen_evolution
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (hRic : RicciThree g)
    (t : ℝ) (ht : 0 < t) (l : Fin 6)
    (hf : P.column E t l ∈ twoFormHodgeDomain hRic)
    (hgen : twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (i : TwoFormEigenIndex (o := o) hRic) :
    HasDerivAt (fun s => inner ℝ (P.column E s l) (twoFormEigenvector hRic i))
      (inner ℝ (P.residual E t l) (twoFormEigenvector hRic i) -
        (i.1.val⁻¹ - 1) * inner ℝ (P.column E t l) (twoFormEigenvector hRic i)) t := by
  obtain ⟨v, hv, hLv⟩ := twoFormEigenvector_smooth hRic i
  have hL : smoothTwoFormToL2 (smoothHodgeLaplacian hRic v : SmoothL2TwoForm o) =
      (i.1.val⁻¹ - 1) • twoFormEigenvector hRic i := by
    have heq : (smoothHodgeLaplacian hRic v : SmoothL2TwoForm o) =
        (i.1.val⁻¹ - 1) • (v : SmoothL2TwoForm o) := hLv
    calc
      _ = smoothTwoFormToL2 ((i.1.val⁻¹ - 1) • (v : SmoothL2TwoForm o)) :=
        congrArg smoothTwoFormToL2 heq
      _ = (i.1.val⁻¹ - 1) • smoothTwoFormToL2 (v : SmoothL2TwoForm o) := map_smul _ _ _
      _ = _ := congrArg ((i.1.val⁻¹ - 1) • ·) hv.symm
  have h := P.weak_evolution E hRic t ht l hf hgen v
  rw [hL, real_inner_smul_right, ← hv] at h
  exact h

def HeatNormalParametrixData.normalizedResidual (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (t : ℝ) (l : Fin 6) : TwoFormL2 o :=
  ((normalizedChartFactor g).toReal)⁻¹ • P.residual E t l

theorem HeatNormalParametrixData.normalized_eigen_evolution
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (hRic : RicciThree g)
    (t : ℝ) (ht : 0 < t) (l : Fin 6)
    (hf : P.column E t l ∈ twoFormHodgeDomain hRic)
    (hgen : twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (i : TwoFormEigenIndex (o := o) hRic) :
    HasDerivAt (fun s => inner ℝ (P.normalizedColumn E s l) (twoFormEigenvector hRic i))
      (inner ℝ (P.normalizedResidual E t l) (twoFormEigenvector hRic i) -
        (i.1.val⁻¹ - 1) * inner ℝ (P.normalizedColumn E t l) (twoFormEigenvector hRic i)) t := by
  have h := (P.eigen_evolution E hRic t ht l hf hgen i).const_mul ((normalizedChartFactor g).toReal)⁻¹
  simpa only [HeatNormalParametrixData.normalizedColumn, heatNormalizedParametrixColumn,
    HeatNormalParametrixData.column, HeatNormalParametrixData.normalizedResidual,
    real_inner_smul_left, mul_sub, mul_left_comm] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual one-form heat residual is combined before taking its L2 norm. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.oneResidual_as_amplitude
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D) (t : ℝ) (l : Fin 4) :
    P.oneResidual E t l =
      heatNormalOneAmplitudeL2 D P.chart P.in_chart P.point_regular P.inside_radius
        (heatNormalOneResidualColumn E P.cutoff t l)
        (heatNormalOneResidualColumn_regular E P.cutoff P.cutoff_regular t l)
        (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
          (heatNormalOneResidualColumn_support E P.cutoff t l))
        ((heatNormalOneResidualColumn_support E P.cutoff t l).trans P.cutoff_support) := by
  exact (heatNormalOneAmplitudeL2_add P.chart P.in_chart P.point_regular P.inside_radius
    (heatNormalOneTimeColumn E P.cutoff t l)
    (heatNormalOneOperatorAmplitude E (heatNormalOneCutoffColumn E P.cutoff t l))
    (heatNormalOneTimeColumn_regular E P.cutoff (P.cutoff_regular.of_le (by norm_num)) t l)
    (heatNormalOneOperatorAmplitude_regular E _ (heatNormalOneCutoffColumn_regular E P.cutoff P.cutoff_regular t l))
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) (heatNormalOneTimeColumn_support E P.cutoff t l))
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      ((heatNormalOneOperatorAmplitude_support E _).trans (heatNormalOneCutoffColumn_support E P.cutoff t l)))
    ((heatNormalOneTimeColumn_support E P.cutoff t l).trans P.cutoff_support)
    (((heatNormalOneOperatorAmplitude_support E _).trans
      (heatNormalOneCutoffColumn_support E P.cutoff t l)).trans P.cutoff_support)).symm

theorem HeatNormalParametrixData.oneResidual_norm_le
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D)
    (B : ℝ) (hB : 0 ≤ B) (t : ℝ) (ht : 0 < t)
    (h : ∀ x k l, |deriv (fun s => heatNormalOneCutoffParametrix E P.cutoff s x k l) t +
      fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
        (fun y q => heatNormalOneCutoffParametrix E P.cutoff t y q l) x k| ≤ B * t)
    (l : Fin 4) : ‖P.oneResidual E t l‖ ≤ 4 * B * t := by
  rw [P.oneResidual_as_amplitude E t l]
  apply (heatNormalOneAmplitudeL2_norm_le P.chart P.exponential P.in_chart P.point_regular
    P.inside_radius _ _ _ _ (4 * (B * t)) (by positivity)
    (fun x => heatNormalOneResidualColumn_bound E P.cutoff t ht B h l x)).trans_eq
  ring

theorem exists_heatNormalOneResidualData (E : HeatNormalOneExtension D)
    (he : e.base ∈ (chartAt FourSpace c).source) (hRic : RicciThree g)
    (hepos : e ∈ o.positive) :
    ∃ P : HeatNormalParametrixData D,
      (∀ t l (v : smoothCovariantFields M 1),
        inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
          inner ℝ (P.oneOperatorColumn E t l) (smoothOneFormL2Linear v)) ∧
      ∃ B ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.oneResidual E t l‖ ≤ B * t := by
  obtain ⟨r₀, C, hr₀, hC, hE, _hInv, hCt, hP, hD⟩ := exists_heatNormalFrameChart D he
  obtain ⟨rd, hrd, hpair⟩ := E.compact_operator_pairing_near he hRic
  obtain ⟨rb, hrb, hbound⟩ := heatNormalOneCutoffParametrix_bound_of_support E hRic hepos
  let R := min r₀ (min rd rb)
  have hR : 0 < R := lt_min hr₀ (lt_min hrd hrb)
  let χ : FourSpace → ℝ := heatNormalChartBump R hR
  have hsR : tsupport χ ⊆ ball 0 R := by
    rw [(heatNormalChartBump R hR).tsupport_eq]
    exact closedBall_subset_ball (by change R / 2 < R; linarith)
  have hsC : tsupport χ ⊆ C.source := by
    rw [hC]
    exact hsR.trans (ball_subset_ball (min_le_left _ _))
  have hRd : R ≤ rd := (min_le_right _ _).trans (min_le_left _ _)
  have hRb : R ≤ rb := (min_le_right _ _).trans (min_le_right _ _)
  let P : HeatNormalParametrixData D := {
    chart := C
    exponential := hE
    in_chart := hCt
    point_regular := hP.of_le (by norm_num)
    inside_radius := hD
    cutoff := χ
    cutoff_regular := (heatNormalChartBump R hR).contDiff
    cutoff_compact := (heatNormalChartBump R hR).hasCompactSupport
    cutoff_support := hsC
    cutoff_zero := (heatNormalChartBump R hR).one_of_mem_closedBall
      (mem_closedBall_self (by change 0 ≤ R / 4; positivity)) }
  refine ⟨P, ?_, ?_⟩
  · intro t l v
    exact hpair C hE hCt P.point_regular hD (heatNormalOneCutoffColumn E χ t l)
      (heatNormalOneCutoffColumn_regular E χ P.cutoff_regular t l)
      (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
        (heatNormalOneCutoffColumn_support E χ t l))
      ((heatNormalOneCutoffColumn_support E χ t l).trans hsC)
      ((heatNormalOneCutoffColumn_support E χ t l).trans (hsR.trans (ball_subset_ball hRd))) v
  · obtain ⟨B, hB, hpoint⟩ := hbound χ (P.cutoff_regular.of_le (by norm_num)) P.cutoff_compact
      (hsR.trans (ball_subset_ball hRb))
      (fun x => by rw [abs_of_nonneg (heatNormalChartBump R hR).nonneg]; exact (heatNormalChartBump R hR).le_one)
      (R / 4) (by positivity)
      (fun x hx => (heatNormalChartBump R hR).one_of_mem_closedBall (ball_subset_closedBall hx))
    refine ⟨4 * B, by positivity, ?_⟩
    intro t ht l
    exact P.oneResidual_norm_le E B hB t ht.1 (hpoint t ht) l

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual compact scalar parametrix satisfies the forced heat ODE
in every eigenmode. Its forcing is its genuine time-minus-Laplacian residual. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

local instance scalarEvolution_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

def HeatScalarChartData.residual (P : HeatScalarChartData D) (t : ℝ) :
    Lp ℝ 2 (normalizedVolume g) := P.timeColumn t - P.laplacianColumn t

def HeatScalarChartData.normalizedResidual (P : HeatScalarChartData D) (t : ℝ) :
    Lp ℝ 2 (normalizedVolume g) := ((normalizedChartFactor g).toReal)⁻¹ • P.residual t

variable [SecondCountableTopology M]
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem HeatScalarChartData.eigen_evolution (P : HeatScalarChartData D)
    (t : ℝ) (ht : 0 < t) (i : ScalarBaseEigenIndex g o d) :
    HasDerivAt (fun s => inner ℝ (P.column s) (scalarBaseEigenvector g o d i))
      (inner ℝ (P.residual t) (scalarBaseEigenvector g o d i) -
        scalarBaseHeatRate g o d i * inner ℝ (P.column t) (scalarBaseEigenvector g o d i)) t := by
  let f : C(M, ℝ) := ⟨(scalarBaseEigenfunction g o d i).val,
    (scalarBaseEigenfunction g o d i).property.continuous⟩
  have hf : ContinuousMap.toLp 2 (normalizedVolume g) ℝ f = scalarBaseEigenvector g o d i :=
    (scalarBaseEigenfunction_L2 g o d i).symm
  have h := P.column_weak_deriv t ht f
  rw [hf] at h
  have hL := scalarFiniteLaplacian_eigen g o d (P.function t) (P.function_regular t) i
  change inner ℝ (P.laplacianColumn t) (scalarBaseEigenvector g o d i) =
    -scalarBaseHeatRate g o d i * inner ℝ (P.column t) (scalarBaseEigenvector g o d i) at hL
  convert h using 1
  change inner ℝ (P.timeColumn t - P.laplacianColumn t) (scalarBaseEigenvector g o d i) -
    scalarBaseHeatRate g o d i * inner ℝ (P.column t) (scalarBaseEigenvector g o d i) = _
  rw [inner_sub_left, hL]
  ring

theorem HeatScalarChartData.normalized_eigen_evolution (P : HeatScalarChartData D)
    (t : ℝ) (ht : 0 < t) (i : ScalarBaseEigenIndex g o d) :
    HasDerivAt (fun s => inner ℝ (P.normalizedColumn s) (scalarBaseEigenvector g o d i))
      (inner ℝ (P.normalizedResidual t) (scalarBaseEigenvector g o d i) -
        scalarBaseHeatRate g o d i *
          inner ℝ (P.normalizedColumn t) (scalarBaseEigenvector g o d i)) t := by
  have h := (P.eigen_evolution d t ht i).const_mul ((normalizedChartFactor g).toReal)⁻¹
  simpa only [HeatScalarChartData.normalizedColumn, HeatScalarChartData.normalizedResidual,
    real_inner_smul_left, mul_sub, mul_left_comm] using h

theorem HeatScalarChartData.normalized_initial_eigen (P : HeatScalarChartData D)
    (i : ScalarBaseEigenIndex g o d) :
    Tendsto (fun t => inner ℝ (P.normalizedColumn t) (scalarBaseEigenvector g o d i))
      (𝓝[Set.Ioi 0] 0) (𝓝 ((scalarBaseEigenfunction g o d i).val e.base)) := by
  let f : C(M, ℝ) := ⟨(scalarBaseEigenfunction g o d i).val,
    (scalarBaseEigenfunction g o d i).property.continuous⟩
  have hf : ContinuousMap.toLp 2 (normalizedVolume g) ℝ f = scalarBaseEigenvector g o d i :=
    (scalarBaseEigenfunction_L2 g o d i).symm
  change Tendsto _ _ (𝓝 (f e.base))
  simpa only [hf] using P.normalizedColumn_initial f

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact support control for the scalar cutoff and its Laplacian. This
allows the geometric operator identity to be used only on the cutoff support. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology BigOperators Matrix.Norms.Elementwise

noncomputable section

theorem heatScalarLift_tsupport {X : Type*} [TopologicalSpace X] [T2Space X]
    (C : OpenPartialHomeomorph FourSpace X) (ψ : FourSpace → ℝ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ C.source) :
    tsupport (heatNormalScalarLift C ψ) ⊆ C '' tsupport ψ := by
  have hK := hc.image_of_continuousOn (C.continuousOn.mono hs)
  exact closure_minimal (heatNormalScalarLift_support C ψ) hK.isClosed

theorem heatScalarOperator_tsupport (a : FourSpace → Mat4)
    (b : FourSpace → Fin 4 → ℝ) (u : FourSpace → ℝ) :
    tsupport (fun x => fourHeatLocalOperator (a x) (b x) 0 u x) ⊆ tsupport u := by
  apply closure_minimal _ (isClosed_tsupport u)
  intro x hx
  by_contra hn
  have hz : u =ᶠ[𝓝 x] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.mp hn
  apply hx
  change fourHeatLocalOperator (a x) (b x) 0 u x = 0
  rw [fourHeatLocalOperator_germ _ _ _ hz]
  have hp (i : Fin 4) : partialDeriv (fun _ : FourSpace => (0 : ℝ)) i = fun _ => 0 := by
    funext y
    simp only [partialDeriv, fderiv_const_apply, _root_.zero_apply]
  simp only [fourHeatLocalOperator, hp, mul_zero, Finset.sum_const_zero, neg_zero, add_zero]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatScalarChartData.function_support (P : HeatScalarChartData D) (t : ℝ) :
    tsupport (P.function t) ⊆ P.chart '' tsupport P.cutoff := by
  have hs := P.extension.scalarCutoff_support P.cutoff t
  exact (heatScalarLift_tsupport P.chart _
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) hs)
    (hs.trans P.cutoff_support)).trans (image_mono hs)

theorem HeatScalarChartData.timeFunction_support (P : HeatScalarChartData D) (t : ℝ) :
    tsupport (P.timeFunction t) ⊆ P.chart '' tsupport P.cutoff := by
  have hs := P.timeAmplitude_support t
  exact (heatScalarLift_tsupport P.chart _
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) hs)
    (hs.trans P.cutoff_support)).trans (image_mono hs)

def HeatScalarChartData.residualAmplitude (P : HeatScalarChartData D) (t : ℝ) (x : FourSpace) : ℝ :=
  P.timeAmplitude t x + fourHeatLocalOperator (P.extension.a x) (P.extension.b x) 0
    (P.extension.scalarCutoff P.cutoff t) x

theorem HeatScalarChartData.residualAmplitude_regular (P : HeatScalarChartData D) (t : ℝ) :
    ContDiff ℝ 2 (P.residualAmplitude t) :=
  ((P.timeAmplitude_regular t).of_le (by norm_num)).add
    (fourHeatLocalOperator_contDiff 2 P.extension.a P.extension.b (fun _ => 0) _
      (fun i j => (P.extension.a_regular i j).of_le (by norm_num))
      (fun i => (P.extension.b_regular i).of_le (by norm_num)) contDiff_const
      (P.extension.scalarCutoff_regular P.cutoff P.cutoff_regular t))

theorem HeatScalarChartData.residualAmplitude_support (P : HeatScalarChartData D) (t : ℝ) :
    tsupport (P.residualAmplitude t) ⊆ tsupport P.cutoff := by
  exact (tsupport_add _ _).trans (union_subset (P.timeAmplitude_support t)
    ((heatScalarOperator_tsupport _ _ _).trans (P.extension.scalarCutoff_support P.cutoff t)))

def HeatScalarChartData.residualFunction (P : HeatScalarChartData D) (t : ℝ) : M → ℝ :=
  heatNormalScalarLift P.chart (P.residualAmplitude t)

theorem HeatScalarChartData.residualFunction_continuous (P : HeatScalarChartData D) (t : ℝ) :
    Continuous (P.residualFunction t) :=
  heatNormalScalarLift_continuous P.chart _ (P.residualAmplitude_regular t).continuous.continuousOn
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) (P.residualAmplitude_support t))
    ((P.residualAmplitude_support t).trans P.cutoff_support)

theorem HeatScalarChartData.residualFunction_support (P : HeatScalarChartData D) (t : ℝ) :
    tsupport (P.residualFunction t) ⊆ P.chart '' tsupport P.cutoff := by
  have hs := P.residualAmplitude_support t
  exact (heatScalarLift_tsupport P.chart _
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) hs)
    (hs.trans P.cutoff_support)).trans (image_mono hs)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual compact normal columns have a common L2 growth constant
for every initial frame in a compact coordinate set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem heatUniformColumn_growth (E : HeatFamilySmoothCoefficients) (r : ℝ) (hr : 0 < r)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonNormalMember g o c E r e),
      frameCoordinateState g c e ∈ K → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l,
      ‖(N.parametrixData hr).normalizedColumn N.extension t l‖ ≤ C / t := by
  let χ : FourSpace → ℝ := heatNormalChartBump r hr
  have hχs : tsupport χ ⊆ ball (0 : FourSpace) r := by
    rw [(heatNormalChartBump r hr).tsupport_eq]
    exact closedBall_subset_ball (by change r / 2 < r; linarith)
  obtain ⟨B, hB, hb⟩ := heatUniformPolynomial_weight_bound (g := g) (o := o) (c := c) E r χ
    (heatNormalChartBump r hr).continuous (heatNormalChartBump r hr).hasCompactSupport hχs K hK
  let A := B / (64 * Real.pi ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let C := 2 * (normalizedChartFactor g).toReal * A
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨‖((normalizedChartFactor g).toReal)⁻¹‖ * (C + 1), by positivity, ?_⟩
  intro e N hq t ht l
  let P := N.parametrixData hr
  have hcut : P.cutoff = χ := rfl
  have hpt (x : FourSpace) : frameExponentialJacobian g o e x *
      ‖heatNormalCutoffColumn N.extension χ t l x‖ ^ 2 ≤ B * fourHeatGaussian t x ^ 2 := by
    rw [heatNormalCutoffColumn_gaussian, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    calc
      _ = (frameExponentialJacobian g o e x * ‖heatNormalPolynomialColumn N.extension χ t l x‖ ^ 2) *
          fourHeatGaussian t x ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hb e N hq t ⟨ht.1.le, ht.2⟩ x l) (sq_nonneg _)
  have hi : Integrable (fun x : FourSpace => B * fourHeatGaussian t x ^ 2) :=
    (fourHeatGaussian_square_integrable t ht.1).const_mul B
  have hm : Continuous (fun x => frameExponentialJacobian g o e x *
      ‖heatNormalCutoffColumn N.extension χ t l x‖ ^ 2) :=
    (frameExponentialJacobian_continuous g o e).mul
      ((heatNormalCutoffColumn_regular N.extension χ
        (heatNormalChartBump r hr).contDiff t l).continuous.norm.pow 2)
  have hfi : Integrable (fun x => frameExponentialJacobian g o e x *
      ‖heatNormalCutoffColumn N.extension χ t l x‖ ^ 2) :=
    hi.mono' hm.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (frameExponentialJacobian_nonneg g o e x) (sq_nonneg _))]
      exact hpt x)
  have hint : (∫ x, frameExponentialJacobian g o e x *
      ‖heatNormalCutoffColumn N.extension χ t l x‖ ^ 2) ≤ A / t ^ 2 := by
    calc
      _ ≤ ∫ x : FourSpace, B * fourHeatGaussian t x ^ 2 := integral_mono hfi hi hpt
      _ = _ := by rw [integral_const_mul, fourHeatGaussian_square_mass t ht.1]; dsimp [A]; ring
  have hn := heatNormalAmplitudeL2_norm_sq_le_integral P.chart P.exponential P.in_chart
    P.point_regular P.inside_radius (heatNormalCutoffColumn N.extension P.cutoff t l)
    (heatNormalCutoffColumn_regular N.extension P.cutoff (P.cutoff_regular.of_le (by norm_num)) t l)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalCutoffColumn_support N.extension P.cutoff t l))
    ((heatNormalCutoffColumn_support N.extension P.cutoff t l).trans P.cutoff_support)
  have hn' : ‖P.column N.extension t l‖ ^ 2 ≤ C / t ^ 2 := by
    have hint' : (∫ x, frameExponentialJacobian g o e x *
        ‖heatNormalCutoffColumn N.extension P.cutoff t l x‖ ^ 2) ≤ A / t ^ 2 := by
      simpa only [hcut] using hint
    exact hn.trans ((mul_le_mul_of_nonneg_left hint' (by positivity)).trans_eq (by dsimp [C]; ring))
  have hs : (‖P.column N.extension t l‖ * t) ^ 2 ≤ C := by
    calc
      _ = ‖P.column N.extension t l‖ ^ 2 * t ^ 2 := by ring
      _ ≤ (C / t ^ 2) * t ^ 2 := mul_le_mul_of_nonneg_right hn' (sq_nonneg t)
      _ = C := by field_simp [ht.1.ne']
  have hcol : ‖P.column N.extension t l‖ ≤ (C + 1) / t := by
    apply (le_div_iff₀ ht.1).mpr
    nlinarith [sq_nonneg C, norm_nonneg (P.column N.extension t l)]
  change ‖((normalizedChartFactor g).toReal)⁻¹ • P.column N.extension t l‖ ≤ _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left hcol (norm_nonneg _)).trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A single bound for the actual signed local Gaussian integral over a
compact family of initial frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem heatUniformSignedIntegral_bound (E : HeatFamilySmoothCoefficients) (r : ℝ) (hr : 0 < r)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ ball 0 r) (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ D ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonNormalMember g o c E r e),
      frameCoordinateState g c e ∈ K → ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖∫ x : FourSpace, fourHeatGaussian t x ^ 2 *
        (frameExponentialJacobian g o e x * χ x ^ 2 *
          heatSignedGram (heatNormalMatrixPolynomial N.extension t x)
            (heatNormalMatrixPolynomial N.extension t x))‖ ≤ D := by
  obtain ⟨C, hC, hb⟩ := heatUniformSignedFirst_quadratic (g := g) (o := o) (c := c)
    E r hr χ hχ hχs K hK
  obtain ⟨B, hB, ht⟩ := heatFamilySignedTail_bound E χ hχ.continuous hc K hK
  refine ⟨(32 * C + B) / (64 * Real.pi ^ 2), by positivity, ?_⟩
  intro e N hq t htt
  simp_rw [heatNormalMatrixPolynomial_signed]
  apply fourHeat_signed_gaussian_bound _ _ C B t hC hB htt.1 (hb e N hq)
  intro x
  rw [N.signedTail_family χ hχs t x]
  exact ht _ hq t ⟨htt.1.le, htt.2⟩ x

end
end PositiveEinsteinFour.Geometry
end


section

/-! The surviving center coefficient of the actual Euler Gram expansion
is the Euler curvature polynomial with its exact Gaussian normalization. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatNormalBundleExtension.eulerAmplitude (E : HeatNormalBundleExtension D)
    (m : ℕ) (x : FourSpace) : HeatEulerFiber :=
  (fourHeatCoefficient E.base.a E.base.b (fun _ => 0) E.base.U m x,
    E.oneCompanion.amplitude m x, E.amplitude m x)

theorem HeatNormalBundleExtension.eulerAmplitude_zero (E : HeatNormalBundleExtension D)
    (x : FourSpace) : E.eulerAmplitude 0 x = E.base.U x • heatEulerUnit := by
  apply Prod.ext
  · change E.base.U x = E.base.U x * 1
    ring
  · apply Prod.ext
    · exact E.oneCompanion.amplitude_zero x
    · exact E.amplitude_zero x

theorem HeatNormalBundleExtension.eulerAmplitude_first_gram
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    heatEulerGram (E.eulerAmplitude 1 0) (E.eulerAmplitude 1 0) =
      (twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e) *
        twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e)).trace - 72 := by
  let α := -fourHeatLocalOperator (E.base.a 0) (E.base.b 0) 0 E.base.U 0
  have hscalar : fourHeatCoefficient E.base.a E.base.b (fun _ => 0) E.base.U 1 0 = α := by
    have h := fourHeatCoefficient_center 0 E.base.a E.base.b (fun _ => 0) E.base.U
      (E.base.U_pos 0).ne'
    simpa only [Nat.cast_zero, zero_add, one_mul, fourHeatCoefficient] using h
  have heq : E.eulerAmplitude 1 0 =
      (α, α • (1 : Mat4) - (3 : ℝ) • 1,
        α • (1 : HeatMat6) - twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e)) := by
    apply Prod.ext
    · exact hscalar
    · apply Prod.ext
      · exact E.oneCompanion.first_amplitude_center
      · exact E.first_amplitude_intrinsic_center he
  rw [heq]
  exact heatEulerGram_scalar_potential α _ (heat_actual_potential_symmetric e)
    (actual_twoFormPotential_trace hRic e)

def HeatNormalBundleExtension.eulerSecondWeight (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (x : FourSpace) : ℝ :=
  frameExponentialJacobian g o e x * χ x ^ 2 *
    (2 * E.base.U x * heatEulerTrace (E.eulerAmplitude 2 x) +
      heatEulerGram (E.eulerAmplitude 1 x) (E.eulerAmplitude 1 x))

omit [T3Space M] [CompactSpace M] in
theorem heatEuler_potential_density (hRic : RicciThree g) (e : FrameBundle g) :
    ((twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e) *
      twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e)).trace - 72) /
      (32 * Real.pi ^ 2) = curvatureEulerDensity (twoFormMetricCurvatureTensor g e) := by
  have h := actual_hodgeEulerTracePolynomial hRic e
  have hl (i j k l : Fin 4) :
      twoFormMetricCurvatureTensor g e ![i,j,l,k] = -twoFormMetricCurvatureTensor g e ![i,j,k,l] := by
    simp only [twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    exact frame_algebraic_lastSkew e.frame i j k l
  unfold hodgeEulerTracePolynomial at h
  simp only [connectionCurvature_euler_trace _ hl, Finset.sum_const_zero, zero_div, add_zero] at h
  convert h using 1
  ring

theorem HeatNormalBundleExtension.eulerSecondWeight_center
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g)
    (he : e.base ∈ (chartAt FourSpace c).source) (χ : FourSpace → ℝ) (hχ : χ 0 = 1) :
    E.eulerSecondWeight χ 0 / (64 * Real.pi ^ 2) =
      curvatureEulerDensity (twoFormMetricCurvatureTensor g e) := by
  have hU : E.base.U 0 = 1 :=
    E.base.U_near.self_of_nhds.trans (heatNormalLeadingAmplitude_zero g o e)
  have htr : heatEulerTrace (E.eulerAmplitude 2 0) = E.eulerSecondAmplitude 0 := rfl
  rw [eulerSecondWeight, frameExponentialJacobian_zero, hχ, hU, htr,
    E.eulerSecondAmplitude_center hRic he, E.eulerAmplitude_first_gram hRic he]
  convert heatEuler_potential_density hRic e using 1
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first Euler coefficient is a jointly C2 family with a uniform
quadratic zero at each actual normal center. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section

def HeatFamilyOneCoefficients.eulerAmplitude (F : HeatFamilyOneCoefficients)
    (m : ℕ) (z : HeatRadialFrameSpace) : HeatEulerFiber :=
  (F.base.scalarAmplitude m z, F.amplitude m z, F.base.amplitude m z)

def heatFamilyEulerFirst (F : HeatFamilyOneCoefficients) (χ : FourSpace → ℝ)
    (z : HeatRadialFrameSpace) : ℝ :=
  χ z.1 ^ 2 / F.base.U z * heatEulerTrace (F.eulerAmplitude 1 z)

theorem heatFamilyEulerFirst_regular (F : HeatFamilyOneCoefficients)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) : ContDiff ℝ 2 (heatFamilyEulerFirst F χ) := by
  have hs : ContDiff ℝ 2 (fun z => heatEulerTrace (F.eulerAmplitude 1 z)) := by
    unfold heatEulerTrace HeatFamilyOneCoefficients.eulerAmplitude Matrix.trace Matrix.diag
    exact ((contDiff_const.mul ((F.base.scalarAmplitude_regular 1 (by omega)).of_le (by norm_num))).sub
      (contDiff_const.mul (ContDiff.sum (fun k _ =>
        (F.amplitude_regular 1 (by omega) k k).of_le (by norm_num))))).add
      (ContDiff.sum (fun k _ => (F.base.amplitude_regular 1 (by omega) k k).of_le (by norm_num)))
  exact (((hχ.comp contDiff_fst).pow 2).div (F.base.U_regular.of_le (by norm_num))
    (fun z => (F.base.U_pos z).ne')).mul hs

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonEulerMember.one_amplitude_family (N : HeatCommonEulerMember g o c F r e)
    (m : ℕ) (hm : m ≤ 3) :
    N.one.amplitude m = fun x => F.amplitude m (x, frameCoordinateState g c e) := by
  unfold HeatNormalOneExtension.amplitude
  rw [N.one_base, N.normal.a_family, N.normal.b_family,
    N.one_B_family, N.one_C_family, N.normal.U_family]
  exact (F.amplitude_slice m hm _).symm

theorem HeatCommonEulerMember.scalar_amplitude_family (N : HeatCommonEulerMember g o c F r e)
    (m : ℕ) (hm : m ≤ 3) :
    N.normal.extension.base.scalarAmplitude m =
      fun x => F.base.scalarAmplitude m (x, frameCoordinateState g c e) := by
  unfold HeatNormalExtension.scalarAmplitude
  rw [N.normal.a_family, N.normal.b_family, N.normal.U_family]
  exact (F.base.scalarAmplitude_slice m hm _).symm

theorem HeatCommonEulerMember.eulerFirst_zero_near (N : HeatCommonEulerMember g o c F r e)
    (hRic : RicciThree g) (χ : FourSpace → ℝ) :
    (fun x => heatFamilyEulerFirst F χ (x, frameCoordinateState g c e)) =ᶠ[𝓝 0] fun _ => 0 := by
  have h := N.one.eulerFirst_zero_near N.normal.extension N.one_base hRic
  filter_upwards [h] with x hx
  have htrace : heatEulerTrace (F.eulerAmplitude 1 (x, frameCoordinateState g c e)) = 0 := by
    change 2 * F.base.scalarAmplitude 1 (x, frameCoordinateState g c e) -
      2 * (F.amplitude 1 (x, frameCoordinateState g c e)).trace +
      (F.base.amplitude 1 (x, frameCoordinateState g c e)).trace = 0
    rw [← congrFun (N.one_amplitude_family 1 (by norm_num)) x,
      ← congrFun (N.normal.amplitude_family 1 (by norm_num)) x,
      ← congrFun (N.scalar_amplitude_family 1 (by norm_num)) x]
    exact hx
  simp only [heatFamilyEulerFirst, htrace, mul_zero]

theorem heatUniformEulerFirst_quadratic (F : HeatFamilyOneCoefficients) (r : ℝ)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hχs : tsupport χ ⊆ ball 0 r)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) (hRic : RicciThree g) :
    ∃ C ≥ (0 : ℝ), ∀ (e : FrameBundle g) (_N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K → ∀ x,
      ‖heatFamilyEulerFirst F χ (x, frameCoordinateState g c e)‖ ≤ C * ‖x‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := heatFamily_quadratic_bound (heatFamilyEulerFirst F χ)
    (heatFamilyEulerFirst_regular F χ hχ) r K hK
  refine ⟨C, hC, ?_⟩
  intro e N hq x
  have hz := N.eulerFirst_zero_near hRic χ
  by_cases hx : x ∈ closedBall (0 : FourSpace) r
  · apply hb _ hq hz.self_of_nhds _ x hx
    rw [hz.fderiv_eq]
    exact fderiv_const_apply _
  · have hxs : x ∉ tsupport χ := fun hs => hx (ball_subset_closedBall (hχs hs))
    have hzero := image_eq_zero_of_notMem_tsupport hxs
    simp only [heatFamilyEulerFirst, hzero, zero_pow (by norm_num : 2 ≠ 0),
      zero_div, zero_mul, norm_zero]
    positivity

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive-time L2 continuity of the actual normal parametrix and residual. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.column_continuous (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (l : Fin 6) :
    ContinuousOn (fun t => P.column E t l) (Ioi 0) := by
  apply heatNormalAmplitudeL2_continuous_family P.chart P.in_chart P.point_regular P.inside_radius
    (fun t => heatNormalCutoffColumn E P.cutoff t l)
    (fun t => heatNormalCutoffColumn_regular E P.cutoff (P.cutoff_regular.of_le (by norm_num)) t l)
    (fun t => P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalCutoffColumn_support E P.cutoff t l))
    (fun t => (heatNormalCutoffColumn_support E P.cutoff t l).trans P.cutoff_support)
    ?_ (tsupport P.cutoff) P.cutoff_compact P.cutoff_support
    (fun t _ => heatNormalCutoffColumn_support E P.cutoff t l)
  exact (heatNormalCutoffColumn_joint_continuousOn E P.cutoff
    (P.cutoff_regular.of_le (by norm_num)) l).mono (prod_mono Subset.rfl (subset_univ _))

theorem HeatNormalParametrixData.residual_continuous (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (l : Fin 6) :
    ContinuousOn (fun t => P.residual E t l) (Ioi 0) := by
  apply heatNormalAmplitudeL2_continuous_family P.chart P.in_chart P.point_regular P.inside_radius
    (fun t => heatNormalResidualColumn E P.cutoff t l)
    (fun t => heatNormalResidualColumn_regular E P.cutoff P.cutoff_regular t l)
    (fun t => P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalResidualColumn_support E P.cutoff t l))
    (fun t => (heatNormalResidualColumn_support E P.cutoff t l).trans P.cutoff_support)
    ?_ (tsupport P.cutoff) P.cutoff_compact P.cutoff_support
    (fun t _ => heatNormalResidualColumn_support E P.cutoff t l)
  exact (heatNormalResidualColumn_joint_continuousOn E P.cutoff
    (P.cutoff_regular.of_le (by norm_num)) l).mono (prod_mono Subset.rfl (subset_univ _))

theorem HeatNormalParametrixData.normalizedColumn_continuous (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (l : Fin 6) :
    ContinuousOn (fun t => P.normalizedColumn E t l) (Ioi 0) := by
  exact (P.column_continuous E l).const_smul ((normalizedChartFactor g).toReal)⁻¹

theorem HeatNormalParametrixData.normalizedResidual_continuous (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (l : Fin 6) :
    ContinuousOn (fun t => P.normalizedResidual E t l) (Ioi 0) := by
  exact (P.residual_continuous E l).const_smul ((normalizedChartFactor g).toReal)⁻¹

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive-time L2 continuity of the actual normal parametrix and residual. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.oneColumn_continuous (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (l : Fin 4) :
    ContinuousOn (fun t => P.oneColumn E t l) (Ioi 0) := by
  apply heatNormalOneAmplitudeL2_continuous_family P.chart P.in_chart P.point_regular P.inside_radius
    (fun t => heatNormalOneCutoffColumn E P.cutoff t l)
    (fun t => (heatNormalOneCutoffColumn_regular E P.cutoff P.cutoff_regular t l).of_le (by norm_num))
    (fun t => P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalOneCutoffColumn_support E P.cutoff t l))
    (fun t => (heatNormalOneCutoffColumn_support E P.cutoff t l).trans P.cutoff_support)
    ?_ (tsupport P.cutoff) P.cutoff_compact P.cutoff_support
    (fun t _ => heatNormalOneCutoffColumn_support E P.cutoff t l)
  exact (heatNormalOneCutoffColumn_joint_continuousOn E P.cutoff
    (P.cutoff_regular.of_le (by norm_num)) l).mono (prod_mono Subset.rfl (subset_univ _))

theorem HeatNormalParametrixData.oneResidual_continuous (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (l : Fin 4) :
    ContinuousOn (fun t => P.oneResidual E t l) (Ioi 0) := by
  have heq : (fun t => P.oneResidual E t l) = (fun t => heatNormalOneAmplitudeL2 D P.chart P.in_chart P.point_regular P.inside_radius
      (heatNormalOneResidualColumn E P.cutoff t l)
      (heatNormalOneResidualColumn_regular E P.cutoff P.cutoff_regular t l)
      (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) (heatNormalOneResidualColumn_support E P.cutoff t l))
      ((heatNormalOneResidualColumn_support E P.cutoff t l).trans P.cutoff_support)) :=
    funext (fun t => P.oneResidual_as_amplitude E t l)
  rw [heq]
  apply heatNormalOneAmplitudeL2_continuous_family P.chart P.in_chart P.point_regular P.inside_radius
    (fun t => heatNormalOneResidualColumn E P.cutoff t l)
    (fun t => heatNormalOneResidualColumn_regular E P.cutoff P.cutoff_regular t l)
    (fun t => P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalOneResidualColumn_support E P.cutoff t l))
    (fun t => (heatNormalOneResidualColumn_support E P.cutoff t l).trans P.cutoff_support)
    ?_ (tsupport P.cutoff) P.cutoff_compact P.cutoff_support
    (fun t _ => heatNormalOneResidualColumn_support E P.cutoff t l)
  exact (heatNormalOneResidualColumn_joint_continuousOn E P.cutoff
    (P.cutoff_regular.of_le (by norm_num)) l).mono (prod_mono Subset.rfl (subset_univ _))

theorem HeatNormalParametrixData.oneNormalizedColumn_continuous (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (l : Fin 4) :
    ContinuousOn (fun t => P.oneNormalizedColumn E t l) (Ioi 0) := by
  exact (P.oneColumn_continuous E l).const_smul ((normalizedChartFactor g).toReal)⁻¹

variable [SecondCountableTopology M]

theorem HeatNormalParametrixData.oneNormalizedResidual_continuous (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (l : Fin 4) :
    ContinuousOn (fun t => P.oneNormalizedResidual E t l) (Ioi 0) := by
  exact (P.oneResidual_continuous E l).const_smul ((normalizedChartFactor g).toReal)⁻¹

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar transport equation and its actual compact cutoff have a
uniform linearly vanishing residual, including the cutoff annulus. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatScalarChartData.residualAmplitude_bound (P : HeatScalarChartData D)
    (ha : ∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hχ : ∀ x, |P.cutoff x| ≤ 1)
    (r : ℝ) (hr : 0 < r) (hinner : ∀ x ∈ ball 0 r, P.cutoff x = 1)
    (hres : ∀ x ∈ tsupport P.cutoff, ∀ t > (0 : ℝ),
      deriv (fun v => P.extension.scalarParametrix v x) t +
        fourHeatLocalOperator (P.extension.a x) (P.extension.b x) 0
          (P.extension.scalarParametrix t) x =
        fourHeatGaussian t x * t ^ 3 * fourHeatLocalOperator (P.extension.a x)
          (P.extension.b x) 0 (P.extension.scalarAmplitude 3) x) :
    ∃ B ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x, |P.residualAmplitude t x| ≤ B * t := by
  let E := P.extension
  let u : Fin 4 → FourSpace → Fin 6 → ℝ := fun m y _ => E.scalarAmplitude m y
  have hu (m : Fin 4) (q : Fin 6) : ContDiff ℝ 2 (fun y => u m y q) :=
    (E.scalarAmplitude_regular m (by omega)).of_le (by norm_num)
  obtain ⟨B₁, hB₁, hb₁⟩ := fourHeatScaledCommutator_gaussian_bound E.a E.b
    (fun _ => 0) P.cutoff u
    (fun i j => (E.a_regular i j).continuous)
    (fun i => (E.b_regular i).continuous) (fun _ _ _ => continuous_const)
    (P.cutoff_regular.of_le (by norm_num)) P.cutoff_compact hu r hr hinner
  let F := fun x => fourHeatLocalOperator (E.a x) (E.b x) 0 (E.scalarAmplitude 3) x
  have hF : Continuous F :=
    (fourHeatLocalOperator_contDiff 2 E.a E.b (fun _ => 0) (E.scalarAmplitude 3)
      (fun i j => (E.a_regular i j).of_le (by norm_num))
      (fun i => (E.b_regular i).of_le (by norm_num)) contDiff_const
      (E.scalarAmplitude_regular 3 (by omega))).continuous
  obtain ⟨A, hA⟩ := P.cutoff_compact.bddAbove_image hF.abs.continuousOn
  let B₀ := max A 0 / (16 * Real.pi ^ 2)
  have hB₀ : 0 ≤ B₀ := by positivity
  refine ⟨B₀ + B₁, add_nonneg hB₀ hB₁, ?_⟩
  intro t ht x
  by_cases hx : x ∈ tsupport P.cutoff
  · have hsym (i j : Fin 4) : E.a x i j = E.a x j i := by
      rw [ha x hx]
      exact congrFun (congrFun (heatNormalInverse_symm g o e x) j) i
    have hQ : |deriv (fun v => E.scalarParametrix v x) t +
        fourHeatLocalOperator (E.a x) (E.b x) 0 (E.scalarParametrix t) x| ≤ B₀ * t := by
      rw [hres x hx t ht.1, abs_mul, abs_mul,
        abs_of_pos (fourHeatGaussian_pos t ht.1 x), abs_of_pos (pow_pos ht.1 3)]
      have hFx : |F x| ≤ max A 0 := (hA (mem_image_of_mem _ hx)).trans (le_max_left _ _)
      calc
        _ ≤ (fourHeatGaussian t x * t ^ 3) * max A 0 :=
          mul_le_mul_of_nonneg_left hFx
            (mul_nonneg (fourHeatGaussian_pos t ht.1 x).le (pow_nonneg ht.1.le 3))
        _ ≤ (fourHeatGaussian t 0 * t ^ 3) * max A 0 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (fourHeatGaussian_le_diagonal t ht.1 x)
              (pow_nonneg ht.1.le 3)) (le_max_right _ _)
        _ = B₀ * t := by
          have hg := fourHeatGaussian_diagonal_power 1 t ht.1
          norm_num only [Nat.reduceAdd, pow_one] at hg
          dsimp only [B₀]
          calc
            _ = max A 0 * (t ^ 3 * fourHeatGaussian t 0) := by ring
            _ = _ := by rw [hg]; ring
    have hcut := fourHeatLocalOperator_cutoff (E.a x) (E.b x) P.cutoff
      (E.scalarParametrix t) x hsym (P.cutoff_regular.contDiffAt.of_le (by norm_num))
      ((E.scalarParametrix_regular t).contDiffAt.of_le (by norm_num))
    have hscaled := fourHeatScaledCommutator_identity E.a E.b (fun _ => 0)
      P.cutoff u hu t ht.1 x 0
    have hz (i : Fin 4) (q : Fin 6) : (0 : Fin 4 → HeatMat6) i 0 q = 0 := rfl
    simp only [fourHeatBundlePolynomial, u, hz, zero_mul,
      Finset.sum_const_zero, add_zero] at hscaled
    have hdt : deriv (fun v => E.scalarParametrix v x) t =
        fourHeatGaussianPolynomialTime (fun m => E.scalarAmplitude m) t x :=
      (fourHeatGaussianPolynomial_hasDerivAt
        (fun m => E.scalarAmplitude m) t ht.1 x).deriv
    have hid : P.residualAmplitude t x =
        P.cutoff x * (deriv (fun v => E.scalarParametrix v x) t +
          fourHeatLocalOperator (E.a x) (E.b x) 0 (E.scalarParametrix t) x) +
        (fourHeatGaussian t x / t) *
          fourHeatScaledCommutator E.a E.b (fun _ => 0) P.cutoff u t x 0 := by
      change P.cutoff x * fourHeatGaussianPolynomialTime
        (fun m => E.scalarAmplitude m) t x +
        fourHeatLocalOperator (E.a x) (E.b x) 0
          (fun y => P.cutoff y * E.scalarParametrix t y) x = _
      rw [hcut, hdt]
      change fourHeatLocalOperator (E.a x) (E.b x) 0 P.cutoff x * E.scalarParametrix t x -
        2 * (∑ i, ∑ j, E.a x i j * partialDeriv P.cutoff i x *
          partialDeriv (E.scalarParametrix t) j x) = _ at hscaled
      linarith [hscaled]
    rw [hid]
    calc
      _ ≤ |P.cutoff x * (deriv (fun v => E.scalarParametrix v x) t +
          fourHeatLocalOperator (E.a x) (E.b x) 0 (E.scalarParametrix t) x)| +
          |(fourHeatGaussian t x / t) *
            fourHeatScaledCommutator E.a E.b (fun _ => 0) P.cutoff u t x 0| := abs_add_le _ _
      _ ≤ B₀ * t + B₁ * t := by
        apply add_le_add _ (hb₁ t ht x 0)
        rw [abs_mul]
        exact (mul_le_mul (hχ x) hQ (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
      _ = _ := by ring
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (P.residualAmplitude_support t h)),
      abs_zero]
    exact mul_nonneg (add_nonneg hB₀ hB₁) ht.1.le

end
end PositiveEinsteinFour.Geometry
end


section

/-! The forcing in the spectral scalar ODE is the actual compactly
supported local parametrix residual, with no domain or operator premise. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatScalarChartData.residualFunction_eq (P : HeatScalarChartData D)
    (ha : ∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hb : ∀ x ∈ tsupport P.cutoff, P.extension.b x = heatNormalDrift g o e x)
    (hd : ∀ x ∈ tsupport P.cutoff, 0 < (heatNormalMetric g o e x).det)
    (t : ℝ) (y : M) :
    P.residualFunction t y = P.timeFunction t y - scalarLaplacianBase g (P.function t) y := by
  by_cases hy : y ∈ P.chart '' tsupport P.cutoff
  · obtain ⟨x, hx, rfl⟩ := hy
    have hs := P.cutoff_support hx
    have hL := P.column_laplacian_local t x hs (hd x hx)
    change heatNormalScalarLift P.chart (P.residualAmplitude t) (P.chart x) =
      heatNormalScalarLift P.chart (P.timeAmplitude t) (P.chart x) - _
    rw [heatNormalScalarLift_source P.chart _ hs, heatNormalScalarLift_source P.chart _ hs]
    change P.timeAmplitude t x + fourHeatLocalOperator (P.extension.a x) (P.extension.b x) 0
      (P.extension.scalarCutoff P.cutoff t) x = _
    rw [ha x hx, hb x hx, hL]
    ring
  · have hR : P.residualFunction t y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hy (P.residualFunction_support t h))
    have hT : P.timeFunction t y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hy (P.timeFunction_support t h))
    have hL : scalarLaplacianBase g (P.function t) y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hy
        (P.function_support t (scalarLaplacianBase_tsupport g (P.function t) h)))
    rw [hR, hT, hL, sub_self]

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance scalarResidual_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem HeatScalarChartData.residual_realization (P : HeatScalarChartData D)
    (ha : ∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hb : ∀ x ∈ tsupport P.cutoff, P.extension.b x = heatNormalDrift g o e x)
    (hd : ∀ x ∈ tsupport P.cutoff, 0 < (heatNormalMetric g o e x).det) (t : ℝ) :
    P.residual t = ContinuousMap.toLp 2 (normalizedVolume g) ℝ
      ⟨P.residualFunction t, P.residualFunction_continuous t⟩ := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (P.timeColumn t) (P.laplacianColumn t),
    scalarFiniteValueL2_coe g (P.timeFunction t) (P.timeFunction_regular t),
    scalarFiniteLaplacianL2_coe g (P.function t) (P.function_regular t),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g)
      (⟨P.residualFunction t, P.residualFunction_continuous t⟩ : C(M, ℝ))] with y hsub hT hL hR
  change (P.timeColumn t - P.laplacianColumn t) y = _
  rw [hsub]
  change scalarFiniteValueL2 g (P.timeFunction t) (P.timeFunction_regular t) y -
    scalarFiniteLaplacianL2 g (P.function t) (P.function_regular t) y = _
  rw [hT, hL, hR]
  exact (P.residualFunction_eq ha hb hd t y).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The compact Euler polynomial and its vanishing lower-order term. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

theorem heatEulerTrace_continuous : Continuous heatEulerTrace := by
  unfold heatEulerTrace Matrix.trace Matrix.diag
  fun_prop

theorem heatEulerGram_continuous :
    Continuous (fun z : HeatEulerFiber × HeatEulerFiber => heatEulerGram z.1 z.2) := by
  unfold heatEulerGram Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  fun_prop

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.eulerAmplitude_continuous
    (E : HeatNormalBundleExtension D) (m : ℕ) (hm : m ≤ 3) : Continuous (E.eulerAmplitude m) := by
  have hs : ContDiff ℝ 1 (fourHeatCoefficient E.base.a E.base.b (fun _ => 0) E.base.U m) :=
    fourHeatCoefficient_contDiff m 1 _ _ _ _
      (fun i j => (E.base.a_regular i j).of_le (by exact_mod_cast (show 1 + 3 * m ≤ 10 by omega)))
      (fun i => (E.base.b_regular i).of_le (by exact_mod_cast (show 1 + 3 * m ≤ 10 by omega)))
      contDiff_const (E.base.U_regular.of_le (by exact_mod_cast (show 1 + 3 * m ≤ 10 by omega)))
      (fun y => (E.base.U_pos y).ne')
  exact hs.continuous.prodMk
    ((continuous_pi (fun k => continuous_pi (fun l =>
      (E.oneCompanion.amplitude_regular m hm k l).continuous))).prodMk
      (continuous_pi (fun k => continuous_pi (fun l => (E.amplitude_regular m hm k l).continuous))))

def HeatNormalBundleExtension.eulerFirst (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (x : FourSpace) : ℝ :=
  frameExponentialJacobian g o e x * χ x ^ 2 * E.base.U x * heatEulerTrace (E.eulerAmplitude 1 x)

def HeatNormalBundleExtension.eulerTail (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (x : FourSpace) : ℝ :=
  frameExponentialJacobian g o e x * χ x ^ 2 *
    (2 * E.base.U x * heatEulerTrace (E.eulerAmplitude 2 x) +
      heatEulerGram (E.eulerAmplitude 1 x) (E.eulerAmplitude 1 x) +
      t * (2 * E.base.U x * heatEulerTrace (E.eulerAmplitude 3 x) +
        2 * heatEulerGram (E.eulerAmplitude 1 x) (E.eulerAmplitude 2 x)) +
      t ^ 2 * (2 * heatEulerGram (E.eulerAmplitude 1 x) (E.eulerAmplitude 3 x) +
        heatEulerGram (E.eulerAmplitude 2 x) (E.eulerAmplitude 2 x)) +
      t ^ 3 * (2 * heatEulerGram (E.eulerAmplitude 2 x) (E.eulerAmplitude 3 x)) +
      t ^ 4 * heatEulerGram (E.eulerAmplitude 3 x) (E.eulerAmplitude 3 x))

def HeatNormalBundleExtension.eulerPolynomial (E : HeatNormalBundleExtension D)
    (t : ℝ) (x : FourSpace) : HeatEulerFiber :=
  E.eulerAmplitude 0 x + t • E.eulerAmplitude 1 x +
    t ^ 2 • E.eulerAmplitude 2 x + t ^ 3 • E.eulerAmplitude 3 x

theorem HeatNormalBundleExtension.eulerPolynomial_gram (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (x : FourSpace) :
    frameExponentialJacobian g o e x * χ x ^ 2 *
      heatEulerGram (E.eulerPolynomial t x) (E.eulerPolynomial t x) =
        2 * t * E.eulerFirst χ x + t ^ 2 * E.eulerTail χ t x := by
  rw [eulerPolynomial, E.eulerAmplitude_zero, heatEulerGram_polynomial]
  unfold eulerFirst eulerTail
  ring

theorem HeatNormalBundleExtension.eulerFirst_continuous (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) : Continuous (E.eulerFirst χ) :=
  (((frameExponentialJacobian_continuous g o e).mul (hχ.pow 2)).mul
    E.base.U_regular.continuous).mul
      (heatEulerTrace_continuous.comp (E.eulerAmplitude_continuous 1 (by norm_num)))

theorem HeatNormalBundleExtension.eulerFirst_compact (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hc : HasCompactSupport χ) : HasCompactSupport (E.eulerFirst χ) := by
  apply hc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_tsupport χ)
  intro x hx
  by_contra hn
  have hz := image_eq_zero_of_notMem_tsupport hn
  exact hx (by simp [HeatNormalBundleExtension.eulerFirst, hz])

theorem HeatNormalBundleExtension.eulerFirst_zero_near (E : HeatNormalBundleExtension D)
    (hRic : RicciThree g) (χ : FourSpace → ℝ) : E.eulerFirst χ =ᶠ[𝓝 0] fun _ => 0 := by
  filter_upwards [E.eulerFirstAmplitude_zero_near hRic] with x hx
  have ht : heatEulerTrace (E.eulerAmplitude 1 x) = 0 := hx
  simp only [eulerFirst, ht, mul_zero]

theorem HeatNormalBundleExtension.eulerTail_continuous (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) :
    Continuous (fun z : ℝ × FourSpace => E.eulerTail χ z.1 z.2) := by
  have hJ := (frameExponentialJacobian_continuous g o e).comp
    (continuous_snd : Continuous (fun z : ℝ × FourSpace => z.2))
  have hU := E.base.U_regular.continuous.comp
    (continuous_snd : Continuous (fun z : ℝ × FourSpace => z.2))
  have hS (m : ℕ) (hm : m ≤ 3) :=
    (heatEulerTrace_continuous.comp (E.eulerAmplitude_continuous m hm)).comp
      (continuous_snd : Continuous (fun z : ℝ × FourSpace => z.2))
  have hG (m n : ℕ) (hm : m ≤ 3) (hn : n ≤ 3) :=
    (heatEulerGram_continuous.comp ((E.eulerAmplitude_continuous m hm).prodMk
      (E.eulerAmplitude_continuous n hn))).comp
        (continuous_snd : Continuous (fun z : ℝ × FourSpace => z.2))
  have htwo : Continuous (fun _ : ℝ × FourSpace => (2 : ℝ)) := continuous_const
  have h0 := ((htwo.mul hU).mul (hS 2 (by norm_num))).add (hG 1 1 (by norm_num) (by norm_num))
  have h1 := ((htwo.mul hU).mul (hS 3 (by norm_num))).add
    (htwo.mul (hG 1 2 (by norm_num) (by norm_num)))
  have h2 := (htwo.mul (hG 1 3 (by norm_num) (by norm_num))).add (hG 2 2 (by norm_num) (by norm_num))
  unfold eulerTail
  exact (hJ.mul ((hχ.comp continuous_snd).pow 2)).mul
    ((((h0.add (continuous_fst.mul h1)).add ((continuous_fst.pow 2).mul h2)).add
      ((continuous_fst.pow 3).mul (htwo.mul (hG 2 3 (by norm_num) (by norm_num))))).add
        ((continuous_fst.pow 4).mul (hG 3 3 (by norm_num) (by norm_num))))

theorem HeatNormalBundleExtension.eulerTail_bound (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    ∃ B ≥ (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖E.eulerTail χ t x‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hc).exists_bound_of_continuousOn
    (E.eulerTail_continuous χ hχ).continuousOn
  refine ⟨max B 0, le_max_right _ _, fun t ht x => ?_⟩
  by_cases hx : x ∈ tsupport χ
  · exact (hB (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)
  · have hz := image_eq_zero_of_notMem_tsupport hx
    simp only [HeatNormalBundleExtension.eulerTail, hz, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, zero_mul, norm_zero]
    exact le_max_right _ _

theorem HeatNormalBundleExtension.eulerTail_zero (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) : E.eulerTail χ 0 0 = E.eulerSecondWeight χ 0 := by
  simp only [eulerTail, eulerSecondWeight, zero_mul, zero_pow (by norm_num : 2 ≠ 0),
    zero_pow (by norm_num : 3 ≠ 0), zero_pow (by norm_num : 4 ≠ 0), add_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A residual bounded by B t has an actual continuous zero extension. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped _root_.Topology

noncomputable section

variable {V : Type*} [NormedAddCommGroup V]

def heatResidualAtZero (R : ℝ → V) : ℝ → V := Function.update R 0 0

theorem heatResidual_tendsto_zero (R : ℝ → V) (B T : ℝ) (hT : 0 < T)
    (hR : ∀ t ∈ Ioc 0 T, ‖R t‖ ≤ B * t) :
    Tendsto R (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ => B * t) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => B * t) := continuous_const.mul continuous_id
    simpa only [mul_zero] using
      hc.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  apply squeeze_zero_norm' _ hlim
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < T :=
    (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht htT
  exact hR t ⟨ht, htT.le⟩

theorem heatResidualAtZero_continuous (R : ℝ → V) (B T : ℝ) (hT : 0 < T)
    (hc : ContinuousOn R (Ioi 0)) (hR : ∀ t ∈ Ioc 0 T, ‖R t‖ ≤ B * t) :
    ContinuousOn (heatResidualAtZero R) (Icc 0 T) := by
  rw [heatResidualAtZero, continuousOn_update_iff, Icc_sdiff_left]
  exact ⟨hc.mono Ioc_subset_Ioi_self, fun _ =>
    (heatResidual_tendsto_zero R B T hT hR).mono_left
      (nhdsWithin_mono _ Ioc_subset_Ioi_self)⟩

theorem heatResidualAtZero_norm (R : ℝ → V) (B T : ℝ)
    (hR : ∀ t ∈ Ioc 0 T, ‖R t‖ ≤ B * t) (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖heatResidualAtZero R t‖ ≤ B * t := by
  rcases ht.1.eq_or_lt with h | h
  · subst t
    simp [heatResidualAtZero]
  · simpa only [heatResidualAtZero, Function.update_of_ne h.ne'] using hR t ⟨h, ht.2⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive-time continuity of the actual scalar cutoff and its residual
in the global scalar L2 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

theorem heatNormalScalarLift_joint_continuous {X : Type*} [TopologicalSpace X] [T2Space X]
    (C : OpenPartialHomeomorph FourSpace X) (A : ℝ → FourSpace → ℝ)
    (hA : ContinuousOn (fun z : ℝ × FourSpace => A z.1 z.2) (Ioi 0 ×ˢ C.source))
    (K : Set FourSpace) (hK : IsCompact K) (hKC : K ⊆ C.source)
    (hs : ∀ t > 0, tsupport (A t) ⊆ K) :
    ContinuousOn (fun z : ℝ × X => heatNormalScalarLift C (A z.1) z.2) (Ioi 0 ×ˢ univ) := by
  have hCK := hK.image_of_continuousOn (C.continuousOn.mono hKC)
  intro z hz
  apply ContinuousAt.continuousWithinAt
  by_cases hx : z.2 ∈ C.target
  · have hi : ContinuousAt (fun w : ℝ × X => C.symm w.2) z :=
      (C.continuousOn_symm.continuousAt (C.open_target.mem_nhds hx)).comp continuousAt_snd
    have hv : ContinuousAt (fun w : ℝ × X => A w.1 (C.symm w.2)) z :=
      (hA.continuousAt ((isOpen_Ioi.prod C.open_source).mem_nhds
        ⟨hz.1, C.map_target hx⟩)).comp (continuousAt_fst.prodMk hi)
    apply hv.congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.eventually (C.open_target.mem_nhds hx)] with w hw
    exact heatNormalScalarLift_on_target C _ hw
  · have hn : z.2 ∉ C '' K := by
      rintro ⟨x, hxK, hxe⟩
      exact hx (hxe ▸ C.map_source (hKC hxK))
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.eventually (hCK.isClosed.isOpen_compl.mem_nhds hn),
      continuousAt_fst.eventually (Ioi_mem_nhds hz.1)] with w hw hwt
    apply not_ne_iff.mp
    intro hne
    obtain ⟨x, hxA, hxe⟩ := heatNormalScalarLift_support C (A w.1) hne
    exact hw ⟨x, hs w.1 hwt hxA, hxe⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatScalarChartData.cutoff_joint_regular (P : HeatScalarChartData D)
    (z : ℝ × FourSpace) (hz : 0 < z.1) :
    ContDiffAt ℝ 2 (fun w : ℝ × FourSpace =>
      P.extension.scalarCutoff P.cutoff w.1 w.2) z := by
  exact ((P.cutoff_regular.of_le (by norm_num)).comp contDiff_snd).contDiffAt.mul
    ((fourHeatGaussian_joint_contDiffAt z hz).mul
      (fourHeatPolynomial_joint_contDiff _ (fun m =>
        (P.extension.scalarAmplitude_regular m (by omega)).of_le (by norm_num))).contDiffAt)

theorem HeatScalarChartData.residualAmplitude_joint_continuous (P : HeatScalarChartData D) :
    ContinuousOn (fun z : ℝ × FourSpace => P.residualAmplitude z.1 z.2) (Ioi 0 ×ˢ univ) := by
  have ht : ContinuousOn (fun z : ℝ × FourSpace => P.timeAmplitude z.1 z.2)
      (Ioi 0 ×ˢ univ) :=
    (P.cutoff_regular.continuous.comp continuous_snd).continuousOn.mul
      (fourHeatGaussianPolynomialTime_continuousOn _
        (fun m => (P.extension.scalarAmplitude_regular m (by omega)).continuous))
  apply ht.add
  intro z hz
  have h := fourHeatBundleOperator_joint_continuousAt P.extension.a P.extension.b
    (fun _ => 0) (fun _ => 0)
    (fun w _ => P.extension.scalarCutoff P.cutoff w.1 w.2) z
    (fun i j => (P.extension.a_regular i j).continuous.continuousAt)
    (fun i => (P.extension.b_regular i).continuous.continuousAt)
    (fun _ _ _ => continuousAt_const) (fun _ _ => continuousAt_const)
    (fun _ => P.cutoff_joint_regular z hz.1) 0
  have hB (i : Fin 4) (q : Fin 6) : (0 : Fin 4 → HeatMat6) i 0 q = 0 := rfl
  have hC (q : Fin 6) : (0 : HeatMat6) 0 q = 0 := rfl
  simpa only [fourHeatBundleOperator, fourHeatBundleFirst, fourHeatBundleZero,
    hB, hC, zero_mul, Finset.sum_const_zero, add_zero] using h.continuousWithinAt

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance scalarContinuity_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem HeatScalarChartData.residual_continuous (P : HeatScalarChartData D)
    (ha : ∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hb : ∀ x ∈ tsupport P.cutoff, P.extension.b x = heatNormalDrift g o e x)
    (hd : ∀ x ∈ tsupport P.cutoff, 0 < (heatNormalMetric g o e x).det) :
    ContinuousOn P.residual (Ioi 0) := by
  have hF : ContinuousOn (fun z : ℝ × M => P.residualFunction z.1 z.2) (Ioi 0 ×ˢ univ) :=
    heatNormalScalarLift_joint_continuous P.chart P.residualAmplitude
      (P.residualAmplitude_joint_continuous.mono (prod_mono Subset.rfl (subset_univ _)))
      (tsupport P.cutoff) P.cutoff_compact P.cutoff_support
      (fun t _ => P.residualAmplitude_support t)
  have hC : ContinuousOn (fun t =>
      (⟨P.residualFunction t, P.residualFunction_continuous t⟩ : C(M, ℝ))) (Ioi 0) :=
    ContinuousMap.continuousOn_of_continuousOn_uncurry _ hF
  exact ((ContinuousMap.toLp 2 (normalizedVolume g) ℝ).continuous.comp_continuousOn hC).congr
    (fun t _ => P.residual_realization ha hb hd t)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A common density-weighted polynomial bound for the actual nearby
normal-frame columns. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatFamilyOnePolynomialColumn (E : HeatFamilyOneCoefficients) (χ : FourSpace → ℝ)
    (t : ℝ) (l : Fin 4) (z : HeatRadialFrameSpace) : FourSpace :=
  WithLp.toLp 2 (fun k => χ z.1 *
    fourHeatPolynomial (fun m x => E.amplitude m (x, z.2) k l) t z.1)

theorem heatFamilyOnePolynomialColumn_continuous (E : HeatFamilyOneCoefficients)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (l : Fin 4) :
    Continuous (fun z : ℝ × HeatRadialFrameSpace => heatFamilyOnePolynomialColumn E χ z.1 l z.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro k
  exact (hχ.comp (continuous_fst.comp continuous_snd)).mul
    (heatFamilyPolynomial_continuous _ (fun m => (E.amplitude_regular m (by omega) k l).continuous))

theorem heatFamilyOnePolynomial_weight_bound (E : HeatFamilyOneCoefficients)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ B ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x l,
      (E.base.U (x, q) ^ 2)⁻¹ * ‖heatFamilyOnePolynomialColumn E χ t l (x, q)‖ ^ 2 ≤ B := by
  have hb (l : Fin 4) : ∃ B ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      (E.base.U (x, q) ^ 2)⁻¹ * ‖heatFamilyOnePolynomialColumn E χ t l (x, q)‖ ^ 2 ≤ B := by
    let W := fun z : ℝ × HeatRadialFrameSpace => (E.base.U z.2 ^ 2)⁻¹ *
      ‖heatFamilyOnePolynomialColumn E χ z.1 l z.2‖ ^ 2
    have hW : Continuous W :=
      (((E.base.U_regular.continuous.comp continuous_snd).pow 2).inv₀
        (fun z => pow_ne_zero 2 (E.base.U_pos z.2).ne')).mul
        ((heatFamilyOnePolynomialColumn_continuous E χ hχ l).norm.pow 2)
    obtain ⟨B, hB⟩ := (isCompact_Icc.prod (hc.prod hK)).bddAbove_image hW.continuousOn
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    intro q hq t ht x
    by_cases hx : x ∈ tsupport χ
    · exact (hB ⟨(t, (x, q)), ⟨ht, hx, hq⟩, rfl⟩).trans (le_max_left _ _)
    · have hz : heatFamilyOnePolynomialColumn E χ t l (x, q) = 0 := by
        apply WithLp.ofLp_injective 2
        funext k
        change χ x * _ = 0
        rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
      rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
      exact le_max_right _ _
  choose B hB hb using hb
  refine ⟨∑ l, B l, Finset.sum_nonneg (fun l _ => hB l), ?_⟩
  intro q hq t ht x l
  exact (hb l q hq t ht x).trans (Finset.single_le_sum (fun a _ => hB a) (Finset.mem_univ l))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonEulerMember.onePolynomialColumn_family (N : HeatCommonEulerMember g o c E r e)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 4) (x : FourSpace) :
    heatNormalOnePolynomialColumn N.one χ t l x =
      heatFamilyOnePolynomialColumn E χ t l (x, frameCoordinateState g c e) := by
  apply WithLp.ofLp_injective 2
  funext k
  change χ x * fourHeatPolynomial _ t x = χ x * fourHeatPolynomial _ t x
  have hu : (fun (m : Fin 4) y => N.one.amplitude m y k l) =
      (fun (m : Fin 4) y => E.amplitude m (y, frameCoordinateState g c e) k l) := by
    funext m y
    exact congrArg (fun f : FourSpace → Mat4 => f y k l) (N.one_amplitude_family m (by omega))
  rw [hu]


theorem heatUniformOnePolynomial_weight_bound (E : HeatFamilyOneCoefficients) (r : ℝ)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ ball 0 r) (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ B ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c E r e),
      frameCoordinateState g c e ∈ K → ∀ t ∈ Icc (0 : ℝ) 1, ∀ x l,
      frameExponentialJacobian g o e x * ‖heatNormalOnePolynomialColumn N.one χ t l x‖ ^ 2 ≤ B := by
  obtain ⟨B, hB, hb⟩ := heatFamilyOnePolynomial_weight_bound E χ hχ hc K hK
  refine ⟨B, hB, ?_⟩
  intro e N hq t ht x l
  by_cases hx : x ∈ tsupport χ
  · have hh := heatNormalLeadingAmplitude_normalization g o e x
      (Real.sqrt_pos.mpr (N.normal.metric_pos x (hχs hx)))
    rw [← (N.normal.actual x (hχs hx)).2.2.2.2, N.normal.U_family] at hh
    rw [eq_inv_of_mul_eq_one_right hh, N.onePolynomialColumn_family]
    exact hb _ hq t ht x l
  · have hz : heatNormalOnePolynomialColumn N.one χ t l x = 0 := by
      apply WithLp.ofLp_injective 2
      funext k
      change χ x * _ = 0
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
    rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    exact hB

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact one-form transport and residual on the entire common normal ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonEulerMember.one_transport (N : HeatCommonEulerMember g o c F r e)
    (hRic : RicciThree g) (he : e ∈ o.positive) (x : FourSpace) (hx : x ∈ ball 0 r) :
    (∀ i, ∑ j : Fin 4, N.one.base.a x i j * x j = x i) ∧
    (∀ j, ∑ i : Fin 4, N.one.base.a x i j * x i = x j) ∧
    fourHeatEikonalDefect (N.one.base.a x) x = 0 ∧
    fourHeatRadialTransport (N.one.base.a x) (N.one.base.b x) N.one.base.U x = 0 ∧
    (∀ k l, (∑ i : Fin 4, x i * N.one.B x i k l) = 0) := by
  rw [N.one_base]
  obtain ⟨hrow, hcol, heik, hU, _⟩ := N.normal.transport hRic he x hx
  refine ⟨hrow, hcol, heik, hU, ?_⟩
  intro k l
  rw [(N.one_actual x hx).1]
  have h := N.normal.frameData.oneFirst_radial hRic he x
    (ball_subset_ball N.normal.radius_le hx) (N.normal.metric_pos x hx).ne'
  simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    using congrArg (fun B : Mat4 => B k l) h

theorem HeatCommonEulerMember.one_amplitude_transport (N : HeatCommonEulerMember g o c F r e)
    (hRic : RicciThree g) (he : e ∈ o.positive) (x : FourSpace) (hx : x ∈ ball 0 r)
    (m : ℕ) (hm : m ≤ 2) (k l : Fin 4) :
    fourHeatRadialTransport (N.one.base.a x) (N.one.base.b x)
      (fun y => N.one.amplitude (m + 1) y k l) x +
      (m + 1 : ℝ) * N.one.amplitude (m + 1) x k l =
    -fourHeatOneOperator (N.one.base.a x) (N.one.base.b x)
      (N.one.B x) (N.one.C x) (fun y q => N.one.amplitude m y q l) x k := by
  obtain ⟨hrow, hcol, _, hU, _⟩ := N.one_transport hRic he x hx
  exact fourHeatOneCoefficient_transport m _ _ _ _ _ x
    (N.one.base.U_regular.of_le (by norm_num)) (fun y => (N.one.base.U_pos y).ne')
    (fun i j => (N.one.base.a_regular i j).of_le (by norm_num))
    (fun i => (N.one.base.b_regular i).of_le (by norm_num))
    (fun i k l => (N.one.B_regular i k l).of_le (by norm_num))
    (fun k l => (N.one.C_regular k l).of_le (by norm_num))
    (fun k l => (N.one.amplitude_regular m (by omega) k l).of_le (by norm_num))
    hrow hcol hU k l

theorem HeatCommonEulerMember.one_parametrix_residual (N : HeatCommonEulerMember g o c F r e)
    (hRic : RicciThree g) (he : e ∈ o.positive) (x : FourSpace) (hx : x ∈ ball 0 r)
    (t : ℝ) (ht : 0 < t) (k l : Fin 4) :
    deriv (fun s => heatNormalOneParametrix N.one s x k l) t +
      fourHeatOneOperator (N.one.base.a x) (N.one.base.b x)
        (N.one.B x) (N.one.C x)
        (fun y q => heatNormalOneParametrix N.one t y q l) x k =
    fourHeatGaussian t x * t ^ 3 * F.lastCoefficient (x, frameCoordinateState g c e) k l := by
  obtain ⟨_, _, hEik, hU, hrad⟩ := N.one_transport hRic he x hx
  have hreg (m : Fin 4) (q : Fin 4) : ContDiff ℝ 2 (fun y => N.one.amplitude m y q l) :=
    (N.one.amplitude_regular m (by omega) q l).of_le (by norm_num)
  have hzero (q : Fin 4) : fourHeatRadialTransport (N.one.base.a x) (N.one.base.b x)
      (fun y => N.one.amplitude 0 y q l) x = 0 := by
    by_cases hql : q = l
    · subst q
      simpa [HeatNormalOneExtension.amplitude, fourHeatOneCoefficient] using hU
    · have hz : (fun y => N.one.amplitude 0 y q l) = fun _ => (0 : ℝ) := by
        funext y
        simp [HeatNormalOneExtension.amplitude, fourHeatOneCoefficient, hql]
      rw [hz]
      simpa only [zero_mul] using
        fourHeatRadialTransport_const_mul (N.one.base.a x) (N.one.base.b x) 0 N.one.base.U x
  have hh := fourHeatOnePolynomial_gaussian_residual (N.one.base.a x) (N.one.base.b x)
    (N.one.B x) (N.one.C x) (fun m y q => N.one.amplitude m y q l) hreg t ht x hrad hEik hzero
    (by intro q; simpa using N.one_amplitude_transport hRic he x hx 0 (by omega) q l)
    (by intro q; convert N.one_amplitude_transport hRic he x hx 1 (by omega) q l using 1 <;> norm_num)
    (by intro q; convert N.one_amplitude_transport hRic he x hx 2 (by omega) q l using 1 <;> norm_num) k
  refine hh.trans ?_
  congr 1
  change fourHeatOneOperator (N.one.base.a x) (N.one.base.b x)
    (N.one.B x) (N.one.C x) (fun y q => N.one.amplitude 3 y q l) x k = _
  rw [show N.one.amplitude 3 = fun y => F.amplitude 3 (y, frameCoordinateState g c e)
    from N.one_amplitude_family 3 (by omega)]
  rw [N.one_base, N.normal.a_family, N.normal.b_family, N.one_B_family, N.one_C_family]
  exact (heatFamilyOneOperator_slice F.base.a F.base.b F.B F.C _
    (fun q => (F.amplitude_regular 3 (by omega) q l).of_le (by norm_num)) _ k).symm


end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual local Euler polynomial has the Euler curvature density
as its squared-Gaussian limit. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.euler_gaussian_limit
    (E : HeatNormalBundleExtension D) (χ : FourSpace → ℝ) (hχ : Continuous χ)
    (hc : HasCompactSupport χ) (hχ0 : χ 0 = 1) (hRic : RicciThree g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    Tendsto (fun t : ℝ => ∫ x : FourSpace, fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x * χ x ^ 2 *
        heatEulerGram (E.eulerPolynomial t x) (E.eulerPolynomial t x)))
      (𝓝[>] 0) (𝓝 (curvatureEulerDensity (twoFormMetricCurvatureTensor g e))) := by
  have hz := E.eulerFirst_zero_near hRic χ
  have hreg : ContDiffAt ℝ 2 (E.eulerFirst χ) 0 :=
    (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hz
  have hd : fderiv ℝ (E.eulerFirst χ) 0 = 0 := by
    rw [hz.fderiv_eq]
    exact fderiv_const_apply _
  have hdn : fderiv ℝ (E.eulerFirst χ) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hz.eventuallyEq_nhds] with x hx
    rw [hx.fderiv_eq]
    exact fderiv_const_apply _
  have hdd : fderiv ℝ (fderiv ℝ (E.eulerFirst χ)) 0 = 0 := by
    rw [hdn.fderiv_eq]
    exact fderiv_const_apply _
  obtain ⟨C, hC⟩ := (E.eulerFirst_compact χ hc).exists_bound_of_continuous
    (E.eulerFirst_continuous χ hχ)
  obtain ⟨B, _, hB⟩ := E.eulerTail_bound χ hχ hc
  have h := fourHeat_signed_gaussian_limit (E.eulerFirst χ)
    (E.eulerFirst_continuous χ hχ) hreg hz.self_of_nhds hd C hC
    (E.eulerTail χ) (E.eulerTail_continuous χ hχ) B 1 zero_lt_one hB
  have hcenter : (1 / (64 * Real.pi ^ 2)) * E.eulerTail χ 0 0 =
      curvatureEulerDensity (twoFormMetricCurvatureTensor g e) := by
    rw [E.eulerTail_zero]
    convert E.eulerSecondWeight_center hRic he χ hχ0 using 1
    ring
  simp only [hdd, _root_.zero_apply, Finset.sum_const_zero, zero_add, hcenter] at h
  simpa only [E.eulerPolynomial_gram] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform bounds for the remaining coefficients of the common Euler polynomial. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section

def HeatFamilyOneCoefficients.eulerPolynomial (F : HeatFamilyOneCoefficients)
    (t : ℝ) (z : HeatRadialFrameSpace) : HeatEulerFiber :=
  F.base.U z • heatEulerUnit + t • F.eulerAmplitude 1 z +
    t ^ 2 • F.eulerAmplitude 2 z + t ^ 3 • F.eulerAmplitude 3 z

def heatFamilyEulerTail (F : HeatFamilyOneCoefficients) (χ : FourSpace → ℝ)
    (t : ℝ) (z : HeatRadialFrameSpace) : ℝ :=
  (F.base.U z ^ 2)⁻¹ * χ z.1 ^ 2 *
    (2 * F.base.U z * heatEulerTrace (F.eulerAmplitude 2 z) +
      heatEulerGram (F.eulerAmplitude 1 z) (F.eulerAmplitude 1 z) +
      t * (2 * F.base.U z * heatEulerTrace (F.eulerAmplitude 3 z) +
        2 * heatEulerGram (F.eulerAmplitude 1 z) (F.eulerAmplitude 2 z)) +
      t ^ 2 * (2 * heatEulerGram (F.eulerAmplitude 1 z) (F.eulerAmplitude 3 z) +
        heatEulerGram (F.eulerAmplitude 2 z) (F.eulerAmplitude 2 z)) +
      t ^ 3 * (2 * heatEulerGram (F.eulerAmplitude 2 z) (F.eulerAmplitude 3 z)) +
      t ^ 4 * heatEulerGram (F.eulerAmplitude 3 z) (F.eulerAmplitude 3 z))

theorem HeatFamilyOneCoefficients.eulerAmplitude_continuous (F : HeatFamilyOneCoefficients)
    (m : ℕ) (hm : m ≤ 3) : Continuous (F.eulerAmplitude m) :=
  (F.base.scalarAmplitude_regular m hm).continuous.prodMk
    ((continuous_pi (fun k => continuous_pi (fun l =>
      (F.amplitude_regular m hm k l).continuous))).prodMk
      (continuous_pi (fun k => continuous_pi (fun l =>
        (F.base.amplitude_regular m hm k l).continuous))))

theorem heatFamilyEulerTail_continuous (F : HeatFamilyOneCoefficients)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) :
    Continuous (fun z : ℝ × HeatRadialFrameSpace => heatFamilyEulerTail F χ z.1 z.2) := by
  have hU := F.base.U_regular.continuous.comp
    (continuous_snd : Continuous (fun z : ℝ × HeatRadialFrameSpace => z.2))
  have hS (m : ℕ) (hm : m ≤ 3) :=
    (heatEulerTrace_continuous.comp (F.eulerAmplitude_continuous m hm)).comp
      (continuous_snd : Continuous (fun z : ℝ × HeatRadialFrameSpace => z.2))
  have hG (m n : ℕ) (hm : m ≤ 3) (hn : n ≤ 3) :=
    (heatEulerGram_continuous.comp ((F.eulerAmplitude_continuous m hm).prodMk
      (F.eulerAmplitude_continuous n hn))).comp
        (continuous_snd : Continuous (fun z : ℝ × HeatRadialFrameSpace => z.2))
  have hJ := (hU.pow 2).inv₀ (fun z => pow_ne_zero 2 (F.base.U_pos z.2).ne')
  have htwo : Continuous (fun _ : ℝ × HeatRadialFrameSpace => (2 : ℝ)) := continuous_const
  have h0 := ((htwo.mul hU).mul (hS 2 (by omega))).add (hG 1 1 (by omega) (by omega))
  have h1 := ((htwo.mul hU).mul (hS 3 (by omega))).add (htwo.mul (hG 1 2 (by omega) (by omega)))
  have h2 := (htwo.mul (hG 1 3 (by omega) (by omega))).add (hG 2 2 (by omega) (by omega))
  exact (hJ.mul ((hχ.comp (continuous_fst.comp continuous_snd)).pow 2)).mul
    ((((h0.add (continuous_fst.mul h1)).add ((continuous_fst.pow 2).mul h2)).add
      ((continuous_fst.pow 3).mul (htwo.mul (hG 2 3 (by omega) (by omega))))).add
        ((continuous_fst.pow 4).mul (hG 3 3 (by omega) (by omega))))

theorem heatFamilyEulerTail_bound (F : HeatFamilyOneCoefficients)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ B ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      ‖heatFamilyEulerTail F χ t (x, q)‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod (hc.prod hK)).bddAbove_image
    (heatFamilyEulerTail_continuous F χ hχ).norm.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro q hq t ht x
  by_cases hx : x ∈ tsupport χ
  · exact (hB ⟨(t, (x, q)), ⟨ht, hx, hq⟩, rfl⟩).trans (le_max_left _ _)
  · simp only [heatFamilyEulerTail, image_eq_zero_of_notMem_tsupport hx,
      zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, norm_zero]
    exact le_max_right _ _

theorem heatFamilyEulerPolynomial_gram (F : HeatFamilyOneCoefficients)
    (χ : FourSpace → ℝ) (t : ℝ) (z : HeatRadialFrameSpace) :
    (F.base.U z ^ 2)⁻¹ * χ z.1 ^ 2 *
      heatEulerGram (F.eulerPolynomial t z) (F.eulerPolynomial t z) =
        2 * t * heatFamilyEulerFirst F χ z + t ^ 2 * heatFamilyEulerTail F χ t z := by
  rw [HeatFamilyOneCoefficients.eulerPolynomial, heatEulerGram_polynomial]
  unfold heatFamilyEulerFirst heatFamilyEulerTail
  field_simp [(F.base.U_pos z).ne']

end
end PositiveEinsteinFour.Geometry
end


section

/-! The squared-norm error needed to pass the L2 column comparison
to the actual diagonal heat trace. -/

namespace PositiveEinsteinFour.Geometry

open Set Filter
open scoped _root_.Topology

noncomputable section

variable {V : Type*} [NormedAddCommGroup V]

theorem heat_norm_square_error_bound (x y : V) (a b : ℝ)
    (ha : ‖x‖ ≤ a) (hb : ‖x - y‖ ≤ b) :
    |‖x‖ ^ 2 - ‖y‖ ^ 2| ≤ (2 * a + b) * b := by
  have hb0 : 0 ≤ b := (norm_nonneg _).trans hb
  have hy : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
    have h := norm_sub_norm_le y x
    rw [norm_sub_rev] at h
    linarith
  have hsum : ‖x‖ + ‖y‖ ≤ 2 * a + b := by linarith
  calc
    _ = |‖x‖ - ‖y‖| * (‖x‖ + ‖y‖) := by
      rw [← abs_of_nonneg (add_nonneg (norm_nonneg x) (norm_nonneg y)), ← abs_mul]
      congr 1
      ring
    _ ≤ b * (2 * a + b) := mul_le_mul ((abs_norm_sub_norm_le x y).trans hb) hsum
      (add_nonneg (norm_nonneg x) (norm_nonneg y)) hb0
    _ = _ := by ring

theorem heat_norm_square_error_tendsto (x y : ℝ → V) (C D T : ℝ) (hT : 0 < T)
    (hx : ∀ t ∈ Ioc 0 T, ‖x t‖ ≤ C / t)
    (hy : ∀ t ∈ Ioc 0 T, ‖x t - y t‖ ≤ D * t ^ 2) :
    Tendsto (fun t => ‖x t‖ ^ 2 - ‖y t‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ => 2 * C * D * t + D ^ 2 * t ^ 4)
      (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => 2 * C * D * t + D ^ 2 * t ^ 4) := by fun_prop
    simpa only [mul_zero, zero_pow (by norm_num : 4 ≠ 0), add_zero] using
      hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  apply squeeze_zero_norm' _ hlim
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < T :=
    (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht htT
  rw [Real.norm_eq_abs]
  calc
    _ ≤ (2 * (C / t) + D * t ^ 2) * (D * t ^ 2) :=
      heat_norm_square_error_bound (x t) (y t) _ _ (hx t ⟨ht, htT.le⟩) (hy t ⟨ht, htT.le⟩)
    _ = _ := by field_simp [(show 0 < t from ht).ne']

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normalized residual has a continuous zero-time extension. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatNormalParametrixData.oneNormalizedResidualZero (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (t : ℝ) (l : Fin 4) : OneFormL2 o :=
  heatResidualAtZero (fun s => P.oneNormalizedResidual E s l) t

theorem HeatNormalParametrixData.oneNormalizedResidual_bound (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (B : ℝ)
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.oneResidual E t l‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 4) :
    ‖P.oneNormalizedResidual E t l‖ ≤ (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) * t := by
  change ‖((normalizedChartFactor g).toReal)⁻¹ • P.oneResidual E t l‖ ≤ _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (hB t ht l) (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm

theorem HeatNormalParametrixData.oneNormalizedResidualZero_continuous
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D) (B : ℝ)
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.oneResidual E t l‖ ≤ B * t) (l : Fin 4) :
    ContinuousOn (fun t => P.oneNormalizedResidualZero E t l) (Icc 0 1) :=
  heatResidualAtZero_continuous _ (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) 1
    zero_lt_one (P.oneNormalizedResidual_continuous E l)
    (fun t ht => P.oneNormalizedResidual_bound E B hB t ht l)

theorem HeatNormalParametrixData.oneNormalizedResidualZero_eq
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D)
    (t : ℝ) (ht : 0 < t) (l : Fin 4) :
    P.oneNormalizedResidualZero E t l = P.oneNormalizedResidual E t l := by
  unfold oneNormalizedResidualZero heatResidualAtZero
  exact Function.update_of_ne ht.ne' _ _

theorem HeatNormalParametrixData.oneNormalizedResidualZero_bound
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D) (B : ℝ)
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.oneResidual E t l‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (l : Fin 4) :
    ‖P.oneNormalizedResidualZero E t l‖ ≤ (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) * t :=
  heatResidualAtZero_norm _ _ 1 (fun s hs => P.oneNormalizedResidual_bound E B hB s hs l) t ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normalized residual has a continuous zero-time extension. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatNormalParametrixData.normalizedResidualZero (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (t : ℝ) (l : Fin 6) : TwoFormL2 o :=
  heatResidualAtZero (fun s => P.normalizedResidual E s l) t

theorem HeatNormalParametrixData.normalizedResidual_bound (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (B : ℝ)
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 6) :
    ‖P.normalizedResidual E t l‖ ≤ (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) * t := by
  change ‖((normalizedChartFactor g).toReal)⁻¹ • P.residual E t l‖ ≤ _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (hB t ht l) (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm

theorem HeatNormalParametrixData.normalizedResidualZero_continuous
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (B : ℝ)
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t) (l : Fin 6) :
    ContinuousOn (fun t => P.normalizedResidualZero E t l) (Icc 0 1) :=
  heatResidualAtZero_continuous _ (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) 1
    zero_lt_one (P.normalizedResidual_continuous E l)
    (fun t ht => P.normalizedResidual_bound E B hB t ht l)

theorem HeatNormalParametrixData.normalizedResidualZero_eq
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D)
    (t : ℝ) (ht : 0 < t) (l : Fin 6) :
    P.normalizedResidualZero E t l = P.normalizedResidual E t l := by
  unfold normalizedResidualZero heatResidualAtZero
  exact Function.update_of_ne ht.ne' _ _

theorem HeatNormalParametrixData.normalizedResidualZero_bound
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (B : ℝ)
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (l : Fin 6) :
    ‖P.normalizedResidualZero E t l‖ ≤ (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) * t :=
  heatResidualAtZero_norm _ _ 1 (fun s hs => P.normalizedResidual_bound E B hB s hs l) t ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar forcing has an O(t) L2 bound and a continuous
zero extension. All local coefficient conditions are realized geometrically. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

local instance scalarGlobalResidual_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem HeatScalarChartData.residual_norm_le (P : HeatScalarChartData D)
    (ha : ∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hb : ∀ x ∈ tsupport P.cutoff, P.extension.b x = heatNormalDrift g o e x)
    (hd : ∀ x ∈ tsupport P.cutoff, 0 < (heatNormalMetric g o e x).det)
    (t B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x, |P.residualAmplitude t x| ≤ B) :
    ‖P.residual t‖ ≤ ‖ContinuousMap.toLp (E := ℝ) 2 (normalizedVolume g) ℝ‖ * B := by
  rw [P.residual_realization ha hb hd t]
  apply (ContinuousMap.toLp (E := ℝ) 2 (normalizedVolume g) ℝ).le_opNorm_of_le
  apply (ContinuousMap.norm_le _ hB).mpr
  intro y
  change |heatNormalScalarLift P.chart (P.residualAmplitude t) y| ≤ B
  by_cases hy : y ∈ P.chart.target
  · rw [heatNormalScalarLift_on_target P.chart _ hy]
    exact hbound _
  · simpa only [heatNormalScalarLift, ite_eq_right hy, abs_zero] using hB

theorem exists_heatScalarGlobalResidual (D : HeatNormalFrameData g o c e)
    (he : e.base ∈ (chartAt FourSpace c).source) (hRic : RicciThree g) (hepos : e ∈ o.positive) :
    ∃ P : HeatScalarChartData D,
      (∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹) ∧
      (∀ x ∈ tsupport P.cutoff, P.extension.b x = heatNormalDrift g o e x) ∧
      (∀ x ∈ tsupport P.cutoff, 0 < (heatNormalMetric g o e x).det) ∧
      ∃ B ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.residual t‖ ≤ B * t := by
  obtain ⟨P, ha, hb, hd, hχ, ⟨r, hr, hinner⟩, hres⟩ :=
    exists_heatScalarAdaptedChart D he hRic hepos
  obtain ⟨B, hB, hbound⟩ := P.residualAmplitude_bound ha hχ r hr hinner hres
  refine ⟨P, ha, hb, hd, ‖ContinuousMap.toLp (E := ℝ) 2 (normalizedVolume g) ℝ‖ * B,
    mul_nonneg (norm_nonneg _) hB, ?_⟩
  intro t ht
  exact (P.residual_norm_le ha hb hd t (B * t) (mul_nonneg hB ht.1.le)
    (hbound t ht)).trans_eq (mul_assoc _ _ _).symm

def HeatScalarChartData.normalizedResidualZero (P : HeatScalarChartData D) :
    ℝ → Lp ℝ 2 (normalizedVolume g) := heatResidualAtZero P.normalizedResidual

theorem HeatScalarChartData.normalizedResidual_bound (P : HeatScalarChartData D)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.residual t‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    ‖P.normalizedResidual t‖ ≤ (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) * t := by
  change ‖((normalizedChartFactor g).toReal)⁻¹ • P.residual t‖ ≤ _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (hB t ht) (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm

theorem HeatScalarChartData.normalizedResidualZero_continuous (P : HeatScalarChartData D)
    (ha : ∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hb : ∀ x ∈ tsupport P.cutoff, P.extension.b x = heatNormalDrift g o e x)
    (hd : ∀ x ∈ tsupport P.cutoff, 0 < (heatNormalMetric g o e x).det)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.residual t‖ ≤ B * t) :
    ContinuousOn P.normalizedResidualZero (Icc 0 1) :=
  heatResidualAtZero_continuous _ (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) 1
    zero_lt_one ((P.residual_continuous ha hb hd).const_smul ((normalizedChartFactor g).toReal)⁻¹)
    (fun t ht => P.normalizedResidual_bound B hB t ht)

theorem HeatScalarChartData.normalizedResidualZero_eq (P : HeatScalarChartData D)
    (t : ℝ) (ht : 0 < t) : P.normalizedResidualZero t = P.normalizedResidual t := by
  unfold normalizedResidualZero heatResidualAtZero
  exact Function.update_of_ne ht.ne' _ _

theorem HeatScalarChartData.normalizedResidualZero_bound (P : HeatScalarChartData D)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.residual t‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖P.normalizedResidualZero t‖ ≤ (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) * t :=
  heatResidualAtZero_norm _ _ 1 (fun s hs => P.normalizedResidual_bound B hB s hs) t ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual compact normal columns have a common L2 growth constant
for every initial frame in a compact coordinate set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem heatUniformOneColumn_growth (E : HeatFamilyOneCoefficients) (r : ℝ) (hr : 0 < r)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c E r e),
      frameCoordinateState g c e ∈ K → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l,
      ‖(N.normal.parametrixData hr).oneNormalizedColumn N.one t l‖ ≤ C / t := by
  let χ : FourSpace → ℝ := heatNormalChartBump r hr
  have hχs : tsupport χ ⊆ ball (0 : FourSpace) r := by
    rw [(heatNormalChartBump r hr).tsupport_eq]
    exact closedBall_subset_ball (by change r / 2 < r; linarith)
  obtain ⟨B, hB, hb⟩ := heatUniformOnePolynomial_weight_bound (g := g) (o := o) (c := c) E r χ
    (heatNormalChartBump r hr).continuous (heatNormalChartBump r hr).hasCompactSupport hχs K hK
  let A := B / (64 * Real.pi ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let C := (normalizedChartFactor g).toReal * A
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨‖((normalizedChartFactor g).toReal)⁻¹‖ * (C + 1), by positivity, ?_⟩
  intro e N hq t ht l
  let P := N.normal.parametrixData hr
  have hcut : P.cutoff = χ := rfl
  have hpt (x : FourSpace) : frameExponentialJacobian g o e x *
      ‖heatNormalOneCutoffColumn N.one χ t l x‖ ^ 2 ≤ B * fourHeatGaussian t x ^ 2 := by
    rw [heatNormalOneCutoffColumn_gaussian, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    calc
      _ = (frameExponentialJacobian g o e x * ‖heatNormalOnePolynomialColumn N.one χ t l x‖ ^ 2) *
          fourHeatGaussian t x ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hb e N hq t ⟨ht.1.le, ht.2⟩ x l) (sq_nonneg _)
  have hi : Integrable (fun x : FourSpace => B * fourHeatGaussian t x ^ 2) :=
    (fourHeatGaussian_square_integrable t ht.1).const_mul B
  have hm : Continuous (fun x => frameExponentialJacobian g o e x *
      ‖heatNormalOneCutoffColumn N.one χ t l x‖ ^ 2) :=
    (frameExponentialJacobian_continuous g o e).mul
      ((heatNormalOneCutoffColumn_regular N.one χ
        (heatNormalChartBump r hr).contDiff t l).continuous.norm.pow 2)
  have hfi : Integrable (fun x => frameExponentialJacobian g o e x *
      ‖heatNormalOneCutoffColumn N.one χ t l x‖ ^ 2) :=
    hi.mono' hm.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (frameExponentialJacobian_nonneg g o e x) (sq_nonneg _))]
      exact hpt x)
  have hint : (∫ x, frameExponentialJacobian g o e x *
      ‖heatNormalOneCutoffColumn N.one χ t l x‖ ^ 2) ≤ A / t ^ 2 := by
    calc
      _ ≤ ∫ x : FourSpace, B * fourHeatGaussian t x ^ 2 := integral_mono hfi hi hpt
      _ = _ := by rw [integral_const_mul, fourHeatGaussian_square_mass t ht.1]; dsimp [A]; ring
  have hn := heatNormalOneAmplitudeL2_norm_sq_integral P.chart P.exponential P.in_chart
    P.point_regular P.inside_radius (heatNormalOneCutoffColumn N.one P.cutoff t l)
    ((heatNormalOneCutoffColumn_regular N.one P.cutoff P.cutoff_regular t l).of_le (by norm_num))
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalOneCutoffColumn_support N.one P.cutoff t l))
    ((heatNormalOneCutoffColumn_support N.one P.cutoff t l).trans P.cutoff_support)
  have hn' : ‖P.oneColumn N.one t l‖ ^ 2 ≤ C / t ^ 2 := by
    have hint' : (∫ x, frameExponentialJacobian g o e x *
        ‖heatNormalOneCutoffColumn N.one P.cutoff t l x‖ ^ 2) ≤ A / t ^ 2 := by
      simpa only [hcut] using hint
    exact (le_of_eq hn).trans ((mul_le_mul_of_nonneg_left hint' (by positivity)).trans_eq (by dsimp [C]; ring))
  have hs : (‖P.oneColumn N.one t l‖ * t) ^ 2 ≤ C := by
    calc
      _ = ‖P.oneColumn N.one t l‖ ^ 2 * t ^ 2 := by ring
      _ ≤ (C / t ^ 2) * t ^ 2 := mul_le_mul_of_nonneg_right hn' (sq_nonneg t)
      _ = C := by field_simp [ht.1.ne']
  have hcol : ‖P.oneColumn N.one t l‖ ≤ (C + 1) / t := by
    apply (le_div_iff₀ ht.1).mpr
    nlinarith [sq_nonneg C, norm_nonneg (P.oneColumn N.one t l)]
  change ‖((normalizedChartFactor g).toReal)⁻¹ • P.oneColumn N.one t l‖ ≤ _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left hcol (norm_nonneg _)).trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


section

/-! One O(t) cutoff-residual constant works for every actual normal frame
in a compact coordinate neighborhood. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem heatUniformOneCutoffResidual (E : HeatFamilyOneCoefficients) (r : ℝ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ ball 0 r) (hχb : ∀ x, |χ x| ≤ 1)
    (s : ℝ) (hs : 0 < s) (hinner : ∀ x ∈ ball 0 s, χ x = 1)
    (hRic : RicciThree g) :
    ∃ B ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c E r e),
      frameCoordinateState g c e ∈ K → e ∈ o.positive →
      ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x k l,
        |deriv (fun v => heatNormalOneCutoffParametrix N.one χ v x k l) t +
          fourHeatOneOperator (N.one.base.a x) (N.one.base.b x)
            (N.one.B x) (N.one.C x)
            (fun y q => heatNormalOneCutoffParametrix N.one χ t y q l) x k| ≤ B * t := by
  obtain ⟨C₀, hC₀, hb⟩ := E.lastCoefficient_compact_bound (tsupport χ ×ˢ K) (hc.prod hK)
  obtain ⟨C₁, hC₁, hcom⟩ := heatFamilyOneCommutator_gaussian_bound E χ hχ hc K hK s hs hinner
  let B₀ := C₀ / (16 * Real.pi ^ 2)
  have hB₀ : 0 ≤ B₀ := by dsimp [B₀]; positivity
  refine ⟨B₀ + C₁, add_nonneg hB₀ hC₁, ?_⟩
  intro e N hq he t ht x k l
  let A := N.one
  let q := frameCoordinateState g c e
  let u : Fin 4 → FourSpace → Fin 4 → ℝ := fun m y a => A.amplitude m y a l
  have hu (m : Fin 4) (a : Fin 4) : ContDiff ℝ 2 (fun y => u m y a) :=
    (A.amplitude_regular m (by omega) a l).of_le (by norm_num)
  by_cases hx : x ∈ tsupport χ
  · have hxr := hχs hx
    have hsym (i j : Fin 4) : A.base.a x i j = A.base.a x j i := by
      rw [N.one_base, (N.normal.actual x hxr).1]
      exact congrFun (congrFun (heatNormalInverse_symm g o e x) j) i
    let Q := deriv (fun v => heatNormalOneParametrix A v x k l) t +
      fourHeatOneOperator (A.base.a x) (A.base.b x) (A.B x) (A.C x)
        (fun y a => heatNormalOneParametrix A t y a l) x k
    have hQ : |Q| ≤ B₀ * t := by
      have hres := N.one_parametrix_residual hRic he x hxr t ht.1 k l
      change Q = fourHeatGaussian t x * t ^ 3 * E.lastCoefficient (x, q) k l at hres
      rw [hres, abs_mul, abs_mul, abs_of_pos (fourHeatGaussian_pos t ht.1 x),
        abs_of_pos (pow_pos ht.1 3)]
      calc
        _ ≤ (fourHeatGaussian t x * t ^ 3) * C₀ :=
          mul_le_mul_of_nonneg_left (hb (x, q) ⟨hx, hq⟩ k l)
            (mul_nonneg (fourHeatGaussian_pos t ht.1 x).le (pow_nonneg ht.1.le 3))
        _ ≤ (fourHeatGaussian t 0 * t ^ 3) * C₀ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (fourHeatGaussian_le_diagonal t ht.1 x)
              (pow_nonneg ht.1.le 3)) hC₀
        _ = C₀ * (t ^ (1 + 2) * fourHeatGaussian t 0) := by ring
        _ = B₀ * t := by rw [fourHeatGaussian_diagonal_power 1 t ht.1, pow_one]; dsimp [B₀]; ring
    have hid := heatNormalOneCutoffParametrix_residual_identity A χ t ht.1 x hχ.contDiffAt
      (A.base.a x) (A.base.b x) (A.B x) (A.C x) hsym k l
    have hscaled := fourHeatOneScaledCommutator_identity A.base.a A.base.b A.B χ u hu t ht.1 x k
    have hfamily : fourHeatOneScaledCommutator A.base.a A.base.b A.B χ u t x k =
        heatFamilyOneCommutator E χ t (x, q) k l := by
      have hu' : u = fun (m : Fin 4) y a => E.amplitude m (y, q) a l := by
        funext m y a
        exact congrArg (fun f : FourSpace → Mat4 => f y a l)
          (N.one_amplitude_family m (by omega))
      rw [hu']
      change fourHeatOneScaledCommutator N.one.base.a N.one.base.b N.one.B χ _ t x k = _
      rw [N.one_base, N.normal.a_family, N.normal.b_family, N.one_B_family]
      rfl
    have hid' : deriv (fun v => heatNormalOneCutoffParametrix A χ v x k l) t +
        fourHeatOneOperator (A.base.a x) (A.base.b x) (A.B x) (A.C x)
          (fun y a => heatNormalOneCutoffParametrix A χ t y a l) x k =
        χ x * Q + (fourHeatGaussian t x / t) * heatFamilyOneCommutator E χ t (x, q) k l := by
      rw [← hfamily, ← hscaled, hid]
      dsimp only [Q, heatNormalOneParametrix, u]
      ring
    change |deriv (fun v => heatNormalOneCutoffParametrix A χ v x k l) t + _| ≤ _
    rw [hid']
    calc
      _ ≤ |χ x * Q| + |(fourHeatGaussian t x / t) * heatFamilyOneCommutator E χ t (x, q) k l| :=
        abs_add_le _ _
      _ ≤ B₀ * t + C₁ * t := by
        apply add_le_add _ (hcom q hq t ht x k l)
        rw [abs_mul]
        exact (mul_le_mul (hχb x) hQ (abs_nonneg Q) (by norm_num)).trans_eq (one_mul _)
      _ = _ := by ring
  · rw [heatNormalOneCutoffParametrix_residual_zero N.one χ t x hx, abs_zero]
    exact mul_nonneg (add_nonneg hB₀ hC₁) ht.1.le

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual one-form operator and Green coefficients on the common normal ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonEulerMember.one_green_regular (N : HeatCommonEulerMember g o c F r e)
    (x : FourSpace) (hx : x ∈ ball 0 r) :
    (∀ i k l, ContDiffAt ℝ 1 (fun y => heatNormalFrameConnection g c N.normal.frameData.point i y k l) x) ∧
    (∀ i j, ContDiffAt ℝ 1 (fun y => (heatNormalMetric g o e y)⁻¹ i j) x) ∧
    ContDiffAt ℝ 1 (frameExponentialJacobian g o e) x ∧
    0 < frameExponentialJacobian g o e x := by
  refine ⟨?_, (N.normal.green_regular x hx).2.1, (N.normal.green_regular x hx).2.2.1,
    (N.normal.green_regular x hx).2.2.2.1⟩
  intro i k l
  exact heatNormalFrameConnection_contDiffAt 1 g c N.normal.frameData.point x
    (N.normal.point_regular x hx)
    (N.normal.frameData.in_chart x (ball_subset_ball N.normal.radius_le hx))
    (N.normal.frame_det x hx) i k l

theorem HeatCommonEulerMember.one_connection_operator (N : HeatCommonEulerMember g o c F r e)
    (x : FourSpace) (hx : x ∈ ball 0 r) (u : FourSpace → Fin 4 → ℝ)
    (hu : ∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) (k : Fin 4) :
    fourHeatOneOperator (N.one.base.a x) (N.one.base.b x) (N.one.B x) (N.one.C x) u x k =
    fourHeatOneCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
      (heatNormalFrameConnection g c N.normal.frameData.point) ((3 : ℝ) • (1 : Mat4)) u x k := by
  rw [N.one_base, (N.normal.actual x hx).1, (N.normal.actual x hx).2.1,
    (N.one_actual x hx).1, (N.one_actual x hx).2]
  unfold heatNormalOneFirst heatNormalOneZero
  exact (fourHeatOneCovariantOperator_eq _ _ _ _ _ x
    (fun i j => (congrArg (fun A : Mat4 => A i j) (heatNormalInverse_symm g o e x)).symm)
    (fun i k l => ((N.one_green_regular x hx).1 i k l).differentiableAt one_ne_zero) hu k).symm

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem HeatCommonEulerMember.actual_one_operator (N : HeatCommonEulerMember g o c F r e)
    (hRic : RicciThree g) (x : FourSpace) (hx : x ∈ ball 0 r)
    (u : smoothCovariantFields M 1) (k : Fin 4) :
    fourHeatOneOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
      (heatNormalOneFirst N.normal.frameData x) (heatNormalOneZero N.normal.frameData x)
      (heatNormalOneFormValue c N.normal.frameData.point u) x k =
    heatNormalOneFormValue c N.normal.frameData.point (smoothOneFormHodgeLaplacian (o := o) u) x k :=
  N.normal.frameData.actual_one_operator_at hRic x (ball_subset_ball N.normal.radius_le hx)
    (N.normal.point_regular x hx) (N.normal.exponential_source x hx) (N.normal.metric_pos x hx) u k

end
end PositiveEinsteinFour.Geometry
end


section

/-! A common actual normal chart and cutoff for all three Euler heat degrees. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

structure HeatEulerChartData (D : HeatNormalFrameData g o c e) where
  base : HeatNormalExtension 10 g o e
  prototype : HeatNormalBundleExtension D
  normal : HeatNormalParametrixData D
  point_regular : ContDiffOn ℝ 4 D.point normal.chart.source
  inverse_regular : ContMDiffOn I4 I4 4 normal.chart.symm normal.chart.target

variable {D : HeatNormalFrameData g o c e}

def HeatEulerChartData.bundle (P : HeatEulerChartData D) : HeatNormalBundleExtension D :=
  { P.prototype with base := P.base }

def HeatEulerChartData.scalar (P : HeatEulerChartData D) : HeatScalarChartData D :=
  { P.normal with
    extension := P.base
    point_regular := P.point_regular
    inverse_regular := P.inverse_regular }

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance heatEulerCommon_probability : MeasureTheory.IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem exists_heatEulerCommonChart (D : HeatNormalFrameData g o c e)
    (he : e.base ∈ (chartAt FourSpace c).source) (hRic : RicciThree g)
    (hepos : e ∈ o.positive) :
    ∃ P : HeatEulerChartData D,
      (∀ x ∈ tsupport P.scalar.cutoff, P.scalar.extension.a x = (heatNormalMetric g o e x)⁻¹) ∧
      (∀ x ∈ tsupport P.scalar.cutoff, P.scalar.extension.b x = heatNormalDrift g o e x) ∧
      (∀ x ∈ tsupport P.scalar.cutoff, 0 < (heatNormalMetric g o e x).det) ∧
      (∃ B ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.scalar.residual t‖ ≤ B * t) ∧
      (∀ t l (v : smoothCovariantFields M 1),
        inner ℝ (P.normal.oneColumn P.bundle.oneCompanion t l)
          (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
        inner ℝ (P.normal.oneOperatorColumn P.bundle.oneCompanion t l) (smoothOneFormL2Linear v)) ∧
      (∃ B ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l,
        ‖P.normal.oneResidual P.bundle.oneCompanion t l‖ ≤ B * t) ∧
      (∀ t l, ∃ hf : P.normal.column P.bundle t l ∈ twoFormHodgeDomain hRic,
        twoFormHodgeGenerator hRic ⟨P.normal.column P.bundle t l, hf⟩ =
          P.normal.operatorColumn P.bundle t l) ∧
      (∃ B ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l,
        ‖P.normal.residual P.bundle t l‖ ≤ B * t) := by
  obtain ⟨S⟩ := exists_heatNormalExtension 10 g o e
  obtain ⟨E₀⟩ := exists_heatNormalBundleExtension D
  let E : HeatNormalBundleExtension D := { E₀ with base := S }
  obtain ⟨rT, hrT, hT⟩ := S.scalarParametrix_residual hRic hepos
  obtain ⟨r₂, hr₂, h₂⟩ := E.parametrix_domain_near he hRic
  obtain ⟨b₂, hb₂, hbound₂⟩ := heatNormalCutoffParametrix_bound_of_support E hRic hepos
  obtain ⟨r₁, hr₁, h₁⟩ := E.oneCompanion.compact_operator_pairing_near he hRic
  obtain ⟨b₁, hb₁, hbound₁⟩ := heatNormalOneCutoffParametrix_bound_of_support
    E.oneCompanion hRic hepos
  have hdet : ContDiffAt ℝ ∞ (fun x => (heatNormalMetric g o e x).det) 0 := by
    simp only [Matrix.det_apply']
    exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul
      (contDiffAt_prod fun i _ => heatNormalMetric_smoothAt_zero g o e (σ i) i)
  have hpos : ∀ᶠ x in 𝓝 (0 : FourSpace), 0 < (heatNormalMetric g o e x).det :=
    hdet.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds (show
      (0 : ℝ) < (heatNormalMetric g o e 0).det from by
      rw [heatNormalMetric_zero, Matrix.det_one]; exact zero_lt_one))
  have hn : ∀ᶠ x in 𝓝 (0 : FourSpace), S.a x = (heatNormalMetric g o e x)⁻¹ ∧
      S.b x = heatNormalDrift g o e x ∧ 0 < (heatNormalMetric g o e x).det ∧
      x ∈ ball 0 rT ∧ x ∈ ball 0 r₂ ∧ x ∈ ball 0 b₂ ∧
      x ∈ ball 0 r₁ ∧ x ∈ ball 0 b₁ := by
    filter_upwards [S.a_near, S.b_near, hpos, ball_mem_nhds (0 : FourSpace) hrT,
      ball_mem_nhds (0 : FourSpace) hr₂, ball_mem_nhds (0 : FourSpace) hb₂,
      ball_mem_nhds (0 : FourSpace) hr₁, ball_mem_nhds (0 : FourSpace) hb₁]
      with x ha hb hd hT h₂ hb₂ h₁ hb₁
    exact ⟨ha, hb, hd, hT, h₂, hb₂, h₁, hb₁⟩
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.mp hn
  obtain ⟨rC, C, hrC, hC, hE, hI, hCt, hP, hD⟩ := exists_heatNormalFrameChart D he
  let R := min r₀ rC
  have hR : 0 < R := lt_min hr₀ hrC
  let χ := heatNormalChartBump R hR
  have hsR : tsupport χ ⊆ ball (0 : FourSpace) R := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by change R / 2 < R; linarith)
  have hsC : tsupport χ ⊆ C.source := by
    rw [hC]
    exact hsR.trans (ball_subset_ball (min_le_right _ _))
  let N : HeatNormalParametrixData D := {
    chart := C, exponential := hE, in_chart := hCt,
    point_regular := hP.of_le (by norm_num), inside_radius := hD,
    cutoff := χ, cutoff_regular := χ.contDiff, cutoff_compact := χ.hasCompactSupport,
    cutoff_support := hsC, cutoff_zero := χ.one_of_mem_closedBall
      (mem_closedBall_self (by change 0 ≤ R / 4; positivity)) }
  let P : HeatEulerChartData D := {
    base := S, prototype := E₀, normal := N,
    point_regular := hP, inverse_regular := hI }
  have hnear (x : FourSpace) (hx : x ∈ tsupport χ) :=
    hball ((ball_subset_ball (min_le_left r₀ rC)) (hsR hx))
  have ha : ∀ x ∈ tsupport P.scalar.cutoff,
      P.scalar.extension.a x = (heatNormalMetric g o e x)⁻¹ := fun x hx => (hnear x hx).1
  have hb : ∀ x ∈ tsupport P.scalar.cutoff,
      P.scalar.extension.b x = heatNormalDrift g o e x := fun x hx => (hnear x hx).2.1
  have hd : ∀ x ∈ tsupport P.scalar.cutoff,
      0 < (heatNormalMetric g o e x).det := fun x hx => (hnear x hx).2.2.1
  have hχ : ∀ x, |χ x| ≤ 1 := fun x => by
    rw [abs_of_nonneg χ.nonneg]; exact χ.le_one
  have hi : ∀ x ∈ ball 0 (R / 4), χ x = 1 :=
    fun x hx => χ.one_of_mem_closedBall (ball_subset_closedBall hx)
  refine ⟨P, ha, hb, hd, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨B, hB, hbound⟩ := P.scalar.residualAmplitude_bound ha hχ (R / 4)
      (by positivity) hi (fun x hx t ht => hT x (hnear x hx).2.2.2.1 t ht)
    refine ⟨‖ContinuousMap.toLp (E := ℝ) 2 (normalizedVolume g) ℝ‖ * B,
      mul_nonneg (norm_nonneg _) hB, fun t ht => ?_⟩
    exact (P.scalar.residual_norm_le ha hb hd t (B * t) (mul_nonneg hB ht.1.le)
      (hbound t ht)).trans_eq (mul_assoc _ _ _).symm
  · intro t l v
    exact h₁ C hE hCt N.point_regular hD (heatNormalOneCutoffColumn E.oneCompanion χ t l)
      (heatNormalOneCutoffColumn_regular E.oneCompanion χ N.cutoff_regular t l)
      (N.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
        (heatNormalOneCutoffColumn_support E.oneCompanion χ t l))
      ((heatNormalOneCutoffColumn_support E.oneCompanion χ t l).trans hsC)
      ((heatNormalOneCutoffColumn_support E.oneCompanion χ t l).trans
        (fun x hx => (hnear x hx).2.2.2.2.2.2.1)) v
  · obtain ⟨B, hB, hbound⟩ := hbound₁ χ (N.cutoff_regular.of_le (by norm_num))
      N.cutoff_compact (fun x hx => (hnear x hx).2.2.2.2.2.2.2) hχ
      (R / 4) (by positivity) hi
    exact ⟨4 * B, by positivity, fun t ht l =>
      N.oneResidual_norm_le E.oneCompanion B hB t ht.1 (hbound t ht) l⟩
  · intro t l
    exact h₂ C hE hCt N.point_regular hD χ N.cutoff_regular N.cutoff_compact hsC
      (fun x hx => (hnear x hx).2.2.2.2.1) t l
  · obtain ⟨B, hB, hbound⟩ := hbound₂ χ (N.cutoff_regular.of_le (by norm_num))
      N.cutoff_compact (fun x hx => (hnear x hx).2.2.2.2.2.1) hχ
      (R / 4) (by positivity) hi
    exact ⟨6 * B, by positivity, fun t ht l =>
      N.residual_norm_le E t ht.1 B hB (hbound t ht) l⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Passing the normal-column L2 error to each signed Gram entry. -/

namespace PositiveEinsteinFour.Geometry

open Set Filter
open scoped _root_.Topology

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem heat_inner_error_bound (x y z w : V) (a b c d : ℝ)
    (ha : ‖x‖ ≤ a) (hb : ‖x - y‖ ≤ b) (hc : ‖z‖ ≤ c) (hd : ‖z - w‖ ≤ d) :
    ‖inner ℝ x z - inner ℝ y w‖ ≤ b * c + (a + b) * d := by
  have hb0 : 0 ≤ b := (norm_nonneg _).trans hb
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hd
  have hy : ‖y‖ ≤ a + b := by
    have hh := norm_sub_norm_le y x
    rw [norm_sub_rev] at hh
    linarith
  have he : inner ℝ x z - inner ℝ y w = inner ℝ (x - y) z + inner ℝ y (z - w) := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  rw [he]
  calc
    _ ≤ ‖inner ℝ (x - y) z‖ + ‖inner ℝ y (z - w)‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ * ‖z‖ + ‖y‖ * ‖z - w‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ b * c + (a + b) * d := add_le_add
      (mul_le_mul hb hc (norm_nonneg z) hb0)
      (mul_le_mul hy hd (norm_nonneg (z - w)) ((norm_nonneg y).trans hy))

theorem heat_inner_error_tendsto (x y z w : ℝ → V) (C₁ C₂ D T : ℝ) (hT : 0 < T)
    (hx : ∀ t ∈ Ioc 0 T, ‖x t‖ ≤ C₁ / t)
    (hz : ∀ t ∈ Ioc 0 T, ‖z t‖ ≤ C₂ / t)
    (hxy : ∀ t ∈ Ioc 0 T, ‖x t - y t‖ ≤ D * t ^ 2)
    (hzw : ∀ t ∈ Ioc 0 T, ‖z t - w t‖ ≤ D * t ^ 2) :
    Tendsto (fun t => inner ℝ (x t) (z t) - inner ℝ (y t) (w t)) (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ => (D * C₂ + C₁ * D) * t + D ^ 2 * t ^ 4)
      (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (fun t : ℝ => (D * C₂ + C₁ * D) * t + D ^ 2 * t ^ 4) := by fun_prop
    simpa only [mul_zero, zero_pow (by norm_num : 4 ≠ 0), add_zero] using
      hcont.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with t ht htT
  calc
    _ ≤ (D * t ^ 2) * (C₂ / t) + (C₁ / t + D * t ^ 2) * (D * t ^ 2) :=
      heat_inner_error_bound (x t) (y t) (z t) (w t) _ _ _ _
        (hx t ⟨ht, htT.le⟩) (hxy t ⟨ht, htT.le⟩) (hz t ⟨ht, htT.le⟩) (hzw t ⟨ht, htT.le⟩)
    _ = _ := by field_simp [(show 0 < t from ht).ne']; ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normal parametrix has the exact Duhamel formula in every
smooth Hodge eigenmode, with its proved delta initial value. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.normalized_eigen_integral
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D)
    (hRic : RicciThree g) (he : e.base ∈ (chartAt FourSpace c).source)
    (hgen : ∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 6)
    (i : TwoFormEigenIndex (o := o) hRic) :
    inner ℝ (P.normalizedColumn E t l) (twoFormEigenvector hRic i) =
      Real.exp (-(i.1.val⁻¹ - 1) * t) *
        twoFormFrameValue o (twoFormEigenSection hRic i).val e l +
      ∫ s in (0 : ℝ)..t, Real.exp (-(i.1.val⁻¹ - 1) * (t - s)) *
        inner ℝ (P.normalizedResidualZero E s l) (twoFormEigenvector hRic i) := by
  apply heat_forced_scalar_formula _ _ _ _ t ht.1
  · exact ((P.normalizedResidualZero_continuous E B hB l).mono
      (Icc_subset_Icc le_rfl ht.2)).inner continuousOn_const
  · have h := P.normalized_initial E he l (twoFormEigenSection hRic i : SmoothL2TwoForm o)
    simpa only [twoFormEigenSection_L2] using h
  · intro s hs
    obtain ⟨hf, hgf⟩ := hgen s l
    rw [P.normalizedResidualZero_eq E s hs l]
    exact P.normalized_eigen_evolution E hRic s hs l hf hgf i

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual one-form parametrix satisfies Duhamel's formula in every
smooth eigenmode, with its proved normalized delta initial value. -/

namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter MeasureTheory
open scoped ContDiff Manifold _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.one_normalized_eigen_integral
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D)
    (hpair : ∀ t l (v : smoothCovariantFields M 1),
      inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
        inner ℝ (P.oneOperatorColumn E t l) (smoothOneFormL2Linear v))
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (he : e.base ∈ (chartAt FourSpace c).source)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.oneResidual E t l‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 4) (i : OneFormEigenIndex hRic d) :
    inner ℝ (P.oneNormalizedColumn E t l) (oneFormEigenvector hRic d i) =
      Real.exp (-oneFormHeatRate hRic d i * t) *
        covariantFieldFramed g (oneFormEigenSection hRic d i).val e ![l] +
      ∫ s in (0 : ℝ)..t, Real.exp (-oneFormHeatRate hRic d i * (t - s)) *
        inner ℝ (P.oneNormalizedResidualZero E s l) (oneFormEigenvector hRic d i) := by
  apply heat_forced_scalar_formula _ _ _ _ t ht.1
  · exact ((P.oneNormalizedResidualZero_continuous E B hB l).mono
      (Icc_subset_Icc le_rfl ht.2)).inner continuousOn_const
  · have h := P.one_normalized_initial E he (oneFormEigenSection hRic d i) l
    simpa only [oneFormEigenSection_L2] using h
  · intro s hs
    rw [P.oneNormalizedResidualZero_eq E s hs l]
    exact P.one_normalized_eigen_evolution E hpair hRic d s hs l i

end
end PositiveEinsteinFour.Geometry
end


section

/-! The genuine scalar spectral heat column equals the constructed
normal parametrix minus its actual Bochner forcing convolution. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem scalar_eq_of_eigen_pairing (v w : Lp ℝ 2 (normalizedVolume g))
    (h : ∀ i : ScalarBaseEigenIndex g o d,
      inner ℝ v (scalarBaseEigenvector g o d i) = inner ℝ w (scalarBaseEigenvector g o d i)) :
    v = w := by
  apply (scalarBaseEigenbasis g o d).repr.injective
  apply lp.ext
  funext i
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, scalarBaseEigenbasis_apply]
  exact (real_inner_comm _ _).trans ((h i).trans (real_inner_comm _ _))

theorem HeatScalarChartData.normalized_eigen_integral (P : HeatScalarChartData D)
    (ha : ∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hb : ∀ x ∈ tsupport P.cutoff, P.extension.b x = heatNormalDrift g o e x)
    (hd : ∀ x ∈ tsupport P.cutoff, 0 < (heatNormalMetric g o e x).det)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.residual t‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (i : ScalarBaseEigenIndex g o d) :
    inner ℝ (P.normalizedColumn t) (scalarBaseEigenvector g o d i) =
      Real.exp (-(i.1.val⁻¹ - 1) * t) * (scalarBaseEigenfunction g o d i).val e.base +
        ∫ s in (0 : ℝ)..t, Real.exp (-(i.1.val⁻¹ - 1) * (t - s)) *
          inner ℝ (P.normalizedResidualZero s) (scalarBaseEigenvector g o d i) := by
  apply heat_forced_scalar_formula _ _ _ _ t ht.1
  · exact ((P.normalizedResidualZero_continuous ha hb hd B hB).mono
      (Icc_subset_Icc le_rfl ht.2)).inner continuousOn_const
  · exact P.normalized_initial_eigen d i
  · intro s hs
    rw [P.normalizedResidualZero_eq s hs]
    exact P.normalized_eigen_evolution d s hs i

theorem HeatScalarChartData.spectral_comparison (P : HeatScalarChartData D)
    (ha : ∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hb : ∀ x ∈ tsupport P.cutoff, P.extension.b x = heatNormalDrift g o e x)
    (hd : ∀ x ∈ tsupport P.cutoff, 0 < (heatNormalMetric g o e x).det)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.residual t‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    P.normalizedColumn t = scalarHeatColumn g o d t.toNNReal (Real.toNNReal_pos.mpr ht.1) e.base +
      scalarHeatConvolution g o d P.normalizedResidualZero t := by
  apply scalar_eq_of_eigen_pairing d
  intro i
  rw [inner_add_left, scalarHeatColumn_eigen,
    scalarHeatConvolution_eigen g o d _ t ht.1.le
      ((P.normalizedResidualZero_continuous ha hb hd B hB).mono
        (Icc_subset_Icc le_rfl ht.2))]
  unfold scalarBaseHeatWeight scalarBaseHeatRate
  rw [Real.coe_toNNReal t ht.1.le]
  rw [show -t * (i.1.val⁻¹ - 1) = -(i.1.val⁻¹ - 1) * t by ring]
  exact P.normalized_eigen_integral d ha hb hd B hB t ht i

theorem HeatScalarChartData.spectral_error_bound (P : HeatScalarChartData D)
    (ha : ∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hb : ∀ x ∈ tsupport P.cutoff, P.extension.b x = heatNormalDrift g o e x)
    (hd : ∀ x ∈ tsupport P.cutoff, 0 < (heatNormalMetric g o e x).det)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.residual t‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    ‖P.normalizedColumn t -
      scalarHeatColumn g o d t.toNNReal (Real.toNNReal_pos.mpr ht.1) e.base‖ ≤
        (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) * t ^ 2 / 2 := by
  rw [P.spectral_comparison d ha hb hd B hB t ht, add_sub_cancel_left]
  exact scalarHeatConvolution_norm_le g o d _ t ht.1.le _ (fun s hs =>
    P.normalizedResidualZero_bound B hB s ⟨hs.1, hs.2.trans ht.2⟩)

theorem exists_heatScalarSpectralComparison (D : HeatNormalFrameData g o c e)
    (he : e.base ∈ (chartAt FourSpace c).source) (hRic : RicciThree g) (hepos : e ∈ o.positive) :
    ∃ (P : HeatScalarChartData D) (C : ℝ), 0 ≤ C ∧
      ∀ (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1),
        ‖P.normalizedColumn t -
          scalarHeatColumn g o d t.toNNReal (Real.toNNReal_pos.mpr ht.1) e.base‖ ≤ C * t ^ 2 := by
  obtain ⟨P, ha, hb, hd, B, hB, hbound⟩ := exists_heatScalarGlobalResidual D he hRic hepos
  refine ⟨P, ‖((normalizedChartFactor g).toReal)⁻¹‖ * B / 2, by positivity, ?_⟩
  intro t ht
  exact (P.spectral_error_bound d ha hb hd B hbound t ht).trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


section

/-! One Gaussian bound for the alternating polynomial of the three actual degrees. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set MeasureTheory Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem heatUniformEulerIntegral_bound (F : HeatFamilyOneCoefficients) (r : ℝ)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ ball 0 r) (K : Set CoordinateFrameSpace) (hK : IsCompact K)
    (hRic : RicciThree g) :
    ∃ D ≥ (0 : ℝ), ∀ (e : FrameBundle g) (_N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K → ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖∫ x : FourSpace, fourHeatGaussian t x ^ 2 *
        ((F.base.U (x, frameCoordinateState g c e) ^ 2)⁻¹ * χ x ^ 2 *
          heatEulerGram (F.eulerPolynomial t (x, frameCoordinateState g c e))
            (F.eulerPolynomial t (x, frameCoordinateState g c e)))‖ ≤ D := by
  obtain ⟨C, hC, hb⟩ := heatUniformEulerFirst_quadratic (g := g) (o := o) (c := c)
    F r χ hχ hχs K hK hRic
  obtain ⟨B, hB, ht⟩ := heatFamilyEulerTail_bound F χ hχ.continuous hc K hK
  refine ⟨(32 * C + B) / (64 * Real.pi ^ 2), by positivity, ?_⟩
  intro e N hq t htt
  simp_rw [heatFamilyEulerPolynomial_gram]
  apply fourHeat_signed_gaussian_bound _ _ C B t hC hB htt.1 (hb e N hq)
  intro x
  exact ht _ hq t ⟨htt.1.le, htt.2⟩ x

end
end PositiveEinsteinFour.Geometry
end


section

/-! The one-form Green identity holds on the full common chart. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonEulerMember.one_compact_green (N : HeatCommonEulerMember g o c F r e)
    (hRic : RicciThree g) (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a)
    (hc : HasCompactSupport a) (hs : tsupport a ⊆ ball 0 r) (v : smoothCovariantFields M 1) :
    (∫ x, frameExponentialJacobian g o e x *
      inner ℝ (a x) (heatNormalOneValue c N.normal.frameData.point (smoothOneFormHodgeLaplacian (o := o) v) x)) =
    ∫ x, frameExponentialJacobian g o e x *
      inner ℝ (heatNormalOneOperatorAmplitude N.one a x) (heatNormalOneValue c N.normal.frameData.point v x) := by
  let u := fun x k => a x k
  let w := fun x k => heatNormalOneFormValue c N.normal.frameData.point v x k
  have hu (k : Fin 4) : ContDiff ℝ 2 (fun x => u x k) :=
    (contDiff_piLp (p := 2)).mp ha k
  have hsc (k : Fin 4) : tsupport (fun x => u x k) ⊆ ball 0 r :=
    (heatOneAmplitude_component_support a k).trans hs
  have hcc (k : Fin 4) : HasCompactSupport (fun x => u x k) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (heatOneAmplitude_component_support a k)
  have hw (x : FourSpace) (hx : x ∈ ball 0 r) (k : Fin 4) :
      ContDiffAt ℝ 2 (fun y => w y k) x := by
    exact heatNormalOneFormValue_regular 2 c N.normal.frameData.point v x
      (N.normal.point_regular x hx) (N.normal.frameData.in_chart x (ball_subset_ball N.normal.radius_le hx)) k
  have hop (x : FourSpace) (k : Fin 4) : heatNormalOneOperatorAmplitude N.one a x k =
      fourHeatOneCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatNormalFrameConnection g c N.normal.frameData.point) (((3 : ℝ) • (1 : Mat4))) u x k :=
    N.one.compact_operator_eq (ball 0 r) (fun y hy => N.one_connection_operator y hy) a ha hs x k
  have htest (x : FourSpace) : frameExponentialJacobian g o e x *
      inner ℝ (a x) (heatNormalOneValue c N.normal.frameData.point (smoothOneFormHodgeLaplacian (o := o) v) x) =
      ∑ k : Fin 4, frameExponentialJacobian g o e x * u x k *
        fourHeatOneCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalFrameConnection g c N.normal.frameData.point) (((3 : ℝ) • (1 : Mat4))) w x k := by
    rw [heat_one_weighted_inner_sum]
    by_cases hx : x ∈ ball 0 r
    · apply Finset.sum_congr rfl
      intro k _
      have hactual := N.actual_one_operator hRic x hx v k
      have hconv := fourHeatOneCovariantOperator_eq
        (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatNormalFrameConnection g c N.normal.frameData.point) ((3 : ℝ) • (1 : Mat4)) w x
        (fun i j => (congrArg (fun A : Mat4 => A i j) (heatNormalInverse_symm g o e x)).symm)
        (fun i k l => ((N.one_green_regular x hx).1 i k l).differentiableAt one_ne_zero) (hw x hx) k
      unfold heatNormalOneFirst heatNormalOneZero at hactual
      rw [← hconv] at hactual
      rw [hactual]
      rfl
    · have hz : a x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
      have hzk (k : Fin 4) : u x k = 0 := by change a x k = 0; rw [hz]; rfl
      simp only [hz, PiLp.zero_apply, hzk, mul_zero, zero_mul, Finset.sum_const_zero]
  have hg := fourHeatOneCovariantOperator_compact_adjoint
    (heatNormalFrameConnection g c N.normal.frameData.point) (fun x => (heatNormalMetric g o e x)⁻¹)
    (frameExponentialJacobian g o e) ((fun _ : FourSpace => (3 : ℝ) • (1 : Mat4))) u w (ball 0 r)
    hu hcc hsc hw (fun x hx => (N.one_green_regular x hx).1) (fun x hx => (N.one_green_regular x hx).2.1)
    (fun x hx => (N.one_green_regular x hx).2.2.1) (fun x hx => (N.one_green_regular x hx).2.2.2.ne')
    (fun _ _ _ _ => continuousAt_const)
    (fun x hx i => N.normal.frameData.connection_skew x (ball_subset_ball N.normal.radius_le hx) i)
    (fun x _ i j => (congrArg (fun A : Mat4 => A i j) (heatNormalInverse_symm g o e x)).symm)
    (fun _ _ k l => by simp [Matrix.one_apply, eq_comm])
  calc
    _ = ∫ x, ∑ k : Fin 4, frameExponentialJacobian g o e x * u x k *
        fourHeatOneCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalFrameConnection g c N.normal.frameData.point) (((3 : ℝ) • (1 : Mat4))) w x k := by
      apply integral_congr_ae
      exact Eventually.of_forall htest
    _ = _ := hg
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [heat_one_weighted_inner_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [hop]
      change _ = _ * _ * w x k
      ring


end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact comparison with the genuine spectral heat column and the
quadratic L2 error bound, using only proved geometric residual estimates. -/

namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem oneForm_eq_of_eigen_pairing (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (f h : OneFormL2 o)
    (hp : ∀ i, inner ℝ f (oneFormEigenvector hRic d i) = inner ℝ h (oneFormEigenvector hRic d i)) :
    f = h := by
  apply (oneFormSpectralEquiv hRic d).injective
  apply lp.ext
  funext i
  change (oneFormEigenbasis hRic d).repr f i = (oneFormEigenbasis hRic d).repr h i
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply]
  simp only [oneFormEigenbasis, HilbertBasis.coe_mk]
  simpa only [real_inner_comm] using hp i

theorem HeatNormalParametrixData.one_spectral_comparison
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D)
    (hpair : ∀ t l (v : smoothCovariantFields M 1),
      inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
        inner ℝ (P.oneOperatorColumn E t l) (smoothOneFormL2Linear v))
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (he : e.base ∈ (chartAt FourSpace c).source)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.oneResidual E t l‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 4) :
    P.oneNormalizedColumn E t l =
      oneFormHeatFrameColumn hRic d t.toNNReal (Real.toNNReal_pos.mpr ht.1) e l +
        oneFormHeatConvolution hRic d (fun s => P.oneNormalizedResidualZero E s l) t := by
  apply oneForm_eq_of_eigen_pairing hRic d
  intro i
  rw [inner_add_left, oneFormHeatFrameColumn_eigen,
    oneFormHeatConvolution_eigen hRic d _ t ht.1.le
      ((P.oneNormalizedResidualZero_continuous E B hB l).mono (Icc_subset_Icc le_rfl ht.2))]
  unfold oneFormHeatWeight
  rw [Real.coe_toNNReal t ht.1.le]
  rw [show -t * oneFormHeatRate hRic d i = -oneFormHeatRate hRic d i * t by ring]
  exact P.one_normalized_eigen_integral E hpair hRic d he B hB t ht l i

theorem HeatNormalParametrixData.one_spectral_error_bound
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D)
    (hpair : ∀ t l (v : smoothCovariantFields M 1),
      inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
        inner ℝ (P.oneOperatorColumn E t l) (smoothOneFormL2Linear v))
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (he : e.base ∈ (chartAt FourSpace c).source)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.oneResidual E t l‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 4) :
    ‖P.oneNormalizedColumn E t l -
      oneFormHeatFrameColumn hRic d t.toNNReal (Real.toNNReal_pos.mpr ht.1) e l‖ ≤
        (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) * t ^ 2 / 2 := by
  rw [P.one_spectral_comparison E hpair hRic d he B hB t ht l, add_sub_cancel_left]
  exact oneFormHeatConvolution_norm_le hRic d _ t ht.1.le _ (fun s hs =>
    P.oneNormalizedResidualZero_bound E B hB s ⟨hs.1, hs.2.trans ht.2⟩ l)

theorem exists_heatNormalOneSpectralComparison (E : HeatNormalOneExtension D)
    (he : e.base ∈ (chartAt FourSpace c).source) (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (hepos : e ∈ o.positive) :
    ∃ (P : HeatNormalParametrixData D) (C : ℝ), 0 ≤ C ∧
      ∀ (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 4),
        ‖P.oneNormalizedColumn E t l -
          oneFormHeatFrameColumn hRic d t.toNNReal (Real.toNNReal_pos.mpr ht.1) e l‖ ≤
            C * t ^ 2 := by
  obtain ⟨P, hpair, B, hB, hb⟩ := exists_heatNormalOneResidualData E he hRic hepos
  refine ⟨P, ‖((normalizedChartFactor g).toReal)⁻¹‖ * B / 2, by positivity, ?_⟩
  intro t ht l
  exact (P.one_spectral_error_bound E hpair hRic d he B hb t ht l).trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact comparison of the actual local parametrix with the global spectral
heat column, followed by the quadratic L2 error bound. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.spectral_comparison
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D)
    (hRic : RicciThree g) (he : e.base ∈ (chartAt FourSpace c).source)
    (hgen : ∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 6) :
    P.normalizedColumn E t l =
      twoFormHeatFrameColumn hRic t.toNNReal (Real.toNNReal_pos.mpr ht.1) e l +
        twoFormHeatConvolution hRic (fun s => P.normalizedResidualZero E s l) t := by
  apply twoForm_eq_of_eigen_pairing hRic
  intro i
  rw [inner_add_left, twoFormHeatFrameColumn_eigen,
    twoFormHeatConvolution_eigen hRic _ t ht.1.le
      ((P.normalizedResidualZero_continuous E B hB l).mono (Icc_subset_Icc le_rfl ht.2))]
  unfold twoFormHeatFrameCoefficient twoFormHeatWeight twoFormHeatRate
  rw [Real.coe_toNNReal t ht.1.le]
  rw [show -t * (i.1.val⁻¹ - 1) = -(i.1.val⁻¹ - 1) * t by ring]
  exact P.normalized_eigen_integral E hRic he hgen B hB t ht l i

theorem HeatNormalParametrixData.spectral_error_bound
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D)
    (hRic : RicciThree g) (he : e.base ∈ (chartAt FourSpace c).source)
    (hgen : ∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 6) :
    ‖P.normalizedColumn E t l -
      twoFormHeatFrameColumn hRic t.toNNReal (Real.toNNReal_pos.mpr ht.1) e l‖ ≤
        (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) * t ^ 2 / 2 := by
  rw [P.spectral_comparison E hRic he hgen B hB t ht l, add_sub_cancel_left]
  exact twoFormHeatConvolution_norm_le hRic _ t ht.1.le _ (fun s hs =>
    P.normalizedResidualZero_bound E B hB s ⟨hs.1, hs.2.trans ht.2⟩ l)

theorem exists_heatNormalSpectralComparison (E : HeatNormalBundleExtension D)
    (he : e.base ∈ (chartAt FourSpace c).source) (hRic : RicciThree g) (hepos : e ∈ o.positive) :
    ∃ (P : HeatNormalParametrixData D) (C : ℝ), 0 ≤ C ∧
      ∀ (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 6),
        ‖P.normalizedColumn E t l -
          twoFormHeatFrameColumn hRic t.toNNReal (Real.toNNReal_pos.mpr ht.1) e l‖ ≤
            C * t ^ 2 := by
  obtain ⟨P, hgen, B, hB, hb⟩ := exists_heatNormalGlobalResidual E he hRic hepos
  refine ⟨P, ‖((normalizedChartFactor g).toReal)⁻¹‖ * B / 2, by positivity, ?_⟩
  intro t ht l
  exact (P.spectral_error_bound E hRic he hgen B hb t ht l).trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar heat diagonal differs by a quantity tending to zero
from the explicit normal-coordinate squared-Gaussian integral. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem HeatScalarChartData.column_square_error_tendsto (P : HeatScalarChartData D)
    (ha : ∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hb : ∀ x ∈ tsupport P.cutoff, P.extension.b x = heatNormalDrift g o e x)
    (hd : ∀ x ∈ tsupport P.cutoff, 0 < (heatNormalMetric g o e x).det)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.residual t‖ ≤ B * t) :
    Tendsto (fun t => ‖P.normalizedColumn t‖ ^ 2 -
      ‖scalarHeatRealColumn g o d t e.base‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, _hC, hc⟩ := P.normalizedColumn_growth
  apply heat_norm_square_error_tendsto _ _ C (‖((normalizedChartFactor g).toReal)⁻¹‖ * B / 2)
    1 zero_lt_one hc
  intro t ht
  rw [scalarHeatRealColumn_pos g o d t ht.1]
  exact (P.spectral_error_bound d ha hb hd B hB t ht).trans_eq (by ring)

theorem HeatScalarChartData.trace_gaussian_error_tendsto (P : HeatScalarChartData D)
    (ha : ∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hb : ∀ x ∈ tsupport P.cutoff, P.extension.b x = heatNormalDrift g o e x)
    (hd : ∀ x ∈ tsupport P.cutoff, 0 < (heatNormalMetric g o e x).det)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.residual t‖ ≤ B * t) :
    Tendsto (fun t => scalarHeatRealDiagonal g o d (t + t) e.base -
      ((normalizedChartFactor g).toReal)⁻¹ *
        ∫ x, fourHeatGaussian t x ^ 2 *
          (frameExponentialJacobian g o e x * (P.polynomial t x) ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
  have h := (P.column_square_error_tendsto d ha hb hd B hB).neg
  simp only [neg_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [scalarHeatRealDiagonal_columns g o d t ht e.base,
    P.normalizedColumn_gaussian_integral, neg_sub]

theorem exists_heatScalarTraceApproximation (D : HeatNormalFrameData g o c e)
    (he : e.base ∈ (chartAt FourSpace c).source) (hRic : RicciThree g) (hepos : e ∈ o.positive) :
    ∃ P : HeatScalarChartData D,
      Tendsto (fun t => scalarHeatRealDiagonal g o d (t + t) e.base -
        ((normalizedChartFactor g).toReal)⁻¹ *
          ∫ x, fourHeatGaussian t x ^ 2 *
            (frameExponentialJacobian g o e x * (P.polynomial t x) ^ 2))
        (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨P, ha, hb, hd, B, _hB, hbound⟩ := exists_heatScalarGlobalResidual D he hRic hepos
  exact ⟨P, P.trace_gaussian_error_tendsto d ha hb hd B hbound⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar and one-form data on the same actual chart and fixed cutoff as degree two. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

def HeatCommonEulerMember.scalarData (N : HeatCommonEulerMember g o c F r e)
    (hr : 0 < r) : HeatScalarChartData N.normal.frameData where
  extension := N.normal.extension.base
  chart := (N.normal.parametrixData hr).chart
  exponential := (N.normal.parametrixData hr).exponential
  in_chart := (N.normal.parametrixData hr).in_chart
  point_regular := fun x hx => (N.point_regular_four x
    ((N.normal.parametrixData_source hr) ▸ hx)).contDiffWithinAt
  inverse_regular := N.normal.inverse_regular.mono (fun _ hy => hy.1)
  inside_radius := (N.normal.parametrixData hr).inside_radius
  cutoff := (N.normal.parametrixData hr).cutoff
  cutoff_regular := (N.normal.parametrixData hr).cutoff_regular
  cutoff_compact := (N.normal.parametrixData hr).cutoff_compact
  cutoff_support := (N.normal.parametrixData hr).cutoff_support
  cutoff_zero := (N.normal.parametrixData hr).cutoff_zero

theorem HeatCommonEulerMember.scalarData_actual (N : HeatCommonEulerMember g o c F r e)
    (hr : 0 < r) :
    (∀ x ∈ tsupport (N.scalarData hr).cutoff,
      (N.scalarData hr).extension.a x = (heatNormalMetric g o e x)⁻¹) ∧
    (∀ x ∈ tsupport (N.scalarData hr).cutoff,
      (N.scalarData hr).extension.b x = heatNormalDrift g o e x) ∧
    (∀ x ∈ tsupport (N.scalarData hr).cutoff, 0 < (heatNormalMetric g o e x).det) := by
  have hs : tsupport (N.scalarData hr).cutoff ⊆ Metric.ball 0 r := by
    exact (N.scalarData hr).cutoff_support.trans (by
      rw [show (N.scalarData hr).chart = (N.normal.parametrixData hr).chart from rfl,
        N.normal.parametrixData_source hr])
  exact ⟨fun x hx => (N.normal.actual x (hs hx)).1,
    fun x hx => (N.normal.actual x (hs hx)).2.1,
    fun x hx => N.normal.metric_pos x (hs hx)⟩

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem HeatCommonEulerMember.one_compact_operator_pairing
    (N : HeatCommonEulerMember g o c F r e) (hRic : RicciThree g)
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 N.normal.frameData.point C.source)
    (hD : C.source ⊆ Metric.ball 0 N.normal.frameData.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 4 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (hsmall : tsupport a ⊆ Metric.ball 0 r)
    (v : smoothCovariantFields M 1) :
    inner ℝ (heatNormalOneAmplitudeL2 N.normal.frameData C hCt hP hD a
      (ha.of_le (by norm_num)) hc hs)
      (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
    inner ℝ (heatNormalOneHodgeImage N.one C hCt hP hD a ha hc hs)
      (smoothOneFormL2Linear v) := by
  have hleft := heatNormalOneAmplitudeL2_pairing_normal N.normal.frameData C hE hCt hP hD a
    (ha.of_le (by norm_num)) hc hs (smoothOneFormHodgeLaplacian (o := o) v)
  have hright := heatNormalOneAmplitudeL2_pairing_normal N.normal.frameData C hE hCt hP hD
    (heatNormalOneOperatorAmplitude N.one a) (heatNormalOneOperatorAmplitude_regular N.one a ha)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOneOperatorAmplitude_support N.one a))
    ((heatNormalOneOperatorAmplitude_support N.one a).trans hs) v
  exact hleft.trans ((congrArg ((normalizedChartFactor g).toReal * ·)
    (N.one_compact_green hRic a (ha.of_le (by norm_num)) hc hsmall v)).trans hright.symm)

theorem HeatCommonEulerMember.parametrixData_one_pairing
    (N : HeatCommonEulerMember g o c F r e) (hr : 0 < r) (hRic : RicciThree g)
    (t : ℝ) (l : Fin 4) (v : smoothCovariantFields M 1) :
    inner ℝ ((N.normal.parametrixData hr).oneColumn N.one t l)
      (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
    inner ℝ ((N.normal.parametrixData hr).oneOperatorColumn N.one t l)
      (smoothOneFormL2Linear v) := by
  let P := N.normal.parametrixData hr
  apply N.one_compact_operator_pairing hRic P.chart P.exponential P.in_chart P.point_regular
    P.inside_radius (heatNormalOneCutoffColumn N.one P.cutoff t l)
    (heatNormalOneCutoffColumn_regular N.one P.cutoff P.cutoff_regular t l)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalOneCutoffColumn_support N.one P.cutoff t l))
    ((heatNormalOneCutoffColumn_support N.one P.cutoff t l).trans P.cutoff_support) _ v
  rw [← N.normal.parametrixData_source hr]
  exact (heatNormalOneCutoffColumn_support N.one P.cutoff t l).trans P.cutoff_support

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform control of signed Gram sums from the actual column estimates. -/

namespace PositiveEinsteinFour.Geometry

open Set
open scoped BigOperators

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem heat_inner_error_uniform (x y z w : V) (C D t : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (ht : t ∈ Ioc (0 : ℝ) 1)
    (hx : ‖x‖ ≤ C / t) (hz : ‖z‖ ≤ C / t)
    (hxy : ‖x - y‖ ≤ D * t ^ 2) (hzw : ‖z - w‖ ≤ D * t ^ 2) :
    ‖inner ℝ x z - inner ℝ y w‖ ≤ 2 * C * D + D ^ 2 := by
  calc
    _ ≤ (D * t ^ 2) * (C / t) + (C / t + D * t ^ 2) * (D * t ^ 2) :=
      heat_inner_error_bound x y z w _ _ _ _ hx hxy hz hzw
    _ = 2 * C * D * t + D ^ 2 * t ^ 4 := by field_simp [ht.1.ne']; ring
    _ ≤ 2 * C * D + D ^ 2 := by
      have hpow : t ^ 4 ≤ 1 := pow_le_one₀ ht.1.le ht.2
      exact add_le_add
        (mul_le_of_le_one_right (by positivity) ht.2)
        (mul_le_of_le_one_right (sq_nonneg D) hpow)

theorem heat_signed_gram_error_uniform {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (x y : ι → V) (C D t : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (ht : t ∈ Ioc (0 : ℝ) 1)
    (hx : ∀ l, ‖x l‖ ≤ C / t) (hxy : ∀ l, ‖x l - y l‖ ≤ D * t ^ 2) :
    ‖(∑ l, ∑ m, A l m * inner ℝ (x l) (x m)) -
      (∑ l, ∑ m, A l m * inner ℝ (y l) (y m))‖ ≤
      (∑ l, ∑ m, ‖A l m‖) * (2 * C * D + D ^ 2) := by
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ l, ∑ m, ‖A l m * (inner ℝ (x l) (x m) - inner ℝ (y l) (y m))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => norm_sum_le _ _)
    _ ≤ ∑ l, ∑ m, ‖A l m‖ * (2 * C * D + D ^ 2) := by
      apply Finset.sum_le_sum
      intro l _
      apply Finset.sum_le_sum
      intro m _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (heat_inner_error_uniform (x l) (y l) (x m) (y m) C D t hC hD ht
          (hx l) (hx m) (hxy l) (hxy m)) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform norm growth and quadratic spectral error for the actual
common family of compact normal parametrices. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

theorem exists_heatActualUniformSpectral (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) :
    ∃ E : HeatFamilySmoothCoefficients, ∃ r : ℝ, ∃ hr : 0 < r,
      ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧
      ∃ C ≥ (0 : ℝ), ∃ D ≥ (0 : ℝ), ∀ e' ∈ U,
        ∃ N : HeatCommonNormalMember g o e.base E r e',
          frameCoordinateState g e.base e' ∈ closedBall (frameCoordinateState g e.base e) 1 ∧
          (∀ t ∈ Ioc (0 : ℝ) 1, ∀ l,
            ‖(N.parametrixData hr).normalizedColumn N.extension t l‖ ≤ C / t) ∧
          (e' ∈ o.positive → ∀ (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 6),
            ‖(N.parametrixData hr).normalizedColumn N.extension t l -
              twoFormHeatFrameColumn hRic t.toNNReal (Real.toNNReal_pos.mpr ht.1) e' l‖ ≤ D * t ^ 2) := by
  obtain ⟨E, r, hr, U₀, hU₀, he₀, B, hB, hN⟩ := exists_heatActualUniformParametrix g o hRic e
  let p := frameCoordinateState g e.base e
  have hcoord : {e' : FrameBundle g | frameCoordinateState g e.base e' ∈ ball p 1} ∈ 𝓝 e :=
    (frameCoordinateState_continuousAt g e.base e (mem_chart_source FourSpace e.base)).preimage_mem_nhds
      (ball_mem_nhds _ zero_lt_one)
  obtain ⟨U, hsub, hU, heU⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU₀.mem_nhds he₀) hcoord)
  obtain ⟨C, hC, hc⟩ := heatUniformColumn_growth (g := g) (o := o) (c := e.base)
    E r hr (closedBall p 1) (isCompact_closedBall _ _)
  refine ⟨E, r, hr, U, hU, heU, C, hC, ‖((normalizedChartFactor g).toReal)⁻¹‖ * B / 2,
    by positivity, ?_⟩
  intro e' he'
  obtain ⟨hUe, hqe⟩ := hsub he'
  obtain ⟨N, hgen, hres⟩ := hN e' hUe
  refine ⟨N, ball_subset_closedBall hqe, hc e' N (ball_subset_closedBall hqe), ?_⟩
  intro hepos t ht l
  have hs : e'.base ∈ (chartAt FourSpace e.base).source := by
    simpa only [frameExponential_zero] using N.exponential_source 0 (mem_ball_self hr)
  exact ((N.parametrixData hr).spectral_error_bound N.extension hRic hs hgen B
    (hres hepos) t ht l).trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual diagonal heat trace differs by a vanishing quantity from
the four squared L2 norms of the constructed normal parametrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter
open scoped ContDiff Manifold _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.oneColumn_square_error_tendsto
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D)
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o)) (he : e.base ∈ (chartAt FourSpace c).source)
    (hpair : ∀ t l (v : smoothCovariantFields M 1),
      inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
        inner ℝ (P.oneOperatorColumn E t l) (smoothOneFormL2Linear v))
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.oneResidual E t l‖ ≤ B * t)
    (l : Fin 4) :
    Tendsto (fun t => ‖P.oneNormalizedColumn E t l‖ ^ 2 -
      ‖oneFormHeatRealColumn hRic d t e l‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, _hC, hc⟩ := P.oneNormalizedColumn_growth E l
  apply heat_norm_square_error_tendsto _ _ C (‖((normalizedChartFactor g).toReal)⁻¹‖ * B / 2)
    1 zero_lt_one hc
  intro t ht
  rw [oneFormHeatRealColumn_pos hRic d t ht.1]
  exact (P.one_spectral_error_bound E hpair hRic d he B hB t ht l).trans_eq (by ring)

theorem HeatNormalParametrixData.oneTrace_error_tendsto
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D)
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o)) (he : e.base ∈ (chartAt FourSpace c).source)
    (hpair : ∀ t l (v : smoothCovariantFields M 1),
      inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
        inner ℝ (P.oneOperatorColumn E t l) (smoothOneFormL2Linear v))
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.oneResidual E t l‖ ≤ B * t) :
    Tendsto (fun t => oneFormHeatRealDiagonal hRic d (t + t) e.base -
      ∑ l : Fin 4, ‖P.oneNormalizedColumn E t l‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hsum : Tendsto (fun t => ∑ l : Fin 4,
      (‖P.oneNormalizedColumn E t l‖ ^ 2 - ‖oneFormHeatRealColumn hRic d t e l‖ ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ
      (fun l _ => P.oneColumn_square_error_tendsto E hRic d he hpair B hB l)
  have hn : Tendsto (fun t => -(∑ l : Fin 4,
      (‖P.oneNormalizedColumn E t l‖ ^ 2 - ‖oneFormHeatRealColumn hRic d t e l‖ ^ 2)))
      (𝓝[>] 0) (𝓝 0) := by simpa only [neg_zero] using hsum.neg
  apply hn.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [oneFormHeatRealDiagonal_columns hRic d t ht e, Finset.sum_sub_distrib, neg_sub]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual diagonal heat trace differs by a vanishing quantity from
the six squared L2 norms of the constructed normal parametrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter
open scoped ContDiff Manifold _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.column_square_error_tendsto
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D)
    (hRic : RicciThree g) (he : e.base ∈ (chartAt FourSpace c).source)
    (hgen : ∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t)
    (l : Fin 6) :
    Tendsto (fun t => ‖P.normalizedColumn E t l‖ ^ 2 -
      ‖twoFormHeatRealColumn (o := o) hRic t e l‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, _hC, hc⟩ := P.normalizedColumn_growth E l
  apply heat_norm_square_error_tendsto _ _ C (‖((normalizedChartFactor g).toReal)⁻¹‖ * B / 2)
    1 zero_lt_one hc
  intro t ht
  rw [twoFormHeatRealColumn_pos hRic t ht.1]
  exact (P.spectral_error_bound E hRic he hgen B hB t ht l).trans_eq (by ring)

theorem HeatNormalParametrixData.trace_error_tendsto
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D)
    (hRic : RicciThree g) (he : e.base ∈ (chartAt FourSpace c).source)
    (hgen : ∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t) :
    Tendsto (fun t => twoFormHeatRealTrace (o := o) hRic (t + t) e.base -
      ∑ l : Fin 6, ‖P.normalizedColumn E t l‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hsum : Tendsto (fun t => ∑ l : Fin 6,
      (‖P.normalizedColumn E t l‖ ^ 2 - ‖twoFormHeatRealColumn (o := o) hRic t e l‖ ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ
      (fun l _ => P.column_square_error_tendsto E hRic he hgen B hB l)
  have hn : Tendsto (fun t => -(∑ l : Fin 6,
      (‖P.normalizedColumn E t l‖ ^ 2 - ‖twoFormHeatRealColumn (o := o) hRic t e l‖ ^ 2)))
      (𝓝[>] 0) (𝓝 0) := by simpa only [neg_zero] using hsum.neg
  apply hn.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [twoFormHeatRealTrace_columns hRic t ht e, Finset.sum_sub_distrib, neg_sub]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The leading small-time coefficient of the actual scalar heat
diagonal, with the chart-volume normalization retained explicitly. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatScalarChartData.polynomial_weight_zero (P : HeatScalarChartData D) :
    frameExponentialJacobian g o e 0 * (P.polynomial 0 0) ^ 2 = 1 := by
  rw [frameExponentialJacobian_zero, one_mul]
  simp only [HeatScalarChartData.polynomial, fourHeatPolynomial,
    zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_pow (by norm_num : (3 : ℕ) ≠ 0), add_zero, P.cutoff_zero, one_mul]
  change P.extension.scalarAmplitude 0 0 ^ 2 = 1
  rw [P.extension.scalarAmplitude_zero, one_pow]

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem HeatScalarChartData.normalizedColumn_scaled_limit (P : HeatScalarChartData D) :
    Tendsto (fun t => t ^ 2 * ‖P.normalizedColumn t‖ ^ 2) (𝓝[>] 0)
      (𝓝 (((normalizedChartFactor g).toReal)⁻¹ * (1 / (64 * Real.pi ^ 2)))) := by
  let W := fun t x => frameExponentialJacobian g o e x * (P.polynomial t x) ^ 2
  have hP : Continuous (fun z : ℝ × FourSpace => P.polynomial z.1 z.2) :=
    (P.cutoff_regular.continuous.comp continuous_snd).mul
      (fourHeatPolynomial_joint_continuous _
        (fun m => (P.extension.scalarAmplitude_regular m (by omega)).continuous))
  have hW : Continuous (fun z : ℝ × FourSpace => W z.1 z.2) :=
    ((frameExponentialJacobian_continuous g o e).comp continuous_snd).mul (hP.pow 2)
  obtain ⟨B, _hB, hb⟩ := P.polynomial_weight_bound
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖W t x‖ ≤ B := by
    intro t ht x
    rw [Real.norm_of_nonneg (mul_nonneg (frameExponentialJacobian_nonneg g o e x) (sq_nonneg _))]
    exact hb t ht x
  have h := fourHeatGaussian_square_family_limit W hW B 1 zero_lt_one hbound
  have hz : W 0 0 = 1 := P.polynomial_weight_zero
  rw [hz, mul_one] at h
  apply (tendsto_const_nhds.mul h).congr'
  exact Eventually.of_forall fun t => by
    change ((normalizedChartFactor g).toReal)⁻¹ *
      (t ^ 2 * ∫ x, fourHeatGaussian t x ^ 2 * W t x) = t ^ 2 * ‖P.normalizedColumn t‖ ^ 2
    rw [P.normalizedColumn_gaussian_integral]
    dsimp only [W]
    ring

variable [SecondCountableTopology M] (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem scalarHeat_leading_pointwise_limit (hRic : RicciThree g) (x : M) :
    Tendsto (fun t => t ^ 2 * scalarHeatRealDiagonal g o d (t + t) x) (𝓝[>] 0)
      (𝓝 (((normalizedChartFactor g).toReal)⁻¹ * (1 / (64 * Real.pi ^ 2)))) := by
  obtain ⟨D⟩ := exists_heatNormalFrameData g o x ⟨x, o.frame x⟩ (mem_chart_source FourSpace x)
  obtain ⟨P, ha, hb, hd, B, _hB, hbound⟩ := exists_heatScalarGlobalResidual D
    (mem_chart_source FourSpace x) hRic (o.frame_positive x)
  have hdiff := (P.column_square_error_tendsto d ha hb hd B hbound).neg
  have ht : Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_id.mono_left nhdsWithin_le_nhds).pow 2 :
      Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ 2)))
  have h := (ht.mul hdiff).add P.normalizedColumn_scaled_limit
  simp only [neg_zero, mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t hpos
  rw [scalarHeatRealDiagonal_columns g o d t hpos x]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform squared-norm errors for finite families of actual heat columns. -/
namespace PositiveEinsteinFour.Geometry
open Set
open scoped BigOperators
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem heat_norm_square_error_uniform (x y : V) (C D t : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (ht : t ∈ Ioc (0 : ℝ) 1)
    (hx : ‖x‖ ≤ C / t) (hxy : ‖x - y‖ ≤ D * t ^ 2) :
    ‖‖x‖ ^ 2 - ‖y‖ ^ 2‖ ≤ 2 * C * D + D ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using
    heat_inner_error_uniform x y x y C D t hC hD ht hx hx hxy hxy

theorem heat_sum_norm_square_error_uniform {ι : Type*} [Fintype ι]
    (x y : ι → V) (C D t : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (ht : t ∈ Ioc (0 : ℝ) 1)
    (hx : ∀ l, ‖x l‖ ≤ C / t) (hxy : ∀ l, ‖x l - y l‖ ≤ D * t ^ 2) :
    ‖(∑ l, ‖x l‖ ^ 2) - (∑ l, ‖y l‖ ^ 2)‖ ≤
      (Fintype.card ι : ℝ) * (2 * C * D + D ^ 2) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ l, ‖‖x l‖ ^ 2 - ‖y l‖ ^ 2‖ := norm_sum_le _ _
    _ ≤ ∑ _ : ι, (2 * C * D + D ^ 2) := Finset.sum_le_sum fun l _ =>
      heat_norm_square_error_uniform (x l) (y l) C D t hC hD ht (hx l) (hxy l)
    _ = _ := by simp [mul_add]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The common actual one-form columns have uniform quadratic spectral error. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem heatUniformOneSpectral (F : HeatFamilyOneCoefficients) (r : ℝ) (hr : 0 < r)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    ∃ C ≥ (0 : ℝ), ∃ D ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K →
      (∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖(N.normal.parametrixData hr).oneNormalizedColumn N.one t l‖ ≤ C / t) ∧
      (e ∈ o.positive → ∀ (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 4),
        ‖(N.normal.parametrixData hr).oneNormalizedColumn N.one t l -
          oneFormHeatFrameColumn hRic d t.toNNReal (Real.toNNReal_pos.mpr ht.1) e l‖ ≤ D * t ^ 2) := by
  let χ : FourSpace → ℝ := heatNormalChartBump r hr
  have hχs : tsupport χ ⊆ ball (0 : FourSpace) r := by
    rw [(heatNormalChartBump r hr).tsupport_eq]
    exact closedBall_subset_ball (by change r / 2 < r; linarith)
  have hχb (x : FourSpace) : |χ x| ≤ 1 := by
    rw [abs_of_nonneg (heatNormalChartBump r hr).nonneg]
    exact (heatNormalChartBump r hr).le_one
  obtain ⟨B, hB, hb⟩ := heatUniformOneCutoffResidual F r K hK χ
    (heatNormalChartBump r hr).contDiff (heatNormalChartBump r hr).hasCompactSupport
    hχs hχb (r / 4) (by positivity)
    (fun x hx => (heatNormalChartBump r hr).one_of_mem_closedBall (ball_subset_closedBall hx)) hRic
  obtain ⟨C, hC, hc⟩ := heatUniformOneColumn_growth (g := g) (o := o) (c := c) F r hr K hK
  refine ⟨C, hC, ‖((normalizedChartFactor g).toReal)⁻¹‖ * (4 * B) / 2, by positivity, ?_⟩
  intro e N hq
  refine ⟨hc e N hq, ?_⟩
  intro he t ht l
  let P := N.normal.parametrixData hr
  have hres (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (k : Fin 4) :
      ‖P.oneResidual N.one s k‖ ≤ (4 * B) * s := by
    exact (P.oneResidual_norm_le N.one B hB s hs.1 (hb e N hq he s hs) k).trans_eq (by ring)
  have hec : e.base ∈ (chartAt FourSpace c).source := by
    simpa only [frameExponential_zero] using N.normal.exponential_source 0 (mem_ball_self hr)
  exact (P.one_spectral_error_bound N.one (N.parametrixData_one_pairing hr hRic)
    hRic d hec (4 * B) hres t ht l).trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A uniform density-weighted scalar polynomial bound over the actual frame family. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section

def heatFamilyScalarPolynomial (E : HeatFamilySmoothCoefficients) (χ : FourSpace → ℝ)
    (t : ℝ) (z : HeatRadialFrameSpace) : ℝ :=
  χ z.1 * fourHeatPolynomial (fun m x => E.scalarAmplitude m (x, z.2)) t z.1

theorem heatFamilyScalarPolynomial_continuous (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) :
    Continuous (fun z : ℝ × HeatRadialFrameSpace => heatFamilyScalarPolynomial E χ z.1 z.2) :=
  (hχ.comp (continuous_fst.comp continuous_snd)).mul
    (heatFamilyPolynomial_continuous _ (fun m => (E.scalarAmplitude_regular m (by omega)).continuous))

theorem heatFamilyScalarPolynomial_weight_bound (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ B ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      (E.U (x, q) ^ 2)⁻¹ * (heatFamilyScalarPolynomial E χ t (x, q)) ^ 2 ≤ B := by
  let W := fun z : ℝ × HeatRadialFrameSpace => (E.U z.2 ^ 2)⁻¹ *
    (heatFamilyScalarPolynomial E χ z.1 z.2) ^ 2
  have hW : Continuous W :=
    (((E.U_regular.continuous.comp continuous_snd).pow 2).inv₀
      (fun z => pow_ne_zero 2 (E.U_pos z.2).ne')).mul
      ((heatFamilyScalarPolynomial_continuous E χ hχ).pow 2)
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod (hc.prod hK)).bddAbove_image hW.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro q hq t ht x
  by_cases hx : x ∈ tsupport χ
  · exact (hB ⟨(t, (x, q)), ⟨ht, hx, hq⟩, rfl⟩).trans (le_max_left _ _)
  · simp only [heatFamilyScalarPolynomial, image_eq_zero_of_notMem_tsupport hx,
      zero_mul, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    exact le_max_right _ _

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonEulerMember.scalarPolynomial_family (N : HeatCommonEulerMember g o c F r e)
    (hr : 0 < r) (t : ℝ) (x : FourSpace) :
    (N.scalarData hr).polynomial t x =
      heatFamilyScalarPolynomial F.base (heatNormalChartBump r hr) t (x, frameCoordinateState g c e) := by
  change (heatNormalChartBump r hr) x * fourHeatPolynomial
    (fun (m : Fin 4) y => N.normal.extension.base.scalarAmplitude m y) t x = _
  have hu : (fun (m : Fin 4) y => N.normal.extension.base.scalarAmplitude m y) =
      (fun (m : Fin 4) y => F.base.scalarAmplitude m (y, frameCoordinateState g c e)) := by
    funext m y
    exact congrFun (N.scalar_amplitude_family m (by omega)) y
  rw [hu]
  rfl

theorem heatUniformScalarPolynomial_weight_bound (F : HeatFamilyOneCoefficients)
    (r : ℝ) (hr : 0 < r) (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ B ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K → ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      frameExponentialJacobian g o e x * ((N.scalarData hr).polynomial t x) ^ 2 ≤ B := by
  let χ : FourSpace → ℝ := heatNormalChartBump r hr
  have hs : tsupport χ ⊆ ball (0 : FourSpace) r := by
    rw [(heatNormalChartBump r hr).tsupport_eq]
    exact closedBall_subset_ball (by change r / 2 < r; linarith)
  obtain ⟨B, hB, hb⟩ := heatFamilyScalarPolynomial_weight_bound F.base χ
    (heatNormalChartBump r hr).continuous (heatNormalChartBump r hr).hasCompactSupport K hK
  refine ⟨B, hB, ?_⟩
  intro e N hq t ht x
  by_cases hx : x ∈ tsupport χ
  · have hh := heatNormalLeadingAmplitude_normalization g o e x
      (Real.sqrt_pos.mpr (N.normal.metric_pos x (hs hx)))
    rw [← (N.normal.actual x (hs hx)).2.2.2.2, N.normal.U_family] at hh
    rw [eq_inv_of_mul_eq_one_right hh, N.scalarPolynomial_family]
    exact hb _ hq t ht x
  · rw [N.scalarPolynomial_family]
    have hz : (heatNormalChartBump r hr) x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp only [heatFamilyScalarPolynomial, hz,
      zero_mul, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    exact hB

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar transport residual is the common last coefficient throughout the ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonEulerMember.scalar_amplitude_transport (N : HeatCommonEulerMember g o c F r e)
    (hRic : RicciThree g) (he : e ∈ o.positive) (x : FourSpace) (hx : x ∈ ball 0 r)
    (m : ℕ) (hm : m ≤ 2) :
    fourHeatRadialTransport (N.normal.extension.base.a x) (N.normal.extension.base.b x)
      (N.normal.extension.base.scalarAmplitude (m + 1)) x +
      (m + 1 : ℝ) * N.normal.extension.base.scalarAmplitude (m + 1) x =
    -fourHeatLocalOperator (N.normal.extension.base.a x) (N.normal.extension.base.b x) 0
      (N.normal.extension.base.scalarAmplitude m) x := by
  obtain ⟨hrow, hcol, _, hU, _⟩ := N.normal.transport hRic he x hx
  let A := N.normal.extension.base
  exact fourHeatCoefficient_transport m A.a A.b (fun _ => 0) A.U x
    (A.U_regular.of_le (by norm_num)) (fun y => (A.U_pos y).ne')
    (fun i j => (A.a_regular i j).of_le (by norm_num))
    (fun i => (A.b_regular i).of_le (by norm_num)) contDiff_const
    ((A.scalarAmplitude_regular m (by omega)).of_le (by norm_num)) hrow hcol hU

theorem HeatCommonEulerMember.scalar_parametrix_residual (N : HeatCommonEulerMember g o c F r e)
    (hRic : RicciThree g) (he : e ∈ o.positive) (x : FourSpace) (hx : x ∈ ball 0 r)
    (t : ℝ) (ht : 0 < t) :
    deriv (fun s => N.normal.extension.base.scalarParametrix s x) t +
      fourHeatLocalOperator (N.normal.extension.base.a x) (N.normal.extension.base.b x) 0
        (N.normal.extension.base.scalarParametrix t) x =
    fourHeatGaussian t x * t ^ 3 * F.base.scalarLastCoefficient (x, frameCoordinateState g c e) := by
  obtain ⟨_, _, heik, hU, _⟩ := N.normal.transport hRic he x hx
  let A := N.normal.extension.base
  have h := fourHeatPolynomial_gaussian_residual (A.a x) (A.b x) 0
    (fun m : Fin 4 => A.scalarAmplitude m)
    (fun m => (A.scalarAmplitude_regular m (by omega)).of_le (by norm_num)) t ht x heik hU
    (by simpa using N.scalar_amplitude_transport hRic he x hx 0 (by omega))
    (by convert N.scalar_amplitude_transport hRic he x hx 1 (by omega) using 1 <;> norm_num [A])
    (by convert N.scalar_amplitude_transport hRic he x hx 2 (by omega) using 1 <;> norm_num [A])
  refine h.trans ?_
  congr 1
  change fourHeatLocalOperator (N.normal.extension.base.a x) (N.normal.extension.base.b x) 0
    (N.normal.extension.base.scalarAmplitude 3) x = _
  rw [N.scalar_amplitude_family 3 (by omega), N.normal.a_family, N.normal.b_family]
  exact (heatFamilyScalarOperator_slice F.base.a F.base.b _
    ((F.base.scalarAmplitude_regular 3 (by omega)).of_le (by norm_num)) _).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Degree-two spectral error for the same common Euler family. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem heatUniformTwoSpectral (F : HeatFamilyOneCoefficients) (r : ℝ) (hr : 0 < r)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) (hRic : RicciThree g) :
    ∃ C ≥ (0 : ℝ), ∃ D ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K →
      (∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖(N.normal.parametrixData hr).normalizedColumn N.normal.extension t l‖ ≤ C / t) ∧
      (e ∈ o.positive → ∀ (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 6),
        ‖(N.normal.parametrixData hr).normalizedColumn N.normal.extension t l -
          twoFormHeatFrameColumn hRic t.toNNReal (Real.toNNReal_pos.mpr ht.1) e l‖ ≤ D * t ^ 2) := by
  let χ : FourSpace → ℝ := heatNormalChartBump r hr
  have hχs : tsupport χ ⊆ ball (0 : FourSpace) r := by
    rw [(heatNormalChartBump r hr).tsupport_eq]
    exact closedBall_subset_ball (by change r / 2 < r; linarith)
  have hχb (x : FourSpace) : |χ x| ≤ 1 := by
    rw [abs_of_nonneg (heatNormalChartBump r hr).nonneg]
    exact (heatNormalChartBump r hr).le_one
  obtain ⟨B, hB, hb⟩ := heatUniformCutoffResidual F.base r K hK χ
    (heatNormalChartBump r hr).contDiff (heatNormalChartBump r hr).hasCompactSupport
    hχs hχb (r / 4) (by positivity)
    (fun x hx => (heatNormalChartBump r hr).one_of_mem_closedBall (ball_subset_closedBall hx)) hRic
  obtain ⟨C, hC, hc⟩ := heatUniformColumn_growth (g := g) (o := o) (c := c) F.base r hr K hK
  refine ⟨C, hC, ‖((normalizedChartFactor g).toReal)⁻¹‖ * (6 * B) / 2, by positivity, ?_⟩
  intro e N hq
  refine ⟨hc e N.normal hq, ?_⟩
  intro he t ht l
  let P := N.normal.parametrixData hr
  have hres (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (k : Fin 6) :
      ‖P.residual N.normal.extension s k‖ ≤ (6 * B) * s := by
    exact P.residual_norm_le N.normal.extension s hs.1 B hB (hb e N.normal hq he s hs) k
  have hec : e.base ∈ (chartAt FourSpace c).source := by
    simpa only [frameExponential_zero] using N.normal.exponential_source 0 (mem_ball_self hr)
  exact (P.spectral_error_bound N.normal.extension hRic hec
    (N.normal.parametrixData_generator hr hRic) (6 * B) hres t ht l).trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual spectral diagonal is approximated by an explicit normal
Gaussian integral with the correct probability-volume normalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped ContDiff Manifold _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.oneColumn_norm_sq_integral
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D) (t : ℝ) (l : Fin 4) :
    ‖P.oneColumn E t l‖ ^ 2 = (normalizedChartFactor g).toReal *
      ∫ x, frameExponentialJacobian g o e x * ‖heatNormalOneCutoffColumn E P.cutoff t l x‖ ^ 2 :=
  heatNormalOneAmplitudeL2_norm_sq_integral P.chart P.exponential P.in_chart P.point_regular
    P.inside_radius (heatNormalOneCutoffColumn E P.cutoff t l)
    ((heatNormalOneCutoffColumn_regular E P.cutoff P.cutoff_regular t l).of_le (by norm_num))
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalOneCutoffColumn_support E P.cutoff t l))
    ((heatNormalOneCutoffColumn_support E P.cutoff t l).trans P.cutoff_support)

theorem HeatNormalParametrixData.oneNormalizedColumn_norm_sq_integral
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D) (t : ℝ) (l : Fin 4) :
    ‖P.oneNormalizedColumn E t l‖ ^ 2 = ((normalizedChartFactor g).toReal)⁻¹ *
      ∫ x, frameExponentialJacobian g o e x * ‖heatNormalOneCutoffColumn E P.cutoff t l x‖ ^ 2 := by
  have he : P.oneNormalizedColumn E t l = ((normalizedChartFactor g).toReal)⁻¹ • P.oneColumn E t l := rfl
  rw [he, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, P.oneColumn_norm_sq_integral E t l]
  have hn := (normalizedChartFactor_toReal_pos g).ne'
  field_simp

theorem HeatNormalParametrixData.oneNormalizedColumn_gaussian_integral
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D) (t : ℝ) (l : Fin 4) :
    ‖P.oneNormalizedColumn E t l‖ ^ 2 = ((normalizedChartFactor g).toReal)⁻¹ *
      ∫ x, fourHeatGaussian t x ^ 2 * (frameExponentialJacobian g o e x *
        ‖heatNormalOnePolynomialColumn E P.cutoff t l x‖ ^ 2) := by
  rw [P.oneNormalizedColumn_norm_sq_integral]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [heatNormalOneCutoffColumn_gaussian, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

variable [SecondCountableTopology M] [PreconnectedSpace M]

theorem HeatNormalParametrixData.oneTrace_gaussian_error_tendsto
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D)
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o)) (he : e.base ∈ (chartAt FourSpace c).source)
    (hpair : ∀ t l (v : smoothCovariantFields M 1),
      inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
        inner ℝ (P.oneOperatorColumn E t l) (smoothOneFormL2Linear v))
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.oneResidual E t l‖ ≤ B * t) :
    Tendsto (fun t => oneFormHeatRealDiagonal hRic d (t + t) e.base -
      ((normalizedChartFactor g).toReal)⁻¹ * ∑ l : Fin 4,
        ∫ x, fourHeatGaussian t x ^ 2 * (frameExponentialJacobian g o e x *
          ‖heatNormalOnePolynomialColumn E P.cutoff t l x‖ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
  have h := P.oneTrace_error_tendsto E hRic d he hpair B hB
  simpa only [P.oneNormalizedColumn_gaussian_integral E, Finset.mul_sum] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual spectral diagonal is approximated by an explicit normal
Gaussian integral with the correct probability-volume normalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped ContDiff Manifold _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.column_norm_sq_integral
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (t : ℝ) (l : Fin 6) :
    ‖P.column E t l‖ ^ 2 = (normalizedChartFactor g).toReal *
      ∫ x, frameExponentialJacobian g o e x * ‖heatNormalCutoffColumn E P.cutoff t l x‖ ^ 2 :=
  heatNormalAmplitudeL2_norm_sq_integral P.chart P.exponential P.in_chart P.point_regular
    P.inside_radius (heatNormalCutoffColumn E P.cutoff t l)
    (heatNormalCutoffColumn_regular E P.cutoff (P.cutoff_regular.of_le (by norm_num)) t l)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalCutoffColumn_support E P.cutoff t l))
    ((heatNormalCutoffColumn_support E P.cutoff t l).trans P.cutoff_support)

theorem HeatNormalParametrixData.normalizedColumn_norm_sq_integral
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (t : ℝ) (l : Fin 6) :
    ‖P.normalizedColumn E t l‖ ^ 2 = ((normalizedChartFactor g).toReal)⁻¹ *
      ∫ x, frameExponentialJacobian g o e x * ‖heatNormalCutoffColumn E P.cutoff t l x‖ ^ 2 := by
  have he : P.normalizedColumn E t l = ((normalizedChartFactor g).toReal)⁻¹ • P.column E t l := rfl
  rw [he, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, P.column_norm_sq_integral E t l]
  have hn := (normalizedChartFactor_toReal_pos g).ne'
  field_simp

theorem HeatNormalParametrixData.normalizedColumn_gaussian_integral
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (t : ℝ) (l : Fin 6) :
    ‖P.normalizedColumn E t l‖ ^ 2 = ((normalizedChartFactor g).toReal)⁻¹ *
      ∫ x, fourHeatGaussian t x ^ 2 * (frameExponentialJacobian g o e x *
        ‖heatNormalPolynomialColumn E P.cutoff t l x‖ ^ 2) := by
  rw [P.normalizedColumn_norm_sq_integral]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [heatNormalCutoffColumn_gaussian, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

theorem HeatNormalParametrixData.trace_gaussian_error_tendsto
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D)
    (hRic : RicciThree g) (he : e.base ∈ (chartAt FourSpace c).source)
    (hgen : ∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t) :
    Tendsto (fun t => twoFormHeatRealTrace (o := o) hRic (t + t) e.base -
      ((normalizedChartFactor g).toReal)⁻¹ * ∑ l : Fin 6,
        ∫ x, fourHeatGaussian t x ^ 2 * (frameExponentialJacobian g o e x *
          ‖heatNormalPolynomialColumn E P.cutoff t l x‖ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
  have h := P.trace_error_tendsto E hRic he hgen B hB
  simpa only [P.normalizedColumn_gaussian_integral E, Finset.mul_sum] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform inverse-time growth of the actual scalar normal columns. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter MeasureTheory
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem heatUniformScalar_square_integral_bound (F : HeatFamilyOneCoefficients)
    (r : ℝ) (hr : 0 < r) (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K → ∀ t ∈ Ioc (0 : ℝ) 1,
      (∫ x, frameExponentialJacobian g o e x *
        ((N.scalarData hr).extension.scalarCutoff (N.scalarData hr).cutoff t x) ^ 2) ≤ C / t ^ 2 := by
  obtain ⟨B, hB, hbound⟩ := heatUniformScalarPolynomial_weight_bound (g := g) (o := o) (c := c) F r hr K hK
  refine ⟨B / (64 * Real.pi ^ 2), by positivity, ?_⟩
  intro e N hq t ht
  let P := N.scalarData hr
  have hp (x : FourSpace) : frameExponentialJacobian g o e x *
      (P.extension.scalarCutoff P.cutoff t x) ^ 2 ≤ B * fourHeatGaussian t x ^ 2 := by
    rw [P.cutoff_gaussian, mul_pow]
    calc
      _ = (frameExponentialJacobian g o e x * (P.polynomial t x) ^ 2) *
          fourHeatGaussian t x ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hbound e N hq t ⟨ht.1.le, ht.2⟩ x) (sq_nonneg _)
  have hi : Integrable (fun x : FourSpace => B * fourHeatGaussian t x ^ 2) :=
    (fourHeatGaussian_square_integrable t ht.1).const_mul B
  have hc : Continuous (fun x => frameExponentialJacobian g o e x *
      (P.extension.scalarCutoff P.cutoff t x) ^ 2) :=
    (frameExponentialJacobian_continuous g o e).mul
      ((P.extension.scalarCutoff_regular P.cutoff P.cutoff_regular t).continuous.pow 2)
  have hfi : Integrable (fun x => frameExponentialJacobian g o e x *
      (P.extension.scalarCutoff P.cutoff t x) ^ 2) :=
    hi.mono' hc.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (frameExponentialJacobian_nonneg g o e x) (sq_nonneg _))]
      exact hp x)
  calc
    _ ≤ ∫ x : FourSpace, B * fourHeatGaussian t x ^ 2 := integral_mono hfi hi hp
    _ = _ := by rw [integral_const_mul, fourHeatGaussian_square_mass t ht.1]; ring

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem heatUniformScalarColumn_growth (F : HeatFamilyOneCoefficients)
    (r : ℝ) (hr : 0 < r) (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K → ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖(N.scalarData hr).column t‖ ≤ C / t := by
  obtain ⟨B, hB, hbound⟩ := heatUniformScalar_square_integral_bound (g := g) (o := o) (c := c) F r hr K hK
  let K := (normalizedChartFactor g).toReal * B
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K + 1, by positivity, ?_⟩
  intro e N hq t ht
  let P := N.scalarData hr
  have hn : ‖P.column t‖ ^ 2 ≤ K / t ^ 2 := by
    rw [P.column_norm_sq_integral]
    exact (mul_le_mul_of_nonneg_left (hbound e N hq t ht) (by positivity)).trans_eq (by dsimp [K]; ring)
  have hs : (‖P.column t‖ * t) ^ 2 ≤ K := by
    calc
      _ = ‖P.column t‖ ^ 2 * t ^ 2 := by ring
      _ ≤ (K / t ^ 2) * t ^ 2 := mul_le_mul_of_nonneg_right hn (sq_nonneg t)
      _ = K := by field_simp [ht.1.ne']
  apply (le_div_iff₀ ht.1).mpr
  nlinarith [sq_nonneg K, norm_nonneg (P.column t)]

theorem heatUniformScalarNormalizedColumn_growth (F : HeatFamilyOneCoefficients)
    (r : ℝ) (hr : 0 < r) (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K → ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖(N.scalarData hr).normalizedColumn t‖ ≤ C / t := by
  obtain ⟨C, hC, hc⟩ := heatUniformScalarColumn_growth (g := g) (o := o) (c := c) F r hr K hK
  refine ⟨‖((normalizedChartFactor g).toReal)⁻¹‖ * C, by positivity, ?_⟩
  intro e N hq t ht
  change ‖((normalizedChartFactor g).toReal)⁻¹ • (N.scalarData hr).column t‖ ≤ _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (hc e N hq t ht) (norm_nonneg _)).trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A common O(t) bound for the genuine scalar cutoff residual. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem heatUniformScalarCutoffResidual (F : HeatFamilyOneCoefficients) (r : ℝ) (hr : 0 < r)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) (hRic : RicciThree g) :
    ∃ B ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K → e ∈ o.positive → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x,
        |(N.scalarData hr).residualAmplitude t x| ≤ B * t := by
  let χ : FourSpace → ℝ := heatNormalChartBump r hr
  obtain ⟨A, hApos, hA⟩ := F.base.scalarLastCoefficient_compact_bound
    (tsupport χ ×ˢ K) ((heatNormalChartBump r hr).hasCompactSupport.prod hK)
  obtain ⟨B₁, hB₁, hb₁⟩ := heatFamilyScalarCommutator_gaussian_bound F.base χ
    (heatNormalChartBump r hr).contDiff
    (heatNormalChartBump r hr).hasCompactSupport K hK (r / 4) (by positivity)
    (fun x hx => (heatNormalChartBump r hr).one_of_mem_closedBall (ball_subset_closedBall hx))
  let B₀ := A / (16 * Real.pi ^ 2)
  have hB₀ : 0 ≤ B₀ := by positivity
  refine ⟨B₀ + B₁, add_nonneg hB₀ hB₁, ?_⟩
  intro e N hq he t ht x
  let P := N.scalarData hr
  let E := P.extension
  let u : Fin 4 → FourSpace → Fin 6 → ℝ := fun m y _ => E.scalarAmplitude m y
  have hu (m : Fin 4) (q : Fin 6) : ContDiff ℝ 2 (fun y => u m y q) :=
    (E.scalarAmplitude_regular m (by omega)).of_le (by norm_num)
  have hs : tsupport P.cutoff ⊆ ball 0 r := by
    exact P.cutoff_support.trans (by
      rw [show P.chart = (N.normal.parametrixData hr).chart from rfl, N.normal.parametrixData_source hr])
  by_cases hx : x ∈ tsupport P.cutoff
  · have hsym (i j : Fin 4) : E.a x i j = E.a x j i := by
      rw [(N.scalarData_actual hr).1 x hx]
      exact congrFun (congrFun (heatNormalInverse_symm g o e x) j) i
    have hQ : |deriv (fun v => E.scalarParametrix v x) t +
        fourHeatLocalOperator (E.a x) (E.b x) 0 (E.scalarParametrix t) x| ≤ B₀ * t := by
      have hres := N.scalar_parametrix_residual hRic he x (hs hx) t ht.1
      change deriv (fun v => E.scalarParametrix v x) t +
        fourHeatLocalOperator (E.a x) (E.b x) 0 (E.scalarParametrix t) x = _ at hres
      rw [hres, abs_mul, abs_mul,
        abs_of_pos (fourHeatGaussian_pos t ht.1 x), abs_of_pos (pow_pos ht.1 3)]
      have hFx := hA (x, frameCoordinateState g c e) ⟨hx, hq⟩
      calc
        _ ≤ (fourHeatGaussian t x * t ^ 3) * A :=
          mul_le_mul_of_nonneg_left hFx
            (mul_nonneg (fourHeatGaussian_pos t ht.1 x).le (pow_nonneg ht.1.le 3))
        _ ≤ (fourHeatGaussian t 0 * t ^ 3) * A :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (fourHeatGaussian_le_diagonal t ht.1 x)
              (pow_nonneg ht.1.le 3)) hApos
        _ = B₀ * t := by
          have hg := fourHeatGaussian_diagonal_power 1 t ht.1
          norm_num only [Nat.reduceAdd, pow_one] at hg
          dsimp only [B₀]
          calc
            _ = A * (t ^ 3 * fourHeatGaussian t 0) := by ring
            _ = _ := by rw [hg]; ring
    have hcut := fourHeatLocalOperator_cutoff (E.a x) (E.b x) P.cutoff
      (E.scalarParametrix t) x hsym (P.cutoff_regular.contDiffAt.of_le (by norm_num))
      ((E.scalarParametrix_regular t).contDiffAt.of_le (by norm_num))
    have hscaled := fourHeatScaledCommutator_identity E.a E.b (fun _ => 0)
      P.cutoff u hu t ht.1 x 0
    have hz (i : Fin 4) (q : Fin 6) : (0 : Fin 4 → HeatMat6) i 0 q = 0 := rfl
    simp only [fourHeatBundlePolynomial, u, hz, zero_mul,
      Finset.sum_const_zero, add_zero] at hscaled
    have hdt : deriv (fun v => E.scalarParametrix v x) t =
        fourHeatGaussianPolynomialTime (fun m => E.scalarAmplitude m) t x :=
      (fourHeatGaussianPolynomial_hasDerivAt
        (fun m => E.scalarAmplitude m) t ht.1 x).deriv
    have hid : P.residualAmplitude t x =
        P.cutoff x * (deriv (fun v => E.scalarParametrix v x) t +
          fourHeatLocalOperator (E.a x) (E.b x) 0 (E.scalarParametrix t) x) +
        (fourHeatGaussian t x / t) *
          fourHeatScaledCommutator E.a E.b (fun _ => 0) P.cutoff u t x 0 := by
      change P.cutoff x * fourHeatGaussianPolynomialTime
        (fun m => E.scalarAmplitude m) t x +
        fourHeatLocalOperator (E.a x) (E.b x) 0
          (fun y => P.cutoff y * E.scalarParametrix t y) x = _
      rw [hcut, hdt]
      change fourHeatLocalOperator (E.a x) (E.b x) 0 P.cutoff x * E.scalarParametrix t x -
        2 * (∑ i, ∑ j, E.a x i j * partialDeriv P.cutoff i x *
          partialDeriv (E.scalarParametrix t) j x) = _ at hscaled
      linarith [hscaled]
    rw [hid]
    calc
      _ ≤ |P.cutoff x * (deriv (fun v => E.scalarParametrix v x) t +
          fourHeatLocalOperator (E.a x) (E.b x) 0 (E.scalarParametrix t) x)| +
          |(fourHeatGaussian t x / t) *
            fourHeatScaledCommutator E.a E.b (fun _ => 0) P.cutoff u t x 0| := abs_add_le _ _
      _ ≤ B₀ * t + B₁ * t := by
        apply add_le_add
        · rw [abs_mul]
          have hχ : |P.cutoff x| ≤ 1 := by
            change |(heatNormalChartBump r hr) x| ≤ 1
            rw [abs_of_nonneg (heatNormalChartBump r hr).nonneg]
            exact (heatNormalChartBump r hr).le_one
          exact (mul_le_mul hχ hQ (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
        · have hfamily : fourHeatScaledCommutator E.a E.b (fun _ => 0) P.cutoff u t x 0 =
              heatFamilyScalarCommutator F.base χ t (x, frameCoordinateState g c e) := by
            have hu' : u = fun (m : Fin 4) y _ => F.base.scalarAmplitude m (y, frameCoordinateState g c e) := by
              funext m y k
              exact congrFun (N.scalar_amplitude_family m (by omega)) y
            rw [hu']
            change fourHeatScaledCommutator N.normal.extension.base.a N.normal.extension.base.b _ _ _ _ _ _ = _
            rw [N.normal.a_family, N.normal.b_family]
            rfl
          rw [hfamily]
          exact hb₁ _ hq t ht x

      _ = _ := by ring
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (P.residualAmplitude_support t h)),
      abs_zero]
    exact mul_nonneg (add_nonneg hB₀ hB₁) ht.1.le


end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact normal-coordinate pairing of the actual normalized heat columns. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatSignedGram_columns (A : HeatMat6) :
    heatSignedGram A A = ∑ l, ∑ m, twoFormHodgeMatrix l m *
      inner ℝ (WithLp.toLp 2 (fun k => A k l) : TwoFormFour) (WithLp.toLp 2 (fun k => A k m)) := by
  simp only [heatSignedGram, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.column_inner_integral
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (t : ℝ) (l m : Fin 6) :
    inner ℝ (P.column E t l) (P.column E t m) = (normalizedChartFactor g).toReal *
      ∫ x, frameExponentialJacobian g o e x *
        inner ℝ (heatNormalCutoffColumn E P.cutoff t l x) (heatNormalCutoffColumn E P.cutoff t m x) :=
  heatNormalAmplitudeL2_inner_integral P.chart P.exponential P.in_chart P.point_regular
    P.inside_radius (heatNormalCutoffColumn E P.cutoff t l) (heatNormalCutoffColumn E P.cutoff t m)
    (heatNormalCutoffColumn_regular E P.cutoff (P.cutoff_regular.of_le (by norm_num)) t l)
    (heatNormalCutoffColumn_regular E P.cutoff (P.cutoff_regular.of_le (by norm_num)) t m)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) (heatNormalCutoffColumn_support E P.cutoff t l))
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) (heatNormalCutoffColumn_support E P.cutoff t m))
    ((heatNormalCutoffColumn_support E P.cutoff t l).trans P.cutoff_support)
    ((heatNormalCutoffColumn_support E P.cutoff t m).trans P.cutoff_support)

theorem HeatNormalParametrixData.normalizedColumn_inner_integral
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (t : ℝ) (l m : Fin 6) :
    inner ℝ (P.normalizedColumn E t l) (P.normalizedColumn E t m) = ((normalizedChartFactor g).toReal)⁻¹ *
      ∫ x, frameExponentialJacobian g o e x *
        inner ℝ (heatNormalCutoffColumn E P.cutoff t l x) (heatNormalCutoffColumn E P.cutoff t m x) := by
  change inner ℝ (((normalizedChartFactor g).toReal)⁻¹ • P.column E t l)
    (((normalizedChartFactor g).toReal)⁻¹ • P.column E t m) = _
  rw [real_inner_smul_left, real_inner_smul_right, P.column_inner_integral E t l m]
  have hn := (normalizedChartFactor_toReal_pos g).ne'
  field_simp

theorem HeatNormalParametrixData.normalizedColumn_gaussian_inner
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (t : ℝ) (l m : Fin 6) :
    inner ℝ (P.normalizedColumn E t l) (P.normalizedColumn E t m) = ((normalizedChartFactor g).toReal)⁻¹ *
      ∫ x, fourHeatGaussian t x ^ 2 * (frameExponentialJacobian g o e x *
        inner ℝ (heatNormalPolynomialColumn E P.cutoff t l x) (heatNormalPolynomialColumn E P.cutoff t m x)) := by
  rw [P.normalizedColumn_inner_integral]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [heatNormalCutoffColumn_gaussian, heatNormalCutoffColumn_gaussian,
      real_inner_smul_left, real_inner_smul_right]
    ring

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem heatNormalPolynomialColumn_zero (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 6) (x : FourSpace) (hx : χ x = 0) :
    heatNormalPolynomialColumn E χ t l x = 0 := by
  apply WithLp.ofLp_injective 2
  funext k
  change χ x * _ = 0
  rw [hx, zero_mul]

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem HeatNormalParametrixData.polynomial_pair_integrable
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (t : ℝ) (l m : Fin 6) :
    Integrable (fun x => fourHeatGaussian t x ^ 2 * (frameExponentialJacobian g o e x *
      inner ℝ (heatNormalPolynomialColumn E P.cutoff t l x) (heatNormalPolynomialColumn E P.cutoff t m x))) := by
  have hc (j : Fin 6) : Continuous (fun x => heatNormalPolynomialColumn E P.cutoff t j x) :=
    (heatNormalPolynomialColumn_continuous E P.cutoff P.cutoff_regular.continuous j).comp
      (continuous_const.prodMk continuous_id)
  apply (((fourHeatGaussian_continuous t).pow 2).mul
    ((frameExponentialJacobian_continuous g o e).mul ((hc l).inner (hc m)))).integrable_of_hasCompactSupport
  apply P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_tsupport P.cutoff)
  intro x hx
  by_contra hn
  have hz := image_eq_zero_of_notMem_tsupport hn
  apply hx
  change fourHeatGaussian t x ^ 2 * (frameExponentialJacobian g o e x *
    inner ℝ (heatNormalPolynomialColumn E P.cutoff t l x) (heatNormalPolynomialColumn E P.cutoff t m x)) = 0
  rw [heatNormalPolynomialColumn_zero E P.cutoff t l x hz, inner_zero_left, mul_zero, mul_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Leading diagonal asymptotic of the actual spectral two-form heat
kernel, with physical and normalized volume factors kept distinct. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped ContDiff Manifold _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem HeatNormalParametrixData.polynomial_weight_zero
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (l : Fin 6) :
    frameExponentialJacobian g o e 0 * ‖heatNormalPolynomialColumn E P.cutoff 0 l 0‖ ^ 2 = 1 := by
  have hU : E.base.U 0 = 1 :=
    E.base.U_near.self_of_nhds.trans (heatNormalLeadingAmplitude_zero g o e)
  rw [frameExponentialJacobian_zero, one_mul]
  simp only [heatNormalPolynomialColumn, PiLp.norm_sq_eq_of_L2, fourHeatPolynomial,
    zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_pow (by norm_num : (3 : ℕ) ≠ 0),
    add_zero, P.cutoff_zero, one_mul]
  simp only [Real.norm_eq_abs, sq_abs]
  change (∑ x : Fin 6, E.amplitude 0 0 x l ^ 2) = 1
  rw [E.amplitude_zero 0, hU]
  simp only [Matrix.smul_apply, smul_eq_mul, one_mul, Matrix.one_apply]
  simp

theorem HeatNormalParametrixData.normalizedColumn_scaled_limit
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (l : Fin 6) :
    Tendsto (fun t => t ^ 2 * ‖P.normalizedColumn E t l‖ ^ 2) (𝓝[>] 0)
      (𝓝 (((normalizedChartFactor g).toReal)⁻¹ * (1 / (64 * Real.pi ^ 2)))) := by
  let W := fun t x => frameExponentialJacobian g o e x *
    ‖heatNormalPolynomialColumn E P.cutoff t l x‖ ^ 2
  have hW : Continuous (fun z : ℝ × FourSpace => W z.1 z.2) :=
    ((frameExponentialJacobian_continuous g o e).comp continuous_snd).mul
      ((heatNormalPolynomialColumn_continuous E P.cutoff P.cutoff_regular.continuous l).norm.pow 2)
  obtain ⟨B, _hB, hb⟩ := heatNormalPolynomialColumn_weight_bound E P.cutoff
    P.cutoff_regular.continuous P.cutoff_compact l
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖W t x‖ ≤ B := by
    intro t ht x
    rw [Real.norm_of_nonneg (mul_nonneg (frameExponentialJacobian_nonneg g o e x) (sq_nonneg _))]
    exact hb t ht x
  have h := fourHeatGaussian_square_family_limit W hW B 1 zero_lt_one hbound
  have hz : W 0 0 = 1 := P.polynomial_weight_zero E l
  rw [hz, mul_one] at h
  apply (tendsto_const_nhds.mul h).congr'
  exact Eventually.of_forall fun t => by
    change ((normalizedChartFactor g).toReal)⁻¹ *
      (t ^ 2 * ∫ x, fourHeatGaussian t x ^ 2 * W t x) = t ^ 2 * ‖P.normalizedColumn E t l‖ ^ 2
    rw [P.normalizedColumn_gaussian_integral E t l]
    dsimp only [W]
    ring

theorem HeatNormalParametrixData.trace_scaled_limit
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D)
    (hRic : RicciThree g) (he : e.base ∈ (chartAt FourSpace c).source)
    (hgen : ∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t) :
    Tendsto (fun t => t ^ 2 * twoFormHeatRealTrace (o := o) hRic (t + t) e.base) (𝓝[>] 0)
      (𝓝 (6 * (((normalizedChartFactor g).toReal)⁻¹ * (1 / (64 * Real.pi ^ 2))))) := by
  have ht : Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_id.mono_left nhdsWithin_le_nhds).pow 2 :
      Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ 2)))
  have herr := ht.mul (P.trace_error_tendsto E hRic he hgen B hB)
  have hsum := tendsto_finsetSum Finset.univ (fun l _ => P.normalizedColumn_scaled_limit E l)
  have h := herr.add hsum
  simp only [mul_zero, zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h
  apply h.congr'
  exact Eventually.of_forall fun t => by
    change t ^ 2 * (twoFormHeatRealTrace hRic (t + t) e.base -
      ∑ l, ‖P.normalizedColumn E t l‖ ^ 2) +
      ∑ l, t ^ 2 * ‖P.normalizedColumn E t l‖ ^ 2 = _
    rw [← Finset.mul_sum]
    ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar members have uniform quadratic spectral error. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric MeasureTheory
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
local instance scalarUniform_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem heatUniformScalarSpectral (F : HeatFamilyOneCoefficients) (r : ℝ) (hr : 0 < r)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    ∃ C ≥ (0 : ℝ), ∃ D ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K →
      (∀ t ∈ Ioc (0 : ℝ) 1, ‖(N.scalarData hr).normalizedColumn t‖ ≤ C / t) ∧
      (e ∈ o.positive → ∀ (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1),
        ‖(N.scalarData hr).normalizedColumn t -
          scalarHeatColumn g o d t.toNNReal (Real.toNNReal_pos.mpr ht.1) e.base‖ ≤ D * t ^ 2) := by
  obtain ⟨B, hB, hb⟩ := heatUniformScalarCutoffResidual F r hr K hK hRic
  obtain ⟨C, hC, hc⟩ := heatUniformScalarNormalizedColumn_growth (g := g) (o := o) (c := c) F r hr K hK
  let L := ‖ContinuousMap.toLp (E := ℝ) 2 (normalizedVolume g) ℝ‖
  refine ⟨C, hC, ‖((normalizedChartFactor g).toReal)⁻¹‖ * (L * B) / 2, by dsimp [L]; positivity, ?_⟩
  intro e N hq
  refine ⟨hc e N hq, ?_⟩
  intro he t ht
  let P := N.scalarData hr
  obtain ⟨ha, hbb, hd⟩ := N.scalarData_actual hr
  have hres (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) : ‖P.residual s‖ ≤ (L * B) * s := by
    exact (P.residual_norm_le ha hbb hd s (B * s) (mul_nonneg hB hs.1.le)
      (hb e N hq he s hs)).trans_eq (by dsimp [L]; ring)
  exact (P.spectral_error_bound d ha hbb hd (L * B) hres t ht).trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The signed Gram integral of the actual normalized normal columns. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalPolynomialColumn_matrix (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 6) (x : FourSpace) :
    heatNormalPolynomialColumn E χ t l x =
      χ x • (WithLp.toLp 2 (fun k => heatNormalMatrixPolynomial E t x k l) : TwoFormFour) := by
  apply WithLp.ofLp_injective 2
  funext k
  exact congrArg (fun r : ℝ => χ x * r) (heatNormalMatrixPolynomial_component E t x k l).symm

theorem heatNormalPolynomialColumn_signed (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (x : FourSpace) :
    (∑ l, ∑ m, twoFormHodgeMatrix l m *
      inner ℝ (heatNormalPolynomialColumn E χ t l x) (heatNormalPolynomialColumn E χ t m x)) =
      χ x ^ 2 * heatSignedGram (heatNormalMatrixPolynomial E t x) (heatNormalMatrixPolynomial E t x) := by
  simp_rw [heatNormalPolynomialColumn_matrix, real_inner_smul_left, real_inner_smul_right]
  rw [heatSignedGram_columns]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  ring

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem HeatNormalParametrixData.signedColumn_integral
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (t : ℝ) :
    (∑ l, ∑ m, twoFormHodgeMatrix l m * inner ℝ (P.normalizedColumn E t l) (P.normalizedColumn E t m)) =
      ((normalizedChartFactor g).toReal)⁻¹ * ∫ x : FourSpace, fourHeatGaussian t x ^ 2 *
        (frameExponentialJacobian g o e x * P.cutoff x ^ 2 *
          heatSignedGram (heatNormalMatrixPolynomial E t x) (heatNormalMatrixPolynomial E t x)) := by
  let F := fun l m x => twoFormHodgeMatrix l m * (fourHeatGaussian t x ^ 2 *
    (frameExponentialJacobian g o e x * inner ℝ (heatNormalPolynomialColumn E P.cutoff t l x)
      (heatNormalPolynomialColumn E P.cutoff t m x)))
  have hF (l m : Fin 6) : Integrable (F l m) :=
    (P.polynomial_pair_integrable E t l m).const_mul _
  have he (l m : Fin 6) : twoFormHodgeMatrix l m *
      inner ℝ (P.normalizedColumn E t l) (P.normalizedColumn E t m) =
      ((normalizedChartFactor g).toReal)⁻¹ * ∫ x, F l m x := by
    rw [P.normalizedColumn_gaussian_inner E t l m]
    dsimp only [F]
    rw [integral_const_mul]
    ring
  simp_rw [he]
  simp only [← Finset.mul_sum]
  congr 1
  have hs (l : Fin 6) : (∑ m, ∫ y, F l m y) = ∫ y, ∑ m, F l m y :=
    (integral_finsetSum _ (fun m _ => hF l m)).symm
  simp_rw [hs]
  rw [← integral_finsetSum _ (fun l _ => integrable_finsetSum _ (fun m _ => hF l m))]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change (∑ l, ∑ m, F l m x) = _
    dsimp only [F]
    calc
      _ = fourHeatGaussian t x ^ 2 * frameExponentialJacobian g o e x *
          (∑ l, ∑ m, twoFormHodgeMatrix l m *
            inner ℝ (heatNormalPolynomialColumn E P.cutoff t l x)
              (heatNormalPolynomialColumn E P.cutoff t m x)) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        apply Finset.sum_congr rfl
        intro m _
        ring
      _ = _ := by rw [heatNormalPolynomialColumn_signed]; ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The three genuine compact column polynomials are one Euler polynomial. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

theorem heatEulerGram_columns (A : HeatEulerFiber) :
    heatEulerGram A A = 2 * A.1 ^ 2 -
      2 * ∑ l : Fin 4, ‖(WithLp.toLp 2 (fun k => A.2.1 k l) : FourSpace)‖ ^ 2 +
      ∑ l : Fin 6, ‖(WithLp.toLp 2 (fun k => A.2.2 k l) : TwoFormFour)‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, heatEulerGram, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatEulerChartData.polynomial_scalar (P : HeatEulerChartData D) (t : ℝ) (x : FourSpace) :
    P.scalar.polynomial t x = P.normal.cutoff x * (P.bundle.eulerPolynomial t x).1 := by
  change P.normal.cutoff x * fourHeatPolynomial
    (fun m => fourHeatCoefficient P.base.a P.base.b (fun _ => 0) P.base.U m) t x = _
  simp only [HeatNormalBundleExtension.eulerPolynomial, HeatNormalBundleExtension.eulerAmplitude,
    Prod.fst_add, fourHeatPolynomial]
  rfl

theorem HeatEulerChartData.polynomial_one (P : HeatEulerChartData D)
    (t : ℝ) (l : Fin 4) (x : FourSpace) :
    heatNormalOnePolynomialColumn P.bundle.oneCompanion P.normal.cutoff t l x =
      P.normal.cutoff x • (WithLp.toLp 2
        (fun k => (P.bundle.eulerPolynomial t x).2.1 k l) : FourSpace) := by
  apply WithLp.ofLp_injective 2
  funext k
  change P.normal.cutoff x * fourHeatPolynomial
    (fun m y => P.bundle.oneCompanion.amplitude m y k l) t x = _
  simp only [HeatNormalBundleExtension.eulerPolynomial, HeatNormalBundleExtension.eulerAmplitude,
    Prod.snd_add, Prod.fst_add, Matrix.add_apply, fourHeatPolynomial]
  rfl

theorem HeatEulerChartData.polynomial_two (P : HeatEulerChartData D)
    (t : ℝ) (l : Fin 6) (x : FourSpace) :
    heatNormalPolynomialColumn P.bundle P.normal.cutoff t l x =
      P.normal.cutoff x • (WithLp.toLp 2
        (fun k => (P.bundle.eulerPolynomial t x).2.2 k l) : TwoFormFour) := by
  rw [heatNormalPolynomialColumn_matrix]
  rfl

theorem HeatEulerChartData.polynomial_euler (P : HeatEulerChartData D) (t : ℝ) (x : FourSpace) :
    2 * (P.scalar.polynomial t x) ^ 2 -
      2 * (∑ l : Fin 4, ‖heatNormalOnePolynomialColumn P.bundle.oneCompanion P.normal.cutoff t l x‖ ^ 2) +
      (∑ l : Fin 6, ‖heatNormalPolynomialColumn P.bundle P.normal.cutoff t l x‖ ^ 2) =
    P.normal.cutoff x ^ 2 * heatEulerGram (P.bundle.eulerPolynomial t x)
      (P.bundle.eulerPolynomial t x) := by
  rw [heatEulerGram_columns, P.polynomial_scalar]
  simp_rw [P.polynomial_one, P.polynomial_two, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp only [← Finset.mul_sum]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The signed spectral diagonal inherits the actual local curvature limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped BigOperators ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormHeatRealSignedTrace (hRic : RicciThree g) (t : ℝ) (x : M) : ℝ :=
  if ht : 0 < t then
    twoFormFiberSignedTrace (twoFormHeatKernel (o := o) hRic t.toNNReal (Real.toNNReal_pos.mpr ht) x x)
  else 0

theorem twoFormHeatRealSignedTrace_columns (hRic : RicciThree g)
    (t : ℝ) (ht : 0 < t) (e : FrameBundle g) (he : e ∈ o.positive) :
    twoFormHeatRealSignedTrace (o := o) hRic (t + t) e.base =
      ∑ l, ∑ m, twoFormHodgeMatrix l m * inner ℝ
        (twoFormHeatRealColumn (o := o) hRic t e l) (twoFormHeatRealColumn (o := o) hRic t e m) := by
  simpa only [twoFormHeatRealSignedTrace, dite_eq_left (add_pos ht ht),
    twoFormHeatRealColumn, dite_eq_left ht, Real.toNNReal_add ht.le ht.le] using
    twoFormHeatKernel_signed_columns hRic t.toNNReal (Real.toNNReal_pos.mpr ht) e he

variable {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.column_inner_error_tendsto
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D)
    (hRic : RicciThree g) (he : e.base ∈ (chartAt FourSpace c).source)
    (hgen : ∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t)
    (l m : Fin 6) :
    Tendsto (fun t => inner ℝ (P.normalizedColumn E t l) (P.normalizedColumn E t m) -
      inner ℝ (twoFormHeatRealColumn (o := o) hRic t e l)
        (twoFormHeatRealColumn (o := o) hRic t e m)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C₁, _, hc₁⟩ := P.normalizedColumn_growth E l
  obtain ⟨C₂, _, hc₂⟩ := P.normalizedColumn_growth E m
  apply heat_inner_error_tendsto _ _ _ _ C₁ C₂
    (‖((normalizedChartFactor g).toReal)⁻¹‖ * B / 2) 1 zero_lt_one hc₁ hc₂
  · intro t ht
    rw [twoFormHeatRealColumn_pos hRic t ht.1]
    exact (P.spectral_error_bound E hRic he hgen B hB t ht l).trans_eq (by ring)
  · intro t ht
    rw [twoFormHeatRealColumn_pos hRic t ht.1]
    exact (P.spectral_error_bound E hRic he hgen B hB t ht m).trans_eq (by ring)

theorem HeatNormalParametrixData.signed_trace_error_tendsto
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D)
    (hRic : RicciThree g) (he : e.base ∈ (chartAt FourSpace c).source) (hepos : e ∈ o.positive)
    (hgen : ∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t) :
    Tendsto (fun t => twoFormHeatRealSignedTrace (o := o) hRic (t + t) e.base -
      ∑ l, ∑ m, twoFormHodgeMatrix l m *
        inner ℝ (P.normalizedColumn E t l) (P.normalizedColumn E t m)) (𝓝[>] 0) (𝓝 0) := by
  have hs := tendsto_finsetSum Finset.univ (fun l _ =>
    tendsto_finsetSum Finset.univ (fun m _ =>
      (P.column_inner_error_tendsto E hRic he hgen B hB l m).const_mul (twoFormHodgeMatrix l m)))
  simp only [mul_zero, Finset.sum_const_zero] at hs
  have hn := hs.neg
  simp only [neg_zero] at hn
  apply hn.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [twoFormHeatRealSignedTrace_columns hRic t ht e hepos]
  simp only [mul_sub, Finset.sum_sub_distrib, neg_sub]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact integration of the common scalar and form column polynomials. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.eulerPolynomial_continuous
    (E : HeatNormalBundleExtension D) (t : ℝ) : Continuous (E.eulerPolynomial t) :=
  (((E.eulerAmplitude_continuous 0 (by norm_num)).add
    ((E.eulerAmplitude_continuous 1 (by norm_num)).const_smul t)).add
      ((E.eulerAmplitude_continuous 2 (by norm_num)).const_smul (t ^ 2))).add
        ((E.eulerAmplitude_continuous 3 (by norm_num)).const_smul (t ^ 3))

theorem heatEuler_cutoff_integrable (χ F : FourSpace → ℝ)
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (hF : Continuous F) (t : ℝ) :
    Integrable (fun x => fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x * χ x ^ 2 * F x)) := by
  apply (((fourHeatGaussian_continuous t).pow 2).mul
    ((((frameExponentialJacobian_continuous g o e).mul (hχ.pow 2))).mul hF)).integrable_of_hasCompactSupport
  apply hc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_tsupport χ)
  intro x hx
  by_contra hn
  have hz := image_eq_zero_of_notMem_tsupport hn
  exact hx (by simp [hz])

theorem HeatEulerChartData.scalar_polynomial_integrable (P : HeatEulerChartData D) (t : ℝ) :
    Integrable (fun x => fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x * (P.scalar.polynomial t x) ^ 2)) := by
  have h := heatEuler_cutoff_integrable (g := g) (o := o) (e := e) P.normal.cutoff
    (fun x => (P.bundle.eulerPolynomial t x).1 ^ 2) P.normal.cutoff_regular.continuous
    P.normal.cutoff_compact ((P.bundle.eulerPolynomial_continuous t).fst.pow 2) t
  convert h using 1
  funext x
  rw [P.polynomial_scalar]
  ring

theorem HeatEulerChartData.one_polynomial_integrable (P : HeatEulerChartData D)
    (t : ℝ) (l : Fin 4) :
    Integrable (fun x => fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x *
        ‖heatNormalOnePolynomialColumn P.bundle.oneCompanion P.normal.cutoff t l x‖ ^ 2)) := by
  have he := (P.bundle.eulerPolynomial_continuous t).snd.fst
  have hcol : Continuous (fun x => (WithLp.toLp 2
      (fun k => (P.bundle.eulerPolynomial t x).2.1 k l) : FourSpace)) :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k =>
      (continuous_apply l).comp ((continuous_apply k).comp he))
  have h := heatEuler_cutoff_integrable (g := g) (o := o) (e := e) P.normal.cutoff
    (fun x => ‖(WithLp.toLp 2 (fun k => (P.bundle.eulerPolynomial t x).2.1 k l) : FourSpace)‖ ^ 2)
    P.normal.cutoff_regular.continuous P.normal.cutoff_compact (hcol.norm.pow 2) t
  convert h using 1
  funext x
  rw [P.polynomial_one, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

theorem HeatEulerChartData.two_polynomial_integrable (P : HeatEulerChartData D)
    (t : ℝ) (l : Fin 6) :
    Integrable (fun x => fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x *
        ‖heatNormalPolynomialColumn P.bundle P.normal.cutoff t l x‖ ^ 2)) := by
  simpa only [real_inner_self_eq_norm_sq] using P.normal.polynomial_pair_integrable P.bundle t l l

theorem HeatEulerChartData.euler_integral (P : HeatEulerChartData D) (t : ℝ) :
    2 * (∫ x, fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x * (P.scalar.polynomial t x) ^ 2)) -
    2 * (∑ l : Fin 4, ∫ x, fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x *
        ‖heatNormalOnePolynomialColumn P.bundle.oneCompanion P.normal.cutoff t l x‖ ^ 2)) +
    (∑ l : Fin 6, ∫ x, fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x *
        ‖heatNormalPolynomialColumn P.bundle P.normal.cutoff t l x‖ ^ 2)) =
    ∫ x, fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x * P.normal.cutoff x ^ 2 *
        heatEulerGram (P.bundle.eulerPolynomial t x) (P.bundle.eulerPolynomial t x)) := by
  let F₀ := fun x => fourHeatGaussian t x ^ 2 *
    (frameExponentialJacobian g o e x * (P.scalar.polynomial t x) ^ 2)
  let F₁ := fun l x => fourHeatGaussian t x ^ 2 *
    (frameExponentialJacobian g o e x *
      ‖heatNormalOnePolynomialColumn P.bundle.oneCompanion P.normal.cutoff t l x‖ ^ 2)
  let F₂ := fun l x => fourHeatGaussian t x ^ 2 *
    (frameExponentialJacobian g o e x *
      ‖heatNormalPolynomialColumn P.bundle P.normal.cutoff t l x‖ ^ 2)
  have h₀ : Integrable F₀ := P.scalar_polynomial_integrable t
  have h₁ (l : Fin 4) : Integrable (F₁ l) := P.one_polynomial_integrable t l
  have h₂ (l : Fin 6) : Integrable (F₂ l) := P.two_polynomial_integrable t l
  have hs₁ : Integrable (fun x => ∑ l, F₁ l x) := integrable_finsetSum _ (fun l _ => h₁ l)
  have hs₂ : Integrable (fun x => ∑ l, F₂ l x) := integrable_finsetSum _ (fun l _ => h₂ l)
  change 2 * (∫ x, F₀ x) - 2 * (∑ l, ∫ x, F₁ l x) + (∑ l, ∫ x, F₂ l x) = _
  rw [← integral_finsetSum _ (fun l _ => h₁ l), ← integral_finsetSum _ (fun l _ => h₂ l),
    ← integral_const_mul, ← integral_const_mul, ← integral_sub (h₀.const_mul 2) (hs₁.const_mul 2)]
  change (∫ x, ((fun y => 2 * F₀ y) - (fun y => 2 * ∑ l, F₁ l y)) x) +
    (∫ x, ∑ l, F₂ l x) = _
  rw [← integral_add ((h₀.const_mul 2).sub (hs₁.const_mul 2)) hs₂]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only [Pi.sub_apply, F₀, F₁, F₂]
    rw [mul_assoc (frameExponentialJacobian g o e x) (P.normal.cutoff x ^ 2),
      ← P.polynomial_euler t x]
    simp only [mul_add, mul_sub, Finset.mul_sum, mul_left_comm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual spectral Hodge-signed diagonal has the local signature
curvature density as its small-time limit, with normalized-volume factor. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter
open scoped BigOperators ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}
  {c : M} {f : OrthonormalFrame g c} {D : HeatNormalFrameData g o c ⟨c, f⟩}

theorem HeatNormalParametrixData.signed_trace_limit
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D)
    (hRic : RicciThree g) (hepos : (⟨c, f⟩ : FrameBundle g) ∈ o.positive)
    (hgen : ∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t) :
    Tendsto (fun t => twoFormHeatRealSignedTrace (o := o) hRic (t + t) c) (𝓝[>] 0)
      (𝓝 (((normalizedChartFactor g).toReal)⁻¹ *
        curvatureSignatureDensity (twoFormMetricCurvatureTensor g ⟨c, f⟩))) := by
  have hnorm := (E.signed_gaussian_limit P.cutoff P.cutoff_regular P.cutoff_compact
    P.cutoff_zero hRic).const_mul ((normalizedChartFactor g).toReal)⁻¹
  have hn : Tendsto (fun t => ∑ l, ∑ m, twoFormHodgeMatrix l m *
      inner ℝ (P.normalizedColumn E t l) (P.normalizedColumn E t m)) (𝓝[>] 0)
      (𝓝 (((normalizedChartFactor g).toReal)⁻¹ *
        curvatureSignatureDensity (twoFormMetricCurvatureTensor g ⟨c, f⟩))) := by
    simpa only [P.signedColumn_integral E] using hnorm
  have h := (P.signed_trace_error_tendsto E hRic (mem_chart_source FourSpace c) hepos hgen B hB).add hn
  simpa only [sub_add_cancel, zero_add] using h

theorem HeatNormalParametrixData.signed_trace_limit_unscaled
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D)
    (hRic : RicciThree g) (hepos : (⟨c, f⟩ : FrameBundle g) ∈ o.positive)
    (hgen : ∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t) :
    Tendsto (fun t => twoFormHeatRealSignedTrace (o := o) hRic t c) (𝓝[>] 0)
      (𝓝 (((normalizedChartFactor g).toReal)⁻¹ *
        curvatureSignatureDensity (twoFormMetricCurvatureTensor g ⟨c, f⟩))) := by
  have h := (P.signed_trace_limit E hRic hepos hgen B hB).comp fourHeatGaussian_half_tendsto
  have ht (t : ℝ) : t / 2 + t / 2 = t := by ring
  simpa only [Function.comp_def, ht] using h

theorem twoFormHeat_signature_pointwise_limit (hRic : RicciThree g) (c : M) :
    Tendsto (fun t => twoFormHeatRealSignedTrace (o := o) hRic t c) (𝓝[>] 0)
      (𝓝 (((normalizedChartFactor g).toReal)⁻¹ *
        curvatureSignatureDensity (twoFormMetricCurvatureTensor g ⟨c, o.frame c⟩))) := by
  obtain ⟨D⟩ := exists_heatNormalFrameData g o c ⟨c, o.frame c⟩ (mem_chart_source FourSpace c)
  obtain ⟨E⟩ := exists_heatNormalBundleExtension D
  obtain ⟨P, hgen, B, _, hB⟩ := exists_heatNormalGlobalResidual E
    (mem_chart_source FourSpace c) hRic (o.frame_positive c)
  exact P.signed_trace_limit_unscaled E hRic (o.frame_positive c) hgen B hB

end
end PositiveEinsteinFour.Geometry
end


section

/-! A uniform bound for the genuine signed heat diagonal near each frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

theorem exists_heatSignedUniformLocal (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) :
    ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧ ∃ B ≥ (0 : ℝ),
      ∀ e' ∈ U, e' ∈ o.positive → ∀ t ∈ Ioc (0 : ℝ) 1,
        ‖twoFormHeatRealSignedTrace (o := o) hRic (t + t) e'.base‖ ≤ B := by
  obtain ⟨E, r, hr, U, hU, heU, C, hC, D, hD, hN⟩ :=
    exists_heatActualUniformSpectral g o hRic e
  let χ : FourSpace → ℝ := heatNormalChartBump r hr
  have hχs : tsupport χ ⊆ ball 0 r := by
    rw [(heatNormalChartBump r hr).tsupport_eq]
    exact closedBall_subset_ball (by change r / 2 < r; linarith)
  obtain ⟨B, hB, hb⟩ := heatUniformSignedIntegral_bound (g := g) (o := o) (c := e.base)
    E r hr χ (heatNormalChartBump r hr).contDiff
      (heatNormalChartBump r hr).hasCompactSupport hχs
      (closedBall (frameCoordinateState g e.base e) 1) (isCompact_closedBall _ _)
  let S : ℝ := ∑ l : Fin 6, ∑ m : Fin 6, ‖twoFormHodgeMatrix l m‖
  let A : ℝ := S * (2 * C * D + D ^ 2)
  let V : ℝ := ‖((normalizedChartFactor g).toReal)⁻¹‖ * B
  refine ⟨U, hU, heU, A + V, by dsimp [A, S, V]; positivity, ?_⟩
  intro e' he' hepos t ht
  obtain ⟨N, hq, hnorm, herr⟩ := hN e' he'
  let P := N.parametrixData hr
  let X : ℝ := ∑ l, ∑ m, twoFormHodgeMatrix l m *
    inner ℝ (P.normalizedColumn N.extension t l) (P.normalizedColumn N.extension t m)
  have hX : ‖X‖ ≤ V := by
    dsimp only [X]
    rw [P.signedColumn_integral, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa only [P, N.parametrixData_cutoff] using hb e' N hq t ht
  have herror : ‖X - twoFormHeatRealSignedTrace (o := o) hRic (t + t) e'.base‖ ≤ A := by
    rw [twoFormHeatRealSignedTrace_columns hRic t ht.1 e' hepos]
    apply heat_signed_gram_error_uniform _ _ _ C D t hC hD ht (hnorm t ht)
    intro l
    rw [twoFormHeatRealColumn_pos hRic t ht.1]
    exact herr hepos t ht l
  calc
    _ ≤ ‖twoFormHeatRealSignedTrace (o := o) hRic (t + t) e'.base - X‖ + ‖X‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ A + V := by rw [norm_sub_rev]; exact add_le_add herror hX

end
end PositiveEinsteinFour.Geometry
end


section

/-! The three actual column polynomials are the components of the common Euler polynomial. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonEulerMember.eulerPolynomial_scalar (N : HeatCommonEulerMember g o c F r e)
    (hr : 0 < r) (t : ℝ) (x : FourSpace) :
    (N.scalarData hr).polynomial t x = (heatNormalChartBump r hr) x *
      (F.eulerPolynomial t (x, frameCoordinateState g c e)).1 := by
  rw [N.scalarPolynomial_family]
  unfold heatFamilyScalarPolynomial HeatFamilyOneCoefficients.eulerPolynomial
    HeatFamilyOneCoefficients.eulerAmplitude
  change (heatNormalChartBump r hr) x * _ = (heatNormalChartBump r hr) x * _
  congr 1
  change F.base.scalarAmplitude 0 (x, frameCoordinateState g c e) +
    t * F.base.scalarAmplitude 1 (x, frameCoordinateState g c e) +
    t ^ 2 * F.base.scalarAmplitude 2 (x, frameCoordinateState g c e) +
    t ^ 3 * F.base.scalarAmplitude 3 (x, frameCoordinateState g c e) = _
  have hz : F.base.scalarAmplitude 0 (x, frameCoordinateState g c e) =
      F.base.U (x, frameCoordinateState g c e) := rfl
  rw [hz]
  change _ = F.base.U (x, frameCoordinateState g c e) * 1 +
    t * F.base.scalarAmplitude 1 (x, frameCoordinateState g c e) +
    t ^ 2 * F.base.scalarAmplitude 2 (x, frameCoordinateState g c e) +
    t ^ 3 * F.base.scalarAmplitude 3 (x, frameCoordinateState g c e)
  ring

theorem HeatCommonEulerMember.eulerPolynomial_one (N : HeatCommonEulerMember g o c F r e)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 4) (x : FourSpace) :
    heatNormalOnePolynomialColumn N.one χ t l x =
      χ x • (WithLp.toLp 2 (fun k =>
        (F.eulerPolynomial t (x, frameCoordinateState g c e)).2.1 k l) : FourSpace) := by
  rw [N.onePolynomialColumn_family]
  rfl

theorem HeatCommonEulerMember.eulerPolynomial_two (N : HeatCommonEulerMember g o c F r e)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 6) (x : FourSpace) :
    heatNormalPolynomialColumn N.normal.extension χ t l x =
      χ x • (WithLp.toLp 2 (fun k =>
        (F.eulerPolynomial t (x, frameCoordinateState g c e)).2.2 k l) : TwoFormFour) := by
  rw [N.normal.polynomialColumn_family]
  rfl

theorem HeatCommonEulerMember.eulerPolynomial_gram (N : HeatCommonEulerMember g o c F r e)
    (hr : 0 < r) (t : ℝ) (x : FourSpace) :
    2 * ((N.scalarData hr).polynomial t x) ^ 2 -
      2 * (∑ l : Fin 4, ‖heatNormalOnePolynomialColumn N.one (heatNormalChartBump r hr) t l x‖ ^ 2) +
      (∑ l : Fin 6, ‖heatNormalPolynomialColumn N.normal.extension (heatNormalChartBump r hr) t l x‖ ^ 2) =
    (heatNormalChartBump r hr) x ^ 2 *
      heatEulerGram (F.eulerPolynomial t (x, frameCoordinateState g c e))
        (F.eulerPolynomial t (x, frameCoordinateState g c e)) := by
  rw [heatEulerGram_columns, N.eulerPolynomial_scalar]
  simp_rw [N.eulerPolynomial_one, N.eulerPolynomial_two, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp only [← Finset.mul_sum]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual de Rham spectral heat density has the local Euler curvature limit. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

def hodgeHeatRealDensity (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (t : ℝ) (x : M) : ℝ :=
  2 * scalarHeatRealDiagonal g o d t x - 2 * oneFormHeatRealDiagonal hRic d t x +
    twoFormHeatRealTrace (o := o) hRic t x

omit [PreconnectedSpace M] in
theorem hodgeHeatRealDensity_pos (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (t : ℝ) (ht : 0 < t) (x : M) :
    hodgeHeatRealDensity hRic d t x =
      hodgeHeatDensity hRic d t.toNNReal (Real.toNNReal_pos.mpr ht) x := by
  simp only [hodgeHeatRealDensity, scalarHeatRealDiagonal, oneFormHeatRealDiagonal,
    twoFormHeatRealTrace, dite_eq_left ht, ite_eq_left ht, hodgeHeatDensity]

variable {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}

theorem HeatEulerChartData.euler_trace_limit (P : HeatEulerChartData D)
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (he : e.base ∈ (chartAt FourSpace c).source)
    (ha : ∀ x ∈ tsupport P.scalar.cutoff, P.scalar.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hb : ∀ x ∈ tsupport P.scalar.cutoff, P.scalar.extension.b x = heatNormalDrift g o e x)
    (hd : ∀ x ∈ tsupport P.scalar.cutoff, 0 < (heatNormalMetric g o e x).det)
    (B₀ : ℝ) (hB₀ : ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.scalar.residual t‖ ≤ B₀ * t)
    (hpair : ∀ t l (v : smoothCovariantFields M 1),
      inner ℝ (P.normal.oneColumn P.bundle.oneCompanion t l)
        (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
      inner ℝ (P.normal.oneOperatorColumn P.bundle.oneCompanion t l) (smoothOneFormL2Linear v))
    (B₁ : ℝ) (hB₁ : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l,
      ‖P.normal.oneResidual P.bundle.oneCompanion t l‖ ≤ B₁ * t)
    (hgen : ∀ t l, ∃ hf : P.normal.column P.bundle t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨P.normal.column P.bundle t l, hf⟩ =
        P.normal.operatorColumn P.bundle t l)
    (B₂ : ℝ) (hB₂ : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l,
      ‖P.normal.residual P.bundle t l‖ ≤ B₂ * t) :
    Tendsto (fun t => hodgeHeatRealDensity hRic d (t + t) e.base) (𝓝[>] 0)
      (𝓝 (((normalizedChartFactor g).toReal)⁻¹ *
        curvatureEulerDensity (twoFormMetricCurvatureTensor g e))) := by
  have h₀ := P.scalar.trace_gaussian_error_tendsto d ha hb hd B₀ hB₀
  have h₁ := P.normal.oneTrace_gaussian_error_tendsto P.bundle.oneCompanion hRic d he hpair B₁ hB₁
  have h₂ := P.normal.trace_gaussian_error_tendsto P.bundle hRic he hgen B₂ hB₂
  have herr := ((h₀.const_mul 2).sub (h₁.const_mul 2)).add h₂
  have hgauss := (P.bundle.euler_gaussian_limit P.normal.cutoff
    P.normal.cutoff_regular.continuous P.normal.cutoff_compact P.normal.cutoff_zero hRic he).const_mul
      ((normalizedChartFactor g).toReal)⁻¹
  convert herr.add hgauss using 1
  · funext t
    rw [← P.euler_integral t]
    unfold hodgeHeatRealDensity
    ring
  · simp only [mul_zero, sub_self, zero_add]

theorem hodgeHeat_euler_pointwise_limit (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M) :
    Tendsto (fun t => hodgeHeatRealDensity hRic d t c) (𝓝[>] 0)
      (𝓝 (((normalizedChartFactor g).toReal)⁻¹ *
        curvatureEulerDensity (twoFormMetricCurvatureTensor g ⟨c, o.frame c⟩))) := by
  obtain ⟨D⟩ := exists_heatNormalFrameData g o c ⟨c, o.frame c⟩ (mem_chart_source FourSpace c)
  obtain ⟨P, ha, hb, hd, ⟨B₀, _, hB₀⟩, hp, ⟨B₁, _, hB₁⟩, hg, ⟨B₂, _, hB₂⟩⟩ :=
    exists_heatEulerCommonChart D (mem_chart_source FourSpace c) hRic (o.frame_positive c)
  have h := (P.euler_trace_limit hRic d (mem_chart_source FourSpace c)
    ha hb hd B₀ hB₀ hp B₁ hB₁ hg B₂ hB₂).comp fourHeatGaussian_half_tendsto
  have ht (t : ℝ) : t / 2 + t / 2 = t := by ring
  simpa only [Function.comp_def, ht] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactness turns the actual local signed heat estimates into a
single bound on the closed manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

theorem exists_heatSignedUniformBase (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (c : M) :
    ∃ V : Set M, IsOpen V ∧ c ∈ V ∧ ∃ B ≥ (0 : ℝ),
      ∀ x ∈ V, ∀ t ∈ Ioc (0 : ℝ) 1,
        ‖twoFormHeatRealSignedTrace (o := o) hRic (t + t) x‖ ≤ B := by
  obtain ⟨S, hS, hpos⟩ := exists_positive_localGramSection g o c
  let σ := localGramSection g c S hS
  obtain ⟨U, hU, hcU, B, hB, hb⟩ := exists_heatSignedUniformLocal g o hRic (σ c)
  have hpre : ∀ᶠ x in 𝓝 c, σ x ∈ U :=
    (continuousAt_localGramSection g c S hS).preimage_mem_nhds (hU.mem_nhds hcU)
  obtain ⟨V, hVsub, hV, hcV⟩ := mem_nhds_iff.mp (Filter.inter_mem hpre hpos)
  refine ⟨V, hV, hcV, B, hB, ?_⟩
  intro x hx t ht
  have h := hb (σ x) (hVsub hx).1 (hVsub hx).2 t ht
  simpa only [σ, localGramSection_base] using h

theorem exists_heatSignedUniformGlobal (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) :
    ∃ B ≥ (0 : ℝ), ∀ x : M, ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖twoFormHeatRealSignedTrace (o := o) hRic (t + t) x‖ ≤ B := by
  classical
  choose U hU hmem B hB hb using exists_heatSignedUniformBase g o hRic
  have hcover : (univ : Set M) ⊆ ⋃ i, U i := fun x _ => mem_iUnion.mpr ⟨x, hmem x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  refine ⟨∑ i ∈ s, B i, Finset.sum_nonneg (fun i _ => hB i), ?_⟩
  intro x t ht
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  exact (hb i x hxi t ht).trans
    (Finset.single_le_sum (fun j _ => hB j) hi)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact Gaussian integral of the actual common-family column supertrace. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonEulerMember.scalar_polynomial_integrable (N : HeatCommonEulerMember g o c F r e)
    (hr : 0 < r) (t : ℝ) : Integrable (fun x => fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x * ((N.scalarData hr).polynomial t x) ^ 2)) := by
  let P := N.scalarData hr
  have hc : Continuous (fun x => fourHeatPolynomial (fun m => P.extension.scalarAmplitude m) t x) :=
    (fourHeatPolynomial_joint_continuous _ (fun m => (P.extension.scalarAmplitude_regular m (by omega)).continuous)).comp
      (continuous_const.prodMk continuous_id)
  have h := heatEuler_cutoff_integrable (g := g) (o := o) (e := e) P.cutoff
    (fun x => (fourHeatPolynomial (fun m => P.extension.scalarAmplitude m) t x) ^ 2)
    P.cutoff_regular.continuous P.cutoff_compact (hc.pow 2) t
  convert h using 1
  funext x
  unfold HeatScalarChartData.polynomial
  ring

theorem HeatCommonEulerMember.one_polynomial_integrable (N : HeatCommonEulerMember g o c F r e)
    (hr : 0 < r) (t : ℝ) (l : Fin 4) : Integrable (fun x => fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x *
        ‖heatNormalOnePolynomialColumn N.one (heatNormalChartBump r hr) t l x‖ ^ 2)) := by
  have hc : Continuous (fun x => (WithLp.toLp 2
      (fun k => fourHeatPolynomial (fun m y => N.one.amplitude m y k l) t x) : FourSpace)) := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro k
    exact (fourHeatPolynomial_joint_continuous _ (fun m => (N.one.amplitude_regular m (by omega) k l).continuous)).comp
      (continuous_const.prodMk continuous_id)
  have h := heatEuler_cutoff_integrable (g := g) (o := o) (e := e) (heatNormalChartBump r hr)
    (fun x => ‖(WithLp.toLp 2
      (fun k => fourHeatPolynomial (fun m y => N.one.amplitude m y k l) t x) : FourSpace)‖ ^ 2)
    (heatNormalChartBump r hr).continuous (heatNormalChartBump r hr).hasCompactSupport (hc.norm.pow 2) t
  convert h using 1
  funext x
  have heq : heatNormalOnePolynomialColumn N.one (heatNormalChartBump r hr) t l x =
      (heatNormalChartBump r hr) x • (WithLp.toLp 2
        (fun k => fourHeatPolynomial (fun m y => N.one.amplitude m y k l) t x) : FourSpace) := rfl
  rw [heq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

theorem HeatCommonEulerMember.euler_integral (N : HeatCommonEulerMember g o c F r e)
    (hr : 0 < r) (t : ℝ) :
    2 * (∫ x, fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x * ((N.scalarData hr).polynomial t x) ^ 2)) -
    2 * (∑ l : Fin 4, ∫ x, fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x *
        ‖heatNormalOnePolynomialColumn N.one (heatNormalChartBump r hr) t l x‖ ^ 2)) +
    (∑ l : Fin 6, ∫ x, fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x *
        ‖heatNormalPolynomialColumn N.normal.extension (heatNormalChartBump r hr) t l x‖ ^ 2)) =
    ∫ x, fourHeatGaussian t x ^ 2 * (frameExponentialJacobian g o e x *
      (heatNormalChartBump r hr) x ^ 2 *
      heatEulerGram (F.eulerPolynomial t (x, frameCoordinateState g c e))
        (F.eulerPolynomial t (x, frameCoordinateState g c e))) := by
  let χ : FourSpace → ℝ := heatNormalChartBump r hr
  let F₀ := fun x => fourHeatGaussian t x ^ 2 *
    (frameExponentialJacobian g o e x * ((N.scalarData hr).polynomial t x) ^ 2)
  let F₁ := fun l x => fourHeatGaussian t x ^ 2 *
    (frameExponentialJacobian g o e x *
      ‖heatNormalOnePolynomialColumn N.one χ t l x‖ ^ 2)
  let F₂ := fun l x => fourHeatGaussian t x ^ 2 *
    (frameExponentialJacobian g o e x *
      ‖heatNormalPolynomialColumn N.normal.extension χ t l x‖ ^ 2)
  have h₀ : Integrable F₀ := N.scalar_polynomial_integrable hr t
  have h₁ (l : Fin 4) : Integrable (F₁ l) := N.one_polynomial_integrable hr t l
  have h₂ (l : Fin 6) : Integrable (F₂ l) := by
    simpa only [F₂, χ, N.normal.parametrixData_cutoff hr, real_inner_self_eq_norm_sq] using
      (N.normal.parametrixData hr).polynomial_pair_integrable N.normal.extension t l l
  have hs₁ : Integrable (fun x => ∑ l, F₁ l x) := integrable_finsetSum _ (fun l _ => h₁ l)
  have hs₂ : Integrable (fun x => ∑ l, F₂ l x) := integrable_finsetSum _ (fun l _ => h₂ l)
  change 2 * (∫ x, F₀ x) - 2 * (∑ l, ∫ x, F₁ l x) + (∑ l, ∫ x, F₂ l x) = _
  rw [← integral_finsetSum _ (fun l _ => h₁ l), ← integral_finsetSum _ (fun l _ => h₂ l),
    ← integral_const_mul, ← integral_const_mul, ← integral_sub (h₀.const_mul 2) (hs₁.const_mul 2)]
  change (∫ x, ((fun y => 2 * F₀ y) - (fun y => 2 * ∑ l, F₁ l y)) x) +
    (∫ x, ∑ l, F₂ l x) = _
  rw [← integral_add ((h₀.const_mul 2).sub (hs₁.const_mul 2)) hs₂]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only [Pi.sub_apply, F₀, F₁, F₂]
    rw [mul_assoc (frameExponentialJacobian g o e x) (χ x ^ 2),
      ← N.eulerPolynomial_gram hr t x]
    simp only [mul_add, mul_sub, Finset.mul_sum, mul_left_comm, χ]


end
end PositiveEinsteinFour.Geometry
end


section

/-! Dominated convergence identifies the actual harmonic signature with
its curvature integral, keeping the chart-volume normalization explicit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatRealSignedTrace_pos (hRic : RicciThree g) (t : ℝ) (ht : 0 < t) (x : M) :
    twoFormHeatRealSignedTrace (o := o) hRic t x =
      twoFormFiberSignedTrace (twoFormHeatKernel (o := o) hRic t.toNNReal
        (Real.toNNReal_pos.mpr ht) x x) := by
  unfold twoFormHeatRealSignedTrace
  exact dite_eq_left ht

theorem twoFormHeatRealSignedTrace_nonpos (hRic : RicciThree g) (t : ℝ) (ht : ¬ 0 < t) (x : M) :
    twoFormHeatRealSignedTrace (o := o) hRic t x = 0 := by
  unfold twoFormHeatRealSignedTrace
  exact dite_eq_right ht

theorem twoFormHeatRealSignedTrace_measurable (hRic : RicciThree g) (t : ℝ) :
    Measurable (twoFormHeatRealSignedTrace (o := o) hRic t) := by
  change Measurable (fun x => twoFormHeatRealSignedTrace (o := o) hRic t x)
  by_cases ht : 0 < t
  · simp_rw [twoFormHeatRealSignedTrace_pos hRic t ht]
    simp_rw [twoFormHeatKernel_signed_diagonal]
    apply Measurable.tsum
    intro i
    exact (smoothTwoForm_pairing_continuous _
      (smoothTwoFormHodge o (twoFormHeatSection hRic (t.toNNReal / 2)
        (half_pos (Real.toNNReal_pos.mpr ht)) (twoFormEigenvector hRic i)))).measurable
  · simpa only [twoFormHeatRealSignedTrace_nonpos hRic t ht] using
      (measurable_const : Measurable (fun _ : M => (0 : ℝ)))

theorem twoFormHeat_signature_integral_limit (hRic : RicciThree g) :
    Tendsto (fun t => ∫ x, twoFormHeatRealSignedTrace (o := o) hRic t x ∂normalizedVolume g)
      (𝓝[>] (0 : ℝ))
      (𝓝 (((normalizedChartFactor g).toReal)⁻¹ *
        ∫ x, orientedSignatureDensity g o x ∂normalizedVolume g)) := by
  let := normalizedVolume_isProbability (actual_finitePositiveVolume g)
  obtain ⟨B, _hB, hb⟩ := exists_heatSignedUniformGlobal g o hRic
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioc (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with t ht ht1
    exact ⟨ht, ht1.le⟩
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᵐ x ∂normalizedVolume g,
      ‖twoFormHeatRealSignedTrace (o := o) hRic t x‖ ≤ B := by
    filter_upwards [hsmall] with t ht
    refine Eventually.of_forall fun x => ?_
    have h := hb x (t / 2) ⟨half_pos ht.1, by linarith [ht.2]⟩
    simpa only [show t / 2 + t / 2 = t by ring] using h
  have hp : ∀ x : M, Tendsto (fun t => twoFormHeatRealSignedTrace (o := o) hRic t x)
      (𝓝[>] 0) (𝓝 (((normalizedChartFactor g).toReal)⁻¹ * orientedSignatureDensity g o x)) :=
    fun x => twoFormHeat_signature_pointwise_limit hRic x
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := normalizedVolume g) (l := 𝓝[>] (0 : ℝ))
    (F := fun t x => twoFormHeatRealSignedTrace (o := o) hRic t x)
    (f := fun x => ((normalizedChartFactor g).toReal)⁻¹ * orientedSignatureDensity g o x)
    (fun _ : M => B)
    (Eventually.of_forall fun t => (twoFormHeatRealSignedTrace_measurable hRic t).aestronglyMeasurable)
    hbound (integrable_const B) (Eventually.of_forall hp)
  simpa only [integral_const_mul] using hlim

theorem harmonicSignature_eq_normalized_curvature_integral (hRic : RicciThree g) :
    (Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) : ℝ) -
      (Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) : ℝ) =
      ((normalizedChartFactor g).toReal)⁻¹ *
        ∫ x, orientedSignatureDensity g o x ∂normalizedVolume g := by
  have hconst : Tendsto
      (fun t => ∫ x, twoFormHeatRealSignedTrace (o := o) hRic t x ∂normalizedVolume g)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) : ℝ) -
        (Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) : ℝ))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp_rw [twoFormHeatRealSignedTrace_pos hRic t ht]
    exact (twoFormHeatKernel_signature_trace hRic t.toNNReal (Real.toNNReal_pos.mpr ht)).symm
  exact tendsto_nhds_unique hconst (twoFormHeat_signature_integral_limit hRic)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normalized column supertrace is the common Euler Gaussian integral. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter MeasureTheory Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

def HeatCommonEulerMember.eulerColumnTrace (N : HeatCommonEulerMember g o c F r e)
    (hr : 0 < r) (t : ℝ) : ℝ :=
  2 * ‖(N.scalarData hr).normalizedColumn t‖ ^ 2 -
    2 * (∑ l : Fin 4, ‖(N.normal.parametrixData hr).oneNormalizedColumn N.one t l‖ ^ 2) +
    (∑ l : Fin 6, ‖(N.normal.parametrixData hr).normalizedColumn N.normal.extension t l‖ ^ 2)

theorem HeatCommonEulerMember.eulerColumnTrace_integral (N : HeatCommonEulerMember g o c F r e)
    (hr : 0 < r) (t : ℝ) :
    N.eulerColumnTrace hr t = ((normalizedChartFactor g).toReal)⁻¹ *
      ∫ x, fourHeatGaussian t x ^ 2 * (frameExponentialJacobian g o e x *
        (heatNormalChartBump r hr) x ^ 2 *
        heatEulerGram (F.eulerPolynomial t (x, frameCoordinateState g c e))
          (F.eulerPolynomial t (x, frameCoordinateState g c e))) := by
  unfold eulerColumnTrace
  rw [(N.scalarData hr).normalizedColumn_gaussian_integral]
  simp_rw [(N.normal.parametrixData hr).oneNormalizedColumn_gaussian_integral,
    (N.normal.parametrixData hr).normalizedColumn_gaussian_integral]
  simp only [← Finset.mul_sum]
  rw [show (N.normal.parametrixData hr).cutoff = heatNormalChartBump r hr from rfl]
  rw [← N.euler_integral hr t]
  ring

theorem HeatCommonEulerMember.eulerColumnTrace_family (N : HeatCommonEulerMember g o c F r e)
    (hr : 0 < r) (t : ℝ) :
    N.eulerColumnTrace hr t = ((normalizedChartFactor g).toReal)⁻¹ *
      ∫ x, fourHeatGaussian t x ^ 2 * ((F.base.U (x, frameCoordinateState g c e) ^ 2)⁻¹ *
        (heatNormalChartBump r hr) x ^ 2 *
        heatEulerGram (F.eulerPolynomial t (x, frameCoordinateState g c e))
          (F.eulerPolynomial t (x, frameCoordinateState g c e))) := by
  rw [N.eulerColumnTrace_integral hr t]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ tsupport (heatNormalChartBump r hr)
  · have hxs : x ∈ ball (0 : FourSpace) r := by
      rw [(heatNormalChartBump r hr).tsupport_eq] at hx
      exact closedBall_subset_ball (by change r / 2 < r; linarith) hx
    have hh := heatNormalLeadingAmplitude_normalization g o e x
      (Real.sqrt_pos.mpr (N.normal.metric_pos x hxs))
    rw [← (N.normal.actual x hxs).2.2.2.2, N.normal.U_family] at hh
    rw [eq_inv_of_mul_eq_one_right hh]
  · simp only [image_eq_zero_of_notMem_tsupport hx, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, zero_mul]

theorem heatUniformEulerColumnTrace_bound (F : HeatFamilyOneCoefficients) (r : ℝ) (hr : 0 < r)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) (hRic : RicciThree g) :
    ∃ B ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K → ∀ t ∈ Ioc (0 : ℝ) 1, ‖N.eulerColumnTrace hr t‖ ≤ B := by
  let χ : FourSpace → ℝ := heatNormalChartBump r hr
  have hs : tsupport χ ⊆ ball (0 : FourSpace) r := by
    rw [(heatNormalChartBump r hr).tsupport_eq]
    exact closedBall_subset_ball (by change r / 2 < r; linarith)
  obtain ⟨B, hB, hb⟩ := heatUniformEulerIntegral_bound (g := g) (o := o) (c := c) F r χ
    (heatNormalChartBump r hr).contDiff (heatNormalChartBump r hr).hasCompactSupport hs K hK hRic
  refine ⟨‖((normalizedChartFactor g).toReal)⁻¹‖ * B, by positivity, ?_⟩
  intro e N hq t ht
  rw [N.eulerColumnTrace_family hr t, norm_mul]
  exact mul_le_mul_of_nonneg_left (hb e N hq t ht) (norm_nonneg _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The proved signature integral in the original metric-volume convention.
The numerical Hausdorff normalization is displayed, not assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem riemannianChartFactor_toReal_pos : 0 < riemannianChartFactor.toReal := by
  rw [riemannianChartFactor, ENNReal.toReal_mul]
  apply mul_pos
  · rw [ENNReal.toReal_ofReal (by positivity)]
    positivity
  · exact_mod_cast euclideanHausdorffFactor_pos

omit [CompactSpace M] [Nonempty M] in
theorem normalizedChartFactor_inv_toReal (g : SmoothMetric M) :
    ((normalizedChartFactor g).toReal)⁻¹ = totalVolume g / riemannianChartFactor.toReal := by
  rw [normalizedChartFactor, ENNReal.toReal_mul, ENNReal.toReal_inv]
  change ((totalVolume g)⁻¹ * riemannianChartFactor.toReal)⁻¹ = _
  rw [mul_inv, inv_inv, div_eq_mul_inv]

theorem deRhamSignature_eq_curvature_integral (hRic : RicciThree g) :
    (deRhamSignature (o := o) hRic : ℝ) = riemannianChartFactor.toReal⁻¹ *
      ∫ x, orientedSignatureDensity g o x ∂volumeMeasure g := by
  rw [deRhamSignature_hodge]
  push_cast
  rw [harmonicSignature_eq_normalized_curvature_integral hRic,
    volumeMeasure_integral_eq_total_mul (actual_finitePositiveVolume g),
    normalizedChartFactor_inv_toReal]
  ring

theorem deRhamSignature_curvature_counts (hRic : RicciThree g) :
    riemannianChartFactor.toReal * (deRhamSignature (o := o) hRic : ℝ) =
      (4 / 3 : ℝ) * volumeRatio g *
        ((∫ x, plusNorm o x ^ 2 ∂normalizedVolume g) -
          ∫ x, minusNorm o x ^ 2 ∂normalizedVolume g) := by
  rw [deRhamSignature_eq_curvature_integral hRic, ← mul_assoc,
    mul_inv_cancel₀ riemannianChartFactor_toReal_pos.ne', one_mul]
  exact integral_orientedSignatureDensity o hRic (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A common bound for the actual Euler heat density on a compact frame family. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem heatUniformEulerDensity_bound (F : HeatFamilyOneCoefficients) (r : ℝ) (hr : 0 < r)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    ∃ B ≥ (0 : ℝ), ∀ (e : FrameBundle g) (_N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K → e ∈ o.positive → ∀ t ∈ Ioc (0 : ℝ) 1,
        ‖hodgeHeatRealDensity hRic d (t + t) e.base‖ ≤ B := by
  obtain ⟨C₀, hC₀, D₀, hD₀, h₀⟩ := heatUniformScalarSpectral F r hr K hK hRic d
  obtain ⟨C₁, hC₁, D₁, hD₁, h₁⟩ := heatUniformOneSpectral F r hr K hK hRic d
  obtain ⟨C₂, hC₂, D₂, hD₂, h₂⟩ := heatUniformTwoSpectral F r hr K hK hRic
  obtain ⟨B, hB, hb⟩ := heatUniformEulerColumnTrace_bound (g := g) (o := o) (c := c) F r hr K hK hRic
  let A₀ := 2 * C₀ * D₀ + D₀ ^ 2
  let A₁ := 2 * C₁ * D₁ + D₁ ^ 2
  let A₂ := 2 * C₂ * D₂ + D₂ ^ 2
  refine ⟨2 * A₀ + 8 * A₁ + 6 * A₂ + B, by dsimp [A₀, A₁, A₂]; positivity, ?_⟩
  intro e N hq he t ht
  let P := N.normal.parametrixData hr
  let P₀ := N.scalarData hr
  have hs₀ := h₀ e N hq
  have hs₁ := h₁ e N hq
  have hs₂ := h₂ e N hq
  have he₀ : ‖‖P₀.normalizedColumn t‖ ^ 2 - ‖scalarHeatRealColumn g o d t e.base‖ ^ 2‖ ≤ A₀ := by
    apply heat_norm_square_error_uniform _ _ C₀ D₀ t hC₀ hD₀ ht (hs₀.1 t ht)
    rw [scalarHeatRealColumn_pos g o d t ht.1]
    exact hs₀.2 he t ht
  have he₁ : ‖(∑ l : Fin 4, ‖P.oneNormalizedColumn N.one t l‖ ^ 2) -
      (∑ l : Fin 4, ‖oneFormHeatRealColumn hRic d t e l‖ ^ 2)‖ ≤ 4 * A₁ := by
    apply (heat_sum_norm_square_error_uniform _ _ C₁ D₁ t hC₁ hD₁ ht (hs₁.1 t ht) ?_).trans_eq
      (by simp only [Fintype.card_fin]; rfl)
    intro l
    rw [oneFormHeatRealColumn_pos hRic d t ht.1]
    exact hs₁.2 he t ht l
  have he₂ : ‖(∑ l : Fin 6, ‖P.normalizedColumn N.normal.extension t l‖ ^ 2) -
      (∑ l : Fin 6, ‖twoFormHeatRealColumn (o := o) hRic t e l‖ ^ 2)‖ ≤ 6 * A₂ := by
    apply (heat_sum_norm_square_error_uniform _ _ C₂ D₂ t hC₂ hD₂ ht (hs₂.1 t ht) ?_).trans_eq
      (by simp only [Fintype.card_fin]; rfl)
    intro l
    rw [twoFormHeatRealColumn_pos hRic t ht.1]
    exact hs₂.2 he t ht l
  have herr : ‖N.eulerColumnTrace hr t - hodgeHeatRealDensity hRic d (t + t) e.base‖ ≤
      2 * A₀ + 8 * A₁ + 6 * A₂ := by
    have hid : N.eulerColumnTrace hr t - hodgeHeatRealDensity hRic d (t + t) e.base =
        2 * (‖P₀.normalizedColumn t‖ ^ 2 - ‖scalarHeatRealColumn g o d t e.base‖ ^ 2) -
        2 * ((∑ l : Fin 4, ‖P.oneNormalizedColumn N.one t l‖ ^ 2) -
          (∑ l : Fin 4, ‖oneFormHeatRealColumn hRic d t e l‖ ^ 2)) +
        ((∑ l : Fin 6, ‖P.normalizedColumn N.normal.extension t l‖ ^ 2) -
          (∑ l : Fin 6, ‖twoFormHeatRealColumn (o := o) hRic t e l‖ ^ 2)) := by
      unfold HeatCommonEulerMember.eulerColumnTrace hodgeHeatRealDensity
      rw [scalarHeatRealDiagonal_columns g o d t ht.1,
        oneFormHeatRealDiagonal_columns hRic d t ht.1 e, twoFormHeatRealTrace_columns hRic t ht.1 e]
      ring
    rw [hid]
    calc
      _ ≤ ‖2 * (‖P₀.normalizedColumn t‖ ^ 2 - ‖scalarHeatRealColumn g o d t e.base‖ ^ 2)‖ +
          ‖2 * ((∑ l : Fin 4, ‖P.oneNormalizedColumn N.one t l‖ ^ 2) -
            (∑ l : Fin 4, ‖oneFormHeatRealColumn hRic d t e l‖ ^ 2))‖ +
          ‖(∑ l : Fin 6, ‖P.normalizedColumn N.normal.extension t l‖ ^ 2) -
            (∑ l : Fin 6, ‖twoFormHeatRealColumn (o := o) hRic t e l‖ ^ 2)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ 2 * A₀ + 2 * (4 * A₁) + 6 * A₂ := by
        simp only [norm_mul, Real.norm_ofNat]
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left he₀ (by norm_num))
          (mul_le_mul_of_nonneg_left he₁ (by norm_num))) he₂
      _ = _ := by ring
  calc
    _ ≤ ‖hodgeHeatRealDensity hRic d (t + t) e.base - N.eulerColumnTrace hr t‖ +
        ‖N.eulerColumnTrace hr t‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := by rw [norm_sub_rev]; exact add_le_add herr (hb e N hq t ht)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactness supplies a single bound for the actual Euler heat density. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]

theorem exists_heatEulerUniformLocal (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o)) (e : FrameBundle g) :
    ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧ ∃ B ≥ (0 : ℝ),
      ∀ e' ∈ U, e' ∈ o.positive → ∀ t ∈ Ioc (0 : ℝ) 1,
        ‖hodgeHeatRealDensity hRic d (t + t) e'.base‖ ≤ B := by
  obtain ⟨F, r, hr, U, hU, heU, hN⟩ := exists_heatUniformEulerFamily g o e
  obtain ⟨B, hB, hb⟩ := heatUniformEulerDensity_bound (g := g) (o := o) (c := e.base)
    F r hr (closedBall (frameCoordinateState g e.base e) (r / 2))
      (isCompact_closedBall _ _) hRic d
  refine ⟨U, hU, heU, B, hB, ?_⟩
  intro e' he' hepos t ht
  obtain ⟨hq, ⟨N⟩⟩ := hN e' he'
  exact hb e' N (ball_subset_closedBall hq) hepos t ht

theorem exists_heatEulerUniformBase (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M) :
    ∃ V : Set M, IsOpen V ∧ c ∈ V ∧ ∃ B ≥ (0 : ℝ),
      ∀ x ∈ V, ∀ t ∈ Ioc (0 : ℝ) 1, ‖hodgeHeatRealDensity hRic d (t + t) x‖ ≤ B := by
  obtain ⟨S, hS, hpos⟩ := exists_positive_localGramSection g o c
  let σ := localGramSection g c S hS
  obtain ⟨U, hU, hcU, B, hB, hb⟩ := exists_heatEulerUniformLocal g o hRic d (σ c)
  have hpre : ∀ᶠ x in 𝓝 c, σ x ∈ U :=
    (continuousAt_localGramSection g c S hS).preimage_mem_nhds (hU.mem_nhds hcU)
  obtain ⟨V, hVsub, hV, hcV⟩ := mem_nhds_iff.mp (Filter.inter_mem hpre hpos)
  refine ⟨V, hV, hcV, B, hB, ?_⟩
  intro x hx t ht
  have h := hb (σ x) (hVsub hx).1 (hVsub hx).2 t ht
  simpa only [σ, localGramSection_base] using h

theorem exists_heatEulerUniformGlobal (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    ∃ B ≥ (0 : ℝ), ∀ x : M, ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖hodgeHeatRealDensity hRic d (t + t) x‖ ≤ B := by
  classical
  choose U hU hmem B hB hb using exists_heatEulerUniformBase g o hRic d
  have hcover : (univ : Set M) ⊆ ⋃ i, U i := fun x _ => mem_iUnion.mpr ⟨x, hmem x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  refine ⟨∑ i ∈ s, B i, Finset.sum_nonneg (fun i _ => hB i), ?_⟩
  intro x t ht
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  exact (hb i x hxi t ht).trans (Finset.single_le_sum (fun j _ => hB j) hi)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Euler heat supertrace converges to its curvature integral.
The numerical chart-volume normalization remains explicit. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem hodgeHeat_euler_integral_limit (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    Tendsto (fun t => ∫ x, hodgeHeatRealDensity hRic d t x ∂normalizedVolume g)
      (𝓝[>] (0 : ℝ))
      (𝓝 (((normalizedChartFactor g).toReal)⁻¹ *
        ∫ x, orientedEulerDensity g o x ∂normalizedVolume g)) := by
  let := normalizedVolume_isProbability (actual_finitePositiveVolume g)
  obtain ⟨B, _hB, hb⟩ := exists_heatEulerUniformGlobal g o hRic d
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioc (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with t ht ht1
    exact ⟨ht, ht1.le⟩
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᵐ x ∂normalizedVolume g,
      ‖hodgeHeatRealDensity hRic d t x‖ ≤ B := by
    filter_upwards [hsmall] with t ht
    refine Eventually.of_forall fun x => ?_
    have h := hb x (t / 2) ⟨half_pos ht.1, by linarith [ht.2]⟩
    simpa only [show t / 2 + t / 2 = t by ring] using h
  have hp : ∀ x : M, Tendsto (fun t => hodgeHeatRealDensity hRic d t x)
      (𝓝[>] 0) (𝓝 (((normalizedChartFactor g).toReal)⁻¹ * orientedEulerDensity g o x)) :=
    fun x => hodgeHeat_euler_pointwise_limit hRic d x
  have hmeas : ∀ᶠ t : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable (hodgeHeatRealDensity hRic d t) (normalizedVolume g) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have heq : hodgeHeatRealDensity hRic d t =
        hodgeHeatDensity hRic d t.toNNReal (Real.toNNReal_pos.mpr ht) := by
      funext x
      exact hodgeHeatRealDensity_pos hRic d t ht x
    rw [heq]
    exact (hodgeHeatDensity_integrable hRic d t.toNNReal (Real.toNNReal_pos.mpr ht)).aestronglyMeasurable
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := normalizedVolume g) (l := 𝓝[>] (0 : ℝ))
    (F := fun t x => hodgeHeatRealDensity hRic d t x)
    (f := fun x => ((normalizedChartFactor g).toReal)⁻¹ * orientedEulerDensity g o x)
    (fun _ : M => B) hmeas hbound (integrable_const B) (Eventually.of_forall hp)
  simpa only [integral_const_mul] using hlim

theorem hodgeComplexEuler_eq_normalized_curvature_integral (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    (hodgeComplexEuler g o : ℝ) = ((normalizedChartFactor g).toReal)⁻¹ *
      ∫ x, orientedEulerDensity g o x ∂normalizedVolume g := by
  have hconst : Tendsto
      (fun t => ∫ x, hodgeHeatRealDensity hRic d t x ∂normalizedVolume g)
      (𝓝[>] (0 : ℝ)) (𝓝 (hodgeComplexEuler g o : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp_rw [hodgeHeatRealDensity_pos hRic d t ht]
    exact (hodgeHeatDensity_integral hRic d t.toNNReal (Real.toNNReal_pos.mpr ht)).symm
  exact tendsto_nhds_unique hconst (hodgeHeat_euler_integral_limit hRic d)

theorem hodgeComplexEuler_eq_curvature_integral (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    (hodgeComplexEuler g o : ℝ) = riemannianChartFactor.toReal⁻¹ *
      ∫ x, orientedEulerDensity g o x ∂volumeMeasure g := by
  rw [hodgeComplexEuler_eq_normalized_curvature_integral hRic d,
    volumeMeasure_integral_eq_total_mul (actual_finitePositiveVolume g),
    normalizedChartFactor_inv_toReal]
  ring

theorem hodgeComplexEuler_curvature_counts (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    riemannianChartFactor.toReal * (hodgeComplexEuler g o : ℝ) =
      2 * volumeRatio g * (1 + (∫ x, plusNorm o x ^ 2 ∂normalizedVolume g) +
        ∫ x, minusNorm o x ^ 2 ∂normalizedVolume g) := by
  rw [hodgeComplexEuler_eq_curvature_integral hRic d, ← mul_assoc,
    mul_inv_cancel₀ riemannianChartFactor_toReal_pos.ne', one_mul]
  exact integral_orientedEulerDensity o hRic (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end

end OAI
