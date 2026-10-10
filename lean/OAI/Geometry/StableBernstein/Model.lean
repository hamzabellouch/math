import Mathlib

namespace OAI

noncomputable section

namespace StableBernstein.W02

open MeasureTheory Manifold Bundle
open scoped Bundle ContDiff

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]

def scalarDifferential (η : M → ℝ) (x : M) : TangentSpace I x →L[ℝ] ℝ :=
  (NormedSpace.fromTangentSpace (η x)).toContinuousLinearMap.comp
    (mfderiv I 𝓘(ℝ, ℝ) η x)
def differentialEnergy (η : M → ℝ) (x : M) : ℝ :=
  ‖(scalarDifferential I η x)‖ ^ 2
def IsSmoothCompactTest (η : M → ℝ) : Prop :=
  ContMDiff I 𝓘(ℝ, ℝ) ∞ η ∧ HasCompactSupport η

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
variable [MeasurableSpace M]

def IntrinsicStability (μ : Measure M) (V : M → ℝ) : Prop :=
  ∀ η : M → ℝ, IsSmoothCompactTest I η →
    (∫ x, V x * η x ^ 2 ∂μ) ≤ ∫ x, differentialEnergy I η x ∂μ

end StableBernstein.W02

namespace StableBernstein.W01

open scoped ContDiff
open Manifold

abbrev E6 := EuclideanSpace ℝ (Fin 6)
abbrev E7 := EuclideanSpace ℝ (Fin 7)
abbrev I6 := 𝓘(ℝ, E6)
abbrev I7 := 𝓘(ℝ, E7)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E6 M]
local instance coordinateTangentNorm (x : M) : NormedAddCommGroup (TangentSpace I6 x) :=
  inferInstanceAs (NormedAddCommGroup E6)
local instance coordinateTangentNormedSpace (x : M) : NormedSpace ℝ (TangentSpace I6 x) :=
  inferInstanceAs (NormedSpace ℝ E6)

structure SmoothImmersion (F : M → E7) : Prop where
  smooth : ContMDiff I6 I7 ∞ F
  injective_differential (x : M) : Function.Injective (mfderiv I6 I7 F x)
def differential (F : M → E7) (x : M) : TangentSpace I6 x →L[ℝ] E7 :=
  (NormedSpace.fromTangentSpace (F x)).toContinuousLinearMap.comp (mfderiv I6 I7 F x)
lemma SmoothImmersion.differential_injective {F : M → E7} (hF : SmoothImmersion F)
    (x : M) : Function.Injective (differential F x) :=
  (NormedSpace.fromTangentSpace (F x)).injective.comp (hF.injective_differential x)
structure GlobalUnitNormal (F ν : M → E7) : Prop where
  smooth : ContMDiff I6 I7 ∞ ν
  unit (x : M) : ‖ν x‖ = 1
  orthogonal (x : M) (v : TangentSpace I6 x) :
    inner ℝ (ν x) (differential F x v) = 0
def inducedMetric (F : M → E7) (x : M) (v w : TangentSpace I6 x) : ℝ :=
  inner ℝ (differential F x v) (differential F x w)
def inducedMetricBilinear (F : M → E7) (x : M) :
    TangentSpace I6 x →L[ℝ] TangentSpace I6 x →L[ℝ] ℝ :=
  (innerSL ℝ (E := E7)).bilinearComp (differential F x) (differential F x)
lemma inducedMetricBilinear_apply (F : M → E7) (x : M) (v w : TangentSpace I6 x) :
    inducedMetricBilinear F x v w = inducedMetric F x v w := rfl
lemma inducedMetric_symm (F : M → E7) (x : M) (v w : TangentSpace I6 x) :
    inducedMetric F x v w = inducedMetric F x w v := real_inner_comm _ _
lemma inducedMetric_self_eq_norm_sq (F : M → E7) (x : M) (v : TangentSpace I6 x) :
    inducedMetric F x v v = ‖differential F x v‖ ^ 2 := real_inner_self_eq_norm_sq _
lemma SmoothImmersion.inducedMetric_pos {F : M → E7} (hF : SmoothImmersion F)
    (x : M) (v : TangentSpace I6 x) (hv : v ≠ 0) : 0 < inducedMetric F x v v := by
  apply real_inner_self_pos.mpr
  intro h
  apply hv
  apply hF.differential_injective x
  simpa using h
def secondFundamentalForm (F ν : M → E7) (x : M) (v w : TangentSpace I6 x) : ℝ :=
  -inner ℝ (differential ν x v) (differential F x w)
def secondFundamentalBilinear (F ν : M → E7) (x : M) :
    TangentSpace I6 x →L[ℝ] TangentSpace I6 x →L[ℝ] ℝ :=
  -(innerSL ℝ (E := E7)).bilinearComp (differential ν x) (differential F x)
def SmoothImmersion.toRiemannianMetric [IsManifold I6 ∞ M]
    {F : M → E7} (hF : SmoothImmersion F) :
    Bundle.RiemannianMetric (fun x : M ↦ TangentSpace I6 x) where
  inner := inducedMetricBilinear F
  symm := inducedMetric_symm F
  pos := hF.inducedMetric_pos
  continuousAt x := by
    change ContinuousAt (fun v : TangentSpace I6 x ↦
      inner ℝ (differential F x v) (differential F x v)) 0
    exact ((differential F x).continuous.inner (differential F x).continuous).continuousAt
  isVonNBounded x := by
    let : FiniteDimensional ℝ (TangentSpace I6 x) := inferInstanceAs (FiniteDimensional ℝ E6)
    apply (NormedSpace.isVonNBounded_iff ℝ).mpr
    obtain ⟨K, _, hK⟩ := (differential F x).toLinearMap.injective_iff_antilipschitz.mp
      (hF.differential_injective x)
    apply (hK.isBounded_preimage (Metric.isBounded_ball (x := (0 : E7)) (r := 1))).subset
    intro v hv
    change inducedMetricBilinear F x v v < 1 at hv
    change differential F x v ∈ Metric.ball (0 : E7) 1
    rw [Metric.mem_ball, dist_zero_right]
    have hv' : ‖differential F x v‖ ^ 2 < 1 := by
      simpa only [inducedMetricBilinear_apply, inducedMetric_self_eq_norm_sq] using hv
    nlinarith [norm_nonneg (differential F x v)]
def HasInducedRiemannianMetric (F : M → E7)
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I6 x)] : Prop :=
  ∀ (x : M) (v w : TangentSpace I6 x),
    (Bundle.RiemannianBundle.g (E := fun x : M ↦ TangentSpace I6 x)).inner x v w =
      inducedMetric F x v w
lemma SmoothImmersion.hasInducedRiemannianMetric [IsManifold I6 ∞ M]
    {F : M → E7} (hF : SmoothImmersion F) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I6 x) :=
      ⟨hF.toRiemannianMetric⟩
    HasInducedRiemannianMetric F := by
  intro x v w
  rfl

end StableBernstein.W01

namespace StableBernstein.W18

open Set Metric
variable {X : Type*} [MetricSpace X]

def ApproximateMidpoints (X : Type*) [MetricSpace X] : Prop :=
  ∀ x y : X, ∀ ε : ℝ, 0 < ε → ∃ z : X,
    dist x z ≤ dist x y / 2 + ε ∧ dist z y ≤ dist x y / 2 + ε
theorem approximate_dyadic_split (hm : ApproximateMidpoints X) (x y : X) (n : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ z : X,
      dist x z ≤ (1 - (1 / 2 : ℝ) ^ n) * dist x y + ε ∧
      dist z y ≤ (1 / 2 : ℝ) ^ n * dist x y + ε := by
  induction n with
  | zero =>
      intro ε hε
      refine ⟨x, ?_, ?_⟩ <;> simp only [pow_zero, sub_self, zero_mul, one_mul, dist_self] <;>
        linarith
  | succ n ih =>
      intro ε hε
      obtain ⟨z, hxz, hzy⟩ := ih (ε / 4) (by linarith)
      obtain ⟨w, hzw, hwy⟩ := hm z y (ε / 4) (by linarith)
      refine ⟨w, ?_, ?_⟩
      · have ht := dist_triangle x z w
        rw [pow_succ]
        nlinarith
      · rw [pow_succ]
        nlinarith
theorem compact_closedBall_extend [LocallyCompactSpace X]
    (hm : ApproximateMidpoints X) {x : X} {r : ℝ} (hr : 0 < r)
    (hc : IsCompact (closedBall x r)) :
    ∃ δ : ℝ, 0 < δ ∧ IsCompact (closedBall x (r + δ)) := by
  obtain ⟨τ, hτ, hcompact⟩ := hc.exists_isCompact_cthickening
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (div_pos hτ (mul_pos (by norm_num : (0 : ℝ) < 4) hr))
    (by norm_num : (1 / 2 : ℝ) < 1)
  let q : ℝ := (1 / 2 : ℝ) ^ n
  have hq : 0 < q := pow_pos (by norm_num) n
  have hq1 : q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hqr : q * r < τ / 4 := by
    have h := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hr)).1 hn
    dsimp [q]
    nlinarith
  let δ : ℝ := q * r / 4
  have hδ : 0 < δ := div_pos (mul_pos hq hr) (by norm_num)
  have hδeq : 4 * δ = q * r := by dsimp [δ]; ring
  refine ⟨δ, hδ, hcompact.of_isClosed_subset isClosed_closedBall ?_⟩
  intro y hy
  have hy' : dist x y ≤ r + δ := mem_closedBall'.1 hy
  obtain ⟨z, hxz, hzy⟩ := approximate_dyadic_split hm x y n δ hδ
  change dist x z ≤ (1 - q) * dist x y + δ at hxz
  change dist z y ≤ q * dist x y + δ at hzy
  have hxmul := mul_le_mul_of_nonneg_left hy' (sub_nonneg.mpr hq1)
  have hymul := mul_le_mul_of_nonneg_left hy' hq.le
  have hqδ := mul_le_mul_of_nonneg_right hq1 hδ.le
  have hqδ0 := mul_nonneg hq.le hδ.le
  have hz : z ∈ closedBall x r := mem_closedBall'.2 (by nlinarith)
  have hdist : dist z y ≤ τ := by nlinarith
  exact mem_cthickening_of_dist_le y z τ (closedBall x r) hz
    (by simpa only [dist_comm] using hdist)
theorem totallyBounded_closedBall_of_compact_smaller
    (hm : ApproximateMidpoints X) {x : X} {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ s : ℝ, s < r → IsCompact (closedBall x s)) :
    TotallyBounded (closedBall x r) := by
  apply Metric.totallyBounded_iff.2
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (div_pos hε (mul_pos (by norm_num : (0 : ℝ) < 8) hr))
    (by norm_num : (1 / 2 : ℝ) < 1)
  let q : ℝ := (1 / 2 : ℝ) ^ n
  have hq : 0 < q := pow_pos (by norm_num) n
  have hq1 : q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hqr : q * r < ε / 8 := by
    have h := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 8) hr)).1 hn
    dsimp [q]
    nlinarith
  let s : ℝ := r - q * r / 2
  have hs : s < r := by dsimp [s]; nlinarith [mul_pos hq hr]
  obtain ⟨t, _, ht, hcover⟩ := (hsmall s hs).finite_cover_balls (by linarith : 0 < ε / 2)
  refine ⟨t, ht, ?_⟩
  intro y hy
  have hy' : dist x y ≤ r := mem_closedBall'.1 hy
  have hδ : 0 < q * r / 4 := div_pos (mul_pos hq hr) (by norm_num)
  obtain ⟨z, hxz, hzy⟩ := approximate_dyadic_split hm x y n (q * r / 4) hδ
  change dist x z ≤ (1 - q) * dist x y + q * r / 4 at hxz
  change dist z y ≤ q * dist x y + q * r / 4 at hzy
  have hxmul := mul_le_mul_of_nonneg_left hy' (sub_nonneg.mpr hq1)
  have hymul := mul_le_mul_of_nonneg_left hy' hq.le
  have hz : z ∈ closedBall x s := by
    apply mem_closedBall'.2
    dsimp [s]
    nlinarith [mul_pos hq hr]
  have hnear : dist y z < ε / 2 := by
    rw [dist_comm]
    nlinarith
  obtain ⟨w, hw, hwz⟩ : ∃ w ∈ t, z ∈ ball w (ε / 2) := by
    obtain ⟨w, hw⟩ := mem_iUnion.1 (hcover hz)
    obtain ⟨hwt, hwz⟩ := mem_iUnion.1 hw
    exact ⟨w, hwt, hwz⟩
  refine mem_iUnion.2 ⟨w, mem_iUnion.2 ⟨hw, ?_⟩⟩
  apply mem_ball.2
  have hzw : dist z w < ε / 2 := mem_ball.1 hwz
  have htri := dist_triangle y z w
  linarith
theorem compact_closedBall_of_compact_smaller [CompleteSpace X]
    (hm : ApproximateMidpoints X) {x : X} {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ s : ℝ, s < r → IsCompact (closedBall x s)) :
    IsCompact (closedBall x r) :=
  isCompact_iff_totallyBounded_isComplete.2
    ⟨totallyBounded_closedBall_of_compact_smaller hm hr hsmall,
      isClosed_closedBall.isComplete⟩
theorem properSpace_of_complete_locallyCompact_approximateMidpoints
    [CompleteSpace X] [LocallyCompactSpace X] (hm : ApproximateMidpoints X) :
    ProperSpace X := by
  constructor
  intro x r
  by_contra hbad
  let S : Set ℝ := {s | IsCompact (closedBall x s)}
  obtain ⟨r₀, hr₀, hc₀⟩ := Metric.exists_isCompact_closedBall x
  have hne : S.Nonempty := ⟨r₀, hc₀⟩
  have hb : BddAbove S := by
    refine ⟨r, ?_⟩
    intro s hs
    by_contra hnot
    have hrs : r ≤ s := (lt_of_not_ge hnot).le
    exact hbad (hs.of_isClosed_subset isClosed_closedBall (closedBall_subset_closedBall hrs))
  let R : ℝ := sSup S
  have hR : 0 < R := lt_of_lt_of_le hr₀ (le_csSup hb hc₀)
  have hcR : IsCompact (closedBall x R) := by
    apply compact_closedBall_of_compact_smaller hm hR
    intro s hs
    obtain ⟨t, ht, hst⟩ := exists_lt_of_lt_csSup hne hs
    exact ht.of_isClosed_subset isClosed_closedBall (closedBall_subset_closedBall hst.le)
  obtain ⟨δ, hδ, hcδ⟩ := compact_closedBall_extend hm hR hcR
  have hle : R + δ ≤ R := le_csSup hb hcδ
  linarith

end StableBernstein.W18

namespace StableBernstein.W04
open Set MeasureTheory

theorem exists_half_speed_integral (v : ℝ → ℝ) (hv : Continuous v)
    (hn : ∀ t, 0 ≤ v t) :
    ∃ t ∈ Icc (0 : ℝ) 1,
      (∫ s in Icc 0 t, v s) = (∫ s in Icc 0 1, v s) / 2 := by
  have hp : ContinuousOn (fun t => ∫ s in Icc 0 t, v s) (Icc (0 : ℝ) 1) :=
    intervalIntegral.continuousOn_primitive_Icc hv.integrableOn_Icc
  have hnonneg : 0 ≤ ∫ s in Icc (0 : ℝ) 1, v s := integral_nonneg hn
  have hzero : (∫ s in Icc (0 : ℝ) 0, v s) = 0 := by simp
  have htarget : (∫ s in Icc (0 : ℝ) 1, v s) / 2 ∈
      Icc (∫ s in Icc (0 : ℝ) 0, v s) (∫ s in Icc (0 : ℝ) 1, v s) := by
    rw [hzero]
    constructor <;> linarith
  exact intermediate_value_Icc zero_le_one hp htarget

end StableBernstein.W04

namespace StableBernstein.W01

section

open scoped ContDiff Bundle
open Manifold

section
variable {M : Type*} [MetricSpace M] [ChartedSpace E6 M] [IsManifold I6 ∞ M]
  [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I6 x)]

structure CompleteInducedMetric (F : M → E7) : Prop where
  metric_induced : HasInducedRiemannianMetric F
  metric_smooth : IsContMDiffRiemannianBundle I6 ∞ E6 (fun x : M ↦ TangentSpace I6 x)
  distance_is_path_length : IsRiemannianManifold I6 M
  complete : CompleteSpace M
lemma CompleteInducedMetric.edist_eq {F : M → E7} (h : CompleteInducedMetric F)
    (x y : M) : edist x y = riemannianEDist I6 x y :=
  h.distance_is_path_length.out x y
instance tangentFiniteDimensional (x : M) : FiniteDimensional ℝ (TangentSpace I6 x) :=
  inferInstanceAs (FiniteDimensional ℝ E6)

end

variable {M : Type*} [MetricSpace M] [ChartedSpace E6 M] [manifold : IsManifold I6 ∞ M]
  [riemannian : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I6 x)]
local instance tangentCompleteSpace (x : M) : CompleteSpace (TangentSpace I6 x) :=
  FiniteDimensional.complete ℝ (TangentSpace I6 x)

omit manifold riemannian in
lemma tangent_dimension [IsManifold I6 ∞ M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I6 x)]
    (x : M) : Module.finrank ℝ (TangentSpace I6 x) = 6 :=
  finrank_euclideanSpace_fin
def tangentOrthonormalBasis (x : M) : OrthonormalBasis (Fin 6) ℝ (TangentSpace I6 x) :=
  (stdOrthonormalBasis ℝ (TangentSpace I6 x)).reindex (finCongr (tangent_dimension x))
def shapeOperator (F ν : M → E7) (x : M) :
    TangentSpace I6 x →L[ℝ] TangentSpace I6 x :=
  InnerProductSpace.continuousLinearMapOfBilin (𝕜 := ℝ) (secondFundamentalBilinear F ν x)
def meanCurvatureTrace (F ν : M → E7) (x : M) : ℝ :=
  LinearMap.trace ℝ (TangentSpace I6 x) (shapeOperator F ν x).toLinearMap
def Minimal (F ν : M → E7) : Prop := ∀ x, meanCurvatureTrace F ν x = 0
def curvatureNormSqInBasis (F ν : M → E7) (x : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I6 x)) : ℝ :=
  ∑ i, ∑ j, secondFundamentalForm F ν x (b i) (b j) ^ 2
def curvatureNormSq (F ν : M → E7) (x : M) : ℝ :=
  curvatureNormSqInBasis F ν x (tangentOrthonormalBasis x)

end

open scoped ContDiff Topology
open Manifold Bundle ContinuousLinearMap

section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E6 M] [IsManifold I6 ∞ M]
local instance smoothPullbackTangentNorm (x : M) : NormedAddCommGroup (TangentSpace I6 x) :=
  inferInstanceAs (NormedAddCommGroup E6)
local instance smoothPullbackTangentNormedSpace (x : M) : NormedSpace ℝ (TangentSpace I6 x) :=
  inferInstanceAs (NormedSpace ℝ E6)

def differentialPairingBilinear (F G : M → E7) (x : M) :
    TangentSpace I6 x →L[ℝ] TangentSpace I6 x →L[ℝ] ℝ :=
  (innerSL ℝ (E := E7)).bilinearComp (differential F x) (differential G x)
lemma contMDiff_differentialPairing (F G : M → E7)
    (hF : ContMDiff I6 I7 ∞ F) (hG : ContMDiff I6 I7 ∞ G) :
    ContMDiff I6 (I6.prod 𝓘(ℝ, E6 →L[ℝ] E6 →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (E6 →L[ℝ] E6 →L[ℝ] ℝ) x
        (differentialPairingBilinear F G x)) := by
  intro x₀
  rw [contMDiffAt_section]
  simp only [hom_trivializationAt_apply]
  let DF := inTangentCoordinates I6 I7 id F (mfderiv I6 I7 F) x₀
  let DG := inTangentCoordinates I6 I7 id G (mfderiv I6 I7 G) x₀
  have hDF : ContMDiffAt I6 𝓘(ℝ, E6 →L[ℝ] E7) ∞ DF x₀ :=
    (hF x₀).mfderiv_const (by simp)
  have hDG : ContMDiffAt I6 𝓘(ℝ, E6 →L[ℝ] E7) ∞ DG x₀ :=
    (hG x₀).mfderiv_const (by simp)
  let realInner : E7 →L[ℝ] E7 →L[ℝ] ℝ := innerSL ℝ
  have hB : ContMDiffAt I6 𝓘(ℝ, E6 →L[ℝ] E6 →L[ℝ] ℝ) ∞
      (fun x ↦ realInner.bilinearComp (DF x) (DG x)) x₀ := by
    convert (hDG.clm_precomp (F₃ := ℝ)).clm_comp
      ((contMDiffAt_const (c := realInner)).clm_comp hDF) using 1
    ext x v w
    rfl
  apply hB.congr_of_eventuallyEq
  filter_upwards [(trivializationAt E6 (TangentSpace I6 (M := M)) x₀).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt E6 (TangentSpace I6 (M := M)) x₀)] with x hx
  ext v w
  rw [inCoordinates_apply_eq₂ hx hx (Set.mem_univ _)]
  simp [realInner, DF, DG, inTangentCoordinates, inCoordinates, differentialPairingBilinear, differential,
    NormedSpace.fromTangentSpace, tangentSpaceCastModel]
  exact congrArg₂ (fun (u z : TangentSpace I6 x) =>
      inner ℝ (differential F x u) (differential G x z))
    (Trivialization.symmL_apply (R := ℝ) _ hx v).symm
    (Trivialization.symmL_apply (R := ℝ) _ hx w).symm
lemma contMDiff_inducedMetricBilinear (F : M → E7) (hF : ContMDiff I6 I7 ∞ F) :
    ContMDiff I6 (I6.prod 𝓘(ℝ, E6 →L[ℝ] E6 →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (E6 →L[ℝ] E6 →L[ℝ] ℝ) x (inducedMetricBilinear F x)) :=
  contMDiff_differentialPairing F F hF hF

end

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E6 M] [IsManifold I6 ∞ M]
open scoped Bundle

lemma HasInducedRiemannianMetric.isContMDiffRiemannianBundle
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I6 x)]
    {F : M → E7} (hmetric : HasInducedRiemannianMetric F) (hF : SmoothImmersion F) :
    IsContMDiffRiemannianBundle I6 ∞ E6 (fun x : M ↦ TangentSpace I6 x) :=
  ⟨inducedMetricBilinear F, contMDiff_inducedMetricBilinear F hF.smooth, hmetric⟩

end StableBernstein.W01

namespace StableBernstein.W04

open Manifold MeasureTheory Set Filter
open scoped Bundle ContDiff ENNReal NNReal Topology
open W01
variable {M : Type*} [MetricSpace M] [ChartedSpace E6 M] [IsManifold I6 ∞ M]
  [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I6 x)]

theorem induced_continuousRiemannianBundle {F : M → E7} (hg : CompleteInducedMetric F) :
    IsContinuousRiemannianBundle E6 (fun x : M ↦ TangentSpace I6 x) := by
  obtain ⟨g, hcont, heq⟩ := hg.metric_smooth.exists_contMDiff
  exact ⟨⟨g, hcont.continuous, heq⟩⟩
theorem continuous_intrinsic_speed {F : M → E7} (hg : CompleteInducedMetric F)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I6 1 γ) :
    Continuous (fun t => ‖mfderiv 𝓘(ℝ, ℝ) I6 γ t (1 : ℝ)‖) := by
  let := induced_continuousRiemannianBundle hg
  have hsection : Continuous (fun t : ℝ =>
      (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hv : Continuous (fun t : ℝ =>
      (⟨γ t, mfderiv 𝓘(ℝ, ℝ) I6 γ t (1 : ℝ)⟩ : TangentBundle I6 M)) :=
    (hγ.continuous_tangentMap le_rfl).comp hsection
  have hi : Continuous (fun t => inner ℝ
      (mfderiv 𝓘(ℝ, ℝ) I6 γ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I6 γ t (1 : ℝ))) :=
    hv.inner_bundle hv
  simpa only [norm_eq_sqrt_real_inner, Function.comp_def] using Real.continuous_sqrt.comp hi
theorem pathELength_eq_ofReal_speed_integral {F : M → E7} (hg : CompleteInducedMetric F)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I6 1 γ) (a b : ℝ) :
    pathELength I6 γ a b = ENNReal.ofReal
      (∫ t in Icc a b, ‖mfderiv 𝓘(ℝ, ℝ) I6 γ t (1 : ℝ)‖) := by
  rw [pathELength_eq_lintegral_mfderiv_Icc]
  simp_rw [← ofReal_norm]
  exact (ofReal_integral_eq_lintegral_ofReal
    (continuous_intrinsic_speed hg hγ).integrableOn_Icc
    (Eventually.of_forall fun _ => norm_nonneg _)).symm
theorem induced_approximateMidpoints {F : M → E7} (hg : CompleteInducedMetric F) :
    W18.ApproximateMidpoints M := by
  intro x y ε hε
  have hpositive : 0 < dist x y + ε := add_pos_of_nonneg_of_pos dist_nonneg hε
  have hr : riemannianEDist I6 x y < ENNReal.ofReal (dist x y + ε) := by
    rw [← hg.edist_eq, edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff hpositive).mpr (by linarith)
  obtain ⟨γ, hx, hy, hγ, hlen, _, _⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hr (show (0 : ℝ) < 1 from zero_lt_one)
  let v : ℝ → ℝ := fun t => ‖mfderiv 𝓘(ℝ, ℝ) I6 γ t (1 : ℝ)‖
  let L : ℝ → ℝ → ℝ := fun a b => ∫ t in Icc a b, v t
  have hv : Continuous v := continuous_intrinsic_speed hg hγ
  have hvnonneg : ∀ t, 0 ≤ v t := fun _ => norm_nonneg _
  have hLnonneg (a b : ℝ) : 0 ≤ L a b := integral_nonneg hvnonneg
  have hlength (a b : ℝ) : pathELength I6 γ a b = ENNReal.ofReal (L a b) :=
    pathELength_eq_ofReal_speed_integral hg hγ a b
  obtain ⟨t, ht, hhalf⟩ := exists_half_speed_integral v hv hvnonneg
  change L 0 t = L 0 1 / 2 at hhalf
  have htotal : L 0 1 < dist x y + ε := by
    apply (ENNReal.ofReal_lt_ofReal_iff hpositive).mp
    simpa only [hlength] using hlen
  have hadd := pathELength_add (I := I6) (γ := γ) ht.1 ht.2
  rw [hlength 0 t, hlength t 1, hlength 0 1,
    ← ENNReal.ofReal_add (hLnonneg 0 t) (hLnonneg t 1)] at hadd
  have haddReal := congrArg ENNReal.toReal hadd
  rw [ENNReal.toReal_ofReal (add_nonneg (hLnonneg 0 t) (hLnonneg t 1)),
    ENNReal.toReal_ofReal (hLnonneg 0 1)] at haddReal
  have hleft := riemannianEDist_le_pathELength hγ.contMDiffOn hx rfl ht.1
  have hright := riemannianEDist_le_pathELength hγ.contMDiffOn rfl hy ht.2
  rw [← hg.edist_eq, edist_dist, hlength 0 t] at hleft
  rw [← hg.edist_eq, edist_dist, hlength t 1] at hright
  have hleftReal := (ENNReal.ofReal_le_ofReal_iff (hLnonneg 0 t)).mp hleft
  have hrightReal := (ENNReal.ofReal_le_ofReal_iff (hLnonneg t 1)).mp hright
  refine ⟨γ t, ?_, ?_⟩ <;> linarith
theorem induced_properSpace {F : M → E7} (hg : CompleteInducedMetric F) : ProperSpace M := by
  let : CompleteSpace M := hg.complete
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E6 M
  exact W18.properSpace_of_complete_locallyCompact_approximateMidpoints
    (induced_approximateMidpoints hg)

end StableBernstein.W04

namespace StableBernstein.W03

open Manifold Set Bundle
open scoped ContDiff Topology Bundle
open StableBernstein.W01

theorem edist_lt_top_of_preconnected {X : Type*} [PseudoEMetricSpace X]
    [PreconnectedSpace X] (x y : X) : edist x y < ⊤ := by
  have hcl : IsClopen (Metric.eball y ⊤) :=
    ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩
  have hall : Metric.eball y ⊤ = univ :=
    hcl.eq_univ ⟨y, Metric.mem_eball_self (by simp)⟩
  have hx : x ∈ Metric.eball y ⊤ := by rw [hall]; trivial
  exact hx

open StableBernstein.W01
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E6 M]
  [IsManifold I6 ∞ M] [hausdorff : T2Space M] [preconnected : PreconnectedSpace M]

omit hausdorff preconnected in
theorem inducedRiemannianBundle_continuous [T2Space M] [PreconnectedSpace M]
    {F : M → E7} (hF : SmoothImmersion F) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I6 x) := ⟨hF.toRiemannianMetric⟩
    IsContinuousRiemannianBundle E6 (fun x : M ↦ TangentSpace I6 x) := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I6 x) := ⟨hF.toRiemannianMetric⟩
  exact ⟨inducedMetricBilinear F,
    (contMDiff_inducedMetricBilinear F hF.smooth).continuous, fun _ _ _ ↦ rfl⟩
@[reducible] def canonicalInducedMetricSpace {F : M → E7} (hF : SmoothImmersion F) : MetricSpace M := by
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E6 M
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I6 x) := ⟨hF.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E6 (fun x : M ↦ TangentSpace I6 x) :=
    inducedRiemannianBundle_continuous hF
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I6 M
  exact EMetricSpace.toMetricSpace (fun x y ↦ (edist_lt_top_of_preconnected x y).ne)
theorem canonicalInducedMetricSpace_edist {F : M → E7} (hF : SmoothImmersion F) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I6 x) := ⟨hF.toRiemannianMetric⟩
    letI : MetricSpace M := canonicalInducedMetricSpace hF
    ∀ x y : M, edist x y = riemannianEDist I6 x y := by
  intro x y
  rfl
theorem canonicalInducedMetricSpace_isRiemannian {F : M → E7} (hF : SmoothImmersion F) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I6 x) := ⟨hF.toRiemannianMetric⟩
    letI : MetricSpace M := canonicalInducedMetricSpace hF
    IsRiemannianManifold I6 M := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I6 x) := ⟨hF.toRiemannianMetric⟩
  let : MetricSpace M := canonicalInducedMetricSpace hF
  exact ⟨canonicalInducedMetricSpace_edist hF⟩
def CanonicallyCompleteInducedMetric {F : M → E7} (hF : SmoothImmersion F) : Prop :=
  letI : MetricSpace M := canonicalInducedMetricSpace hF
  CompleteSpace M
theorem completeInducedMetric_of_canonical_complete {F : M → E7} (hF : SmoothImmersion F)
    (hcomplete : CanonicallyCompleteInducedMetric hF) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I6 x) := ⟨hF.toRiemannianMetric⟩
    letI : MetricSpace M := canonicalInducedMetricSpace hF
    CompleteInducedMetric F := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I6 x) := ⟨hF.toRiemannianMetric⟩
  let : MetricSpace M := canonicalInducedMetricSpace hF
  exact ⟨hF.hasInducedRiemannianMetric,
    hF.hasInducedRiemannianMetric.isContMDiffRiemannianBundle hF,
    canonicalInducedMetricSpace_isRiemannian hF, hcomplete⟩

end StableBernstein.W03

namespace StableBernstein

open scoped ContDiff Bundle
open Manifold
universe u
open W01 W02

def FullConclusion {M : Type*} [TopologicalSpace M] [ChartedSpace E6 M]
    (F ν : M → E7) : Prop :=
  (∀ (x : M) (v w : TangentSpace I6 x), secondFundamentalForm F ν x v w = 0) ∧
  ∃ P : AffineSubspace ℝ E7,
    Module.finrank ℝ P.direction = 6 ∧ Set.range F = (P : Set E7)

end StableBernstein

namespace StableBernstein.W02

section

open MeasureTheory Manifold Matrix
open scoped Bundle ContDiff ENNReal
open StableBernstein.W01
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E6 M] [IsManifold I6 ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace I6 x)]

def inverseChartBasisVector (x : M) (y : E6) (i : Fin 6) :
    TangentSpace I6 ((extChartAt I6 x).symm y) :=
  mfderiv I6 I6 (extChartAt I6 x).symm y
    ((NormedSpace.fromTangentSpace y).symm (EuclideanSpace.single i 1))
def chartMetricMatrix (F : M → E7) (x : M) (y : E6) : Matrix (Fin 6) (Fin 6) ℝ :=
  fun i j => inducedMetric F ((extChartAt I6 x).symm y)
    (inverseChartBasisVector x y i) (inverseChartBasisVector x y j)
def chartVolumeDensity (F : M → E7) (x : M) (y : E6) : ℝ :=
  Real.sqrt (Matrix.det (chartMetricMatrix F x y))

end

open MeasureTheory Manifold Bundle Set Filter
open scoped Bundle ContDiff Topology ENNReal

section
open StableBernstein.W01
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E6 M] [IsManifold I6 ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I6 x)]

def chartInverseExtension (x : M) : E6 → M := by
  classical
  exact (extChartAt I6 x).target.piecewise (extChartAt I6 x).symm (fun _ => x)
def chartRiemannianMeasure (F : M → E7) (x : M) : Measure M :=
  Measure.map (chartInverseExtension x)
    ((volume.restrict (extChartAt I6 x).target).withDensity
      (fun y => ENNReal.ofReal (chartVolumeDensity F x y)))

end

open StableBernstein.W01
variable {M : Type*} [MetricSpace M] [measurable : MeasurableSpace M] [borel : BorelSpace M]
  [ChartedSpace E6 M] [manifold : IsManifold I6 ∞ M]
  [riemannian : RiemannianBundle (fun x : M => TangentSpace I6 x)]
  [SecondCountableTopology M] [Nonempty M]

omit measurable borel manifold riemannian in
lemma exists_countable_chart_cover [MeasurableSpace M] [BorelSpace M]
    [IsManifold I6 ∞ M] [RiemannianBundle (fun x : M => TangentSpace I6 x)] :
    ∃ c : ℕ → M, (⋃ n, (extChartAt I6 (c n)).source) = univ := by
  obtain ⟨s, hsc, hsU⟩ := countable_cover_nhds
    (fun x : M => (isOpen_extChartAt_source (I := I6) x).mem_nhds (mem_extChartAt_source x))
  have hsne : s.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h] at hsU
    exact Set.empty_ne_univ (by simpa using hsU)
  obtain ⟨c, hc⟩ := hsc.exists_eq_range hsne
  refine ⟨c, ?_⟩
  simpa only [hc, biUnion_range] using hsU
def volumeChartCenters : ℕ → M := Classical.choose (exists_countable_chart_cover (M := M))
def volumeChartPiece (n : ℕ) : Set M :=
  disjointed (fun n => (extChartAt I6 (volumeChartCenters (M := M) n)).source) n
def riemannianVolume (F : M → E7) : Measure M :=
  Measure.sum (fun n => (chartRiemannianMeasure F (volumeChartCenters n)).restrict (volumeChartPiece n))

end StableBernstein.W02

namespace StableBernstein

open Manifold
open scoped ContDiff Bundle
open W01 W02
universe u

def RiemannianGeometricStability {M : Type u}
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E6 M] [IsManifold I6 ∞ M]
    [SecondCountableTopology M] [Nonempty M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I6 x)]
    (F ν : M → E7) : Prop :=
  IntrinsicStability I6 (riemannianVolume F) (curvatureNormSq F ν)

end StableBernstein

open Manifold Bundle
open scoped ContDiff Bundle
namespace StableBernstein
open W01 W02 W03
universe u

theorem secondCountable_of_complete_induced_metric
    {M : Type u} [MetricSpace M] [ChartedSpace E6 M] [IsManifold I6 ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I6 x)]
    {F : M → E7} (hmetric : CompleteInducedMetric F) : SecondCountableTopology M := by
  let : ProperSpace M := W04.induced_properSpace hmetric
  infer_instance
theorem canonical_complete_secondCountable
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace E6 M] [IsManifold I6 ∞ M] [PreconnectedSpace M]
    {F : M → E7} (hF : SmoothImmersion F)
    (hc : CanonicallyCompleteInducedMetric hF) : SecondCountableTopology M := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I6 x) := ⟨hF.toRiemannianMetric⟩
  let : MetricSpace M := canonicalInducedMetricSpace hF
  exact secondCountable_of_complete_induced_metric
    (completeInducedMetric_of_canonical_complete hF hc)
def IntrinsicStableBernstein : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace E6 M] [IsManifold I6 ∞ M] [Nonempty M] [ConnectedSpace M]
    (F ν : M → E7) (hF : SmoothImmersion F)
    (hc : CanonicallyCompleteInducedMetric hF),
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I6 x) := ⟨hF.toRiemannianMetric⟩
    letI : MetricSpace M := canonicalInducedMetricSpace hF
    letI : MeasurableSpace M := borel M
    letI : BorelSpace M := ⟨rfl⟩
    letI : SecondCountableTopology M := canonical_complete_secondCountable hF hc
    GlobalUnitNormal F ν → Minimal F ν → RiemannianGeometricStability F ν →
      FullConclusion F ν

end StableBernstein

end

end OAI
