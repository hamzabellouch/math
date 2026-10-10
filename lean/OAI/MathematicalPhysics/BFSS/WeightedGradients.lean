import Mathlib
import OAI.MathematicalPhysics.BFSS.ClosedProfiles
import OAI.MathematicalPhysics.BFSS.SobolevGraphs
import OAI.MathematicalPhysics.BFSS.LocalL2

namespace OAI

/-! Weighted smooth cutoff approximation and limiting profile gradients. -/

namespace BFSSSliceSobolev
noncomputable section
open MeasureTheory Set Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem exists_small_weight_cutoff (w : E → ℝ) (hw : Continuous w) (hw0 : 0 < w 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ φ : ContDiffBump (0 : E), φ.rOut < η ∧
      ∀ x ∈ Metric.closedBall 0 φ.rOut, w 0/2 ≤ w x := by
  have hn : {x : E | w 0/2 < w x} ∈ 𝓝 0 :=
    hw.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by linarith : w 0/2 < w 0))
  obtain ⟨r,hr,hs⟩ := Metric.mem_nhds_iff.mp hn
  let s := min r η / 2
  have hs0 : 0 < s := half_pos (lt_min hr hη)
  have hsr : s < r := by dsimp [s]; nlinarith [min_le_left r η]
  have hsη : s < η := by dsimp [s]; nlinarith [min_le_right r η]
  let φ : ContDiffBump (0 : E) := ⟨s/2,s,half_pos hs0,by linarith⟩
  refine ⟨φ,hsη,?_⟩
  intro x hx
  exact (hs (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt hsr))).le

def cutoffRatio (w : E → ℝ) (φ : ContDiffBump (0 : E)) (x : E) : ℝ :=
  w 0*φ x / max (w 0/2) (w x)

omit [MeasurableSpace E] [BorelSpace E] in
lemma cutoffRatio_continuous (w : E → ℝ) (hw : Continuous w) (hw0 : 0 < w 0)
    (φ : ContDiffBump (0 : E)) : Continuous (cutoffRatio w φ) := by
  apply (continuous_const.mul φ.continuous).div (continuous_const.max hw)
  intro x
  exact ne_of_gt ((half_pos hw0).trans_le (le_max_left _ _))

omit [MeasurableSpace E] [BorelSpace E] in
lemma cutoffRatio_bound (w : E → ℝ) (hw0 : 0 < w 0) (φ : ContDiffBump (0 : E)) (x : E) :
    |cutoffRatio w φ x| ≤ 2 := by
  have hd : 0 < max (w 0/2) (w x) := (half_pos hw0).trans_le (le_max_left _ _)
  unfold cutoffRatio
  rw [abs_of_nonneg (div_nonneg (mul_nonneg hw0.le φ.nonneg) hd.le),div_le_iff₀ hd]
  have hp := mul_le_mul_of_nonneg_left (φ.le_one (x := x)) hw0.le
  nlinarith [le_max_left (w 0/2) (w x)]

omit [MeasurableSpace E] [BorelSpace E] in
lemma cutoffRatio_zero (w : E → ℝ) (hw0 : 0 < w 0) (φ : ContDiffBump (0 : E)) :
    cutoffRatio w φ 0 = 1 := by
  unfold cutoffRatio
  rw [φ.one_of_mem_closedBall (by simpa using φ.rIn_pos.le), max_eq_right (by linarith : w 0/2 ≤ w 0),mul_one,div_self hw0.ne']

omit [MeasurableSpace E] [BorelSpace E] in
lemma cutoffRatio_mul (w : E → ℝ) (hw0 : 0 < w 0) (φ : ContDiffBump (0 : E))
    (hφ : ∀ x ∈ Metric.closedBall 0 φ.rOut, w 0/2 ≤ w x) (x : E) :
    cutoffRatio w φ x * w x = w 0*φ x := by
  by_cases hx : x ∈ Metric.closedBall 0 φ.rOut
  · have hp := hφ x hx
    have hx0 : w x ≠ 0 := ne_of_gt ((half_pos hw0).trans_le hp)
    unfold cutoffRatio
    rw [max_eq_right hp,div_mul_cancel₀ _ hx0]
  · have hz : φ x = 0 := φ.zero_of_le_dist (le_of_lt (lt_of_not_ge (Metric.mem_closedBall.not.mp hx)))
    simp only [cutoffRatio,hz,mul_zero,zero_div,zero_mul]

variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

omit [CompleteSpace F] in
theorem smooth_raw_tendsto (w : E → ℝ) (hw : Continuous w) (hw0 : 0 < w 0)
    (φ : ContDiffBump (0 : E)) (hφ : ∀ x ∈ Metric.closedBall 0 φ.rOut, w 0/2 ≤ w x)
    (h : ℕ → ℝ) (hzero : Tendsto h atTop (𝓝 0))
    (f : ℕ → Core (E := E) (F := F)) (p : ℕ → Lp F 2 μ) (u : Lp F 2 μ)
    (hp : ∀ n, (p n : E → F) =ᵐ[μ] fun x => w (h n • x) • f n x)
    (hu : Tendsto p atTop (𝓝 u)) :
    Tendsto (fun n => toL2 μ ((w 0) • scaledCutoff φ (h n) (f n))) atTop (𝓝 u) := by
  let a : ℕ → E → ℝ := fun n x => cutoffRatio w φ (h n • x)
  have ha (n : ℕ) : Continuous (a n) :=
    (cutoffRatio_continuous w hw hw0 φ).comp (continuous_const.smul continuous_id)
  have haB (n : ℕ) : ∀ᵐ x ∂μ, |a n x| ≤ 2 :=
    Filter.Eventually.of_forall (fun x => cutoffRatio_bound w hw0 φ _)
  have halim : ∀ᵐ x ∂μ, Tendsto (fun n => a n x) atTop (𝓝 1) := by
    filter_upwards [] with x
    have hx : Tendsto (fun n => h n • x) atTop (𝓝 (0 : E)) := by
      simpa only [zero_smul] using hzero.smul_const x
    have hc : Tendsto (cutoffRatio w φ) (𝓝 (0 : E)) (𝓝 (cutoffRatio w φ 0)) :=
      (cutoffRatio_continuous w hw hw0 φ).continuousAt
    rw [cutoffRatio_zero w hw0 φ] at hc
    exact hc.comp hx
  have ht := BFSSLocalL2.boundedMul_tendsto a (fun n => (ha n).aestronglyMeasurable)
    2 (by norm_num) haB halim p u hu
  have he (n : ℕ) : BFSSLocalL2.boundedMul (a n) (ha n).aestronglyMeasurable 2 (haB n) (p n) =
      toL2 μ ((w 0) • scaledCutoff φ (h n) (f n)) := by
    apply Lp.ext
    filter_upwards [BFSSLocalL2.boundedMul_ae (a n) (ha n).aestronglyMeasurable 2 (haB n) (p n),
      hp n,toL2_ae μ ((w 0) • scaledCutoff φ (h n) (f n))] with x hx hp hx'
    rw [hx,hp,hx']
    change a n x • (w (h n • x) • f n x) = w 0 • (φ (h n • x) • f n x)
    rw [smul_smul,smul_smul,cutoffRatio_mul w hw0 φ hφ]
  simpa only [he] using ht
end
end BFSSSliceSobolev
namespace BFSSSliceSobolev
noncomputable section
open MeasureTheory Set Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
variable {ι : Type*} [Fintype ι] (e : ι → E)

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma op_derivative_sq_integrable (f : Core (E := E) (F := F)) :
    Integrable (fun x => ‖fderiv ℝ (f : E → F) x‖^2) μ := by
  have hc : Continuous (fderiv ℝ (f : E → F)) := f.contDiff.continuous_fderiv (by simp)
  apply (hc.norm.pow 2).integrable_of_hasCompactSupport
  have hf := f.hasCompactSupport.fderiv ℝ
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  filter_upwards [hf] with x hx
  simp only [Pi.zero_apply] at hx ⊢
  change ‖fderiv ℝ (f : E → F) x‖^2 = 0
  rw [hx,norm_zero,zero_pow (by decide : 2 ≠ 0)]

omit [CompleteSpace F] in
theorem scaledCutoff_gradient_bound (φ : ContDiffBump (0 : E)) {h D A B : ℝ}
    (hh : 0 < h) (hD : ∀ x, ‖fderiv ℝ (φ : E → ℝ) x‖ ≤ D)
    (he : ∀ j, ‖e j‖ = 1) (f : Core (E := E) (F := F))
    (hA : (∫ x in Metric.closedBall 0 (φ.rOut/h), ‖fderiv ℝ (f : E → F) x‖^2 ∂μ) ≤ A)
    (hB : (∫ x in Metric.closedBall 0 (φ.rOut/h), ‖f x‖^2 ∂μ) ≤ B) :
    ‖gradient μ e (scaledCutoff φ h f)‖^2 ≤
      (Fintype.card ι : ℝ)*(2*A+2*(D*h)^2*B) := by
  classical
  let S : Set E := Metric.closedBall 0 (φ.rOut/h)
  let g := scaledCutoff φ h f
  have hsupport : tsupport (g : E → F) ⊆ S := scaledCutoff_support φ hh f
  have hfi : Integrable (fun x => ‖f x‖^2) μ :=
    (f.continuous.norm.pow 2).integrable_of_hasCompactSupport (norm_sq_compact f f.hasCompactSupport)
  have hfdi := op_derivative_sq_integrable μ f
  have hbound (j : ι) : (∫ x, ‖fderiv ℝ (g : E → F) x (e j)‖^2 ∂μ) ≤
      2*A+2*(D*h)^2*B := by
    calc
      _ = ∫ x in S, ‖fderiv ℝ (g : E → F) x (e j)‖^2 ∂μ := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        have hz : fderiv ℝ (g : E → F) x = 0 := by
          by_contra hn
          exact hx (hsupport (support_fderiv_subset ℝ hn))
        simp only [hz,_root_.zero_apply,norm_zero,zero_pow (by decide : 2 ≠ 0)]
      _ ≤ ∫ x in S, 2*‖fderiv ℝ (f : E → F) x‖^2+2*(D*h)^2*‖f x‖^2 ∂μ := by
        exact setIntegral_mono_on (derivative_sq_integrable μ g (e j)).integrableOn
          ((hfdi.const_mul 2).add (hfi.const_mul (2*(D*h)^2))).integrableOn
          Metric.isClosed_closedBall.measurableSet
          (fun x _ => scaledCutoff_fderiv_bound φ hh.le hD f x (e j) (he j))
      _ = 2*(∫ x in S, ‖fderiv ℝ (f : E → F) x‖^2 ∂μ)+
          2*(D*h)^2*(∫ x in S, ‖f x‖^2 ∂μ) := by
        rw [integral_add (hfdi.integrableOn.const_mul 2) (hfi.integrableOn.const_mul (2*(D*h)^2))]
        simp only [integral_const_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num))
        (mul_le_mul_of_nonneg_left hB (by positivity))
  rw [gradient_norm_sq,integral_finsetSum]
  · calc
      _ ≤ ∑ j : ι, (2*A+2*(D*h)^2*B) := Finset.sum_le_sum (fun j _ => hbound j)
      _ = _ := by simp; ring
  · intro j _
    exact derivative_sq_integrable μ g (e j)
end
end BFSSSliceSobolev

namespace BFSSSliceSobolev
noncomputable section
open MeasureTheory Set Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [TopologicalSpace.SeparableSpace F]
variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
variable {ι : Type*} [Fintype ι] (e : ι → E)

theorem local_bounds_closedGradient (w : E → ℝ) (hw : Continuous w) (hw0 : 0 < w 0)
    (he : ∀ j, ‖e j‖ = 1) {η A B : ℝ} (hη : 0 < η) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n ∧ h n ≤ 1) (hzero : Tendsto h atTop (𝓝 0))
    (raw : ℕ → Core (E := E) (F := F))
    (hbound : ∀ n R, 0 ≤ R → h n*R < η →
      (∫ x in Metric.closedBall 0 R, ‖raw n x‖^2 ∂μ) ≤ B ∧
      (∫ x in Metric.closedBall 0 R, ‖fderiv ℝ (raw n : E → F) x‖^2 ∂μ) ≤ A)
    (profiles : ℕ → Lp F 2 μ) (u : Lp F 2 μ)
    (hreps : ∀ n, (profiles n : E → F) =ᵐ[μ] fun x => w (h n • x) • raw n x)
    (hu : Tendsto profiles atTop (𝓝 u)) :
    ∃ v : Gradient (F := F) μ (ι := ι), (u,v) ∈ closedGraph μ e := by
  classical
  obtain ⟨φ,hφη,hφw⟩ := exists_small_weight_cutoff w hw hw0 hη
  have hφder : Continuous (fderiv ℝ (φ : E → ℝ)) :=
    (φ.contDiff : ContDiff ℝ 1 (φ : E → ℝ)).continuous_fderiv (by norm_num)
  obtain ⟨D₀,hD₀⟩ := ((φ.hasCompactSupport.fderiv ℝ).isCompact_range hφder).isBounded.exists_norm_le
  let D := max D₀ 0
  have hD0 : 0 ≤ D := le_max_right _ _
  have hD : ∀ x, ‖fderiv ℝ (φ : E → ℝ) x‖ ≤ D :=
    fun x => (hD₀ _ (mem_range_self x)).trans (le_max_left _ _)
  let a := fun n => (w 0) • scaledCutoff φ (h n) (raw n)
  have ha : Tendsto (fun n => toL2 μ (a n)) atTop (𝓝 u) :=
    smooth_raw_tendsto μ w hw hw0 φ hφw h hzero raw profiles u hreps hu
  let d : ℝ := Fintype.card ι
  have hd : 0 ≤ d := Nat.cast_nonneg _
  let C := d*(2*A+2*D^2*B)
  have hC0 : 0 ≤ C := mul_nonneg hd (add_nonneg (by positivity) (by positivity))
  have hgn (n : ℕ) : ‖gradient μ e (a n)‖ ≤ w 0*Real.sqrt C := by
    have hR : 0 ≤ φ.rOut/h n := div_nonneg φ.rOut_pos.le (hh n).1.le
    have hRh : h n*(φ.rOut/h n) < η := by
      have heq : h n*(φ.rOut/h n) = φ.rOut := by field_simp [(hh n).1.ne']
      rw [heq]
      exact hφη
    have hb := hbound n (φ.rOut/h n) hR hRh
    have hAi := hb.2
    have hBi := hb.1
    have hs := scaledCutoff_gradient_bound μ e φ (hh n).1 hD
      he (raw n) hAi hBi
    have hhD : (D*h n)^2 ≤ D^2 :=
      pow_le_pow_left₀ (mul_nonneg hD0 (hh n).1.le) (mul_le_of_le_one_right hD0 (hh n).2) 2
    have hsC : ‖gradient μ e (scaledCutoff φ (h n) (raw n))‖^2 ≤ C :=
      hs.trans (mul_le_mul_of_nonneg_left
        (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhD (by norm_num)) hB)) hd)
    have hgs : ‖gradient μ e (scaledCutoff φ (h n) (raw n))‖ ≤ Real.sqrt C :=
      (Real.le_sqrt (norm_nonneg _) hC0).mpr hsC
    change ‖gradient μ e ((w 0) • _)‖ ≤ _
    rw [map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hw0]
    exact mul_le_mul_of_nonneg_left hgs hw0.le
  obtain ⟨v,σ,hσ,hv,_,_⟩ := closedGraph_extract μ e a u
    (w 0*Real.sqrt C) ha hgn
  exact ⟨v,hv⟩
end
end BFSSSliceSobolev

namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory Set Filter Topology
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] normalSlice gaugeAction coreToL2 normalCoordinateField normalCoreField

def normalCoordinateCore (q : Boson N) (h : ℝ) (f : SmoothCore N) :
    BFSSSliceSobolev.Core (E := M.NormalCoordinates q) (F := Fermion N) :=
  ⟨M.normalCoordinateField q h f,M.normalCoordinateField_contDiff q h f,
    M.normalCoordinateField_compactSupport q h f,by intro x hx; trivial⟩

lemma normalCoordinateCore_apply (q : Boson N) (h : ℝ) (f : SmoothCore N)
    (x : M.NormalCoordinates q) : M.normalCoordinateCore q h f x = M.normalCoordinateField q h f x := rfl
end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData.GaugeData
noncomputable section
open MeasureTheory Set
variable {N : ℕ} {M : AlgebraData N} (G : M.GaugeData)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2
  AlgebraData.normalCoordinateField AlgebraData.normalCoordinateCore AlgebraData.normalCoreField
local instance weightedGradientsSliceNormedAddCommGroup (q : Boson N) : NormedAddCommGroup (M.normalSlice q →L[ℝ] Fermion N) := inferInstance
local instance weightedGradientsSliceNormedSpace (q : Boson N) : NormedSpace ℝ (M.normalSlice q →L[ℝ] Fermion N) := inferInstance
local instance weightedGradientsCoordinateNormedAddCommGroup (q : Boson N) : NormedAddCommGroup (M.NormalCoordinates q →L[ℝ] Fermion N) := inferInstance
local instance weightedGradientsCoordinateNormedSpace (q : Boson N) : NormedSpace ℝ (M.NormalCoordinates q →L[ℝ] Fermion N) := inferInstance

lemma normalCoordinateCore_local_bounds (hN : 2 ≤ N) (q : Boson N) :
    ∃ η B K : ℝ, 0 < η ∧ 0 < B ∧ 0 ≤ K ∧
    ∀ h R : ℝ, 0 < h → h ≤ 1 → 0 ≤ R → h*R < η →
    ∀ f : G.invariantCore,
      (∫ x : M.NormalCoordinates q in Metric.closedBall 0 R, ‖M.normalCoordinateCore q h f.val x‖^2) ≤
        B * ‖coreToL2 f.val‖^2 ∧
      (∫ x : M.NormalCoordinates q in Metric.closedBall 0 R,
        ‖fderiv ℝ (M.normalCoordinateCore q h f.val : M.NormalCoordinates q → Fermion N) x‖^2) ≤
        B * (M.deformedCoreEnergy h 1 f.val + K*‖coreToL2 f.val‖^2) := by
  obtain ⟨η,B,K,hη,hB,hK,hbound⟩ := G.normalCoreField_local_bounds hN q
  refine ⟨η,B,K,hη,hB,hK,?_⟩
  intro h R hh hh1 hR hhR f
  have hb := hbound h R hh hh1 hR hhR f
  constructor
  · unfold AlgebraData.normalCoordinateCore
    change (∫ x : M.NormalCoordinates q in Metric.closedBall 0 R, ‖M.normalCoordinateField q h f.val x‖^2) ≤ _
    rw [M.normalCoordinateField_integral]
    exact hb.1
  · unfold AlgebraData.normalCoordinateCore
    change (∫ x : M.NormalCoordinates q in Metric.closedBall 0 R, ‖fderiv ℝ (M.normalCoordinateField q h f.val) x‖^2) ≤ _
    exact (M.normalCoordinateField_derivative_integral q h R f.val).trans hb.2
end
end BFSSQuantum.AlgebraData.GaugeData
namespace BFSSQuantum.AlgebraData.GaugeData.MeasuredNormalPatch
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal
variable {N : ℕ} {M : AlgebraData N} {G : M.GaugeData} {q : Boson N}
variable (P : G.MeasuredNormalPatch q)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2
  AlgebraData.normalCoordinateField AlgebraData.normalCoordinateCore AlgebraData.normalCoreField

local instance weightedGradientsPatchSliceNormedAddCommGroup : NormedAddCommGroup (M.normalSlice q →L[ℝ] Fermion N) := inferInstance
local instance weightedGradientsPatchSliceNormedSpace : NormedSpace ℝ (M.normalSlice q →L[ℝ] Fermion N) := inferInstance
local instance weightedGradientsPatchCoordinateNormedAddCommGroup : NormedAddCommGroup (M.NormalCoordinates q →L[ℝ] Fermion N) := inferInstance
local instance weightedGradientsPatchCoordinateNormedSpace : NormedSpace ℝ (M.NormalCoordinates q →L[ℝ] Fermion N) := inferInstance

local instance weightedGradientsFermionSeparableSpace : TopologicalSpace.SeparableSpace (Fermion N) := inferInstance
local instance weightedGradientsFermionCompleteSpace : CompleteSpace (Fermion N) := inferInstance
local instance weightedGradientsFermionInnerProductSpace : InnerProductSpace ℝ (Fermion N) := inferInstance

lemma coordinateWeight_zero_pos : 0 < M.normalCoordinateWeight q P.density P.cutoff 0 := by
  have hq := P.cutoff_one q (P.orbit_neighborhood (M.self_mem_gaugeOrbit q))
  simp only [AlgebraData.normalCoordinateWeight,map_zero,Submodule.coe_zero,add_zero,hq,mul_one]
  exact Real.sqrt_pos.mpr P.density_zero_pos

theorem profile_limit_gradient (hN : 2 ≤ N) (h : ℕ → ℝ)
    (hh : ∀ n, 0 < h n ∧ h n ≤ 1) (hzero : Tendsto h atTop (𝓝 0))
    (f : ℕ → G.invariantCore) (E : ℝ≥0)
    (hnorm : ∀ n, ‖coreToL2 (f n).val‖^2 ≤ E)
    (henergy : ∀ n, M.deformedCoreEnergy (h n) 1 (f n).val ≤ E)
    (u : Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)))
    (hu : Tendsto (fun n => P.profile (h n) (f n)) atTop (𝓝 u)) :
    ∃ v : BFSSSliceSobolev.Gradient (F := Fermion N) (volume : Measure (M.NormalCoordinates q))
        (ι := Fin (Module.finrank ℝ (M.normalSlice q))),
      (u,v) ∈ BFSSSliceSobolev.closedGraph volume
        (EuclideanSpace.basisFun (Fin (Module.finrank ℝ (M.normalSlice q))) ℝ) := by
  classical
  let w := M.normalCoordinateWeight q P.density P.cutoff
  have hw : Continuous w := M.normalCoordinateWeight_continuous q P.density P.cutoff
    P.density_continuous P.cutoff_continuous
  have hw0 : 0 < w 0 := P.coordinateWeight_zero_pos
  have hlocal := @BFSSQuantum.AlgebraData.GaugeData.normalCoordinateCore_local_bounds N M G hN q
  rcases hlocal with ⟨η,B,K,hη,hB,hK,hbound⟩
  let e := EuclideanSpace.basisFun (Fin (Module.finrank ℝ (M.normalSlice q))) ℝ
  let raw := fun n => M.normalCoordinateCore q (h n) (f n).val
  apply BFSSSliceSobolev.local_bounds_closedGradient volume e w hw hw0
    (fun j => e.orthonormal.norm_eq_one j) hη
    (mul_nonneg hB.le (add_nonneg E.property (mul_nonneg hK E.property)))
    (mul_nonneg hB.le E.property) h hh hzero raw ?_ (fun n => P.profile (h n) (f n)) u ?_ hu
  · intro n R hR hhR
    have hb := hbound (h n) R (hh n).1 (hh n).2 hR hhR (f n)
    exact ⟨hb.1.trans (mul_le_mul_of_nonneg_left (hnorm n) hB.le),
      hb.2.trans (mul_le_mul_of_nonneg_left
        (add_le_add (henergy n) (mul_le_mul_of_nonneg_left (hnorm n) hK)) hB.le)⟩
  · intro n
    filter_upwards [P.profile_ae (h n) (f n)] with x hx
    rw [hx, AlgebraData.normalMeasuredCoordinates]
    dsimp only [raw]
    rw [AlgebraData.normalCoordinateCore_apply]
end
end BFSSQuantum.AlgebraData.GaugeData.MeasuredNormalPatch

end OAI
