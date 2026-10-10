import OAI.Geometry.SurfaceImmersion.Geometry.InitialInputBounds
import OAI.Geometry.SurfaceImmersion.Correction.AdaptiveExactControl

namespace OAI

/-! Build the first actual correction stage from finite metric accuracy. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance initialStageFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance initialStageFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance initialStageDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance initialStageDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance initialStageSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance initialStageSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
variable {g : SmoothMetric M} {F : M → Space} {d : CorrectionGeometry g F}
namespace PreparedCorrection

/-- All conditions refer only to the original immersion through order 442
and its metric error through order 440. The first corrected map is the
specified scalar contraction, with no existence hypothesis on a sequence. -/
theorem initial_stage_of_scaled_bounds (c : PreparedCorrection d)
    (hF : ContMDiff planeModel spaceModel ∞ F)
    {t σ P Q C D e : ℝ} (ht : 0 < t) (htsmall : t ≤ 1/32) (htε : t < c.ε 0)
    (hσ : 0 < σ) (htσ : t ≤ σ)
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hD : 0 ≤ D) (he : 0 ≤ e)
    (hmap0 : d.A.ShiftedBound 2 0 1 P F) (hmap : d.A.ShiftedBound 2 440 σ C F)
    (hmetric0 : d.A.TensorWeightedBound 1 0 Q g.inner)
    (hmetric : d.A.TensorWeightedBound 1 440 D g.inner)
    (herror : d.A.TensorWeightedBound t 440 ((t^(10 : ℝ))^2*e) (inducedTensor F-g.inner))
    (hMB : P+(t/σ)*C ≤ c.budget) (hHB : Q+t*D+e ≤ c.budget)
    (hnear : (t^(10 : ℝ))^2*P ≤ c.ρ/8) (hemetric : e ≤ c.a/8) :
    ∃ seed : c.Stage t 0, seed.map = Real.sqrt (1-(t^(10 : ℝ))^2) • F := by
  let δ := t^(10 : ℝ)
  let G := Real.sqrt (1-δ^2) • F
  have ht1 : t ≤ 1 := by linarith
  have hδ : 0 < δ := Real.rpow_pos_of_pos ht _
  have hδle : δ ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  have hδsq : δ^2 ≤ 1 := pow_le_one₀ hδ.le hδle
  have hG : ContMDiff planeModel spaceModel ∞ G := space_smul_contMDiff hF _
  have hmap0σ : d.A.ShiftedBound 2 0 σ P F := by
    intro i j hj x
    have hj2 : j - 2 = 0 := by omega
    simpa only [hj2,pow_zero,one_mul] using hmap0 i j hj x
  have hin := d.A.contracted_initial_input_scaled hF (ne_of_gt hδ) hδsq ht.le ht1
    hσ htσ hP hC hD he hmap0σ hmap hmetric0 hmetric herror hMB hHB
  have hdisp : d.A.WeightedBound 1 2 (c.ρ/8) (G-F) := by
    have hbase := d.A.shifted_zero_to_weighted hmap0
    have hh := d.A.weightedBound_const_smul hF hbase (Real.sqrt (1-δ^2)-1)
    have hid : G-F = (Real.sqrt (1-δ^2)-1) • F := by
      dsimp [G]
      rw [sub_smul,one_smul]
    rw [hid]
    intro i
    apply (hh i).mono_const
    exact (mul_le_mul_of_nonneg_right (initial_contraction_displacement hδsq) hP).trans hnear
  have hdef := d.A.normalized_initial_error_bound hF g.contMDiff
    (ne_of_gt hδ) hδsq he herror
  have hencoded := d.A.tensorEncode_bound
    ((d.A.normalizedTensorDefect_smooth g.contMDiff δ hG).sub_section g.contMDiff)
    ht he (fun i => (hdef i).mono_order (show 0 ≤ 440 from Nat.zero_le _))
  have hm : ∀ x, ‖d.A.tensorEncode (normalizedTensorDefect g.inner δ G) x-
      d.A.tensorEncode g.inner x‖ ≤ c.a/8 := by
    intro x
    have hh := (hencoded.norm_le (mem_univ x)).trans hemetric
    simpa only [d.A.tensorEncode_sub,Pi.sub_apply] using hh
  refine ⟨⟨0,G,hG,?_,?_,?_,?_⟩,rfl⟩
  · exact htε
  · simpa only [ExactCorrection.correctionScale,correctionInputOrder,correctionOrder,
      Nat.zero_add,Nat.cast_ofNat,show 40*(10+1) = 440 from rfl] using hin
  · simpa only [stageRadius,Finset.range_zero,Finset.sum_empty,mul_zero,add_zero] using hdisp
  · simpa only [ExactCorrection.correctionScale,correctionOrder,Nat.zero_add,Nat.cast_ofNat] using hm


/-- All conditions refer only to the original immersion through order 442
and its metric error through order 440. The first corrected map is the
specified scalar contraction, with no existence hypothesis on a sequence. -/
theorem initial_stage_of_bounds (c : PreparedCorrection d)
    (hF : ContMDiff planeModel spaceModel ∞ F)
    {t P Q C D e : ℝ} (ht : 0 < t) (htsmall : t ≤ 1/32) (htε : t < c.ε 0)
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hD : 0 ≤ D) (he : 0 ≤ e)
    (hmap0 : d.A.ShiftedBound 2 0 1 P F) (hmap : d.A.ShiftedBound 2 440 1 C F)
    (hmetric0 : d.A.TensorWeightedBound 1 0 Q g.inner)
    (hmetric : d.A.TensorWeightedBound 1 440 D g.inner)
    (herror : d.A.TensorWeightedBound t 440 ((t^(10 : ℝ))^2*e) (inducedTensor F-g.inner))
    (hMB : P+t*C ≤ c.budget) (hHB : Q+t*D+e ≤ c.budget)
    (hnear : (t^(10 : ℝ))^2*P ≤ c.ρ/8) (hemetric : e ≤ c.a/8) :
    ∃ seed : c.Stage t 0, seed.map = Real.sqrt (1-(t^(10 : ℝ))^2) • F := by
  exact c.initial_stage_of_scaled_bounds hF ht htsmall htε zero_lt_one
    (by linarith) hP hC hD he hmap0 hmap hmetric0 hmetric herror
    (by simpa only [div_one] using hMB) hHB hnear hemetric


/-- The actual exact correction tends to the original map in C² as the
initial smoothing scale tends to zero. This retains the size of the initial
contraction instead of replacing it by the fixed geometric radius. -/
theorem exact_correction_initial_displacement (c : PreparedCorrection d)
    (hF : ContMDiff planeModel spaceModel ∞ F) {t P : ℝ}
    (ht : 0 < t) (htsmall : t ≤ 1/32) (hP : 0 ≤ P)
    (hmap : d.A.ShiftedBound 2 0 1 P F)
    (seed : c.Stage t 0)
    (hseed : seed.map = Real.sqrt (1-(t^(10 : ℝ))^2) • F) :
    ∃ G : M → Space, IsSmoothIsometricImmersion M g G ∧
      d.A.WeightedBound 1 2 ((t^(10 : ℝ))^2*P+2*c.ρ*t) (G-F) := by
  have ht1 : t ≤ 1 := by linarith
  have hδle : t^(10 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  have hδsq : (t^(10 : ℝ))^2 ≤ 1 :=
    pow_le_one₀ (Real.rpow_nonneg ht.le _) hδle
  have hbase := d.A.shifted_zero_to_weighted hmap
  have hh := d.A.weightedBound_const_smul hF hbase (Real.sqrt (1-(t^(10 : ℝ))^2)-1)
  have hsf : d.A.WeightedBound 1 2 ((t^(10 : ℝ))^2*P) (seed.map-F) := by
    have hid : seed.map-F = (Real.sqrt (1-(t^(10 : ℝ))^2)-1) • F := by
      rw [hseed,sub_smul,one_smul]
    rw [hid]
    intro i
    exact (hh i).mono_const
      (mul_le_mul_of_nonneg_right (initial_contraction_displacement hδsq) hP)
  obtain ⟨G,hG,hGs,_⟩ := c.exact_correction_with_control hF ht htsmall seed
  refine ⟨G,hG,?_⟩
  have hb := d.A.weightedBound_add (seed.smooth.sub hF) (hG.1.sub seed.smooth)
    zero_le_one hsf hGs
  have hid : G-F = (seed.map-F)+(G-seed.map) := by abel
  rw [hid]
  exact hb

end PreparedCorrection
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
