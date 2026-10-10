import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveOperatorStability

namespace OAI

/-! Compact C1 control of the actual inverse and square-root amplitude map.
The parameter bounds are fixed before a later family is composed with it. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance amplitudeFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance amplitudeFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance amplitudeFiberComplete : CompleteSpace TensorFiber := inferInstance
local instance amplitudeDualAdd : ContinuousAdd (Plane →L[ℝ] ℝ) := inferInstance
local instance amplitudeDualSmul : ContinuousSMul ℝ (Plane →L[ℝ] ℝ) := inferInstance
local instance amplitudeFiberGroup : AddCommGroup TensorFiber := amplitudeFiberNormed.toAddCommGroup
variable {ι : Type*} [Fintype ι]

abbrev PrimitiveAmplitudeData (ι : Type*) := PrimitiveOperatorData ι × TensorFiber

def primitiveParameterInverse (z : PrimitiveAmplitudeData ι) : TensorFiber →L[ℝ] TensorFiber :=
  (primitiveDataOperator z.1).inverse

def primitiveParameterCoefficient (i : ι) (z : PrimitiveAmplitudeData ι) : ℝ :=
  z.1.1.1 i (primitiveParameterInverse z z.2)

def primitiveParameterAmplitude (i : ι) (z : PrimitiveAmplitudeData ι) : ℝ :=
  z.1.1.2 i * Real.sqrt (primitiveParameterCoefficient i z)

lemma primitiveParameterInverse_smoothAt {z : PrimitiveAmplitudeData ι}
    (hz : (primitiveDataOperator z.1).IsInvertible) :
    ContDiffAt ℝ ∞ primitiveParameterInverse z :=
  hz.contDiffAt_map_inverse.comp z
    (primitiveDataOperator_smooth.contDiffAt.comp z contDiffAt_fst)

lemma primitiveParameterCoefficient_smoothAt (i : ι) {z : PrimitiveAmplitudeData ι}
    (hz : (primitiveDataOperator z.1).IsInvertible) :
    ContDiffAt ℝ ∞ (primitiveParameterCoefficient i) z := by
  have hq : ContDiff ℝ ∞ (fun w : PrimitiveAmplitudeData ι => w.1.1.1 i) := by
    exact (contDiff_apply ℝ (TensorFiber →L[ℝ] ℝ) i).comp
      (contDiff_fst.comp (contDiff_fst.comp contDiff_fst))
  exact hq.contDiffAt.clm_apply
    ((primitiveParameterInverse_smoothAt hz).clm_apply contDiffAt_snd)

lemma primitiveParameterAmplitude_smoothAt (i : ι) {z : PrimitiveAmplitudeData ι}
    (hz : (primitiveDataOperator z.1).IsInvertible)
    (hp : 0 < primitiveParameterCoefficient i z) :
    ContDiffAt ℝ ∞ (primitiveParameterAmplitude i) z := by
  have hw : ContDiff ℝ ∞ (fun w : PrimitiveAmplitudeData ι => w.1.1.2 i) := by
    exact (contDiff_apply ℝ ℝ i).comp
      (contDiff_snd.comp (contDiff_fst.comp contDiff_fst))
  exact hw.contDiffAt.mul ((Real.contDiffAt_sqrt hp.ne').comp z
    (primitiveParameterCoefficient_smoothAt i hz))

private def parameterNormData (i : ι) (z : PrimitiveAmplitudeData ι) :=
  (primitiveParameterInverse z,
    (fderiv ℝ primitiveParameterInverse z,
      (primitiveParameterAmplitude i z, fderiv ℝ (primitiveParameterAmplitude i) z)))

private lemma parameterNormData_continuousAt (i : ι) {z : PrimitiveAmplitudeData ι}
    (hz : (primitiveDataOperator z.1).IsInvertible)
    (hp : 0 < primitiveParameterCoefficient i z) :
    ContinuousAt (parameterNormData i) z := by
  have hi := primitiveParameterInverse_smoothAt hz
  have ha := primitiveParameterAmplitude_smoothAt i hz hp
  exact hi.continuousAt.prodMk
    ((hi.continuousAt_fderiv (by simp)).prodMk
      (ha.continuousAt.prodMk (ha.continuousAt_fderiv (by simp))))

/-- One neighborhood and one C1 constant control inverse operators and actual
amplitudes uniformly around any compact positive family of finite data. -/
theorem compact_primitive_amplitude_C1 (i : ι) {K : Set (PrimitiveAmplitudeData ι)}
    (hK : IsCompact K)
    (hgood : ∀ z ∈ K, (primitiveDataOperator z.1).IsInvertible ∧
      0 < primitiveParameterCoefficient i z) :
    ∃ eps C : ℝ, 0 < eps ∧ 1 ≤ C ∧
      ∀ z ∈ K, ∀ z' : PrimitiveAmplitudeData ι, ‖z'-z‖ < eps →
        (primitiveDataOperator z'.1).IsInvertible ∧
        0 < primitiveParameterCoefficient i z' ∧
        ‖primitiveParameterInverse z'‖ ≤ C ∧
        ‖fderiv ℝ primitiveParameterInverse z'‖ ≤ C ∧
        |primitiveParameterAmplitude i z'| ≤ C ∧
        ‖fderiv ℝ (primitiveParameterAmplitude i) z'‖ ≤ C := by
  have hc : ContinuousOn (parameterNormData i) K := fun z hz =>
    (parameterNormData_continuousAt i (hgood z hz).1 (hgood z hz).2).continuousWithinAt
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn (f := parameterNormData i) hc
  let C : ℝ := max 1 (B+1)
  let O : Set (PrimitiveAmplitudeData ι) := {z |
    (primitiveDataOperator z.1).IsInvertible ∧
    0 < primitiveParameterCoefficient i z ∧ ‖parameterNormData i z‖ < C}
  have hO : IsOpen O := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hg : ∀ᶠ w in 𝓝 z,
        (primitiveDataOperator w.1).IsInvertible ∧
          0 < primitiveParameterCoefficient i w :=
      (isOpen_primitiveDataPositive i).eventually_mem ⟨hz.1,hz.2.1⟩
    have hnorm : ContinuousAt (fun w => ‖parameterNormData i w‖) z :=
      ContinuousAt.norm (f := parameterNormData i)
        (parameterNormData_continuousAt i hz.1 hz.2.1)
    have hn : ∀ᶠ w in 𝓝 z, ‖parameterNormData i w‖ < C :=
      hnorm.eventually (gt_mem_nhds hz.2.2)
    exact (hg.and hn).mono (fun _ h => ⟨h.1.1,h.1.2,h.2⟩)
  have hKO : K ⊆ O := by
    intro z hz
    refine ⟨(hgood z hz).1,(hgood z hz).2,?_⟩
    exact (hB z hz).trans_lt ((lt_add_one B).trans_le (le_max_right _ _))
  obtain ⟨eps,heps,hnear⟩ := hK.exists_thickening_subset_open hO hKO
  refine ⟨eps,C,heps,le_max_left _ _,?_⟩
  intro z hz z' hdist
  have hmem : z' ∈ O := hnear (Metric.mem_thickening_iff.mpr
    ⟨z,hz,by simpa only [dist_eq_norm] using hdist⟩)
  have hb : ‖parameterNormData i z'‖ ≤ C := hmem.2.2.le
  have hinv := (norm_fst_le (parameterNormData i z')).trans hb
  have hder := (norm_fst_le (parameterNormData i z').2).trans
    ((norm_snd_le (parameterNormData i z')).trans hb)
  have ha := (norm_fst_le (parameterNormData i z').2.2).trans
    ((norm_snd_le (parameterNormData i z').2).trans
      ((norm_snd_le (parameterNormData i z')).trans hb))
  have had := (norm_snd_le (parameterNormData i z').2.2).trans
    ((norm_snd_le (parameterNormData i z').2).trans
      ((norm_snd_le (parameterNormData i z')).trans hb))
  change ‖primitiveParameterAmplitude i z'‖ ≤ C at ha
  exact ⟨hmem.1,hmem.2.1,hinv,hder,by simpa only [Real.norm_eq_abs] using ha,had⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
