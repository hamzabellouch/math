import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.UniformEnvelope
import OAI.Analysis.BiholderTransport.Regularity.MovingPrefix
import OAI.Analysis.BiholderTransport.LocalFlow.ModelTangentJet

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section FrameMetric
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def frameMetric (a:M) (b:Model n) : Model n →L[ℝ] Model n →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (movingPrefixEnergy a 1 b)) 0

omit [Nonempty M] in
lemma frameMetric_apply {a:M} {b:Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (d e:Model n) :
    frameMetric a b d e=inner ℝ (chartFiberInverse a b d) (chartFiberInverse a b e) := by
  have hp : (1:ℝ) • chartFiberInverse a b 0∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) := by
    simpa only [map_zero,smul_zero] using zero_mem_injectivityDomain
      (n := n) ((extChartAt 𝓘(ℝ,Model n) a).symm b)
  simpa only [frameMetric,chartFiberInverse,one_mul] using movingPrefixEnergy_hessian hb hp d e

omit [Nonempty M] in
lemma frameMetric_continuousAt {a:M} {b:Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) : ContinuousAt (frameMetric a) b := by
  have hp : (1:ℝ) • chartFiberInverse a b 0∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) := by
    simpa only [map_zero,smul_zero] using zero_mem_injectivityDomain
      (n := n) ((extChartAt 𝓘(ℝ,Model n) a).symm b)
  have H := (ContDiffAt.partial_snd_fderiv_two (movingPrefixEnergy_contDiffAt hb hp)).continuousAt
  exact ContinuousAt.comp (f := fun z:Model n=>(z,(0:Model n))) H
    (show ContinuousAt (fun z:Model n=>(z,(0:Model n))) b from
    continuousAt_id.prodMk continuousAt_const)

omit [Nonempty M] in
lemma frameMetric_center (a:M) (d e:Model n) :
    frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) d e=
      inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from d) e := by
  rw [frameMetric_apply ((extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a))]
  have ha := (extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)
  dsimp only [chartFiberInverse]
  rw [ha,center_frame_identity,center_frame_identity]

omit [Nonempty M] in
lemma frameMetric_center_coercive (a:M) : ∃ δ>0,∀ d:Model n,
    δ*‖d‖^2≤frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) d d := by
  let T := trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a
  let A := T.continuousLinearMapAt ℝ a
  let K := ‖A‖+1
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨1/K^2,by positivity,?_⟩
  intro d
  have hid : A (show TangentSpace 𝓘(ℝ,Model n) a from d)=d := by
    have H := T.continuousLinearMapAt_symmL (R := ℝ) (mem_baseSet_trivializationAt (Model n)
      (TangentSpace 𝓘(ℝ,Model n)) a) d
    simpa only [T,center_frame_identity] using H
  have hnorm := A.le_opNorm (show TangentSpace 𝓘(ℝ,Model n) a from d)
  rw [hid] at hnorm
  have hnorm' : ‖d‖≤K*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖ :=
    hnorm.trans (mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (norm_nonneg _))
  rw [frameMetric_center,real_inner_self_eq_norm_sq]
  have H := pow_le_pow_left₀ (norm_nonneg d) hnorm' 2
  rw [mul_pow] at H
  calc
    1/K^2*‖d‖^2 = ‖d‖^2/K^2 := by ring
    _ ≤ ‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2 :=
      (div_le_iff₀ (sq_pos_of_pos hK)).mpr (by nlinarith only [H])

end FrameMetric
end WeakMTWTransport

end
end

end OAI
