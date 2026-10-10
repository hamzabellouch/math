import Mathlib
import OAI.Probability.SKBarriers.Scalar.SuffixPartitionSusceptibility
import OAI.Probability.SKBarriers.Hierarchy.ConstantWeightMean
import OAI.Probability.SKBarriers.Parisi.CDFJointSusceptibility
import OAI.Probability.SKBarriers.Locking.NarrowScheduleScale
import OAI.Probability.SKBarriers.Locking.NarrowBlockStats
import OAI.Probability.SKBarriers.Locking.NarrowTimeAnalytic
import OAI.Probability.SKBarriers.Locking.FourBlockAtom
import OAI.Probability.SKBarriers.Locking.FourBlockQuadratic
import OAI.Probability.SKBarriers.Locking.FourBlockMass

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def narrowCDFMean (β : ℝ) (α : ℝ → ℝ) (r h θ : ℝ) : ℝ := β^2*(θ/h)*(∫ x in r..r+h,α x)

namespace NarrowTimeBlocks
variable {α : ℝ → ℝ} {r h q : ℝ} (C : NarrowTimeBlocks α r h q)

theorem scaled_v_mean (β : ℝ) (hα : Monotone α) (θ : ℝ) :
    weightedMean (scaleIncrementChain β (C.v θ))=narrowCDFMean β α r h θ := by
  rw [weightedMean_scale,C.v_mean,C.right_area hα]
  unfold narrowCDFMean; ring

theorem quadratic_le (β : ℝ) (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hmα : Monotone α)
    (hr : 0≤r) (hrq : r≤q) (hq : q≤1) (hh : 0<h) {a θ : ℝ} (ha : 0<a) (hθ : 0≤θ) :
    narrowBaseQuadratic (scaleIncrementChain β (C.c a)) (scaleIncrementChain β (C.v θ))
      (scaleIncrementChain β (C.w a)) (scaleIncrementChain β C.t)≤
      β^2*((2*a^2+θ^2)/h)*scalarCDFSusceptibilityAverage β α q+
      2*narrowCDFMean β α r h θ*(β^2*a)*scalarCDFJointSusceptibility β α r q+
      narrowTentError (narrowCDFMean β α r h θ) (β^2*a) (β^2*θ) (α (r+h)-α (r-h)) := by
  let b := scaleIncrementChain β C.b
  let l := scaleIncrementChain β C.l
  let j := scaleIncrementChain β C.j
  let k := scaleIncrementChain β C.k
  let t := scaleIncrementChain β C.t
  let κ := a/h
  let η := θ/h
  have hc : scaleIncrementChain β (C.c a)=fourBlockCommon κ b l := by
    simp only [c,scaleIncrementChain_append,zeroWeightChain_scale,constantWeightChain_scale]; rfl
  have hv : scaleIncrementChain β (C.v θ)=fourBlockFuture η j k := by
    simp only [v,scaleIncrementChain_append,zeroWeightChain_scale,constantWeightChain_scale]; rfl
  have hw : scaleIncrementChain β (C.w a)=fourBlockFuture (-κ) j k := by
    simp only [w,scaleIncrementChain_append,zeroWeightChain_scale,constantWeightChain_scale,neg_div]; rfl
  have heFull : (b++l)++(j++k)++t=scaleIncrementChain β
      (weightedUnderlying (C.c a)++weightedUnderlying (C.w a)++C.t) := by
    simp only [C.c_underlying,C.w_underlying,scaleIncrementChain_append]; rfl
  have hm : ∀ p∈(b++l)++(j++k)++t,p.1∈Icc (0:ℝ) 1 := by
    rw [heFull]; exact scaleIncrementChain_mass β _ (C.full_mass a)
  have hs : ((b++l)++(j++k)++t).Pairwise (fun p q => p.1≤q.1) := by
    rw [heFull]; exact scaleIncrementChain_sorted β _ (C.full_sorted hmα a)
  have hmF := fourBlockTent_mass κ b l j k (fun p hp => hm p (List.mem_append_left _ hp))
  have hsF := fourBlockTent_sorted κ b l j k (List.pairwise_append.mp hs).1
  have M := C.v_mean_bounds hmα hh hθ
  have hM : 0≤weightedMean (scaleIncrementChain β (C.v θ)) := by
    rw [weightedMean_scale]
    exact mul_nonneg (sq_nonneg β) ((mul_nonneg hθ (hα r).1).trans M.1)
  have hmean : 0≤weightedMean (fourBlockFuture η j k) := hv ▸ hM
  have hB : 0≤β^2*a := mul_nonneg (sq_nonneg β) ha.le
  have hn := ne_of_gt hh
  have an := ne_of_gt ha
  have hld : rawVariance l=(β^2*a)*(h/a) := by
    dsimp only [l]; rw [rawVariance_scale,C.l_variance]
    field_simp
  have hjd : rawVariance j=(β^2*a)*(h/a) := by
    dsimp only [j]; rw [rawVariance_scale,C.j_variance]
    field_simp
  have HK : κ*(h/a)=1 := by dsimp only [κ]; field_simp
  have H := fourBlockQuadratic_tent_le κ η b l j k t hm hs hmean (div_pos hh ha) hB HK hld hjd
  let A := scalarTentAtomMass (fourBlockTent κ b l j k).length (fun i => ((fourBlockTent κ b l j k).get i).1)
      (fourBlockLeft κ b l j k) (fourBlockRight κ b l j k)
  have hA : 0≤A := scalarTentAtomMass_nonneg _ _ (fun i => hmF _ (List.get_mem _ i))
    (mass_get_monotone hsF) _ _
  have hlL : 0<l.length := by
    dsimp only [l]; simp only [scaleIncrementChain,List.length_map]
    exact rawVariance_pos_length (show 0<rawVariance C.l by rw [C.l_variance]; exact hh)
  have hjL : 0<j.length := by
    dsimp only [j]; simp only [scaleIncrementChain,List.length_map]
    exact rawVariance_pos_length (show 0<rawVariance C.j by rw [C.j_variance]; exact hh)
  have hAω : A≤α (r+h)-α (r-h) := fourBlockTent_atom_le κ b l j k hlL hjL
    (scaleIncrementChain_mass (P:=fun x => α (r-h)≤x) β _ (fun p hp => (C.left.raw_mass_interval hmα p hp).1))
    (scaleIncrementChain_mass (P:=fun x => x≤α (r+h)) β _ (fun p hp => (C.right.raw_mass_interval hmα p hp).2))
  have Herr := narrowTentError_mono (R:=weightedAbsCross (fourBlockFuture η j k)) hmean hB hA hAω
  have H0 : narrowBaseQuadratic (fourBlockCommon κ b l) (fourBlockFuture η j k) (fourBlockFuture (-κ) j k) t≤narrowVariance (fourBlockCommon κ b l) (fourBlockFuture η j k) (fourBlockFuture (-κ) j k)*
      narrowSusceptibility (fourBlockCommon κ b l) (fourBlockFuture (-κ) j k) t+
      2*weightedMean (fourBlockFuture η j k)*(β^2*a)*narrowJointMoment (fourBlockCommon κ b l) (fourBlockFuture (-κ) j k) t+
      narrowTentError (weightedMean (fourBlockFuture η j k)) (β^2*a) (weightedAbsCross (fourBlockFuture η j k)) A := by
    simpa only [narrowTentError,A,add_assoc] using H
  have H' := H0.trans (add_le_add le_rfl Herr)
  rw [← hc,← hv,← hw] at H'
  rw [narrowVariance_scale,C.variance_stats hn,C.scalar_susceptibility β hα hmα ⟨hr.trans hrq,hq⟩ a,
    C.scalar_joint β hα hmα hr hrq hq a,C.scaled_v_mean β hmα θ,weightedAbsCross_scale,C.v_absCross hh hθ] at H'
  exact H'

end NarrowTimeBlocks

end SK.Analytic

end
end

end OAI
