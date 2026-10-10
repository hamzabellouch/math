import Mathlib
import OAI.Probability.Perceptron.Cascade.WeightedCDF
import OAI.Probability.Perceptron.Variational.SynchronizedLimit

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma scalarArray_nonnegative (μ : Measure PairedOverlapArray) [IsProbabilityMeasure μ]
    (hGG : JointGhirlandaGuerra μ) {f : ℝ×ℝ→ℝ} (hf : Measurable f)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray f Q)))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, f (Q i i) ≤ 1) :
    ∀ᵐ Q ∂μ, 0 ≤ f (Q 0 1) := by
  let ν := μ.map (scalarArray f)
  have hm := scalarArray_measurable hf
  have : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  have hg : ∀ᵐ Q ∂ν, ∀ n, Matrix.PosSemidef (overlapBlock id n Q) :=
    (ae_map_iff hm.aemeasurable measurableSet_gram_arrays).mpr hGram
  have hd : ∀ᵐ Q ∂ν, ∀ i, Q i i ≤ 1 :=
    (ae_map_iff hm.aemeasurable (by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun i =>  measurableSet_le
        ((measurable_pi_apply i).comp (measurable_pi_apply i)) measurable_const)).mpr hdiag
  have hs : ∀ᵐ Q ∂ν, ∀ i j, Q i j=Q j i := hg.mono fun Q hQ =>  gram_array_symmetric Q hQ
  have hp (n : ℕ) : ∀ᵐ Q ∂ν, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, Q i j := by
    filter_upwards [hg] with Q hQ
    simpa [dotProduct,Matrix.mulVec,overlapBlock] using (hQ n).dotProduct_mulVec_nonneg (fun _ =>  (1:ℝ))
  have hn := gg_overlap_nonnegative ν (fun i j =>  by fun_prop) hs hd hp (scalarArray_gg μ hGG hf)
  exact ae_of_ae_map hm.aemeasurable hn

lemma compact_spin_nonnegative (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hGG : JointGhirlandaGuerra (compactRealLaw ν))
    (hR : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), ∀ n, Matrix.PosSemidef (fun i j : Fin n =>  (Q i j).1.val)) :
    ∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), 0 ≤ (Q 0 1).1.val := by
  have hr : ∀ᵐ Q ∂compactRealLaw ν, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray Prod.fst Q)) :=
    ae_map_iff compactArrayReal_measurable.aemeasurable (measurableSet_gram_arrays.preimage
      (scalarArray_measurable measurable_fst)) |>.mpr hR
  exact ae_of_ae_map compactArrayReal_measurable.aemeasurable
    (scalarArray_nonnegative (compactRealLaw ν) hGG measurable_fst hr (compactRealLaw_diagonals ν).1)

def compactPositivePair (x : CompactJointOverlap) : Time×Time :=
  (⟨max 0 x.1.val,le_max_left _ _,max_le (by norm_num) x.1.property.2⟩,x.2)

lemma compactPositivePair_measurable : Measurable compactPositivePair := by
  unfold compactPositivePair
  fun_prop

def compactPositivePairLaw (ν : ProbabilityMeasure (CompactArray CompactJointOverlap)) : Measure (Time×Time) :=
  (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => compactPositivePair (Q 0 1))

instance compactPositivePairLaw_probability (ν : ProbabilityMeasure (CompactArray CompactJointOverlap)) :
    IsProbabilityMeasure (compactPositivePairLaw ν) :=
  (Measure.isProbabilityMeasure_map_iff ((compactPositivePair_measurable.comp (show Measurable (fun Q : CompactArray CompactJointOverlap => Q 0 1) from by fun_prop)).aemeasurable)).2 inferInstance

lemma compactPositivePairLaw_no_crossing (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hGG : JointGhirlandaGuerra (compactRealLaw ν))
    (hNo : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _),
      ¬ ((Q 0 1).1.val < (Q 0 2).1.val ∧ (Q 0 2).2.val < (Q 0 1).2.val)) (r t : Time) :
    compactPositivePairLaw ν (Iic r×ˢIoi t)=0 ∨ compactPositivePairLaw ν (Ioi r×ˢIic t)=0 := by
  let A : Set (ℝ×ℝ) := {x | max 0 x.1 ≤ r.val ∧ t.val < x.2}
  let B : Set (ℝ×ℝ) := {x | r.val < max 0 x.1 ∧ x.2 ≤ t.val}
  have hA : MeasurableSet A := by dsimp [A]; measurability
  have hB : MeasurableSet B := by dsimp [B]; measurability
  have hno : ∀ᵐ Q ∂compactRealLaw ν, ¬ ((Q 0 1).1 < (Q 0 2).1 ∧ (Q 0 2).2 < (Q 0 1).2) :=
    (ae_map_iff compactArrayReal_measurable.aemeasurable (by measurability)).mpr hNo
  have hh := joint_gg_crossed_regions_null (compactRealLaw ν) hGG hno A B hA hB
    (by
      intro a ha b hb
      refine ⟨?_,hb.2.trans_lt ha.2⟩
      have hm : max 0 a.1 < max 0 b.1 := ha.1.trans_lt hb.1
      exact lt_of_not_ge fun h =>  (not_le_of_gt hm) (max_le_max_left 0 h))
  have he (S : Set (ℝ×ℝ)) (hS : MeasurableSet S) :
      (compactRealLaw ν) {Q | Q 0 1∈S}=(ν : Measure (CompactArray CompactJointOverlap)) {Q | compactPairReal (Q 0 1)∈S} := by
    exact Measure.map_apply compactArrayReal_measurable (hS.preimage (by fun_prop))
  rw [he A hA,he B hB] at hh
  have hm : Measurable (fun Q : CompactArray CompactJointOverlap => compactPositivePair (Q 0 1)) :=
    compactPositivePair_measurable.comp (by fun_prop)
  unfold compactPositivePairLaw
  rw [Measure.map_apply hm (measurableSet_Iic.prod measurableSet_Ioi),
    Measure.map_apply hm (measurableSet_Ioi.prod measurableSet_Iic)]
  exact hh

lemma compactPositivePairLaw_quantile (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hGG : JointGhirlandaGuerra (compactRealLaw ν))
    (hNo : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _),
      ¬ ((Q 0 1).1.val < (Q 0 2).1.val ∧ (Q 0 2).2.val < (Q 0 1).2.val)) :
    (volume : Measure Time).map (fun u =>
      (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst) u,
       boundedQuantile ((compactPositivePairLaw ν).map Prod.snd) u))=compactPositivePairLaw ν :=
  no_crossing_quantile_coupling _ (compactPositivePairLaw_no_crossing ν hGG hNo)

lemma compactPositivePairLaw_label (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hT : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), ∀ n,
      Matrix.PosSemidef (fun i j : Fin n => (Q i j).2.val)) :
    (compactPositivePairLaw ν).map Prod.snd=
      (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 1 0).2) := by
  have hm : Measurable (fun Q : CompactArray CompactJointOverlap => compactPositivePair (Q 0 1)) :=
    compactPositivePair_measurable.comp (by fun_prop)
  unfold compactPositivePairLaw
  rw [Measure.map_map measurable_snd hm]
  apply Measure.map_congr
  filter_upwards [hT] with Q hQ
  apply Subtype.ext
  exact gram_array_symmetric (fun i j => (Q i j).2.val) hQ 0 1

variable (k : ℕ) (f : ℝ →ᵇ ℝ) (p d : ℕ → ℕ) (w : Fin (k+1) → ℝ)
variable (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1)
variable (t : ℕ → ℝ≥0) (h : ℕ → Fin (k+1) → ℝ)
variable (hh0 : ∀ n l, 0 ≤ h n l) (hh : ∀ n, Monotone (h n))
variable (u : (n : ℕ) → Fin (n+1) → ℝ)
variable (hu : ∀ n, u n ∈ Icc (fun _ => 1) (fun _ => 2))
variable (hmin : ∀ n, IsMinOn (fun v => quadraticBoxPenalty (sourcePenaltyWeight (n+1)) v-
  sourceExpectedPressure n k f (fun j => p j.val) (fun j => d j.val) (h n) (stepCumulative w) (t n) v)
  (Icc (fun _ : Fin (n+1) => 1) (fun _ => 2)) (u n))
variable {H T : ℝ} (hH : 0 ≤ H) (hhH : ∀ n, h n 0 ≤ H) (ht : ∀ n, (t n:ℝ) ≤ T)
variable (hcover : ∀ a b : ℕ, 1 ≤ a+b → ∃ j, p j=a ∧ d j=b)

include hw hw1 hh0 hh hu hmin hH hhH ht hcover in

theorem source_contact_limit_quantile
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ → ℕ} (hs : StrictMono s)
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f
      (fun a => p a.val) (fun a => d a.val) (h (s n)) (u (s n)) (stepCumulative w) (t (s n))) atTop (𝓝 ν)) :
    (∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), 0 ≤ (Q 0 1).1.val) ∧
    (compactPositivePairLaw ν).map Prod.snd=sourceLabelLaw k w ∧
    (volume : Measure Time).map (fun a =>
      (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst) a,
       boundedQuantile ((compactPositivePairLaw ν).map Prod.snd) a))=compactPositivePairLaw ν := by
  have hz := stepCumulative_strictMono w hw
  have hz0 := stepCumulative_pos w hw
  have hz1 := stepCumulative_lt_one w hw hw1
  have hg := source_contact_limit_joint_gg k f p d (stepCumulative w) hz hz0 hz1 t h hh0 hh u hu hmin hH hhH ht hs hlim hcover
  have hgg := compactRealLaw_gg ν hg
  obtain ⟨hr,htt⟩ := sourceGibbsArray_limit_gram k f (fun _ a => p a.val)
    (fun _ a => d a.val) h u (stepCumulative w) t s hlim
  have hn := source_contact_limit_no_crossing k f p d (stepCumulative w) hz hz0 hz1 t h hh0 hh u hu hmin hH hhH ht hcover hs hlim
  refine ⟨compact_spin_nonnegative ν hgg hr,?_,compactPositivePairLaw_quantile ν hgg hn⟩
  rw [compactPositivePairLaw_label ν htt]
  exact source_array_limit_label_law k f p d w hw hw1 h hh0 hh u
    (fun n j => ne_of_gt ((by norm_num : (0:ℝ) < 1).trans_le ((hu n).1 j))) t
    (fun b hb => by simpa only [zero_add] using hcover 0 b (by omega)) hs hlim


end SphericalPerceptronFreeEnergy
end

end OAI
