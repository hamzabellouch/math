import Mathlib
import OAI.Probability.Perceptron.Interpolation.ArrayTangentConsistency
import OAI.Probability.Perceptron.Cavity.BulkMarkedArray

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped BoundedContinuousFunction ContDiff NNReal

lemma marked_tangent_canonical (K : ℝ) (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (he : ∀ e : Equiv.Perm ℕ,MeasurePreserving (compactRelabel (K:=BulkPairRange K) e) (μ : Measure _) (μ : Measure _))
    (a : ℝ→ℝ)
    (hgraph : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j,i≠j→(Q i j).2.val=a (Q i j).1.val)
    (G : ℝ→ᵇℝ)
    (hT : (∫ Q,markedTangentR K G (compactBlock 2 Q) ∂(μ : Measure _))-
      (∫ Q,markedTangentPair K G (compactBlock 2 Q) ∂(μ : Measure _))+
      2*(∫ Q,markedTangentTriple K G (compactBlock 3 Q) ∂(μ : Measure _))=0) :
    (∫ Q : CompactArray (BulkPairRange K),G (Q 0 1).1.val*((Q 0 1).1.val-a (Q 0 1).1.val*(1-(Q 0 1).1.val^2)+
      2*a (Q 0 2).1.val*((Q 1 2).1.val-(Q 0 1).1.val*(Q 0 2).1.val)) ∂(μ : Measure _))=0 := by
  let F1 := (markedTangentR K G).compContinuous ⟨compactBlock 2,compactBlock_continuous 2⟩
  let F2 := (markedTangentPair K G).compContinuous ⟨compactBlock 2,compactBlock_continuous 2⟩
  let F3 := (markedTangentTriple K G).compContinuous ⟨compactBlock 3,compactBlock_continuous 3⟩
  let F4 : CompactArray (BulkPairRange K)→ᵇℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun Q=>G (Q 0 1).1.val*(Q 0 2).2.val*((Q 1 2).1.val-(Q 0 1).1.val*(Q 0 2).1.val),by fun_prop⟩
  let e : Equiv.Perm ℕ := (Equiv.swap 0 1).trans (Equiv.swap 1 2)
  have hp : (∫ Q,F3 Q ∂(μ : Measure _))=∫ Q,F4 Q ∂(μ : Measure _) := by
    have h := integral_map (μ:=(μ : Measure (CompactArray (BulkPairRange K)))) (he e).measurable.aemeasurable F3.measurable.aestronglyMeasurable
    rw [(he e).map_eq] at h
    change (∫ Q,F3 Q ∂(μ : Measure _))=∫ Q,F3 (compactRelabel e Q) ∂(μ : Measure _) at h
    rw [h]
    apply integral_congr_ae
    filter_upwards [] with Q
    simp [F3,F4,markedTangentTriple,compactBlock,compactRelabel,e,Equiv.swap_apply_def]
  have hi1 := F1.integrable (μ : Measure _)
  have hi2 := F2.integrable (μ : Measure _)
  have hi4 := F4.integrable (μ : Measure _)
  have hi12 : Integrable (fun Q=>F1 Q-F2 Q) (μ : Measure _) := hi1.sub hi2
  have hz : (∫ Q,(F1 Q-F2 Q)+2*F4 Q ∂(μ : Measure _))=0 := by
    rw [integral_add hi12 (hi4.const_mul 2),integral_sub hi1 hi2,integral_const_mul,←hp]
    exact hT
  rw [←hz]
  apply integral_congr_ae
  filter_upwards [hgraph] with Q hQ
  have h01 := hQ 0 1 (by omega)
  have h02 := hQ 0 2 (by omega)
  change G (Q 0 1).1.val*((Q 0 1).1.val-a (Q 0 1).1.val*(1-(Q 0 1).1.val^2)+
    2*a (Q 0 2).1.val*((Q 1 2).1.val-(Q 0 1).1.val*(Q 0 2).1.val))=
    ((Q 0 1).1.val*G (Q 0 1).1.val-G (Q 0 1).1.val*(Q 0 1).2.val*(1-(Q 0 1).1.val^2))+
      2*(G (Q 0 1).1.val*(Q 0 2).2.val*((Q 1 2).1.val-(Q 0 1).1.val*(Q 0 2).1.val))
  rw [h01,h02]
  ring

def nonnegativeSpinTime (q : CompactOverlap) : Time :=
  ⟨max q.val 0,le_max_right _ _,max_le q.property.2 zero_le_one⟩
lemma nonnegativeSpinTime_continuous : Continuous nonnegativeSpinTime := by
  unfold nonnegativeSpinTime
  fun_prop
lemma nonnegativeSpinTime_val {q : CompactOverlap} (hq : 0≤q.val) :
    (nonnegativeSpinTime q).val=q.val := max_eq_left hq

def markedTimeLaw (K : ℝ) (μ : ProbabilityMeasure (CompactArray (BulkPairRange K))) :
    ProbabilityMeasure (CompactArray Time) :=
  compactMapLaw (fun p : BulkPairRange K=>nonnegativeSpinTime p.1)
    (nonnegativeSpinTime_continuous.comp continuous_fst) μ

lemma markedTimeLaw_factor (K : ℝ) (μ : ProbabilityMeasure (CompactArray (BulkPairRange K))) :
    markedTimeLaw K μ=compactMapLaw nonnegativeSpinTime nonnegativeSpinTime_continuous
      (compactMapLaw Prod.fst continuous_fst μ) := by
  apply Subtype.ext
  change Measure.map _ (μ : Measure (CompactArray (BulkPairRange K)))=
    Measure.map _ (Measure.map _ (μ : Measure (CompactArray (BulkPairRange K))))
  rw [Measure.map_map (compactMapArray_continuous nonnegativeSpinTime_continuous).measurable
    (compactMapArray_continuous continuous_fst).measurable]
  rfl

lemma marked_time_self_consistency (K : ℝ) (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (he : ∀ e : Equiv.Perm ℕ,MeasurePreserving (compactRelabel (K:=BulkPairRange K) e) (μ : Measure _) (μ : Measure _))
    (hGG : ∀ n (i : Fin n) (F : CompactBlock CompactOverlap n→ᵇℝ) (g : CompactOverlap→ᵇℝ),
      compactGGDefect (compactMapLaw Prod.fst continuous_fst μ) n i F g=0)
    (hsy : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j,(Q i j).1=(Q j i).1)
    (hul : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j k,
      min (Q i j).1.val (Q i k).1.val≤(Q j k).1.val)
    (hn : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j,0≤(Q i j).1.val)
    (a : ℝ→ℝ) (ha : Measurable a) {A : ℝ} (hA : 0≤A) (hab : ∀ x,0≤a x ∧ a x≤A)
    (hgraph : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j,i≠j→(Q i j).2.val=a (Q i j).1.val)
    (hT : ∀ G : ℝ→ᵇℝ,ContDiff ℝ 1 (G : ℝ→ℝ)→
      (∫ Q,markedTangentR K G (compactBlock 2 Q) ∂(μ : Measure _))-
      (∫ Q,markedTangentPair K G (compactBlock 2 Q) ∂(μ : Measure _))+
      2*(∫ Q,markedTangentTriple K G (compactBlock 3 Q) ∂(μ : Measure _))=0) :
    let ν := (markedTimeLaw K μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)
    (∀ᵐ x : Time ∂ν,a x=∫ y in 0..(x:ℝ),(realTail ν y)⁻¹^2) ∧
      ∀ᵐ x : Time ∂ν,(x:ℝ)≤A/(1+A) := by
  let e : BulkPairRange K→Time := fun p=>nonnegativeSpinTime p.1
  have hec : Continuous e := nonnegativeSpinTime_continuous.comp continuous_fst
  have hm : Measurable (compactMapArray e) := (compactMapArray_continuous hec).measurable
  have hs : ∀ᵐ Q ∂(markedTimeLaw K μ : Measure (CompactArray Time)),∀ i j,Q i j=Q j i := by
    apply (ae_map_iff hm.aemeasurable (by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i=>MeasurableSet.iInter fun j=>measurableSet_eq_fun (by fun_prop) (by fun_prop))).mpr
    filter_upwards [hsy] with Q hQ
    intro i j
    exact congrArg nonnegativeSpinTime (hQ i j)
  have hu : ∀ᵐ Q ∂(markedTimeLaw K μ : Measure (CompactArray Time)),∀ i j k,min (Q i j:ℝ) (Q i k:ℝ)≤(Q j k:ℝ) := by
    apply (ae_map_iff hm.aemeasurable (by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i=>MeasurableSet.iInter fun j=>MeasurableSet.iInter fun k=>
        measurableSet_le (by fun_prop) (by fun_prop))).mpr
    filter_upwards [hul,hn] with Q hQ hN
    intro i j k
    simpa only [compactMapArray,e,nonnegativeSpinTime_val (hN i j),nonnegativeSpinTime_val (hN i k),
      nonnegativeSpinTime_val (hN j k)] using hQ i j k
  apply array_tangent_self_consistency (markedTimeLaw K μ)
    (by rw [markedTimeLaw_factor]; exact compactMapLaw_gg _ _ _ hGG 2 0)
    (compactMapLaw_exchangeable e hec μ (Equiv.swap 0 1) (he _)) hs hu
    (fun x=>a x.val) (ha.comp measurable_subtype_coe) hA (fun x=>hab x.val)
  intro G hG
  rw [show (markedTimeLaw K μ : Measure (CompactArray Time))=(μ : Measure _).map (compactMapArray e) from rfl,
    integral_map hm.aemeasurable (show AEStronglyMeasurable (fun Q : CompactArray Time=>G (Q 0 1)*
      ((Q 0 1:ℝ)-a (Q 0 1)*(1-(Q 0 1:ℝ)^2)+2*a (Q 0 2)*((Q 1 2:ℝ)-(Q 0 1:ℝ)*(Q 0 2:ℝ)))) _ from (show Measurable (fun Q : CompactArray Time=>G (Q 0 1)*
      ((Q 0 1:ℝ)-a (Q 0 1)*(1-(Q 0 1:ℝ)^2)+2*a (Q 0 2)*((Q 1 2:ℝ)-(Q 0 1:ℝ)*(Q 0 2:ℝ)))) from by fun_prop).aestronglyMeasurable)]
  rw [←marked_tangent_canonical K μ he a hgraph G (hT G hG)]
  apply integral_congr_ae
  filter_upwards [hn] with Q hN
  simp only [compactMapArray,e,nonnegativeSpinTime_val (hN 0 1),nonnegativeSpinTime_val (hN 0 2),nonnegativeSpinTime_val (hN 1 2)]

end SphericalPerceptronFreeEnergy
end

end OAI
