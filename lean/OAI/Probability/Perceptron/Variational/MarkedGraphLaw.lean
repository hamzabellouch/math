import Mathlib
import OAI.Probability.Perceptron.Variational.MarkedTangentCanonical
import OAI.Probability.Perceptron.Variational.RoundedCoupling

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

abbrev markedTimePair (K : ℝ) (μ : ProbabilityMeasure (CompactArray (BulkPairRange K))) : Measure Time :=
  (markedTimeLaw K μ : Measure (CompactArray Time)).map (fun Q => Q 0 1)

instance markedTimePair_isProbability (K : ℝ) (μ : ProbabilityMeasure (CompactArray (BulkPairRange K))) :
    IsProbabilityMeasure (markedTimePair K μ) :=
  inferInstance

lemma markedTimePair_ae {K : ℝ} (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    {P : Time → Prop} (hP : ∀ᵐ r ∂markedTimePair K μ, P r) :
    ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), P (nonnegativeSpinTime (Q 0 1).1) := by
  have h := ae_of_ae_map (show Measurable (fun Q : CompactArray Time => Q 0 1) from by fun_prop).aemeasurable hP
  exact ae_of_ae_map (compactMapArray_continuous
    (nonnegativeSpinTime_continuous.comp (show Continuous (Prod.fst : BulkPairRange K → CompactOverlap) from continuous_fst))).measurable.aemeasurable h

theorem marked_graph_law {K B d : ℝ} (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hB : B < 1) (hd0 : 0 ≤ d) (hdK : d ≤ K)
    (he : ∀ e : Equiv.Perm ℕ, MeasurePreserving (compactRelabel (K:=BulkPairRange K) e)
      (μ : Measure _) (μ : Measure _))
    (hn : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i j, 0 ≤ (Q i j).1.val)
    (hD1 : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i, (Q i i).1.val = 1)
    (hD2 : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i, (Q i i).2.val = d)
    (hBd : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i j, (Q i j).2.val ≤ d)
    (a : ℝ → ℝ) (ha0 : ∀ r, 0 ≤ a r)
    (hag : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i j, i ≠ j → (Q i j).2.val = a (Q i j).1.val)
    (hsc : ∀ᵐ r : Time ∂markedTimePair K μ, a r.val = ∫ t in 0..r.val, (realTail (markedTimePair K μ) t)⁻¹^2)
    (hbound : ∀ᵐ r : Time ∂markedTimePair K μ, r.val ≤ B) :
    (markedTimeLaw K μ).map (timeMarkedDecode
      (continuousCavityProfile (markedTimePair K μ) B hd0 hdK)
      (cavityTrueDiagonal hd0 hdK)) = μ := by
  let P := continuousCavityProfile (markedTimePair K μ) B hd0 hdK
  let D := cavityTrueDiagonal hd0 hdK
  let e : BulkPairRange K → Time := fun p => nonnegativeSpinTime p.1
  have hP : Continuous P := continuousCavityProfile_continuous (markedTimePair K μ) hB hd0 hdK
  have hec : Continuous e := nonnegativeSpinTime_continuous.comp continuous_fst
  have h01 : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), P (e (Q 0 1)) = Q 0 1 := by
    filter_upwards [markedTimePair_ae μ hsc,markedTimePair_ae μ hbound,hn,hBd,hag] with Q hS hBnd hN hBd hAg
    have hval : (e (Q 0 1)).val = (Q 0 1).1.val := nonnegativeSpinTime_val (hN 0 1)
    apply Prod.ext
    · exact Subtype.ext hval
    · apply Subtype.ext
      apply continuousCavityProfile_eq (markedTimePair K μ) hd0 hdK hbound hBnd
      · rw [hAg 0 1 (by omega)]; exact ha0 _
      · exact hBd 0 1
      · change a (e (Q 0 1)).val = _ at hS
        rw [hval] at hS
        rw [hAg 0 1 (by omega)]
        change a (Q 0 1).1.val = ∫ t in 0..(e (Q 0 1)).val, (realTail (markedTimePair K μ) t)⁻¹^2
        rw [hval]
        exact hS
  have h10 := (he (Equiv.swap 0 1)).quasiMeasurePreserving.ae h01
  have h10' : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), P (e (Q 1 0)) = Q 1 0 := by
    simpa only [compactRelabel,Equiv.swap_apply_left,Equiv.swap_apply_right] using h10
  have hoff := compact_exchangeable_offdiag_ae μ he (fun p => P (e p) = p) h10'
  have hall : (timeMarkedDecode P D ∘ compactMapArray e) =ᵐ[(μ : Measure (CompactArray (BulkPairRange K)))] id := by
    filter_upwards [hoff,hD1,hD2] with Q hO hD1 hD2
    funext i j
    dsimp only [Function.comp_def,timeMarkedDecode,compactMapArray,id_eq]
    by_cases hij : i = j
    · rw [ite_eq_left hij]
      subst j
      exact Prod.ext (Subtype.ext (hD1 i).symm) (Subtype.ext (hD2 i).symm)
    · rw [ite_eq_right hij]
      exact hO i j hij
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (timeMarkedDecode P D) (Measure.map (compactMapArray e)
    (μ : Measure (CompactArray (BulkPairRange K)))) = (μ : Measure (CompactArray (BulkPairRange K)))
  rw [Measure.map_map (timeMarkedDecode_measurable hP.measurable D)
    (compactMapArray_continuous hec).measurable,
    Measure.map_congr hall,Measure.map_id]

end SphericalPerceptronFreeEnergy

end

end OAI
