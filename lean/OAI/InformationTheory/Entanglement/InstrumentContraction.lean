import OAI.InformationTheory.Entanglement.HilbertChannel
import OAI.InformationTheory.Entanglement.HilbertLawMetric

namespace OAI

noncomputable section
open scoped BigOperators ENNReal MeasureTheory InnerProductSpace ComplexOrder
open MeasureTheory ContinuousLinearMap
namespace SecretKey
variable {T : Type*} [MeasurableSpace T]
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι κ : Type*}
namespace TraceInstrument
variable {b : HilbertBasis ι ℂ H} {c : HilbertBasis κ ℂ K}
variable (I : TraceInstrument b c T)
omit [CompleteSpace H] in
lemma law_total_trace (A : TraceClass b) (hA : 0≤(A : H→L[ℂ]H)) :
    (I.law A hA).traceMeasure Set.univ=ENNReal.ofReal (hilbertTrace b (A : H→L[ℂ]H)) := by
  rw [← traceClassTrace_re,← I.trace_preserving A,traceClassTrace_re,
    ← I.law_value A hA _ MeasurableSet.univ,← (I.law A hA).trace_value _ MeasurableSet.univ]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

theorem variation_contract (A : TraceClass b)
    (hA : HermitianTraceClass b (A : H→L[ℂ]H)) :
    hilbertVariation c (fun s => (I.event s A : K→L[ℂ]K))≤hilbertENorm b (A : H→L[ℂ]H) := by
  obtain ⟨hp,hn⟩ := hermitian_parts_finite b hA
  let P : TraceClass b := ⟨posPart (A : H→L[ℂ]H),Submodule.subset_span hp⟩
  let N : TraceClass b := ⟨negPart (A : H→L[ℂ]H),Submodule.subset_span hn⟩
  have he : P-N=A := Subtype.ext (CFC.posPart_sub_negPart _ hA.1)
  have hval (s : Set T) (hs : MeasurableSet s) :
      (I.event s A : K→L[ℂ]K)=(I.law P hp.1).value s-(I.law N hn.1).value s := by
    rw [I.law_value _ _ _ hs,I.law_value _ _ _ hs,← Submodule.coe_sub,← map_sub,he]
  rw [hilbertVariation_congr c hval,hilbertENorm_eq b hA.2]
  apply (hilbertVariation_difference_le c (I.law P hp.1) (I.law N hn.1)).trans
  have hpos : 0≤hilbertTrace b (P : H→L[ℂ]H) :=
    tsum_nonneg (fun i => (nonneg_iff_isPositive.mp hp.1).re_inner_nonneg_right _)
  rw [I.law_total_trace P hp.1,I.law_total_trace N hn.1,
    ← ENNReal.ofReal_add hpos,hilbertTraceNorm_jordan b hA]
  exact tsum_nonneg (fun i => (nonneg_iff_isPositive.mp hn.1).re_inner_nonneg_right _)

theorem output_distance_contract (A B : TraceClass b)
    (hA : 0≤(A : H→L[ℂ]H)) (hB : 0≤(B : H→L[ℂ]H)) :
    hilbertVariation c (fun s => (I.law A hA).value s-(I.law B hB).value s)≤
      hilbertENorm b ((A : H→L[ℂ]H)-(B : H→L[ℂ]H)) := by
  have ht := (positive_difference_traceClass b
    ((traceClass_positive_iff b _).mp ⟨A.property,hA⟩)
    ((traceClass_positive_iff b _).mp ⟨B.property,hB⟩)).1
  have h := I.variation_contract (A-B) ht
  apply le_trans ?_ h
  apply le_of_eq
  apply hilbertVariation_congr
  intro s hs
  rw [I.law_value _ _ _ hs,I.law_value _ _ _ hs,map_sub,Submodule.coe_sub]
end TraceInstrument

end SecretKey

end

end OAI
