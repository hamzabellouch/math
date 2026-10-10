import OAI.InformationTheory.Entanglement.TraceInstrument

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
open ContinuousLinearMap
namespace SecretKey
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι κ : Type*}
omit [CompleteSpace H] [CompleteSpace K] in
lemma cp_trace_positive (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    {F : TraceClass b →ₗ[ℂ] TraceClass c} (hF : TraceCP b c F)
    {A : TraceClass b} (hA : 0 ≤ (A : H →L[ℂ] H)) : 0 ≤ (F A : K →L[ℂ] K) := by
  have hp : TraceBlockPositive b (fun _ _ : Unit => A) := by
    intro x
    simpa using (nonneg_iff_isPositive.mp hA).inner_nonneg_right (x ())
  have h := hF Unit inferInstance _ hp
  apply nonneg_iff_isPositive.mpr
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have hx : 0 ≤ inner ℂ x ((F A : K →L[ℂ] K) x) := by simpa using h (fun _ => x)
  have hx' : 0 ≤ inner ℂ ((F A : K →L[ℂ] K) x) x := by
    rw [← inner_conj_symm]
    exact star_nonneg_iff.mpr hx
  exact ⟨Complex.ext rfl (Complex.nonneg_iff.mp hx').2, (Complex.nonneg_iff.mp hx').1⟩

structure TraceChannel (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K) where
  map : TraceClass b →ₗ[ℂ] TraceClass c
  cp : TraceCP b c map
  trace_preserving : ∀ A, traceClassTrace c (map A)=traceClassTrace b A
omit [CompleteSpace H] in
lemma finitePositiveTrace_add (b : HilbertBasis ι ℂ H) {A B : H →L[ℂ] H}
    (hA : HasFinitePositiveTrace b A) (hB : HasFinitePositiveTrace b B) :
    HasFinitePositiveTrace b (A+B) := by
  refine ⟨add_nonneg hA.1 hB.1,?_⟩
  simpa only [add_apply,inner_add_right,Complex.add_re] using hA.2.add hB.2

theorem hilbertTraceNorm_triangle (b : HilbertBasis ι ℂ H) {A B : H →L[ℂ] H}
    (hA : HermitianTraceClass b A) (hB : HermitianTraceClass b B) :
    HermitianTraceClass b (A+B) ∧
      hilbertTraceNorm b (A+B) ≤ hilbertTraceNorm b A+hilbertTraceNorm b B := by
  obtain ⟨hp,hn⟩ := hermitian_parts_finite b hA
  obtain ⟨hq,hm⟩ := hermitian_parts_finite b hB
  have he : A+B=(posPart A+posPart B)-(negPart A+negPart B) := by
    rw [add_sub_add_comm,CFC.posPart_sub_negPart A hA.1,CFC.posPart_sub_negPart B hB.1]
  obtain ⟨hc,hbound⟩ := positive_difference_traceClass b
    (finitePositiveTrace_add b hp hq) (finitePositiveTrace_add b hn hm)
  rw [← he] at hc hbound
  refine ⟨hc,?_⟩
  rw [hilbertTraceNorm_jordan b hA,hilbertTraceNorm_jordan b hB]
  rw [hilbertTrace_add b _ _ hp.2 hq.2,hilbertTrace_add b _ _ hn.2 hm.2] at hbound
  linarith
namespace TraceChannel
variable {b : HilbertBasis ι ℂ H} {c : HilbertBasis κ ℂ K}
variable (F : TraceChannel b c)
omit [CompleteSpace H] [CompleteSpace K] in
lemma positive (A : TraceClass b) (hA : 0 ≤ (A : H →L[ℂ] H)) :
    HasFinitePositiveTrace c (F.map A : K →L[ℂ] K) :=
  (traceClass_positive_iff c _).mp ⟨(F.map A).property,cp_trace_positive b c F.cp hA⟩
omit [CompleteSpace H] [CompleteSpace K] in
lemma real_trace (A : TraceClass b) :
    hilbertTrace c (F.map A : K →L[ℂ] K)=hilbertTrace b (A : H →L[ℂ] H) := by
  rw [← traceClassTrace_re,← traceClassTrace_re,F.trace_preserving]

theorem traceNorm_contract (A : TraceClass b) (hA : HermitianTraceClass b (A : H →L[ℂ] H)) :
    HermitianTraceClass c (F.map A : K →L[ℂ] K) ∧
      hilbertTraceNorm c (F.map A : K →L[ℂ] K) ≤ hilbertTraceNorm b (A : H →L[ℂ] H) := by
  obtain ⟨hp,hn⟩ := hermitian_parts_finite b hA
  let P : TraceClass b := ⟨posPart (A : H →L[ℂ] H),Submodule.subset_span hp⟩
  let N : TraceClass b := ⟨negPart (A : H →L[ℂ] H),Submodule.subset_span hn⟩
  have he : P-N=A := Subtype.ext (CFC.posPart_sub_negPart _ hA.1)
  have heF : (F.map A : K →L[ℂ] K)=(F.map P : K →L[ℂ] K)-(F.map N : K →L[ℂ] K) := by
    rw [← Submodule.coe_sub,← map_sub,he]
  obtain ⟨hc,hbound⟩ := positive_difference_traceClass c (F.positive P hp.1) (F.positive N hn.1)
  rw [← heF] at hc hbound
  refine ⟨hc,?_⟩
  rw [F.real_trace,F.real_trace] at hbound
  exact hbound.trans_eq (hilbertTraceNorm_jordan b hA).symm
end TraceChannel

end SecretKey

end

end OAI
