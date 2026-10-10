import OAI.Dynamics.StandardMap.CriticalLaws

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology Classical
namespace StandardMapEntropy
lemma compact_nonaffine_finite_tests (F : Set DistanceArray) (hF : IsCompact F) (hFa : F⊆affineLocusᶜ) :
    ∃ t : Finset ArrayTestIndex, ∃ c : ℝ, 0<c ∧ ∀ d∈F,c ≤ ∑ i∈t,arrayTest i d := by
  classical
  by_cases hne : F.Nonempty
  · let U : ArrayTestIndex → Set DistanceArray := fun i => {d | 0<arrayTest i d}
    have hU : ∀ i,IsOpen (U i) := fun i => isOpen_lt continuous_const (continuous_arrayTest i)
    have hcover : F⊆⋃ i,U i := by
      intro d hd
      obtain ⟨i,hi⟩ := (nonaffine_iff_positive_test d).mp (hFa hd)
      exact Set.mem_iUnion.mpr ⟨i,hi⟩
    obtain ⟨t,ht⟩ := hF.elim_finite_subcover U hU hcover
    let f : DistanceArray → ℝ := fun d => ∑ i∈t,arrayTest i d
    have hcont : Continuous f := continuous_finsetSum _ (fun i hi => continuous_arrayTest i)
    have hpos : ∀ d∈F,0<f d := by
      intro d hd
      obtain ⟨i,hi,hd⟩ := Set.mem_iUnion₂.mp (ht hd)
      exact lt_of_lt_of_le hd (Finset.single_le_sum (fun j hj => arrayTest_nonneg j d) hi)
    obtain ⟨d,hd,hmin⟩ := hF.exists_isMinOn hne hcont.continuousOn
    exact ⟨t,f d,hpos d hd,fun e he => hmin he⟩
  · exact ⟨∅,1,by norm_num,fun d hd => (hne ⟨d,hd⟩).elim⟩
end StandardMapEntropy

end OAI
