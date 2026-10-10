import OAI.Analysis.CircleDomains.Rigidity.CountableTraceEnumeration

namespace OAI

open Set Function
noncomputable section
namespace CircleDomainRigidity

 theorem traceEnumeration_iUnion {ι X : Type*} [Encodable ι] (V : ι → Set X) :
    (⋃ n, traceEnumeration V ∅ n) = ⋃ j, V j := by
  ext x
  constructor
  · intro hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    by_cases h : n ∈ Set.range (Encodable.encode : ι → ℕ)
    · obtain ⟨j,rfl⟩ := h
      rw [traceEnumeration_encode] at hn
      exact mem_iUnion.mpr ⟨j,hn⟩
    · rw [traceEnumeration_missing V ∅ h] at hn
      exact hn.elim
  · intro hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨Encodable.encode j,by simpa only [traceEnumeration_encode] using hj⟩

end CircleDomainRigidity

end

end OAI
