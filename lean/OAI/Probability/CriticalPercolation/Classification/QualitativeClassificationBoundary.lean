import Mathlib
import OAI.Probability.CriticalPercolation.Classification.FiniteClassificationObstruction
import OAI.Probability.CriticalPercolation.Nilpotent.FiniteKernelNilpotent

namespace OAI

section
noncomputable section
open Set Function Topology

namespace CriticalPercolation.CompactQuotient
variable {A : Type*} [Group A]

lemma virtuallyNilpotent_of_finiteByVirtuallyNilpotent
    (h : FiniteByVirtuallyNilpotent A) : Group.IsVirtuallyNilpotent A := by
  obtain ⟨F,hn,hF,N,hN,hi⟩ := h
  let _ := hn
  apply virtuallyNilpotent_of_finite_kernel (QuotientGroup.mk' F)
  · simpa only [QuotientGroup.ker_mk'] using hF
  · exact ⟨N,hN,⟨hi⟩⟩

lemma finiteByVirtuallyNilpotent_of_virtuallyNilpotent
    (h : Group.IsVirtuallyNilpotent A) : FiniteByVirtuallyNilpotent A := by
  obtain ⟨N,hN,hi⟩ := h
  let _ := hN
  let f : A →* A ⧸ (⊥ : Subgroup A) := QuotientGroup.mk' ⊥
  have hf : Surjective f := QuotientGroup.mk_surjective
  have hnil : Group.IsNilpotent (N.map f) := Group.nilpotent_of_surjective
    (f.subgroupMap N) (f.subgroupMap_surjective N)
  have hindex : (N.map f).index=N.index := by
    apply N.index_map_eq hf
    change (QuotientGroup.mk' (⊥ : Subgroup A)).ker≤N
    rw [QuotientGroup.ker_mk']
    exact bot_le
  refine ⟨⊥,inferInstance,by simp,N.map f,hnil,?_⟩
  rw [hindex]
  exact hi.index_ne_zero

theorem finiteByVirtuallyNilpotent_iff :
    FiniteByVirtuallyNilpotent A ↔ Group.IsVirtuallyNilpotent A :=
  ⟨virtuallyNilpotent_of_finiteByVirtuallyNilpotent,
    finiteByVirtuallyNilpotent_of_virtuallyNilpotent⟩

end CriticalPercolation.CompactQuotient
namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

theorem not_virtuallyNilpotent_quotient_of_classification_failure {K : ℝ}
    (h : HasFiniteApproximateQuotientCounterexample Γ K) :
    let _ : TopologicalSpace X := ⊥
    let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
    ∃ H : Subgroup (Γ ≃g Γ), ∃ hn : H.Normal, let _ := hn
      IsCompact (H : Set (Γ ≃g Γ)) ∧ IsOpen (H : Set (Γ ≃g Γ)) ∧
      1≤K ∧ Group.FG ((Γ ≃g Γ) ⧸ H) ∧
      CompactQuotient.UniformFiniteApproximatePowers ((Γ ≃g Γ) ⧸ H) K ∧
      ¬Group.IsVirtuallyNilpotent ((Γ ≃g Γ) ⧸ H) := by
  let _ : TopologicalSpace X := ⊥
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  obtain ⟨H,hn,hc,ho,hfg,hpow,hfail⟩ := h
  let _ := hn
  exact ⟨H,hn,hc,ho,CompactQuotient.one_le_of_uniformFiniteApproximatePowers hpow,
    hfg,hpow,fun hv => hfail
      (CompactQuotient.finiteByVirtuallyNilpotent_of_virtuallyNilpotent hv)⟩

end CriticalPercolation.GraphTopology
end
end

end OAI
