import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalSupply

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma supported_groupAt_eligible {N K M G : ℕ} {L : Length}
    (g : Fin G) (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (ω : ConfigurationPath N L) (a : GridAllocation N K (G*M))
    (ha : ∀v,a v∈(allocationPMF (eligibleList m r R C S s₀ u v ω) (G*M)).support)
    (v : Fin 3→Fin K) (i : Fin N) (hi : i∈groupAt g a v) :
    Eligible m r R C S s₀ u v i ω := by
  cases he : a v with
  | none => simp [groupAt,he] at hi
  | some f =>
    simp only [groupAt,he,Finset.mem_image,Finset.mem_univ,true_and] at hi
    obtain ⟨k,rfl⟩ := hi
    exact (Finset.mem_filter.mp (allocationPMF_support _ _ _ (ha v) f he _)).2

theorem physicalDatum_selected_geometry {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (g : Fin G) (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (ω : ConfigurationPath N L) (a : GridAllocation N K (G*M))
    (ha : ∀v,a v∈(allocationPMF (eligibleList m r R C S s₀ u v ω) (G*M)).support)
    (i : Fin N) (hi : i∈groupUnion g a) :
    let d := physicalDatum g m r R C S s₀ u (ω,a)
    ‖datumStart hL d i-anchorPoint (datumHome hL d i)‖≤3 ∧
    ‖datumEnd hL d i-anchorPoint (datumHome hL d i)‖≤3 ∧
    ∀j,j≠i→s₀<torusDistance L (projectPoint L (datumStart hL d i)) (projectPoint L (datumStart hL d j)) ∧
      s₀<torusDistance L (projectPoint L (datumEnd hL d i)) (projectPoint L (datumEnd hL d j)) := by
  dsimp only
  obtain ⟨v,_,hiv⟩ := Finset.mem_biUnion.mp hi
  have he := supported_groupAt_eligible g m r R C S s₀ u ω a ha v i hiv
  have hh := physicalDatum_home hL hK g m r R C S s₀ u ω a v i he
  refine ⟨?_,?_,?_⟩
  · unfold datumStart
    rw [hh]
    exact nearestLift_bound L (anchorPoint v) (ω 0 i) ((centeredCell_distance he.1.1).trans (by norm_num))
  · unfold datumEnd
    rw [hh]
    exact nearestLift_bound L (anchorPoint v) (ω 1 i) he.1.2.1
  · intro j hj
    simp only [datumStart,datumEnd,nearestLift_project]
    exact he.1.2.2 j hj

lemma groupAt_card_le {N K M G : ℕ} (g : Fin G) (a : GridAllocation N K (G*M)) (v : Fin 3→Fin K) :
    (groupAt g a v).card≤M := by
  cases he : a v with
  | none => simp [groupAt,he]
  | some f => simpa only [groupAt,he,Finset.card_univ,Fintype.card_fin] using
      (Finset.card_image_le (s:=Finset.univ) (f:=fun k : Fin M ↦ f (groupPosition M G g k)))

theorem physicalDatum_group_multiplicity {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (g : Fin G) (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (ω : ConfigurationPath N L) (a : GridAllocation N K (G*M))
    (ha : ∀v,a v∈(allocationPMF (eligibleList m r R C S s₀ u v ω) (G*M)).support)
    (v : Fin 3→Fin K) :
    (Finset.univ.filter (fun i : {i // i∈groupUnion g a} ↦
      datumHome hL (physicalDatum g m r R C S s₀ u (ω,a)) i=v)).card≤M := by
  let s := Finset.univ.filter (fun i : {i // i∈groupUnion g a} ↦
      datumHome hL (physicalDatum g m r R C S s₀ u (ω,a)) i=v)
  have hs : s.image Subtype.val⊆groupAt g a v := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨w,_,hjw⟩ := Finset.mem_biUnion.mp j.property
    have he := supported_groupAt_eligible g m r R C S s₀ u ω a ha w j hjw
    have hh := physicalDatum_home hL hK g m r R C S s₀ u ω a w j he
    have hv := (Finset.mem_filter.mp hj).2
    have hw : w=v := hh.symm.trans hv
    simpa only [hw] using hjw
  have hc := (Finset.card_le_card hs).trans (groupAt_card_le g a v)
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hc
  exact hc

end HardSphere.Groups
end
end

end OAI
