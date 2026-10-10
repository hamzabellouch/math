import Mathlib

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology
namespace CompactFamilyControl
variable {A B E : Type*} [TopologicalSpace A] [TopologicalSpace B] [T2Space B]
  [PseudoMetricSpace E]

 theorem near_compact_fiber {K : Set A} (hK : IsCompact K) {p : A → B}
     (hp : ContinuousOn p K) {c : B} {U : Set A} (hU : IsOpen U)
     (hc : ∀ a ∈ K, p a = c → a ∈ U) :
     ∀ᶠ z in 𝓝 c, ∀ a ∈ K, p a = z → a ∈ U := by
   have hbad : IsCompact (p '' (K \ U)) := (hK.diff hU).image_of_continuousOn (hp.mono sdiff_subset)
   have hnot : c ∉ p '' (K \ U) := by
     rintro ⟨a,ha,he⟩
     exact ha.2 (hc a ha.1 he)
   filter_upwards [hbad.isClosed.isOpen_compl.mem_nhds hnot] with z hz a ha he
   by_contra hu
   exact hz ⟨a,⟨ha,hu⟩,he⟩

 theorem uniform_near_fiber {K : Set A} (hK : IsCompact K) {p : A → B}
     (hp : Continuous p) (c : B) (Z : E) (P : A → E → ℝ → Prop)
     (hmono : ∀ a X C D, C ≤ D → P a X C → P a X D)
     (hloc : ∀ a ∈ K, p a = c → ∃ U : Set A, IsOpen U ∧ a ∈ U ∧
       ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ a' ∈ U, ∀ X ∈ Metric.ball Z r, P a' X C) :
     ∃ V ∈ 𝓝 c, ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
       ∀ a ∈ K, p a ∈ V → ∀ X ∈ Metric.ball Z r, P a X C := by
   classical
   let F := {a ∈ K | p a = c}
   have hF : IsCompact F := hK.inter_right (isClosed_eq hp continuous_const)
   choose U hU haU r C hr hC hbound using (fun a : F => hloc a a.property.1 a.property.2)
   obtain ⟨L,hL⟩ := hF.elim_finite_subcover U hU (by
     intro a ha
     exact mem_iUnion.mpr ⟨⟨a,ha⟩,haU ⟨a,ha⟩⟩)
   let W := ⋃ a ∈ L, U a
   have hW : IsOpen W := isOpen_biUnion (fun a _ => hU a)
   have hnear := near_compact_fiber hK hp.continuousOn hW (fun a ha he => hL ⟨ha,he⟩)
   have hball : (⋂ a ∈ L, Metric.ball Z (r a)) ∈ 𝓝 Z :=
     (Filter.biInter_mem L.finite_toSet).mpr (fun a ha => Metric.ball_mem_nhds Z (hr a))
   obtain ⟨ρ,hρ,hρb⟩ := Metric.mem_nhds_iff.mp hball
   let D := ∑ a ∈ L, C a
   have hD : 0 ≤ D := Finset.sum_nonneg (fun a _ => hC a)
   refine ⟨{z | ∀ a ∈ K, p a = z → a ∈ W},hnear,ρ,D,hρ,hD,?_⟩
   intro a ha hpa X hX
   obtain ⟨i,hi,hai⟩ := mem_iUnion₂.mp (hpa a ha rfl)
   have hXi : X ∈ Metric.ball Z (r i) := mem_iInter₂.mp (hρb hX) i hi
   apply hmono a X (C i) D _ (hbound i a hai X hXi)
   exact Finset.single_le_sum (fun j _ => hC j) hi
end CompactFamilyControl
end

end WeakMTWGlobalSupport

end OAI
