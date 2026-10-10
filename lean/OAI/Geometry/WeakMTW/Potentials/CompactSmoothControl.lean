import Mathlib

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff NNReal
namespace CompactSmoothControl
 theorem compact_filter {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
     {K : Set X} (hK : IsCompact K) {f : X → Y} (hf : ContinuousOn f K)
     {P : Set Y} (hP : IsClosed P) : IsCompact (K ∩ f ⁻¹' P) := by
   let : CompactSpace K := isCompact_iff_compactSpace.mp hK
   have hS : IsClosed {a : K | f a.val ∈ P} :=
     hP.preimage (continuousOn_iff_continuous_domRestrict.mp hf)
   have h := hS.isCompact.image (continuous_subtype_val : Continuous (Subtype.val : K → X))
   convert h using 1
   ext x
   simp only [mem_inter_iff,mem_preimage,mem_image,mem_ofPred_eq]
   constructor
   · rintro ⟨hx,hP⟩
     exact ⟨⟨x,hx⟩,hP,rfl⟩
   · rintro ⟨a,ha,rfl⟩
     exact ⟨a.property,ha⟩

 theorem compact_lipschitz {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
     [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E} (hK : IsCompact K)
     {f : E → F} (hf : ∀ x ∈ K, ContDiffAt ℝ 1 f x) :
     ∃ C : ℝ≥0, LipschitzOnWith C f K := by
   apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
   intro x hx
   obtain ⟨C,U,hU,hL⟩ := (hf x hx).exists_lipschitzOnWith
   exact ⟨C,U,mem_nhdsWithin_of_mem_nhds hU,hL⟩
end CompactSmoothControl
end

end WeakMTWGlobalSupport

end OAI
