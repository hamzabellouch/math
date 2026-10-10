import Mathlib
import OAI.Geometry.Cannon.Flows.Domain

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
open Set Topology
open Set MeasureTheory
open scoped BigOperators
open scoped NNReal ENNReal
open Set Metric
open Set Filter Topology
open Set Filter Topology Metric
open Set Metric Topology
open Set unitInterval

namespace CannonMagnification

open Set Metric Filter Topology

lemma continuousOn_onDomain {X : Type*} [TopologicalSpace X] {Ω : Set X}
    (f : C(Ω,ℝ)) : ContinuousOn (onDomain f) Ω := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert f.continuous using 1
  ext x
  exact onDomain_eq f x.val x.property

lemma uniform_onDomain {X : Type*} [MetricSpace X] {Ω : Set X}
    (f : ℕ → X → ℝ) (F : C(Ω,ℝ))
    (hlim : ∀ K : Set Ω, IsCompact K →
      TendstoUniformlyOn (fun i z => f i z.val) F atTop K)
    (K : Set X) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    TendstoUniformlyOn f (onDomain F) atTop K := by
  let K' : Set Ω := Subtype.val ⁻¹' K
  have hK' : IsCompact K' := IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK
    (by simpa only [Subtype.range_coe] using hKΩ)
  intro u hu
  filter_upwards [hlim K' hK' u hu] with i hi
  intro z hz
  simpa only [onDomain_eq F z (hKΩ hz)] using hi ⟨z,hKΩ hz⟩ hz

end CannonMagnification

end
end
end
end
end
end
end
end
end
end

end OAI
