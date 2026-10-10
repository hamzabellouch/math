import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Compactness.Compact

namespace OAI

/-! A compact curve with a unique endpoint preimage has no distant
parameter values accumulating at that endpoint, even after a compact
set avoiding the endpoint is added. -/
noncomputable section
open Set unitInterval
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [T2Space M]

theorem compact_curve_endpoint_neighborhood {γ : I → M} (hγ : Continuous γ)
    {p : M} (hunique : ∀ t, γ t = p → t = 0)
    {K : Set M} (hK : IsCompact K) (hpK : p ∉ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧
      ∀ x ∈ V, x ∈ range γ ∪ K → ∃ t : I, (t:ℝ) < ε ∧ γ t = x := by
  let A : Set I := {t | ε ≤ (t:ℝ)}
  have hA : IsCompact A := (isClosed_le continuous_const continuous_subtype_val).isCompact
  have hL : IsCompact (γ '' A ∪ K) := (hA.image hγ).union hK
  have hpL : p ∉ γ '' A ∪ K := by
    rintro (⟨t,ht,he⟩ | ht)
    · have hz := hunique t he
      subst t
      change ε ≤ 0 at ht
      exact (not_le_of_gt hε) ht
    · exact hpK ht
  refine ⟨(γ '' A ∪ K)ᶜ,hL.isClosed.isOpen_compl,hpL,?_⟩
  intro x hx hxi
  rcases hxi with ⟨t,rfl⟩ | hxi
  · refine ⟨t,?_,rfl⟩
    by_contra hn
    exact hx (Or.inl ⟨t,le_of_not_gt hn,rfl⟩)
  · exact False.elim (hx (Or.inr hxi))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
