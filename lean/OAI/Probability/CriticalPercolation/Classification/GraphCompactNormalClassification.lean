import Mathlib
import OAI.Probability.CriticalPercolation.Classification.RelativeClassification
import OAI.Probability.CriticalPercolation.Growth.GraphRelativeGrowth
import OAI.Probability.CriticalPercolation.GraphTopology.CommensurableClosure
import OAI.Probability.CriticalPercolation.Classification.DiscreteWeakGromovBridge
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphQuotientPolynomial

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical Pointwise

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

theorem compact_open_normal_of_sparse_polynomial
    [TopologicalSpace X] [DiscreteTopology X]
    (hc : Γ.Connected) (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, (reachBall Γ o n).ncard≤n^d) :
    let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
    ∃ H : Subgroup (Γ ≃g Γ), H.Normal ∧ IsCompact (H:Set (Γ ≃g Γ)) ∧ IsOpen (H:Set (Γ ≃g Γ)) := by
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  let K := vertexStabilizer Γ o
  let S := displacement Γ o 1
  have h1 : (1:Γ ≃g Γ)∈S := one_mem_displacement Γ o 1
  have hi : S⁻¹=S := by ext g; exact displacement_inv Γ
  have hgen : Subgroup.closure S=⊤ := displacement_generates Γ hc ht o
  obtain ⟨N,hNn,hNb,hNi⟩ := RelativeGrowth.bounded_normal_commensurable d
    (Γ ≃g Γ) K S h1 hi hgen (vertexStabilizer_bounded Γ o) (displacement_relativeDegree Γ hl o d hpoly)
  let := hNn
  let H := N.topologicalClosure
  have hHn : H.Normal := Subgroup.is_normal_topologicalClosure N
  have hcH : IsCompact (H:Set (Γ ≃g Γ)) := by
    obtain ⟨n,hn⟩ := hNb
    have hNs : (N:Set (Γ ≃g Γ))⊆displacement Γ o n := hn.trans (displacement_pow_subset Γ o n)
    apply (compact_displacement Γ hc hl o n).of_isClosed_subset N.isClosed_topologicalClosure
    exact closure_minimal hNs (isClosed_eval_mem Γ o _)
  have hoH : IsOpen (H:Set (Γ ≃g Γ)) :=
    RelativeGrowth.topologicalClosure_open_of_relIndex K N (open_stabilizer Γ o) hNi
  exact ⟨H,hHn,hcH,hoH⟩

theorem compact_open_virtually_nilpotent_quotient_of_sparse_polynomial
    (hc : Γ.Connected) (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, (reachBall Γ o n).ncard≤n^d) :
    HasCompactOpenVirtuallyNilpotentQuotient Γ := by
  let _ : TopologicalSpace X := ⊥
  let _ : DiscreteTopology X := ⟨rfl⟩
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  obtain ⟨H,hHn,hcH,hoH⟩ := compact_open_normal_of_sparse_polynomial Γ hc hl ht o d hpoly
  let := hHn
  have hg := quotient_sparse_polynomial_word_growth Γ hc hl ht o d hpoly H hoH
  obtain ⟨N,hNn,hNi⟩ := CompactQuotient.virtuallyNilpotent_of_sparse_word_growth hg
  exact ⟨H,hHn,hcH,hoH,N,hNn,hNi.index_ne_zero⟩

end CriticalPercolation.GraphTopology
end
end

end OAI
