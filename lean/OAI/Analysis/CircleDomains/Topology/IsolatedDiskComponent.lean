import OAI.Analysis.CircleDomains.Topology.AnalyticCircleImage

namespace OAI

/-! A closed disk with an exterior collar contained in the domain is an
entire complementary component. -/
open Set Function Filter Metric Complex
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma connectedComponentIn_eq_of_relative_clopen {X:Type*} [TopologicalSpace X]
    {S K:Set X} (hK:IsPreconnected K) (hKS:K⊆S)
    (hKC:IsClopen (((↑):S→X) ⁻¹' K)) {x:X} (hx:x∈K) : connectedComponentIn S x=K := by
  apply Subset.antisymm
  · rw [connectedComponentIn_eq_image (hKS hx)]
    rintro y ⟨z,hz,rfl⟩
    exact hKC.connectedComponent_subset (show (⟨x,hKS hx⟩:S)∈(((↑):S→X) ⁻¹' K) from hx) hz
  · exact hK.subset_connectedComponentIn hx hKS

lemma closedBall_complementary_component {D V:Set ℂ} {c:ℂ} {r:ℝ}
    (hV:IsOpen V) (hbd:sphere c r⊆V)
    (hK:closedBall c r⊆Dᶜ) (hcollar:V\closedBall c r⊆D)
    {x:ℂ} (hx:x∈closedBall c r) : connectedComponentIn Dᶜ x=closedBall c r := by
  let W := ball c r∪V
  have hW:IsOpen W := isOpen_ball.union hV
  have hKW:closedBall c r⊆W := by
    intro y hy
    rcases lt_or_eq_of_le (mem_closedBall.mp hy) with h|h
    · exact Or.inl h
    · exact Or.inr (hbd (mem_sphere.mpr h))
  have he : (((↑):↥(Dᶜ)→ℂ) ⁻¹' closedBall c r)=(((↑):↥(Dᶜ)→ℂ) ⁻¹' W) := by
    ext y
    constructor
    · exact fun hy => hKW hy
    · intro hy
      rcases hy with hy|hy
      · exact ball_subset_closedBall hy
      · by_contra hn
        exact y.property (hcollar ⟨hy,hn⟩)
  have hopen : IsOpen (((↑):↥(Dᶜ)→ℂ) ⁻¹' closedBall c r) := by
    rw [he]
    exact hW.preimage continuous_subtype_val
  exact connectedComponentIn_eq_of_relative_clopen (convex_closedBall c r).isPreconnected
    hK ⟨isClosed_closedBall.preimage continuous_subtype_val,hopen⟩ hx

end CircleDomainRigidity

end

end OAI
