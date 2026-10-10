import OAI.Geometry.KahlerSplitting.Biholomorphism

namespace OAI

section

noncomputable section
open Set
open scoped Manifold ContDiff
namespace UniversalCoverSplitting
universe u v
variable {n r₁ r₂ : ℕ}

theorem main (X : ComplexManifold.{u} n) [CompactSpace X.Carrier]
    [ConnectedSpace X.Carrier] (hn : 2 ≤ n) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (g : KahlerMetric X) (S : HolomorphicSplitting X r₁ r₂)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    (Z : ComplexManifold.{v} n) (π : OrdinaryUniversalCover X Z) :
    ∃ (Y₁ : ComplexManifold.{v} r₁) (Y₂ : ComplexManifold.{v} r₂),
      ConnectedSpace Y₁.Carrier ∧ ConnectedSpace Y₂.Carrier ∧
      SimplyConnectedSpace Y₁.Carrier ∧ SimplyConnectedSpace Y₂.Carrier ∧
      CompatibleProduct S π Y₁ Y₂ := by
  have _ := hn
  have _ := hr₁
  have _ := hr₂
  let := π.connected
  let o : Z.Carrier := Classical.choice inferInstance
  obtain ⟨P⟩ := exists_productRetracts g h₁ h₂ π o
  let := P.simplyConnected_first g
  let := P.simplyConnected_second g
  refine ⟨P.Y₁,P.Y₂,inferInstance,inferInstance,inferInstance,inferInstance,?_⟩
  obtain ⟨Φ,hΦ,hd,hdi⟩ := P.pair_biholomorph g
  refine ⟨Φ,hd,hdi,?_,?_⟩
  · rw [hΦ]
    exact P.first_tangent g
  · rw [hΦ]
    exact P.second_tangent g

end UniversalCoverSplitting
end
end

end OAI
