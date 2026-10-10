import OAI.GroupTheory.PolycyclicRecognition.Algebra.SubgroupShapiroReturn
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteIndexTopHomology

namespace OAI

/-! # The degree of a finite-index inclusion in top homology -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem finiteIndex_subgroup_topHomology_degree (H : Subgroup G) [H.FiniteIndex]
    (D : Rep ℤ G) {n : ℕ} (eD : D.V ≃ₗ[ℤ] ℤ)
    (e : ∀ A : Rep ℤ G, groupHomology A n ≃ₗ[ℤ] (D ⟶ A))
    (he : ∀ (A B : Rep ℤ G) (f : A ⟶ B) (x : groupHomology A n),
      e B (groupHomology.map (MonoidHom.id G) f n x) = e A x ≫ f) :
    ∃ (u : groupHomology (Rep.res H.subtype D) n ≃ₗ[ℤ] ℤ)
      (v : groupHomology D n ≃ₗ[ℤ] ℤ),
      ∀ x, v (subgroupHomologyInclusion H D n x) = (H.index : ℤ) * u x := by
  obtain ⟨u, v, h⟩ := finiteIndex_topHomology_return H D eD e he
  let s := (subgroupShapiroIso H (Rep.res H.subtype D) n).toLinearEquiv
  refine ⟨s.trans u, v, ?_⟩
  intro x
  have hx := congrArg (fun f => f x) (subgroupShapiro_return H D n)
  change groupHomology.map (MonoidHom.id G) (finiteIndexReturn H D) n (s x) =
    subgroupHomologyInclusion H D n x at hx
  change v (subgroupHomologyInclusion H D n x) = (H.index : ℤ) * u (s x)
  rw [← hx]
  exact h (s x)

theorem IsIntegralPoincareDualityGroup.exists_topHomology_index {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) :
    ∃ D : Rep ℤ G, Nonempty (D.V ≃ₗ[ℤ] ℤ) ∧
      ∀ (H : Subgroup G) (_ : H.FiniteIndex),
        ∃ (u : groupHomology (Rep.res H.subtype D) n ≃ₗ[ℤ] ℤ)
          (v : groupHomology D n ≃ₗ[ℤ] ℤ),
          ∀ x, v (subgroupHomologyInclusion H D n x) = (H.index : ℤ) * u x := by
  obtain ⟨D, ⟨eD⟩, e, he⟩ := hG.topHomology_natural
  refine ⟨D, ⟨eD⟩, ?_⟩
  intro H hH
  exact finiteIndex_subgroup_topHomology_degree H D eD e he

end PolycyclicRecognition

end

end OAI
