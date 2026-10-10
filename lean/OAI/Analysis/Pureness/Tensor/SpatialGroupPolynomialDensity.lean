import OAI.Analysis.Pureness.Tensor.SpatialTensorContinuousLegs
import OAI.Analysis.Pureness.GroupAlgebra.ReducedGroupCStarAlgebra

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped TensorProduct
variable {A H G : Type*} [Group G] [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H))

def spatialGroupPolynomial :
    Submodule ℂ (representedSpatialTensor α (reducedGroupAlgebra G).subtype) :=
  Submodule.span ℂ (Set.range fun p : A × G =>
    spatialCompletionMap α (reducedGroupAlgebra G).subtype
      (p.1 ⊗ₜ[ℂ] (reducedGroupUnitary G p.2 : reducedGroupAlgebra G)))

lemma spatialGroupPolynomial_generator (a : A) (g : G) :
    spatialCompletionMap α (reducedGroupAlgebra G).subtype
      (a ⊗ₜ[ℂ] (reducedGroupUnitary G g : reducedGroupAlgebra G)) ∈
        spatialGroupPolynomial (G := G) α := Submodule.subset_span ⟨(a,g), rfl⟩

lemma reducedGroup_closed_submodule_eq_top (P : Submodule ℂ (reducedGroupAlgebra G))
    (hP : IsClosed (P : Set (reducedGroupAlgebra G)))
    (hgen : ∀ g : G, (reducedGroupUnitary G g : reducedGroupAlgebra G) ∈ P) : P = ⊤ := by
  let i : groupRegularSpan G →⋆ₐ[ℂ] reducedGroupAlgebra G :=
    StarSubalgebra.inclusion (StarSubalgebra.le_topologicalClosure _)
  have hd : DenseRange i := by
    change DenseRange (Set.inclusion (StarSubalgebra.le_topologicalClosure (groupRegularSpan G)))
    exact (denseRange_inclusion_iff _).mpr Set.Subset.rfl
  apply top_unique
  intro b _
  refine hd.induction_on b hP ?_
  intro a
  have h : ∀ x (hx : x ∈ Submodule.span ℂ (Set.range (groupLeft (G := G)))),
      (⟨x, StarSubalgebra.le_topologicalClosure (groupRegularSpan G) hx⟩ :
        reducedGroupAlgebra G) ∈ P := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hgen g
    | zero => exact P.zero_mem
    | add x y hx hy ihx ihy => exact P.add_mem ihx ihy
    | smul c x hx ih => exact P.smul_mem c ih
  exact h a.val a.property

theorem spatialGroupPolynomial_dense :
    Dense (spatialGroupPolynomial (G := G) α :
      Set (representedSpatialTensor α (reducedGroupAlgebra G).subtype)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  let P := (spatialGroupPolynomial α (G := G)).topologicalClosure
  have hp : IsClosed (P : Set (representedSpatialTensor α (reducedGroupAlgebra G).subtype)) :=
    Submodule.isClosed_topologicalClosure (spatialGroupPolynomial (G := G) α)
  have ht (a : A) (b : reducedGroupAlgebra G) :
      spatialCompletionMap α (reducedGroupAlgebra G).subtype (a ⊗ₜ[ℂ] b) ∈ P := by
    let L := spatialTensorRightLeg α (reducedGroupAlgebra G).subtype a
    have he : P.comap L.toLinearMap = ⊤ :=
      reducedGroup_closed_submodule_eq_top _ (hp.preimage L.continuous) (fun g =>
        Submodule.le_topologicalClosure _ (spatialGroupPolynomial_generator α a g))
    have hb : b ∈ P.comap L.toLinearMap := by rw [he]; trivial
    exact hb
  apply top_unique
  intro x _
  refine (representedSpatialTensor_dense α (reducedGroupAlgebra G).subtype).induction_on x hp ?_
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a b => exact ht a b
  | add z w hz hw => simpa only [map_add] using P.add_mem hz hw
end CuntzPureness

end

end OAI
