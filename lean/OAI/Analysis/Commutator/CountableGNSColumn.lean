import Mathlib
import OAI.Analysis.Commutator.FaithfulNormalRepresentationLinks
import OAI.Analysis.Commutator.NormalGNSSeparable
import OAI.Analysis.Commutator.NormalRepresentationColumns
import OAI.Analysis.Commutator.CountableOrthogonal
import OAI.Analysis.Commutator.InfiniteLinkColumn

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped Topology InnerProductSpace ComplexOrder

universe u

namespace Kadison.NormalRepresentation

open HilbertBiprod PartialIsometryOrder BiprodLinkColumn

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma embedding_of_links {G : Type u} {A : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [TopologicalSpace.SeparableSpace H] [TopologicalSpace.SeparableSpace G]
    (algebra : VonNeumannAlgebra (Space H G))
    (first : A → (H →L[ℂ] H)) (second : A → (G →L[ℂ] G))
    (links : ∃ family : Set (Intertwiner algebra),
      OrthogonalLinks algebra right left family ∧
        (familySpace algebra right left family).starProjection=left)
    (intertwines : ∀ (link : Intertwiner algebra) (element : A),
      (component algebra link).comp (first element)=
        (second element).comp (component algebra link)) :
    ∃ ι : Type u, Countable ι ∧ ∃ embedding : H →ₗᵢ[ℂ] lp (fun _ : ι => G) 2,
      ∀ (element : A) (vector : H) (index : ι),
        embedding (first element vector) index=second element (embedding vector index) := by
  obtain ⟨family,orthogonal,spans⟩ := links
  let embedding := infiniteColumn algebra family orthogonal spans
  refine ⟨family,links_countable algebra right left family orthogonal,embedding,?_⟩
  intro element vector index
  exact congrArg (fun operator : H →L[ℂ] G => operator vector)
    (intertwines index.val element)

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

theorem exists_countable_gns_embedding [TopologicalSpace.SeparableSpace H]
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) :
    ∃ ι : Type u, Countable ι ∧ ∃ V : H →ₗᵢ[ℂ] lp (fun _ : ι => τ.GNS) 2,
      ∀ (a : M) (x : H) (i : ι),V (a.val x) i=τ.gnsStarAlgHom a (V x i) := by
  let : TopologicalSpace.SeparableSpace τ.GNS := NormalGNS.separable_gns M τ hnormal
  exact embedding_of_links (H:=H) (G:=τ.GNS) (A:=M)
    (diagonalAlgebra M τ hnormal).commutant (fun element => element.val) τ.gnsStarAlgHom
    (exists_orthogonal_links_of_faithful (H:=H) M τ hnormal hfaith)
    (link_intertwines M τ hnormal)

end Kadison.NormalRepresentation

end

end
end

end OAI
