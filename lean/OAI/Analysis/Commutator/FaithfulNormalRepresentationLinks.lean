import Mathlib
import OAI.Analysis.Commutator.NormalRepresentationLinks
import OAI.Analysis.Commutator.StandardTrace
import OAI.Analysis.Commutator.FullCentralSupportLinks

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.NormalRepresentation

open HilbertBiprod PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma faithful_diagonal_support {G A : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] [CStarAlgebra A]
    (first : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (second : A →⋆ₐ[ℂ] (G →L[ℂ] G))
    (bicommutant : Set.centralizer (Set.centralizer (Set.range (diagHom first second))) =
      Set.range (diagHom first second)) (faithful : Function.Injective second) :
    (FactorCorner.supportSpace (BicommutantRange.ofStarHom (diagHom first second)
      bicommutant).commutant (right (H:=H) (G:=G))).starProjection=1 := by
  let algebra := BicommutantRange.ofStarHom (diagHom first second) bicommutant
  let projection := (FactorCorner.supportSpace algebra.commutant
    (right (H:=H) (G:=G))).starProjection
  have membership : projection ∈ algebra := by
    have membership := FactorCorner.projection_commutant algebra.commutant
      (right (H:=H) (G:=G))
    rw [VonNeumannAlgebra.coe_commutant] at membership
    rwa [algebra.centralizer_centralizer] at membership
  obtain ⟨element,image_eq⟩ := membership
  have fixes_right : projection * right=right := by
    apply ContinuousLinearMap.ext
    intro vector
    apply Submodule.starProjection_eq_self_iff.mpr
    exact FactorCorner.generator_mem algebra.commutant
      (right (H:=H) (G:=G)) algebra.commutant.one_mem vector
  rw [←image_eq] at fixes_right
  have second_eq : second element=1 := by
    apply ContinuousLinearMap.ext
    intro vector
    have evaluation := congrArg (fun operator : Space H G →L[ℂ] Space H G =>
      (operator (inr vector)).ofLp.2) fixes_right
    exact evaluation
  have element_eq : element=1 := faithful (by simpa using second_eq)
  change projection=1
  rw [←image_eq,element_eq,map_one]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

lemma right_full_central_support (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) :
    (FactorCorner.supportSpace (diagonalAlgebra M τ hnormal).commutant
      (right (H:=H) (G:=τ.GNS))).starProjection=1 := by
  exact faithful_diagonal_support (A:=M) (H:=H) (G:=τ.GNS)
    M.toStarSubalgebra.subtype τ.gnsStarAlgHom
    (NormalOperatorHom.diagonal_gns_range M τ hnormal) (NormalGNS.gns_injective M τ hfaith)

theorem exists_orthogonal_links_of_faithful
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) :
    ∃ S : Set (Link (diagonalAlgebra M τ hnormal).commutant
      (right (H:=H) (G:=τ.GNS)) left),
      OrthogonalLinks _ _ _ S ∧ (familySpace _ _ _ S).starProjection=left := by
  obtain ⟨S,hS⟩ := exists_maximal_orthogonalLinks (diagonalAlgebra M τ hnormal).commutant
    (right (H:=H) (G:=τ.GNS)) left
  refine ⟨S,hS.1,?_⟩
  exact maximal_family_spans_of_full_support _ _ _
    (right_full_central_support M τ hnormal hfaith)
    (right_mem_commutant M τ hnormal) (left_mem_commutant M τ hnormal)
    right_projection left_projection S hS

end Kadison.NormalRepresentation

end

end
end

end OAI
