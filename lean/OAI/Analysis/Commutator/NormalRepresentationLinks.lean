import Mathlib
import OAI.Analysis.Commutator.DiagonalBlockCommutant
import OAI.Analysis.Commutator.NormalBiprodGNS
import OAI.Analysis.Commutator.OrthogonalLinkFamily
import OAI.Analysis.Commutator.RepresentedFactorTransport
import OAI.Analysis.Commutator.TracialConjugation

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.NormalRepresentation

open HilbertBiprod PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

lemma gns_nontrivial (h1 : τ 1=1) : Nontrivial τ.GNS := by
  let v := TracialGNS.algebraVector τ (1:M)
  have hv : inner ℂ v v=1 := by
    rw [TracialGNS.inner_algebraVector]
    simpa using h1
  have hne : v≠0 := by
    intro h
    rw [h,inner_zero_left] at hv
    exact zero_ne_one hv
  exact ⟨⟨v,0,hne⟩⟩

def diagonalAlgebra (hnormal : NormalGNS.BoundedWOTContinuous M τ) :
    VonNeumannAlgebra (Space H τ.GNS) :=
  BicommutantRange.ofStarHom (A:=M) (H:=Space H τ.GNS)
    (diagHom (A:=M) (H:=H) (G:=τ.GNS) M.toStarSubalgebra.subtype τ.gnsStarAlgHom)
    (NormalOperatorHom.diagonal_gns_range M τ hnormal)

lemma diagonal_factor (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hM : FactorCorner.IsFactor M) : FactorCorner.IsFactor (diagonalAlgebra M τ hnormal) :=
  FactorCorner.image_factor M hM _
    (diagHom_injective M.toStarSubalgebra.subtype τ.gnsStarAlgHom Subtype.val_injective)
    (NormalOperatorHom.diagonal_gns_range M τ hnormal)

lemma left_mem_commutant (hnormal : NormalGNS.BoundedWOTContinuous M τ) :
    left (H:=H) (G:=τ.GNS)∈(diagonalAlgebra M τ hnormal).commutant :=
  left_mem_diagonal_commutant (A:=M) (H:=H) (G:=τ.GNS)
    M.toStarSubalgebra.subtype τ.gnsStarAlgHom (NormalOperatorHom.diagonal_gns_range M τ hnormal)

lemma right_mem_commutant (hnormal : NormalGNS.BoundedWOTContinuous M τ) :
    right (H:=H) (G:=τ.GNS)∈(diagonalAlgebra M τ hnormal).commutant :=
  right_mem_diagonal_commutant (A:=M) (H:=H) (G:=τ.GNS)
    M.toStarSubalgebra.subtype τ.gnsStarAlgHom (NormalOperatorHom.diagonal_gns_range M τ hnormal)

theorem exists_orthogonal_links (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hM : FactorCorner.IsFactor M) (h1 : τ 1=1) :
    ∃ S : Set (Link (diagonalAlgebra M τ hnormal).commutant
      (right (H:=H) (G:=τ.GNS)) left),
      OrthogonalLinks _ _ _ S ∧ (familySpace _ _ _ S).starProjection=left := by
  let : Nontrivial τ.GNS := gns_nontrivial M τ h1
  obtain ⟨S,hS⟩ := exists_maximal_orthogonalLinks (diagonalAlgebra M τ hnormal).commutant
    (right (H:=H) (G:=τ.GNS)) left
  refine ⟨S,hS.1,?_⟩
  exact maximal_family_spans _ _ _
    (FactorCorner.commutant_factor _ (diagonal_factor M τ hnormal hM))
    (right_mem_commutant M τ hnormal) (left_mem_commutant M τ hnormal)
    right_projection left_projection right_ne_zero S hS

end Kadison.NormalRepresentation

end

end
end

end OAI
