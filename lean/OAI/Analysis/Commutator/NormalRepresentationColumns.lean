import Mathlib
import OAI.Analysis.Commutator.BiprodLinkColumn
import OAI.Analysis.Commutator.NormalRepresentationLinks
import OAI.Analysis.Commutator.OperatorAmplification
import OAI.Analysis.Commutator.StandardTrace

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.NormalRepresentation

open HilbertBiprod PartialIsometryOrder BiprodLinkColumn OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hnormal : NormalGNS.BoundedWOTContinuous M τ)

lemma link_intertwines (v : Intertwiner (diagonalAlgebra M τ hnormal).commutant) (a : M) :
    (component _ v).comp (a:H →L[ℂ] H)=(τ.gnsStarAlgHom a).comp (component _ v) := by
  apply component_intertwines _ M.toStarSubalgebra.subtype τ.gnsStarAlgHom v a
  have hv : star v.val ∈ (diagonalAlgebra M τ hnormal).commutant :=
    (diagonalAlgebra M τ hnormal).commutant.star_mem' v.mem
  have ha : block (a:H →L[ℂ] H) (τ.gnsStarAlgHom a)∈diagonalAlgebra M τ hnormal := by
    exact ⟨a,rfl⟩
  rw [←SetLike.mem_coe,VonNeumannAlgebra.coe_commutant] at hv
  exact hv _ ha

variable (S : Set (Intertwiner (diagonalAlgebra M τ hnormal).commutant))

lemma finiteColumn_intertwines (s : Finset S) (a : M) :
    (finiteColumn _ S s).comp (a:H →L[ℂ] H)=
      (diagonal (H:=τ.GNS) s (τ.gnsStarAlgHom a)).comp (finiteColumn _ S s) := by
  classical
  ext x i
  exact congrArg (fun T : H →L[ℂ] τ.GNS => T x) (link_intertwines M τ hnormal i.val.val a)

lemma diagonal_representation_injective (ι : Type*) [Fintype ι] [Nonempty ι]
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) :
    Function.Injective ((diagonal (H:=τ.GNS) ι).comp τ.gnsStarAlgHom) := by
  classical
  intro a b hab
  apply NormalGNS.gns_injective M τ hfaith
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  ext x
  have h := congrArg (fun T : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι =>
    T (single ι i x) i) hab
  simpa only [StarAlgHom.comp_apply,diagonal_apply,single_apply,ite_true] using h

end Kadison.NormalRepresentation

end

end
end

end OAI
