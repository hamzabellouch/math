import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteModuleIndependentBound
import Mathlib.RingTheory.FiniteType

namespace OAI

/-! # A coefficient-independent size bound for a group-ring presentation -/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra
variable {Q : Type} [CommMonoid Q]

theorem monoidAlgebra_generators_of_closure (s : Finset Q)
    (hs : Submonoid.closure (s : Set Q) = ⊤) (K : Type) [CommRing K] :
    ∃ a : Fin (Fintype.card s) → K[Q], Algebra.adjoin K (Set.range a) = ⊤ := by
  let f₀ : MvPolynomial s K →ₐ[K] K[Q] :=
    MvPolynomial.aeval (fun i => MonoidAlgebra.of K Q i.val)
  have hf₀ : Function.Surjective f₀ :=
    MonoidAlgebra.mvPolynomial_aeval_of_surjective_of_closure hs
  let e := MvPolynomial.renameEquiv K (Fintype.equivFin s)
  let f := f₀.comp e.symm.toAlgHom
  have hf : Function.Surjective f := hf₀.comp e.symm.surjective
  let a : Fin (Fintype.card s) → K[Q] := fun i => f (MvPolynomial.X i)
  refine ⟨a, ?_⟩
  have heq : MvPolynomial.aeval a = f := by ext i; simp [a]
  rw [Algebra.adjoin_range_eq_range_aeval, heq]
  exact (AlgHom.range_eq_top f).mpr hf

end PolycyclicRecognition

end

end OAI
