import Mathlib
import OAI.Analysis.Commutator.BalancedSymmetry
import OAI.Analysis.Commutator.MatrixVectorTrace

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.MatrixGNS

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype ι]

local instance : DecidableEq ι := Classical.decEq ι

variable (τ : A →ₚ[ℂ] ℂ)

omit [Fintype ι] in
lemma algebraArray_eq_zero_iff
    (hfaith : ∀ a : A, τ (star a*a)=0 → a=0) (X : CStarMatrix ι ι A) :
    algebraArray τ X=0 ↔ X=0 := by
  constructor
  · intro h
    apply CStarMatrix.ext
    intro i j
    have hv := congrArg (fun v : ArraySpace (ι:=ι) τ => v i j) h
    exact (TracialGNS.coe_preGNS_eq_zero_iff τ hfaith (X i j)).mp hv
  · rintro rfl
    ext i j
    change (τ.toPreGNS 0 : τ.GNS)=0
    exact (TracialGNS.coe_preGNS_eq_zero_iff τ hfaith 0).mpr rfl

lemma trace_faithful [Nonempty ι]
    (hfaith : ∀ a : A, τ (star a*a)=0 → a=0) (X : CStarMatrix ι ι A)
    (hz : trace (ι:=ι) τ (star X*X)=0) : X=0 := by
  have hv : representation τ X (vacuum (ι:=ι) τ)=0 := by
    change VectorFunctional.functional (vacuum (ι:=ι) τ)
      (representation τ (star X*X))=0 at hz
    rw [map_mul,map_star,VectorFunctional.functional_star_mul] at hz
    exact inner_self_eq_zero.mp hz
  rw [representation_vacuum] at hv
  apply (algebraArray_eq_zero_iff τ hfaith X).mp
  exact (smul_eq_zero.mp hv).resolve_left (scale_ne_zero (ι:=ι))

omit [Fintype ι] in
lemma balanced_symmetry_trace_zero
    (hτ : ∀ a b : A, τ (a*b)=τ (b*a)) (x : A) (hx : ‖x‖≤1) :
    trace (ι:=Fin 2) τ (BalancedDilation.symmetry x)=0 := by
  rw [trace_apply]
  rw [BalancedDilation.symmetry_diagonal_trace τ hτ x hx,mul_zero]

end Kadison.MatrixGNS

end

end
end

end OAI
