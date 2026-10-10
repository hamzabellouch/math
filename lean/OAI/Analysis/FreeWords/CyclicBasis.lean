import Mathlib
import OAI.Analysis.FreeWords.CyclicMatrix
import OAI.Analysis.FreeWords.ProjectionRound

namespace OAI

noncomputable section

namespace KKLocalPatching

open KKTraceTransfer KKFreeLiftFrontier KKUltraTrace KKFactorSupport KKProjectionSupport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

variable (ρ : Matrix G G ℂ →⋆ₐ[ℂ] ConcreteAlgebra M)

variable (hρ : ∀ a, τ.map (ρ a)=(Fintype.card G : ℂ)⁻¹*Matrix.trace a)

local instance cyclicBasisPartialOrder : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance cyclicBasisStarOrderedRing : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

include hρ

theorem shift_orthonormal : Orthonormal ℂ (fun g : G => gnsVector (tracePositive τ) (ρ (shiftMatrix g))) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro g h
  rw [gnsVector_inner]
  change τ.map (star (ρ (shiftMatrix g))*ρ (shiftMatrix h))=_
  rw [← map_star,← map_mul,shift_star,← shift_add]
  by_cases he : g=h
  · subst h
    rw [neg_add_cancel,shift_zero,map_one,τ.normalized,ite_eq_left rfl]
  · rw [ite_eq_right he,hρ,shift_trace _ (by
      intro hh
      have eqh : h=g := by
        calc h = g+(-g+h) := by simp
             _ = g := by rw [hh,add_zero]
      exact he eqh.symm),mul_zero]

theorem cyclic_bessel (x : ConcreteAlgebra M) :
    ∑ g : G, ‖τ.map (ρ (shiftMatrix g)*x)‖^2 ≤ (traceNorm τ x)^2 := by
  have h := (shift_orthonormal τ ρ hρ).comp (Equiv.neg G) (Equiv.neg G).injective
  have hh := h.sum_inner_products_le (s:=Finset.univ) (gnsVector (tracePositive τ) x)
  simp only [Function.comp_apply,Equiv.neg_apply,gnsVector_inner,
    ← map_star,shift_star,neg_neg] at hh
  rw [traceNorm_eq_gns]
  exact hh

end

end KKLocalPatching
end

end OAI
