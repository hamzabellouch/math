import Mathlib
import OAI.Analysis.FreeWords.RoundingMatrixUnitary

namespace OAI

noncomputable section

namespace KKProjectionSupport

open KKTraceTransfer KKUltraTrace KKFreeLiftFrontier KKSpectralSupport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

end

end KKProjectionSupport

namespace KKProjectionSupport

open KKTraceTransfer KKFreeLiftFrontier KKSpectralSupport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem chosen_unitary_matrix_approximation (M : VonNeumannAlgebra H)
    (τ : FaithfulNormalTrace M) (hF : IsFactor M) (hD : IsDiffuse M)
    (u : unitary (ConcreteAlgebra M)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (_hn : 0 < n)
      (ρ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M)
      (v : unitary (Matrix (Fin n) (Fin n) ℂ)),
      Function.Injective ρ ∧ traceNorm τ (u.val-ρ v.val) < ε := by
  classical
  obtain ⟨m,l,p,c,hp,ho,h1,hc,he⟩ := unitary_finite_spectrum_approximation M u (ε/2) (half_pos hε)
  obtain ⟨n,hn,ρ,v,hρ,hv⟩ := rounded_unitary_matrix M τ hF hD p hp ho h1 c hc (ε/2) (half_pos hε)
  refine ⟨n,hn,ρ,v,hρ,?_⟩
  have ha : traceNorm τ (u.val-∑ i, c i • p i) < ε/2 :=
    (traceNorm_le_norm τ _).trans_lt he
  have ht := traceNorm_add_le τ (u.val-∑ i, c i • p i) ((∑ i, c i • p i)-ρ v.val)
  rw [sub_add_sub_cancel] at ht
  linarith

end

end KKProjectionSupport
end

end OAI
