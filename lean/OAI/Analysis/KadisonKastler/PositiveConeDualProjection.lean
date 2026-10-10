import OAI.Analysis.KadisonKastler.PositiveConeOrthogonality
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

namespace OAI

/-! # Projection onto the generated positive cone

The Hilbert projection theorem gives a positive part and an orthogonal
residual in the dual cone. Both vectors are fixed by the conjugation.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positiveDualProjectionRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem exists_positiveCone_dual_decomposition
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ=ξ) (x : H) (hx : J x=x) :
    ∃ v r : H, v ∈ modularPositiveCone (M := M) J ξ ∧ J r=r ∧
      (∀ w ∈ modularPositiveCone (M := M) J ξ, 0 ≤ inner ℝ r w) ∧
      inner ℝ r v=0 ∧ x=v-r := by
  let C := modularPositiveCone (M := M) J ξ
  have h0 : (0 : H) ∈ C := zero_mem_modularPositiveCone J ξ
  obtain ⟨v,hv,hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    ⟨0,h0⟩ (modularPositiveCone_isClosed J ξ).isComplete C.convex x
  have hineq := (norm_eq_iInf_iff_real_inner_le_zero C.convex hv).mp hmin
  have hvJ := modularPositiveCone_fixed J hright ξ hξ hv
  have hinner : inner ℝ (x-v) v=0 := by
    have hzero := hineq 0 h0
    have htwo := hineq (v+v) (C.add_mem hv hv)
    simp only [zero_sub,inner_neg_right] at hzero
    rw [add_sub_cancel_left] at htwo
    linarith
  refine ⟨v,v-x,hv,?_,?_,?_,by abel⟩
  · rw [map_sub,hvJ,hx]
  · intro w hw
    have h := hineq (w+v) (C.add_mem hw hv)
    rw [add_sub_cancel_right,inner_sub_left] at h
    rw [inner_sub_left]
    linarith
  · rw [inner_sub_left] at hinner ⊢
    linarith

end

end KadisonKastler

end OAI
