import OAI.Analysis.KadisonKastler.PositiveConePowersStormer
import OAI.Analysis.KadisonKastler.PositiveUnitaryTransport
import OAI.Analysis.KadisonKastler.CentralDefectStateBound

namespace OAI

/-! # State commutators control unitary central-vector defects

Powers–Størmer, followed by a unitary change of coordinates, gives the
reverse estimate needed to compare the state and vector centralizer tests.
-/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance unitaryStateDefectRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem sandwich_unitary_state_norm_sub_le (ξ : H) (u : unitary (Algebra M)) :
    ‖sandwichFunctional (vectorFunctional ξ) (star u).val-vectorFunctional (M := M) ξ‖ ≤
      ‖vectorStateCommutator ξ u.val‖ := by
  apply (sandwichFunctional (vectorFunctional ξ) (star u).val-
    vectorFunctional (M := M) ξ).opNorm_le_bound (norm_nonneg _)
  intro a
  have he : (sandwichFunctional (vectorFunctional ξ) (star u).val-
      vectorFunctional (M := M) ξ) a = vectorStateCommutator ξ u.val (a*star u.val) := by
    simp only [sub_apply,sandwichFunctional_apply,Unitary.coe_star,star_star]
    change vectorFunctional ξ (u.val*a*star u.val)-vectorFunctional ξ a =
      vectorFunctional ξ (u.val*(a*star u.val)-(a*star u.val)*u.val)
    rw [map_sub,mul_assoc a, u.property.1,mul_one]
    simp only [mul_assoc]
  rw [he]
  exact ((vectorStateCommutator ξ u.val).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left
      ((norm_mul_le _ _).trans (by
        have h := norm_unitary_le_one (star u)
        change ‖star u.val‖ ≤ 1 at h
        exact mul_le_of_le_one_right (norm_nonneg _) h)) (norm_nonneg _))

theorem centralVectorDefect_unitary_norm_eq
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (ξ : H) (u : unitary (Algebra M)) :
    ‖centralVectorDefect J ξ u.val.val‖ =
      ‖(modularUnitary J hJ (star u) : H →L[ℂ] H) ξ-ξ‖ := by
  have hmul : u.val.val*star u.val.val=1 :=
    congrArg (fun a : Algebra M => a.val) u.property.2
  have he : (ambientAlgebraUnitary u : H →L[ℂ] H)
      ((modularUnitary J hJ (star u) : H →L[ℂ] H) ξ-ξ) =
      -(centralVectorDefect J ξ u.val.val) := by
    change u.val.val ((star u.val.val*conjugationOperator J (star u.val.val)) ξ-ξ)=_
    rw [map_sub]
    have hfirst : u.val.val ((star u.val.val*conjugationOperator J (star u.val.val)) ξ) =
        conjugationOperator J (star u.val.val) ξ := by
      change (u.val.val*(star u.val.val*conjugationOperator J (star u.val.val))) ξ=_
      rw [← mul_assoc,hmul,one_mul]
    rw [hfirst,centralVectorDefect_apply]
    abel
  have hn := Unitary.norm_map (ambientAlgebraUnitary u)
    ((modularUnitary J hJ (star u) : H →L[ℂ] H) ξ-ξ)
  rw [he,norm_neg] at hn
  exact hn

theorem centralVectorDefect_unitary_sq_le_stateCommutator
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (u : unitary (Algebra M)) :
    ‖centralVectorDefect J ξ u.val.val‖^2 ≤ ‖vectorStateCommutator ξ u.val‖ := by
  have hc := reference_mem_modularPositiveCone (M := M) J hJ ξ
  have hu := modularQuadratic_preserves_positiveCone J hJ hright ξ (star u).val hc
  have hs := positiveCone_norm_sq_le_state_norm J hJ hright hleft ξ hξ hcyc hpos hu hc
  rw [← modularUnitary_coe J hJ (star u),
    modularUnitary_vectorFunctional J hJ hright] at hs
  rw [centralVectorDefect_unitary_norm_eq J hJ ξ u]
  exact hs.trans (sandwich_unitary_state_norm_sub_le ξ u)

end

end KadisonKastler

end OAI
