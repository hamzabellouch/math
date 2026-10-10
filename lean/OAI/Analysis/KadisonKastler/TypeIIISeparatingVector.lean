import OAI.Analysis.KadisonKastler.SymmetricSupportTransfer
import Mathlib.Analysis.Normed.Module.RCLike.Real

namespace OAI

/-! # A separating unit vector in any separable type III representation

Every nonzero vector-state support is equivalent to the identity. Moving
the vector through that equivalence makes its state faithful on the
original represented algebra.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem TypeIIIFactor.exists_separating_unit_vector (hM : TypeIIIFactor M) :
    ∃ ξ : H, ‖ξ‖ = 1 ∧ Function.Injective (algebraVectorMap M ξ) := by
  obtain ⟨η,hη⟩ := exists_norm_eq H (show (0 : ℝ) ≤ 1 by norm_num)
  let p := vectorSupportProjection M η
  have hp : p.val ≠ 0 := by
    intro h
    have hfix := vectorSupportProjection_apply M η
    change p.val.val η = η at hfix
    rw [h] at hfix
    have hzero : η = 0 := hfix.symm
    have h01 : (0 : ℝ) = 1 := by simpa only [hzero,norm_zero] using hη
    exact zero_ne_one h01
  obtain ⟨v,hv,hvp⟩ := hM.exists_isometry_onto_projection p.val p.property hp
  have hv' : star v.val * v.val = 1 := congrArg Subtype.val hv
  have hvp' : v.val * star v.val = p.val.val := congrArg Subtype.val hvp
  let ξ := star v.val η
  have hfix : v.val ξ = η := by
    change (v.val * star v.val) η = η
    rw [hvp']
    exact vectorSupportProjection_apply M η
  have hn : ‖ξ‖ = 1 := (norm_apply_of_operator_isometry v.val hv' ξ).symm.trans
    ((congrArg norm hfix).trans hη)
  have hs (a : Algebra M) (ha : a.val ξ = 0) : a = 0 := by
    apply support_transfer_separating M η v (1 : Algebra M.commutant) hv hvp'
      (by simp) a
    simpa only [OneMemClass.coe_one,mul_one] using ha
  refine ⟨ξ,hn,?_⟩
  intro a b hab
  apply sub_eq_zero.mp
  apply hs (a - b)
  change a.val ξ - b.val ξ = 0
  exact sub_eq_zero.mpr hab

end

end KadisonKastler

end OAI
