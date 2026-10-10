import OAI.NumberTheory.Ostmann.Tree.AffineSelfBound

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

theorem norm_mulChar_unit (χ : MulChar (ZMod p) ℂ) (u : (ZMod p)ˣ) : ‖χ u‖=1 := by
  simpa only [MulChar.coe_equivToUnitHom] using
    Complex.norm_eq_one_of_mem_rootsOfUnity (MulChar.apply_mem_rootsOfUnity (χ := χ) u)

def reciprocalTwist (g : ZMod p → ℂ) (η : MulChar (ZMod p) ℂ) (c : ZMod p)
    (h : ZMod p) : ℂ := g h⁻¹*η h⁻¹*ZMod.stdAddChar (c*h⁻¹)

@[simp] theorem reciprocalTwist_zero (g : ZMod p → ℂ) (η : MulChar (ZMod p) ℂ)
    (c : ZMod p) (hg : g 0=0) : reciprocalTwist g η c 0=0 := by
  simp [reciprocalTwist, hg]

theorem reciprocalTwist_mean (g : ZMod p → ℂ) (η : MulChar (ZMod p) ℂ)
    (c : ZMod p) : mean (reciprocalTwist g η c)=mixedCorrelation g η c := by
  unfold mean reciprocalTwist mixedCorrelation
  congr 1
  exact inv_involutive.bijective.sum_comp
    (fun h : ZMod p => g h*η h*ZMod.stdAddChar (c*h))

theorem reciprocalTwist_norm (g : ZMod p → ℂ) (η : MulChar (ZMod p) ℂ)
    (c h : ZMod p) (hg : g 0=0) : ‖reciprocalTwist g η c h‖=‖g h⁻¹‖ := by
  by_cases hh : h=0
  · subst h
    simp [reciprocalTwist, hg]
  · have hi : h⁻¹ ≠ 0 := inv_ne_zero hh
    have he := norm_mulChar_unit η (Units.mk0 h⁻¹ hi)
    change ‖η h⁻¹‖=1 at he
    have hephase : ‖ZMod.stdAddChar (c*h⁻¹)‖=1 :=
      AddChar.norm_apply (ZMod.stdAddChar : AddChar (ZMod p) ℂ) _
    simp only [reciprocalTwist, norm_mul, he, hephase, mul_one]

theorem reciprocalTwist_l2Sq (g : ZMod p → ℂ) (η : MulChar (ZMod p) ℂ)
    (c : ZMod p) (hg : g 0=0) : l2Sq (reciprocalTwist g η c)=l2Sq g := by
  simp only [l2Sq, reciprocalTwist_norm g η c _ hg]
  congr 1
  exact inv_involutive.bijective.sum_comp (fun h : ZMod p => ‖g h‖^2)

theorem reciprocalTwist_affine_bound (g : ZMod p → ℂ) (η : MulChar (ZMod p) ℂ)
    (c : ZMod p) (hg0 : g 0=0) (hg : l2Sq g ≤ 1) :
    l2Sq (weightedAffine (fun r => conj (reciprocalTwist g η c r)) (reciprocalTwist g η c)) ≤
      (correlationBound g : ℝ)^4 + Real.sqrt (3/(p:ℝ)) := by
  have hG := weightedAffine_self_bound (reciprocalTwist g η c)
    (reciprocalTwist_zero g η c hg0) (by rwa [reciprocalTwist_l2Sq g η c hg0])
  rw [reciprocalTwist_mean] at hG
  exact hG.trans (add_le_add
    (pow_le_pow_left₀ (norm_nonneg _) (norm_mixedCorrelation_le g η c) 4) le_rfl)

end
end Ostmann.FiniteField

end OAI
