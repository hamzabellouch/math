import OAI.NumberTheory.CubicMoment.Estimates.PrimaryProductCoefficients
import OAI.NumberTheory.CubicMoment.Estimates.IdealMoebiusBounds

namespace OAI

/-! Uniqueness of the primary squarefree-times-cube coordinates in the
published cubic theta coefficient formulas. -/
noncomputable section
namespace CubicFirstMoment

/-- Primary normalization removes the cube-root unit ambiguity, and the
squarefree exponent is the residue modulo three of each prime valuation. -/
theorem primary_squarefree_cube_unique {c d c' d' : Eisenstein}
    (hc : primary c) (hd : primary d) (hc' : primary c') (hd' : primary d')
    (hcs : Squarefree c) (hcs' : Squarefree c') (he : c*d^3 = c'*d'^3) :
    c = c' ∧ d = d' := by
  have hce := (idealExponentOf_squarefree_iff (primary_ne_zero hc)).mpr hcs
  have hce' := (idealExponentOf_squarefree_iff (primary_ne_zero hc')).mpr hcs'
  have hexp := congrArg idealExponentOf he
  rw [idealExponentOf_mul (primary_ne_zero hc) (pow_ne_zero 3 (primary_ne_zero hd)),
    idealExponentOf_mul (primary_ne_zero hc') (pow_ne_zero 3 (primary_ne_zero hd')),
    idealExponentOf_pow (primary_ne_zero hd),idealExponentOf_pow (primary_ne_zero hd')] at hexp
  have hpoint (p : EisensteinIdealPrime) :
      idealExponentOf c p = idealExponentOf c' p ∧ idealExponentOf d p = idealExponentOf d' p := by
    have h := congrArg (fun f : EisensteinIdealExponent => f p) hexp
    simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul] at h
    have hc1 := hce p
    have hc2 := hce' p
    omega
  constructor
  · apply primary_eq_of_idealExponentOf_eq hc hc'
    ext p
    exact (hpoint p).1
  · apply primary_eq_of_idealExponentOf_eq hd hd'
    ext p
    exact (hpoint p).2

end CubicFirstMoment

end

end OAI
