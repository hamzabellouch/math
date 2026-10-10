import OAI.NumberTheory.CubicMoment.Estimates.PrincipalIdealTheta
import OAI.NumberTheory.CubicMoment.Estimates.IdealThetaMellin
import OAI.NumberTheory.CubicMoment.Estimates.HeckeThetaCompletion

namespace OAI

/-! Continuation of the principal ideal series from the actual principal
theta function, retaining its simple pole at one. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

def principalThetaConstant : ℂ := (Nat.card (Eisensteinˣ):ℂ)⁻¹

lemma principalThetaConstant_ne_zero : principalThetaConstant ≠ 0 :=
  inv_ne_zero residueTheta_unit_multiplicity_ne_zero

def principalIdealFEPair : WeakFEPair ℂ where
  f t := principalThetaConstant+idealTheta (residueHeckeScale 1) (fun _ => 1) t
  g t := principalThetaConstant+idealTheta (residueHeckeScale 1) (fun _ => 1) t
  k := 1
  ε := 1
  f₀ := principalThetaConstant
  g₀ := principalThetaConstant
  hf_int := (continuousOn_const.add (idealTheta_continuousOn
    (residueHeckeScale_pos (q := 1) one_ne_zero) _ (by simp))).locallyIntegrableOn measurableSet_Ioi
  hg_int := (continuousOn_const.add (idealTheta_continuousOn
    (residueHeckeScale_pos (q := 1) one_ne_zero) _ (by simp))).locallyIntegrableOn measurableSet_Ioi
  hk := zero_lt_one
  hε := one_ne_zero
  hf_top r := by
    simpa only [add_sub_cancel_left] using idealTheta_isBigO_rpow
      (residueHeckeScale_pos (q := 1) one_ne_zero) (fun _ => 1) (by simp) r
  hg_top r := by
    simpa only [add_sub_cancel_left] using idealTheta_isBigO_rpow
      (residueHeckeScale_pos (q := 1) one_ne_zero) (fun _ => 1) (by simp) r
  h_feq t ht := by
    simp only [Real.rpow_one,one_mul,smul_eq_mul]
    rw [principalIdealTheta_inversion ht]
    unfold principalThetaConstant
    have hU := residueTheta_unit_multiplicity_ne_zero
    field_simp
    ring

lemma principalIdealFEPair_right {s : ℂ} (hs : 1 < s.re) :
    principalIdealFEPair.Λ s=(residueHeckeScale 1:ℂ)^s*Complex.Gamma s*
      normDirichletSeries (fun _ => 1) idealExponentNorm s := by
  have he := (principalIdealFEPair.hasMellin hs).2
  change mellin (fun t => principalThetaConstant+
    idealTheta (residueHeckeScale 1) (fun _ => 1) t-principalThetaConstant) s = _ at he
  simp only [add_sub_cancel_left] at he
  rw [←he]
  exact idealTheta_mellin (residueHeckeScale_pos (q := 1) one_ne_zero) _ (by simp) hs

def principalIdealZeta (s : ℂ) : ℂ :=
  thetaHeckeL (residueHeckeScale 1) principalIdealFEPair.Λ s

lemma principalIdealZeta_right {s : ℂ} (hs : 1 < s.re) :
    principalIdealZeta s=normDirichletSeries (fun _ => 1) idealExponentNorm s := by
  rw [principalIdealZeta,thetaHeckeL,principalIdealFEPair_right hs]
  have hA : (residueHeckeScale 1:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (residueHeckeScale_pos (q := 1) one_ne_zero).ne'
  have hG := Complex.Gamma_ne_zero_of_re_pos (show 0 < s.re by linarith)
  rw [Complex.cpow_neg]
  have hp : (residueHeckeScale 1:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hA)
  field_simp

end CubicFirstMoment

end

end OAI
