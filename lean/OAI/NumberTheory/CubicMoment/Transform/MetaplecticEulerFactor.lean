import OAI.NumberTheory.CubicMoment.Transform.MetaplecticHeight
import OAI.NumberTheory.CubicMoment.Estimates.PrimaryPrimeEstimateTransfer
import OAI.NumberTheory.CubicMoment.Estimates.IdealDirichletInverse
import OAI.NumberTheory.CubicMoment.Estimates.IdealDirichletHolomorphic

namespace OAI

/-! The completed cubic Gauss series uses an actual primary coprimality
Euler factor. It is identified with a complete principal ideal series and
is nonzero throughout the half-plane needed for decompletion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primaryCoprimeZeta (r : Eisenstein) (s : ℂ) : ℂ :=
  ∑' u : PrimaryArgument, if IsCoprime r (u:Eisenstein) then (norm u:ℂ)^(-s) else 0

lemma primary_ideal_tsum (f : Eisenstein → ℂ) :
    (∑' ν : EisensteinIdealExponent, if primary (idealPrimaryGenerator ν) then
      f (idealPrimaryGenerator ν) else 0) = ∑' u : PrimaryArgument, f u := by
  let g (ν : EisensteinIdealExponent) : ℂ :=
    if primary (idealPrimaryGenerator ν) then f (idealPrimaryGenerator ν) else 0
  have hi : Function.Injective (fun u : PrimaryArgument => idealExponentOf u.val) := by
    intro a b h
    exact Subtype.ext (idealExponentOf_inj_primary a.property b.property h)
  have hs : Function.support g ⊆ Set.range (fun u : PrimaryArgument => idealExponentOf u.val) := by
    intro ν hν
    have hp : primary (idealPrimaryGenerator ν) := by
      by_contra hn
      exact hν (by simp [g,hn])
    exact ⟨⟨idealPrimaryGenerator ν,hp⟩,idealExponentOf_primaryGenerator ν⟩
  rw [←hi.tsum_eq hs]
  apply tsum_congr
  intro u
  simp [g,idealPrimaryGenerator_at_element u.property,u.property]

lemma principal_residue_at_primary {q a : Eisenstein} (ha : primary a) :
    residueIdealChar q (1 : MulChar (Residues q) ℂ) (idealExponentOf a) =
      (1 : MulChar (Residues q) ℂ) (Ideal.Quotient.mk (modulus q) a) := by
  have hu : AngularUnitCompatible q (1 : MulChar (Residues q) ℂ) 0 := by
    intro u
    rw [theta_zero,mul_one]
    exact MulChar.one_apply (u.isUnit.map (Ideal.Quotient.mk (modulus q)))
  simpa only [angularResidueIdealChar_zero,theta_zero,mul_one] using
    angularResidueIdealChar_at_element (1 : MulChar (Residues q) ℂ) hu (primary_ne_zero ha)

lemma principal_residue_coprime_primary (r : Eisenstein) {a : Eisenstein} (ha : primary a) :
    (1 : MulChar (Residues (3*r)) ℂ) (Ideal.Quotient.mk (modulus (3*r)) a) =
      if IsCoprime r a then 1 else 0 := by
  by_cases hc : IsCoprime r a
  · rw [ite_eq_left hc]
    apply MulChar.one_apply
    exact residue_isUnit_of_isCoprime ((primary_coprime_three ha).symm.mul_left hc)
  · rw [ite_eq_right hc]
    apply MulChar.map_nonunit
    intro hunit
    exact hc ((isCoprime_of_residue_isUnit hunit).of_mul_left_right)

lemma primaryCoprimeZeta_eq_ideal {r : Eisenstein} (_hr : r ≠ 0) (s : ℂ) :
    primaryCoprimeZeta r s =
      normDirichletSeries (residueIdealChar (3*r) (1 : MulChar (Residues (3*r)) ℂ))
        idealExponentNorm s := by
  have h3 : (3:Eisenstein) ∣ 3*r := dvd_mul_right _ _
  have hsum := primary_ideal_tsum (fun a => if IsCoprime r a then (norm a:ℂ)^(-s) else 0)
  rw [primaryCoprimeZeta,←hsum,normDirichletSeries]
  apply tsum_congr
  intro ν
  by_cases hp : primary (idealPrimaryGenerator ν)
  · rw [ite_eq_left hp,←idealPrimaryGenerator_norm ν]
    have he := principal_residue_at_primary (q := 3*r) hp
    rw [idealExponentOf_primaryGenerator ν,principal_residue_coprime_primary r hp] at he
    rw [he]
    split_ifs <;> simp
  · rw [ite_eq_right hp,residueIdealChar_zero_nonprimary h3 _ ν hp,zero_mul]

lemma primaryCoprimeZeta_ne_zero {r : Eisenstein} (hr : r ≠ 0)
    {s : ℂ} (hs : 1 < s.re) : primaryCoprimeZeta r s ≠ 0 := by
  have hq : (3:Eisenstein)*r ≠ 0 := mul_ne_zero (by norm_num) hr
  rw [primaryCoprimeZeta_eq_ideal hr]
  apply idealDirichlet_ne_zero _ (residueIdealChar_norm_le_one hq _) _
    (residueIdealChar_add _ _) hs
  simp [residueIdealChar,idealExponentGenerator]

def metaplecticCompletionEuler (r : Eisenstein) (s : ℂ) : ℂ :=
  primaryCoprimeZeta r (3*s-1/2)

lemma metaplecticCompletionEuler_ne_zero {r : Eisenstein} (hr : r ≠ 0)
    {s : ℂ} (hs : (1/2:ℝ) < s.re) : metaplecticCompletionEuler r s ≠ 0 := by
  apply primaryCoprimeZeta_ne_zero hr
  have he : (3*s-(1/2:ℂ)).re = 3*s.re-1/2 := by simp
  rw [he]
  linarith

lemma primaryCoprimeZeta_differentiableAt {r : Eisenstein} (hr : r ≠ 0)
    {s : ℂ} (hs : 1 < s.re) : DifferentiableAt ℂ (primaryCoprimeZeta r) s := by
  have hq : (3:Eisenstein)*r ≠ 0 := mul_ne_zero (by norm_num) hr
  have he : primaryCoprimeZeta r =
      normDirichletSeries (residueIdealChar (3*r) (1 : MulChar (Residues (3*r)) ℂ))
        idealExponentNorm := funext (primaryCoprimeZeta_eq_ideal hr)
  rw [he]
  exact idealDirichlet_differentiableAt _ (residueIdealChar_norm_le_one hq _) hs

lemma metaplecticCompletionEuler_differentiableOn {r : Eisenstein} (hr : r ≠ 0) :
    DifferentiableOn ℂ (metaplecticCompletionEuler r) {s : ℂ | (1/2:ℝ) < s.re} := by
  intro s hs
  change (1/2:ℝ) < s.re at hs
  have he : (3*s-(1/2:ℂ)).re = 3*s.re-1/2 := by simp
  exact ((primaryCoprimeZeta_differentiableAt hr (by rw [he]; linarith)).comp s
    (by fun_prop)).differentiableWithinAt

lemma metaplecticCompletionEuler_at_pole (r : Eisenstein) :
    metaplecticCompletionEuler r (5/6) = (metaplecticEulerAtTwo r:ℂ) := by
  have he : (3*(5/6:ℂ)-1/2) = 2 := by norm_num
  simp only [metaplecticCompletionEuler,he,primaryCoprimeZeta,metaplecticEulerAtTwo,
    Complex.ofReal_tsum]
  apply tsum_congr
  intro u
  split_ifs
  · simpa using (Complex.ofReal_cpow (norm_nonneg (u:Eisenstein)) (-2:ℝ)).symm
  · simp

end CubicFirstMoment

end

end OAI
