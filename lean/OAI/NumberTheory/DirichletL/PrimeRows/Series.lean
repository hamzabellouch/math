import OAI.NumberTheory.DirichletL.PrimeRows.Agreement
import OAI.NumberTheory.DirichletL.Hecke.Reciprocal

namespace OAI

noncomputable section
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def continuedSeries (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (rowCharacter S hS.prime u) w*
    HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x*
      continuedCorrection S hS η u x w z

theorem continuedSeries_eq_initial (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    continuedSeries S hS η u x w z=markedIdealHighSeries S 1 η u.val x w z := by
  have hx0 : x≠0 := by intro h; simp only [h,Complex.zero_re] at hx; linarith
  have hx1 : x≠1 := by intro h; simp only [h,Complex.one_re] at hx; linarith
  rw [continuedSeries,HeckeReciprocal.reciprocal_eq_inv _ hx0 hx1,
    high_L_factorization_continued S hS η u x w z hx hw hz,div_eq_mul_inv]

theorem continuedSeries_differentiableAt_x (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (7/8 : ℝ)<x.re) (hbeta : HeckeZeroSupremum.beta<x.re)
    (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    DifferentiableAt ℂ (fun x =>continuedSeries S hS η u x w z) x := by
  exact ((HeckeReciprocal.reciprocal_differentiableAt _ hbeta).const_mul _).mul
    ((continuedCorrection_analytic_x S hS η u w z hw hz) x hx).differentiableAt

theorem continuedSeries_differentiableAt_w (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)<w.re) (hz : (4/25 : ℝ)≤z.re)
    (hpole : w≠1 ∨ (rowCharacter S hS.prime u).residue≠1) :
    DifferentiableAt ℂ (fun w =>continuedSeries S hS η u x w z) w := by
  have hw0 : w≠0 := by intro h; simp only [h,Complex.zero_re] at hw; linarith
  exact (((LFunction_differentiableAt (rowCharacter S hS.prime u) hw0 hpole).const_mul _).mul_const _).mul
    ((continuedCorrection_analytic_w S hS η u x z hx hz) w hw).differentiableAt

theorem continuedSeries_differentiableAt_z (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)<z.re)
    (hpole : 6*z≠1) :
    DifferentiableAt ℂ (fun z =>continuedSeries S hS η u x w z) z := by
  have hz0 : 6*z≠0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [Complex.mul_re] at he
    linarith
  exact ((((LFunction_differentiableAt (fixedSourcePrincipal S hS.prime) hz0 (Or.inl hpole)).comp z
    (differentiableAt_id.const_mul 6)).mul_const _).mul_const _).mul
      ((continuedCorrection_analytic_z S hS η u x w hx hw) z hz).differentiableAt

end SevenEighths.ProbeHighRowFamily

end

end OAI
