import OAI.NumberTheory.Ostmann.QuadraticSieveGaussEvaluationPeriodic

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open Complex
open scoped BigOperators

def quadraticResidueWeight (q : ℕ) [NeZero q] (a : Fin q) : ℂ :=
  ZMod.stdAddChar ((a.val : ZMod q)^2)

def inverseResidueWeight (q : ℕ) (a : Fin 4) : ℂ :=
  ZMod.stdAddChar (-(q : ZMod 4)*(a.val : ZMod 4)^2)

theorem divMod_residue_zmod (q : ℕ) [NeZero q] (n : ℤ) :
    ((Int.divModEquiv q n).2.val : ZMod q)=(n : ZMod q) := by
  have hr := (Int.divModEquiv q).symm_apply_apply n
  have hz := congrArg (fun m : ℤ => (m : ZMod q)) hr
  simpa using hz

theorem quadraticResidueWeight_int (q : ℕ) [NeZero q] (n : ℤ) :
    quadraticResidueWeight q ((Int.divModEquiv q n).2) =
      Complex.exp (2*(Real.pi : ℂ)*I*(n : ℂ)^2/(q : ℂ)) := by
  rw [quadraticResidueWeight,divMod_residue_zmod,←Int.cast_pow,ZMod.stdAddChar_coe]
  push_cast
  rfl

theorem inverseResidueWeight_int (q : ℕ) (n : ℤ) :
    inverseResidueWeight q ((Int.divModEquiv 4 n).2) =
      Complex.exp (-(Real.pi : ℂ)*I*(q : ℂ)*(n : ℂ)^2/2) := by
  rw [inverseResidueWeight,divMod_residue_zmod]
  have h : -(q : ZMod 4)*(n : ZMod 4)^2 = ((-(q : ℤ)*n^2 : ℤ) : ZMod 4) := by
    push_cast
    rfl
  rw [h,ZMod.stdAddChar_coe]
  push_cast
  congr 1
  ring

theorem stdAddChar_four_one : ZMod.stdAddChar (1 : ZMod 4)=I := by
  calc
    _ = Complex.exp (2*(Real.pi : ℂ)*I*1/4) := by
      simpa using (ZMod.stdAddChar_coe (N := 4) 1)
    _ = Complex.exp ((Real.pi : ℂ)/2*I) := by congr 1; ring
    _ = I := Complex.exp_pi_div_two_mul_I

theorem stdAddChar_four_neg_one : ZMod.stdAddChar (-1 : ZMod 4)=-I := by
  calc
    _ = Complex.exp (2*(Real.pi : ℂ)*I*(-1)/4) := by
      simpa using (ZMod.stdAddChar_coe (N := 4) (-1))
    _ = Complex.exp (-(Real.pi : ℂ)/2*I) := by congr 1; ring
    _ = -I := Complex.exp_neg_pi_div_two_mul_I

theorem inverseResidueWeight_sum_one {q : ℕ} (hq : q%4=1) :
    (∑ a : Fin 4, inverseResidueWeight q a)=2*(1-I) := by
  have hq4 : (q : ZMod 4)=1 := (ZMod.natCast_eq_natCast_iff' q 1 4).mpr (by simpa using hq)
  norm_num [inverseResidueWeight,hq4,Fin.sum_univ_succ,stdAddChar_four_neg_one,
    show (-4 : ZMod 4)=0 by decide, show (-9 : ZMod 4)=-1 by decide]
  ring

theorem inverseResidueWeight_sum_three {q : ℕ} (hq : q%4=3) :
    (∑ a : Fin 4, inverseResidueWeight q a)=2*(1+I) := by
  have hq4 : (q : ZMod 4)=3 := (ZMod.natCast_eq_natCast_iff' q 3 4).mpr (by simpa using hq)
  norm_num [inverseResidueWeight,hq4,Fin.sum_univ_succ,stdAddChar_four_one,
    show (-3 : ZMod 4)=1 by decide, show (-12 : ZMod 4)=0 by decide,
    show (-27 : ZMod 4)=1 by decide, show (4 : ZMod 4)=0 by decide,
    show (9 : ZMod 4)=1 by decide]
  simp only [show (4 : ZMod 4)=0 by decide, show (9 : ZMod 4)=1 by decide,
    AddChar.map_zero_eq_one, stdAddChar_four_one]
  ring

end Ostmann.QuadraticSieve

end

end OAI
