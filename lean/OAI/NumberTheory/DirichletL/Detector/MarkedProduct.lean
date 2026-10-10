import OAI.NumberTheory.DirichletL.Detector.MarkedLocal
import OAI.NumberTheory.DirichletL.Detector.SourceExclusions

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeEuler ProbeEulerFinsupp
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma source_idealHighLocalFactor_ne_zero (S : Finset Id) (hS : SourceExclusions S)
    (η : HeckeFamily.Character) (P : PrimeIdeal) (hP : P.val∉S) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    idealHighLocalFactor η P.val x w z≠0 := by
  rw [idealHighLocalFactor_rational η P (outside_prime_supported S hS.bad P hP) x w z hx hw hz]
  have hQ : (1:ℝ)<Ideal.absNorm P.val := by
    have hh := hS.tail.norm_four P hP
    exact_mod_cast (by omega : 1<Ideal.absNorm P.val)
  have hQ0 : (0:ℝ)<Ideal.absNorm P.val := by linarith
  have hD : ‖HeckeFamily.idealCoeff η P.val*(Ideal.absNorm P.val:ℂ)^(-x)‖<1 := by
    rw [norm_mul,Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hQ0),Complex.neg_re]
    apply (mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) (HeckeFamily.idealCoeff_norm_le_one η P.val)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  have hV : ‖(Ideal.absNorm P.val:ℂ)^(-6*z)‖<1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hQ0)]
    apply Real.rpow_lt_one_of_one_lt_of_neg hQ
    norm_num [Complex.mul_re]
    linarith
  have hW : ‖(Ideal.absNorm P.val:ℂ)^(-w)‖<1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hQ0),Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  apply mul_ne_zero
  · exact div_ne_zero (one_sub_ne_zero_of_norm_lt_one _ hD)
      (mul_ne_zero (one_sub_ne_zero_of_norm_lt_one _ hV) (one_sub_ne_zero_of_norm_lt_one _ hW))
  · exact factor_ne_zero_of_defect _ ((idealClosedCorrection_bound η P (hS.tail.norm_four P hP)
      x w z (by linarith) (by linarith) (by linarith)).trans (hS.tail.half ⟨P,hP⟩))

theorem markedIdealHighSeries_eq_product (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η 1 x w z=
      markedIdealHighSeries S 1 η 1 x w z *
        ∏P∈T,idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z := by
  let R := fun P : PrimeIdeal=>if P∈T then
    idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z else 1
  have hR : HasProd R (∏P∈T,idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T) (f:=R) (L:=SummationFilter.unconditional PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [R,Finset.prod_ite_mem,Finset.inter_self] using hh
  have he := (excludedIdealHighSeries_hasProd S hS.prime η x w z hx hw hz).mul hR
  have heq (P : PrimeIdeal) :
      (∑'b : HighValuation,excludedHighPrimeTerm S η x w z P b)*R P=
      ∑'b : HighValuation,markedLocal T completedValuationMark (excludedHighPrimeTerm S η x w z) P b := by
    by_cases hp : P∈T
    · rw [selectedLocal_outside S hS.prime T η P (hT P hp) x w z hx hw hz,ite_eq_left hp]
      have hu : (∑'b : HighValuation,excludedHighPrimeTerm S η x w z P b)=idealHighLocalFactor η P.val x w z := by
        simpa only [excludedHighPrimeTerm,excludedHighArray,ite_eq_right (hT P hp)] using
          excludedHighLocalFactor S hS.prime η x w z hx hw hz P
      rw [hu,show R P=idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z from ite_eq_left hp]
      exact mul_div_cancel₀ _ (source_idealHighLocalFactor_ne_zero S hS η P (hT P hp) x w z hx hw hz)
    · simp only [R,hp,ite_false,mul_one,markedLocal,one_mul]
  have he' : HasProd (fun P : PrimeIdeal=>∑'b : HighValuation,
      markedLocal T completedValuationMark (excludedHighPrimeTerm S η x w z) P b)
      (markedIdealHighSeries S 1 η 1 x w z *
        ∏P∈T,idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z) := by
    convert he using 1
    funext P
    exact (heq P).symm
  exact (markedIdealHighSeries_hasProd S hS.prime T η x w z hx hw hz).unique he'

theorem source_markedHigh_L_factorization (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η 1 x w z=
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
       HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
       HeckeFamily.LFunction (η.excludePrimes S hS.prime) x * globalClosedCorrection η S x w z) *
        ∏P∈T,idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z := by
  rw [markedIdealHighSeries_eq_product S hS T hT η x w z hx hw hz,
    source_principalHigh_L_factorization S hS η x w z hx hw hz]

end SevenEighths.ProbePhysical
end

end OAI
