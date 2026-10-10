import OAI.NumberTheory.DirichletL.Detector.HighRowsExcluded

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def rowHighPrimeTerm (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (P : PrimeIdeal) (b : HighValuation) : ℂ :=
  bareIdealHighSummand η u x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)

def idealRowHighLocalFactor (η : HeckeFamily.Character) (u : O) (P : Id) (x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l : ℕ, ∑' k : ℕ, ∑' m : ℕ,
    bareIdealHighSummand η u x w z (P^e.val) (P^l) (P^k) (P^m)

lemma rowHighPrimeTerm_summable_norm (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal) :
    Summable (fun b : HighValuation=>‖rowHighPrimeTerm η u x w z P b‖) := by
  have hs := ((bareIdealHighSummand_summable η u x w z hx hw hz).norm.comp_injective
    highIdeals_injective).comp_injective (Finsupp.single_injective P)
  simpa only [Function.comp_def,highIdeals_single,rowHighPrimeTerm] using hs

lemma rowHighPrimeTerm_zero_of_two_le (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (P : PrimeIdeal) (e l k m : ℕ) (he : 2≤e) :
    rowHighPrimeTerm η u x w z P ((e,l),(k,m))=0 := by
  by_contra hn
  have hs := bareIdealHighSummand_support η u x w z (P.val^e) (P.val^l) (P.val^k) (P.val^m) hn
  have hc := hs.1.eq_zero_or_one_of_pow_of_not_isUnit P.property.not_isUnit
  omega

theorem rowHighPrimeTerm_tsum_eq_localFactor (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal) :
    (∑' b : HighValuation,rowHighPrimeTerm η u x w z P b)=
      idealRowHighLocalFactor η u P.val x w z := by
  have hs := (rowHighPrimeTerm_summable_norm η u x w z hx hw hz P).of_norm
  rw [hs.tsum_prod,hs.prod.tsum_prod]
  have he (e l : ℕ) :
      (∑' b : ℕ×ℕ, rowHighPrimeTerm η u x w z P ((e,l),b))=
        ∑' k,∑' m,rowHighPrimeTerm η u x w z P ((e,l),(k,m)) :=
    (hs.prod_factor (e,l)).tsum_prod
  simp_rw [he]
  rw [tsum_eq_sum (s:=Finset.range 2) (fun e he=>by
    have hh : 2≤e := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using he)
    simp only [rowHighPrimeTerm_zero_of_two_le η u x w z P e _ _ _ hh,tsum_zero]),
    ←Fin.sum_univ_eq_sum_range]
  rfl

theorem bareIdealHighSeries_row_hasProd_localFactor (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>idealRowHighLocalFactor η u P.val x w z)
      (bareIdealHighSeries η u x w z) := by
  have h := bareIdealHighSeries_row_hasProd η u x w z hx hw hz
  change HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,rowHighPrimeTerm η u x w z P b) _ at h
  simpa only [rowHighPrimeTerm_tsum_eq_localFactor η u x w z hx hw hz] using h

theorem excludedRowHighLocalFactor (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal) :
    (∑' b : HighValuation,markedIdealHighSummand S 1 η u x w z
      (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)) =
      if P.val∈S then 1 else idealRowHighLocalFactor η u P.val x w z := by
  by_cases hP : P.val∈S
  · rw [ite_eq_left hP]
    have he (b : HighValuation) : markedIdealHighSummand S 1 η u x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)=if b=0 then 1 else 0 := by
      rw [markedIdealHighSummand,highIdealMask_prime_inside S hS P hP b]
      by_cases hb : b=0
      · subst b
        simp only [Prod.fst_zero,Prod.snd_zero,pow_zero,bareIdealHighSummand_row_one,mul_one]
      · simp only [ite_eq_right hb,zero_mul]
    simp only [he,tsum_ite_eq]
  · rw [ite_eq_right hP]
    simp only [markedIdealHighSummand,highIdealMask_prime_outside S hS P hP,one_mul]
    exact rowHighPrimeTerm_tsum_eq_localFactor η u x w z hx hw hz P

theorem excludedIdealHighSeries_row_hasProd_outside (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>idealRowHighLocalFactor η u P.val.val x w z)
      (markedIdealHighSeries S 1 η u x w z) := by
  have h := excludedIdealHighSeries_row_hasProd S hS η u x w z hx hw hz
  simp only [excludedRowHighLocalFactor S hS η u x w z hx hw hz] at h
  apply (hasProd_subtype_iff_mulIndicator
    (s:={P : PrimeIdeal | P.val∉S})
    (f:=fun P : PrimeIdeal=>idealRowHighLocalFactor η u P.val x w z)).mpr
  convert h using 1
  funext P
  simp only [Set.mulIndicator,Set.mem_ofPred_eq]
  split_ifs <;> simp_all

end SevenEighths.ProbePhysical
end

end OAI
