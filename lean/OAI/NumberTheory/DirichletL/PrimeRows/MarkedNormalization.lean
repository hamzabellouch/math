import OAI.NumberTheory.DirichletL.PrimeRows.MarkedProduct

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEulerFinsupp CanonicalRowCompletion
local notation "O" => HeckeFamily.O

def localNormalization (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  (1-CubicEisenstein.fullIdealWeight (6*z) P.val)*
    (1-idealRowHom u.val P.val*CubicEisenstein.fullIdealWeight w P.val)/
    (1-idealCoeff η P.val*starRingEnd ℂ (idealRowHom u.val P.val)*CubicEisenstein.fullIdealWeight x P.val)

def markedLocalCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  idealRowMarkedLocalFactor η u.val P x w z*localNormalization η u P x w z

theorem localCorrection_eq_normalization (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) :
    localCorrection η u P x w z=idealRowHighLocalFactor η u.val P.val x w z*
      localNormalization η u P x w z := by
  unfold localCorrection localNormalization
  ring

lemma lift_outside_hasProd (S : Finset (Ideal O)) (f : PrimeIdeal→ℂ) (a : ℂ)
    (h : HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>f P.val) a) :
    HasProd (fun P : PrimeIdeal=>if P.val∈S then 1 else f P) a := by
  have hh := (hasProd_subtype_iff_mulIndicator (s:={P : PrimeIdeal | P.val∉S}) (f:=f)).mp h
  convert hh using 1
  funext P
  simp only [Set.mulIndicator,Set.mem_ofPred_eq]
  split_ifs <;> simp_all

theorem localNormalization_hasProd (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 1<x.re) (hw : 1<w.re) (hz : 1<(6*z).re) :
    HasProd (fun P : PrimeIdeal=>if P.val∈S then 1 else localNormalization η u P x w z)
      ((LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹*
        (LFunction (rowCharacter S hS u) w)⁻¹*LFunction ((targetRow η u).excludePrimes S hS) x) := by
  apply lift_outside_hasProd
  have hZ := (fixedSourcePrincipal_hasProd S hS (6*z) hz).inv₀
    (LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz)
  have hW := (rowCharacter_hasProd S hS hbad u w hw).inv₀
    (LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw)
  have hD := targetRow_hasProd S hS hbad η u x hx
  simpa only [localNormalization,inv_inv,div_eq_mul_inv] using (hZ.mul hW).mul hD

theorem markedRowSeries_normalized (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η u.val x w z*
      ((LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹*
        (LFunction (rowCharacter S hS u) w)⁻¹*LFunction ((targetRow η u).excludePrimes S hS) x)=
      globalCorrection (markExclusions S T) η u x w z*
        ∏P∈T,markedLocalCorrection η u P x w z := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re];linarith
  have hleft := (markedRowSeries_hasProd S hS T η u.val x w z hx hw hz).mul
    (localNormalization_hasProd S hS hbad η u x w z hx1 hw1 hz1)
  have hbase := lift_outside_hasProd (markExclusions S T) (fun P=>localCorrection η u P x w z) _
    (globalCorrection_multipliable (markExclusions S T) (markExclusions_prime S hS T)
      (hbad.trans Finset.subset_union_left) η u x w z hx hw hz).hasProd
  let R := fun P : PrimeIdeal=>if P∈T then markedLocalCorrection η u P x w z else 1
  have hR : HasProd R (∏P∈T,markedLocalCorrection η u P x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T) (f:=R)
      (L:=SummationFilter.unconditional PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [R,Finset.prod_ite_mem,Finset.inter_self] using hh
  have heq (P : PrimeIdeal) :
      (∑'b : HighValuation,markedLocal T completedValuationMark (excludedRowPrimeTerm S η u.val x w z) P b)*
        (if P.val∈S then 1 else localNormalization η u P x w z)=
      (if P.val∈markExclusions S T then 1 else localCorrection η u P x w z)*R P := by
    by_cases hP : P∈T
    · rw [selectedRowLocal_outside S hS T η u.val P (hT P hP) x w z hx hw hz,
        ite_eq_left hP,ite_eq_right (hT P hP),ite_eq_left ((mem_markExclusions S T P).mpr (Or.inr hP))]
      simp only [R,ite_eq_left hP,one_mul,markedLocalCorrection]
    · simp only [markedLocal,ite_eq_right hP,one_mul,R,mul_one]
      change (∑'b : HighValuation,markedIdealHighSummand S 1 η u.val x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))*_=_
      rw [excludedRowHighLocalFactor S hS η u.val x w z hx hw hz]
      simp only [mem_markExclusions,hP,or_false]
      by_cases hPS : P.val∈S
      · simp only [ite_eq_left hPS,one_mul]
      · simp only [ite_eq_right hPS,localCorrection_eq_normalization]
  have hright := hbase.mul hR
  apply hleft.unique
  convert hright using 1
  · funext P
    exact heq P
  · rfl

theorem markedRowSeries_original_L_factorization (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η u.val x w z=
      (LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (rowCharacter S hS u) w/
        LFunction ((targetRow η u).excludePrimes S hS) x)*
      (globalCorrection (markExclusions S T) η u x w z*
        ∏P∈T,markedLocalCorrection η u P x w z) := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re];linarith
  have hZ := LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz1
  have hW := LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw1
  have hD := LFunction_ne_zero_of_one_lt_re ((targetRow η u).excludePrimes S hS) hx1
  rw [←markedRowSeries_normalized S hS hbad T hT η u x w z hx hw hz]
  field_simp

end SevenEighths.ProbeHighRowFamily

end

end OAI
