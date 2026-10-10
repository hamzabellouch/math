import OAI.NumberTheory.DirichletL.PrimeRows.CentralSplit
import OAI.NumberTheory.DirichletL.PrimeRows.WeightedTuple

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

def centralRowScalar (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  (star ((calibrationForSet S hmax).residueMonoid u.val)*
    (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) w*
      HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x))*
    continuedCorrection S hS η u x w z

theorem calibratedTupleValue_central {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (P : Fin K→PrimeIdeal)
    (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (a e : ℝ) (x w z : ℂ)
    (htail : FirstTail (4*e) S) (ha : (51/100:ℝ)≤a) (ha1 : a≤1)
    (he : 0<e) (he1 : e≤1/1000) (hx : x.re=a+16*e)
    (hw : w.re=1-a-6*e) (hz : z.re=17/50)
    (hQ : ∀i,(480:ℝ)≤(P i).val.absNorm)
    (hη : ∀i,IsCoprime (P i).val η.modulus)
    (hsmall : ∀i,198*((P i).val.absNorm:ℝ)^(-10*e)≤1/2) :
    calibratedTupleValue S hS hmax η u P hPS W Y x w z=
      centralRowScalar S hS hmax η u x w z*
        ∏i,W i (((P i).val.absNorm:ℝ)/Y i)*((P i).val.absNorm:ℂ)^(z-1)*
          centralNormalizedSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z := by
  have hrestore := continuedCorrection_restore (4*e) S hS htail (Finset.univ.image P)
    (tupleOutside S P hPS) η u x w z (by rw [hx];linarith) (by rw [hz])
    (by rw [hw];linarith) (by rw [hx,hw];linarith)
  rw [Finset.prod_image hP.injOn] at hrestore
  have hn : (∏i,supportedCorrection η u (P i) x w z)≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _ hz0
    have h := (central_actual_local_bounds η u (P i)
      (outside_prime_supported S hS.bad (P i) (hPS i)) (hη i) a e x w z
      (hQ i) (hsmall i) ha ha1 he he1 hx hw hz).1
    rw [hz0,norm_zero] at h
    norm_num at h
  rw [calibratedTupleValue_factor S hS hmax η u P hP hPS W Y x w z]
  unfold centralRowScalar centralNormalizedSlot
  rw [hrestore]
  simp only [Finset.prod_mul_distrib,Finset.prod_div_distrib]
  field_simp

theorem calibrated_prime_slots_separate {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (T : Fin K→Finset PrimeIdeal)
    (hPS : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (a e : ℝ) (x w z : ℂ)
    (htail : FirstTail (4*e) S) (ha : (51/100:ℝ)≤a) (ha1 : a≤1)
    (he : 0<e) (he1 : e≤1/1000) (hx : x.re=a+16*e)
    (hw : w.re=1-a-6*e) (hz : z.re=17/50)
    (hQ : ∀i P,P∈T i→(480:ℝ)≤P.val.absNorm)
    (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
    (hsmall : ∀i P,P∈T i→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) :
    (∑P:(∀i,T i),calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
      (fun i=>hPS i (P i).val (P i).property) W Y x w z)=
      centralRowScalar S hS hmax η u x w z*
        ∏i,∑P:T i,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
          centralNormalizedSlot η u P.val
            (outside_prime_supported S hS.bad P.val (hPS i P.val P.property)) x w z := by
  calc
    _ = ∑P:(∀i,T i),centralRowScalar S hS hmax η u x w z*
        ∏i,W i (((P i).val.val.absNorm:ℝ)/Y i)*((P i).val.val.absNorm:ℂ)^(z-1)*
          centralNormalizedSlot η u (P i).val
            (outside_prime_supported S hS.bad (P i).val (hPS i (P i).val (P i).property)) x w z := by
      apply Finset.sum_congr rfl
      intro P _
      exact calibratedTupleValue_central S hS hmax η u (fun i=>(P i).val) (hdis P)
        (fun i=>hPS i (P i).val (P i).property) W Y a e x w z htail ha ha1 he he1 hx hw hz
        (fun i=>hQ i (P i).val (P i).property) (fun i=>hη i (P i).val (P i).property)
        (fun i=>hsmall i (P i).val (P i).property)
    _ = _ := by
      rw [←Finset.mul_sum]
      congr 1
      exact (Fintype.prod_sum (fun i (P:T i)=>W i ((P.val.val.absNorm:ℝ)/Y i)*
        (P.val.val.absNorm:ℂ)^(z-1)*centralNormalizedSlot η u P.val
          (outside_prime_supported S hS.bad P.val (hPS i P.val P.property)) x w z)).symm

end SevenEighths.ProbeHighRowFamily
end

end OAI
