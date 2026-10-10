import OAI.NumberTheory.DirichletL.PrimeRows.ExhaustivePartition
import OAI.NumberTheory.DirichletL.Detector.CanonicalPhysicalRows

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CompletedGauss CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

def physicalRowValue {K : ℕ} (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (T : Fin K→Finset PrimeIdeal) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (u : FreeRow) : ℂ :=
  ∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
    rowIntegral η S (calibrationForSet S hmax) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u

theorem physicalRowValue_summable {K : ℕ} (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Summable (physicalRowValue S hmax η T W Yp W0 W1 X Y Z) := by
  have hs (P : ∀i,T i) : Summable (fun u : FreeRow=>
      (∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        rowIntegral η S (calibrationForSet S hmax) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u) :=
    (rowIntegral_summable η S _ _ (fun i=>supported_primaryGenerator_ne_zero _ (hT i _ (P i).property))
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ).mul_left _
  have hh (F : Finset (∀i,T i)) : Summable (fun u : FreeRow=>∑P∈F,
      (∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        rowIntegral η S (calibrationForSet S hmax) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u) := by
    induction F using Finset.induction_on with
    | empty => simp
    | @insert P F hP ih => simpa only [Finset.sum_insert hP] using (hs P).add ih
  exact hh Finset.univ

theorem canonical_physical_probe_partition {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z L U : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (hL : 1≤L) (hLU : L≤U) :
    compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
      (fun i=>canonicalSlotSupport (T i)) W Yp X Y Z=
      (∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z)+
      ((∑n∈smallDyadicIndices L,finitePhysicalRows S hmax η (smallDyadicRows L n) T W Yp W0 W1 X Y Z)+
        finitePhysicalRows S hmax η (rowBand L U) T W Yp W0 W1 X Y Z+
        (∑'n : ℕ,finitePhysicalRows S hmax η (dyadicRows U n) T W Yp W0 W1 X Y Z)) := by
  let f := physicalRowValue S hmax η T W Yp W0 W1 X Y Z
  have hf := physicalRowValue_summable S hmax η T hT W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  rw [compensatedPhysicalProbe_eq_canonical_rows η S hmax hS.prime hS.bad ((by simp [fixedBadPrimes] : fixedBadPrimes.Nonempty).mono hS.bad) T hT W Yp
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
  change (∑'u,f u)=_
  rw [hf.tsum_eq_add_tsum_ite principalFreeRow]
  have heq : (fun u : FreeRow=>if u=principalFreeRow then 0 else f u)=
      (fun u : FreeRow=>if u.val=1 then 0 else f u) := by
    funext u
    have hu : u=principalFreeRow ↔ u.val=1 := by
      constructor
      · intro h;subst u;rfl
      · intro h;exact Subtype.ext h
    simp only [hu]
  rw [heq,nonprincipal_rows_partition L U hL hLU f hf]
  congr 1
  · dsimp [f,physicalRowValue]
    simp only [rowIntegral_principal]

end SevenEighths.ProbeHighRowFamily

end

end OAI
