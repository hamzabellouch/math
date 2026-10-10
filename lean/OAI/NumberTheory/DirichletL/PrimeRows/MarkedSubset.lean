import OAI.NumberTheory.DirichletL.PrimeRows.MarkedNormalization
import OAI.NumberTheory.DirichletL.Detector.TuplePrime

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEulerFinsupp
local notation "O" => HeckeFamily.O

theorem markedRowSeries_subset_replacement (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (T J : Finset PrimeIdeal) (hJ : J⊆T) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S (∏P∈T\J,P.val) η u x w z=
      markedIdealHighSeries (markExclusions S T) 1 η u x w z*
        (∏P∈T\J,idealRowMarkedLocalFactor η u P x w z)*
        (∏P∈J,idealRowHighLocalFactor η u P.val x w z) := by
  let A := fun P : PrimeIdeal=>if P∈T\J then idealRowMarkedLocalFactor η u P x w z else 1
  let B := fun P : PrimeIdeal=>if P∈J then idealRowHighLocalFactor η u P.val x w z else 1
  have hA : HasProd A (∏P∈T\J,idealRowMarkedLocalFactor η u P x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T\J) (f:=A)
      (L:=SummationFilter.unconditional PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [A,Finset.prod_ite_mem,Finset.inter_self] using hh
  have hB : HasProd B (∏P∈J,idealRowHighLocalFactor η u P.val x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=J) (f:=B)
      (L:=SummationFilter.unconditional PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [B,Finset.prod_ite_mem,Finset.inter_self] using hh
  have he := ((excludedIdealHighSeries_row_hasProd (markExclusions S T)
    (markExclusions_prime S hS T) η u x w z hx hw hz).mul hA).mul hB
  have heq (P : PrimeIdeal) :
      ((∑'b : HighValuation,markedIdealHighSummand (markExclusions S T) 1 η u x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))*A P)*B P=
      ∑'b : HighValuation,markedLocal (T\J) completedValuationMark
        (excludedRowPrimeTerm S η u x w z) P b := by
    rw [excludedRowHighLocalFactor _ (markExclusions_prime S hS T) η u x w z hx hw hz]
    by_cases hPJ : P∈J
    · have hPT := hJ hPJ
      have hPA : P∉T\J := by simp only [Finset.mem_sdiff]; tauto
      rw [ite_eq_left ((mem_markExclusions S T P).mpr (Or.inr hPT)),
        selectedRowLocal_outside S hS (T\J) η u P (hT P hPT) x w z hx hw hz,ite_eq_right hPA]
      simp only [A,B,ite_eq_right hPA,ite_eq_left hPJ,one_mul]
    · by_cases hPT : P∈T
      · have hPA : P∈T\J := Finset.mem_sdiff.mpr ⟨hPT,hPJ⟩
        rw [ite_eq_left ((mem_markExclusions S T P).mpr (Or.inr hPT)),
          selectedRowLocal_outside S hS (T\J) η u P (hT P hPT) x w z hx hw hz,ite_eq_left hPA]
        simp only [A,B,ite_eq_left hPA,ite_eq_right hPJ,one_mul,mul_one]
      · have hPA : P∉T\J := fun h=>hPT (Finset.mem_sdiff.mp h).1
        simp only [A,B,ite_eq_right hPA,ite_eq_right hPJ,mul_one,markedLocal,one_mul]
        change _=∑'b : HighValuation,markedIdealHighSummand S 1 η u x w z
          (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)
        rw [excludedRowHighLocalFactor S hS η u x w z hx hw hz]
        simp only [mem_markExclusions,hPT,or_false]
  apply (markedRowSeries_hasProd S hS (T\J) η u x w z hx hw hz).unique
  convert he using 1
  funext P
  exact (heq P).symm

def spectralCompensatedRow (S : Finset (Ideal O)) (T : Finset PrimeIdeal)
    (η : Character) (u : O) (x w z : ℂ) (B q : PrimeIdeal→ℂ) : ℂ :=
  ∑J∈T.powerset,(-1:ℂ)^J.card*(∏P∈J,q P)*(∏P∈T\J,B P)*
    markedIdealHighSeries S (∏P∈T\J,P.val) η u x w z

theorem spectralCompensatedRow_eq_product (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : O)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    spectralCompensatedRow S T η u x w z B q=
      markedIdealHighSeries (markExclusions S T) 1 η u x w z*
        ∏P∈T,(B P*idealRowMarkedLocalFactor η u P x w z-
          q P*idealRowHighLocalFactor η u P.val x w z) := by
  rw [spectralCompensatedRow,Finset.prod_sub,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [markedRowSeries_subset_replacement S hS T J (Finset.mem_powerset.mp hJ) hT η u x w z hx hw hz]
  simp only [Finset.prod_mul_distrib]
  ring

theorem indexedCompensatedHigh_eq_spectral {K : ℕ} (η : Character) (S : Finset (Ideal O))
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P)
    (hs : ∀i,CanonicalQuadraticSieve.Supported (P i).val) (u : O) (x w z : ℂ) :
    indexedCompensatedHigh η S (fun i=>CompletedGauss.primaryGenerator (P i).val) u x w z=
      spectralCompensatedRow S (Finset.univ.image P) η u x w z
        (fun Q=>star (idealCoeff η Q.val)*(Q.val.absNorm:ℂ)^x)
        (fun Q=>(Q.val.absNorm:ℂ)^(-w)) := by
  unfold indexedCompensatedHigh spectralCompensatedRow
  rw [Finset.powerset_image,Finset.sum_image (Finset.image_injective hP).injOn]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Finset.card_image_of_injective J hP,←Finset.image_sdiff _ _ hP]
  simp only [Finset.prod_image hP.injOn]
  have hnorm (i : Fin K) : (elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)=
      ((P i).val.absNorm:ℂ) := by
    rw [primaryTuple_norm (P i) (hs i)]
    norm_cast
  have hc (i : Fin K) : elementCoeff η (CompletedGauss.primaryGenerator (P i).val)=
      idealCoeff η (P i).val := targetMonoid_primaryGenerator η (P i).val (hs i)
  simp only [tupleIndexedCoefficient,hnorm,hc,span_tupleProduct,
    span_primaryGenerator_of_supported _ (hs _)]

end SevenEighths.ProbeHighRowFamily

end

end OAI
