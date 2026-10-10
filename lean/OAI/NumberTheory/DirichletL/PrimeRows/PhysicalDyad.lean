import OAI.NumberTheory.DirichletL.PrimeRows.SourceTransport
import OAI.NumberTheory.DirichletL.PrimeRows.SmallDyad

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def finitePhysicalRows {K : ℕ} (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset PrimeIdeal)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ∑u∈R,∑P:(∀i,T i),(∏i,W i (((P i).val.val.absNorm:ℝ)/Yp i))*
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val.val) W0 W1 X Y Z u

def weightedRowOnLines {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) (t : HeightSpace) : ℂ :=
  sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*
    frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩*
    calibratedTupleValue S hS hmax η u P hPS W Yp
      ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)

lemma weightedRowOnLines_eq {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) (t : HeightSpace) :
    weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z σ υ r t=
      (∏i,W i (((P i).val.absNorm:ℝ)/Yp i))*
        continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r t := by
  have hnorm (i : Fin K) : (elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)=
      ((P i).val.absNorm:ℂ) := by
    rw [primaryTuple_norm (P i) (outside_prime_supported S hS.bad (P i) (hPS i))]
    norm_cast
  unfold weightedRowOnLines continuedRowOnLines continuedPhysicalRowKernel calibratedTupleValue
  simp only [hnorm,Finset.prod_mul_distrib]
  ring

section
variable {K : ℕ} (e σ υ r : ℝ) (he : 0<e) (he' : e<1/1000)
    (hσ : (7/8:ℝ)≤σ) (hσβ : HeckeZeroSupremum.beta+8*e≤σ) (hσ3 : σ≤3)
    (hυ : (1/2:ℝ)≤υ) (hυ3 : υ≤3) (hr : (17/50:ℝ)≤r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (η : Character) (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)

include he he' hσ hσβ hσ3 hυ hυ3 hr hfirst hR hdis ha0 ha1 hW0 hW1 hX hY hZ in
theorem finitePhysicalRows_eq_integral :
    Integrable (fun t : HeightSpace=>∑u∈R,∑P:(∀i,T i),
      weightedRowOnLines S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
        η u W Yp W0 W1 X Y Z σ υ r t) heightMeasure ∧
    finitePhysicalRows S hmax η R T W Yp W0 W1 X Y Z=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫t : HeightSpace,(∑u∈R,∑P:(∀i,T i),
          weightedRowOnLines S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
            η u W Yp W0 W1 X Y Z σ υ r t) ∂heightMeasure := by
  let f (u : FreeRow) (P : ∀i,T i) := weightedRowOnLines S hS hmax
    (fun i=>(P i).val) (fun i=>hT i _ (P i).property) η u W Yp W0 W1 X Y Z σ υ r
  have hsource (u : FreeRow) (hu : u∈R) (P : ∀i,T i) := rowIntegral_source_lines e σ υ r he he' hσ hσβ hσ3 hυ hυ3 hr
    S hS hmax hfirst (fun i=>(P i).val) (hdis P) (fun i=>hT i _ (P i).property) η u (hR u hu)
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  have hfi (u : FreeRow) (hu : u∈R) (P : ∀i,T i) : Integrable (f u P) heightMeasure := by
    have heq : f u P=(fun t=>(∏i,W i (((P i).val.val.absNorm:ℝ)/Yp i))*
        continuedRowOnLines S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
          η u W0 W1 X Y Z σ υ r t) := by
      funext t
      exact weightedRowOnLines_eq S hS hmax _ _ η u W Yp W0 W1 X Y Z σ υ r t
    rw [heq]
    exact (hsource u hu P).1.const_mul _
  have hiu (u : FreeRow) (hu : u∈R) : Integrable (fun t=>∑P:(∀i,T i),f u P t) heightMeasure :=
    integrable_finsetSum _ (fun P hP=>hfi u hu P)
  have hi : Integrable (fun t=>∑u∈R,∑P:(∀i,T i),f u P t) heightMeasure :=
    integrable_finsetSum _ hiu
  refine ⟨hi,?_⟩
  change finitePhysicalRows S hmax η R T W Yp W0 W1 X Y Z=_*(∫t,∑u∈R,∑P:(∀i,T i),f u P t ∂heightMeasure)
  rw [integral_finsetSum R hiu]
  unfold finitePhysicalRows
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [integral_finsetSum Finset.univ (fun P hP=>hfi u hu P),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  rw [(hsource u hu P).2]
  have hi' : (∫t,f u P t ∂heightMeasure)=
      (∏i,W i (((P i).val.val.absNorm:ℝ)/Yp i))*
        ∫t,continuedRowOnLines S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
          η u W0 W1 X Y Z σ υ r t ∂heightMeasure := by
    simp_rw [f,weightedRowOnLines_eq]
    exact integral_const_mul _ _
  rw [hi']
  ring

include he he' hσ hσβ hσ3 hυ hυ3 hr hfirst hR hdis ha0 ha1 hW0 hW1 hX hY hZ in
theorem norm_finitePhysicalRows_le_absolute :
    ‖finitePhysicalRows S hmax η R T W Yp W0 W1 X Y Z‖≤
      ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*
        absolutePhysicalDyadIntegral S hS hmax η R T hT W Yp W0 W1 X Y Z σ υ r := by
  let f (u : FreeRow) (P : ∀i,T i) := weightedRowOnLines S hS hmax
    (fun i=>(P i).val) (fun i=>hT i _ (P i).property) η u W Yp W0 W1 X Y Z σ υ r
  have hfi (u : FreeRow) (hu : u∈R) (P : ∀i,T i) : Integrable (f u P) heightMeasure := by
    have hi := continuedPhysicalRowKernel_integrable e σ υ r he he' hσ hσβ hυ hr S hS hmax hfirst
      (fun i=>(P i).val) (hdis P) (fun i=>hT i _ (P i).property) η u (hR u hu)
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
    have heq : f u P=(fun t=>(∏i,W i (((P i).val.val.absNorm:ℝ)/Yp i))*
        continuedRowOnLines S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
          η u W0 W1 X Y Z σ υ r t) := by
      funext t
      exact weightedRowOnLines_eq S hS hmax _ _ η u W Yp W0 W1 X Y Z σ υ r t
    rw [heq]
    exact hi.const_mul _
  let g (t : HeightSpace) := ‖sourceMellinWeight W0 W1 X Y Z
      ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)‖*
    physicalDyadNorm S hS hmax η R T hT W Yp
      ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
  have hg (t : HeightSpace) : (∑u∈R,∑P:(∀i,T i),‖f u P t‖)=g t := by
    simp only [f,g,weightedRowOnLines,physicalDyadNorm,norm_mul,Finset.mul_sum,mul_assoc]
  have hgi : Integrable g heightMeasure := by
    have hh : Integrable (fun t=>∑u∈R,∑P:(∀i,T i),‖f u P t‖) heightMeasure :=
      integrable_finsetSum R (fun u hu=>integrable_finsetSum Finset.univ (fun P hP=>(hfi u hu P).norm))
    exact hh.congr (Filter.Eventually.of_forall hg)
  obtain ⟨hi,heq⟩ := finitePhysicalRows_eq_integral e σ υ r he he' hσ hσβ hσ3 hυ hυ3 hr S hS hmax
    hfirst η R hR T hT hdis W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  have hp (t : HeightSpace) : ‖∑u∈R,∑P:(∀i,T i),f u P t‖≤g t := by
    rw [←hg]
    apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum (fun u hu=>norm_sum_le _ _)
  rw [heq,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (norm_integral_le_integral_norm _).trans (integral_mono hi.norm hgi hp)

end
end SevenEighths.ProbeHighRowFamily

end

end OAI
