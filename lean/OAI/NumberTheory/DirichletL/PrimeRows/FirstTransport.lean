import OAI.NumberTheory.DirichletL.PrimeRows.FirstIntegral
import OAI.NumberTheory.DirichletL.PrimeRows.SourceTransport
import OAI.NumberTheory.DirichletL.PrimeRows.FirstWShift

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma FirstTail.mono_parameter {eps eps' : ℝ} {S : Finset (Ideal O)}
    (h : FirstTail eps S) (hle : eps≤eps') : FirstTail eps' S := by
  have hp : 0<eps' := h.positive.trans_le hle
  refine ⟨hp,h.norm_four,?_⟩
  apply le_trans _ h.small
  apply ((firstPrimeDefectBound_summable eps' hp).subtype _).tsum_le_tsum _ h.summable
  intro P
  unfold firstPrimeDefectBound
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le
  · have hn := h.norm_four P.val P.property
    exact_mod_cast (by omega : 1≤P.val.val.absNorm)
  · have hm := min_le_min_right (1/50:ℝ) hle
    linarith

theorem continuedRowOnLines_first_w_transport {K : ℕ}
    (l r ξ : ℝ) (hl : -(1/100:ℝ)≤l) (hlr : l≤r) (hξ : (17/50:ℝ)≤ξ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    (∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 l ξ p ∂heightMeasure)=
      ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 r ξ p ∂heightMeasure := by
  have hi (q : ℝ) (hq : -(1/100:ℝ)≤q) :
      Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 q ξ) heightMeasure :=
    continuedPhysicalRowKernel_first_integrable q ξ hq hξ S hS hmax hfirst P hPS η u hu W0 W1
      a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  rw [integral_prod _ (hi l hl),integral_prod _ (hi r (hl.trans hlr))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  exact nonprincipal_first_w_integral_eq (1/2) (by norm_num) S hS (by norm_num;exact hfirst) hmax P hPS η u hu
    W0 W1 a1 b1 ha1 hW1 X Y Z hY ((2:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I) l r hlr
    (by norm_num) hl (by simpa using hξ) (by norm_num;linarith)

theorem rowIntegral_first_w_lines {K : ℕ}
    (υ r : ℝ) (hυ : -(1/100:ℝ)≤υ) (hυ3 : υ≤3) (hr : (17/50:ℝ)≤r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r) heightMeasure ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r p ∂heightMeasure := by
  have hβ : HeckeZeroSupremum.beta+8*(1/2000:ℝ)≤2 := by linarith [HeckeZeroSupremum.beta_le_one]
  obtain ⟨_,hphysical⟩ := rowIntegral_source_lines (1/2000) 2 3 r (by norm_num) (by norm_num)
    (by norm_num) hβ (by norm_num) (by norm_num) le_rfl hr S hS hmax hfirst P hP hPS η u hu W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  have hw := continuedRowOnLines_first_w_transport υ 3 r hυ hυ3 hr S hS hmax hfirst P hPS η u hu W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  exact ⟨continuedPhysicalRowKernel_first_integrable υ r hυ hr S hS hmax hfirst P hPS η u hu W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ,hphysical.trans (by rw [hw])⟩

theorem rowIntegral_central_start {K : ℕ}
    (a e : ℝ) (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 (1-a-6*e) (17/50)) heightMeasure ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 (1-a-6*e) (17/50) p ∂heightMeasure :=
  rowIntegral_first_w_lines (1-a-6*e) (17/50) (by linarith) (by linarith) le_rfl
    S hS hmax (hfirst.mono_parameter (by linarith)) P hP hPS η u hu W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ

end SevenEighths.ProbeHighRowFamily

end

end OAI
