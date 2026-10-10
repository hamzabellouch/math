import OAI.NumberTheory.DirichletL.PrimeRows.ZShift
import OAI.NumberTheory.DirichletL.PrimeRows.FixedIntegral
import OAI.NumberTheory.DirichletL.PrimeRows.IteratedShift

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma FirstTail.of_ge_one_fiftieth {S : Finset (Ideal O)} (h : FirstTail (1/4) S)
    {eps : ℝ} (heps : (1/50:ℝ)≤eps) : FirstTail eps S := by
  refine ⟨by linarith,h.norm_four,?_⟩
  simpa only [firstPrimeDefectBound,min_eq_right heps,
    min_eq_right (by norm_num : (1/50:ℝ)≤1/4)] using h.small

private lemma height_integral_wxz (f : HeightSpace→ℂ) (hf : Integrable f heightMeasure) :
    (∫p : HeightSpace,f p ∂heightMeasure)=∫w : ℝ,∫x : ℝ,∫z : ℝ,f ((x,z),w) := by
  rw [integral_prod_symm _ hf]
  apply integral_congr_ae
  filter_upwards [hf.prod_left_ae] with w hw
  exact integral_prod _ hw

def continuedRowOnLines {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z σ υ r : ℝ) (t : HeightSpace) : ℂ :=
  continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
    ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)

theorem continuedRowOnLines_z_transport {K : ℕ}
    (e σ υ l r : ℝ) (he : 0<e) (he' : e<1/1000)
    (hσ : (7/8:ℝ)≤σ) (hσβ : HeckeZeroSupremum.beta+8*e≤σ)
    (hυ : (1/2:ℝ)≤υ) (hl : (17/50:ℝ)≤l) (hlr : l≤r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    (∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ l p ∂heightMeasure)=
      ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r p ∂heightMeasure := by
  have hi (q : ℝ) (hq : (17/50:ℝ)≤q) :
      Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ q) heightMeasure :=
    continuedPhysicalRowKernel_integrable e σ υ q he he' hσ hσβ hυ hq S hS hmax hfirst P hP hPS η u hu
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  rw [height_integral_wxz _ (hi l hl),height_integral_wxz _ (hi r (hl.trans hlr))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tw
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tx
  exact first_z_integral_eq (1/4) (by norm_num) S hS
    (hfirst.of_ge_one_fiftieth (by norm_num)) hmax P hPS η u W0 W1 a0 b0 ha0 hW0
    X Y Z hX hZ ((σ:ℂ)+tx*I) ((υ:ℂ)+tw*I) l r hlr
    (by simp;linarith) (by simp;linarith) (by simp;linarith) hl

theorem rowIntegral_wz_transport {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (υ r : ℝ) (hυ : (1/2:ℝ)≤υ) (hυ3 : υ≤3) (hr : (17/50:ℝ)≤r) (hr2 : r≤2) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ r) heightMeasure ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ r p ∂heightMeasure := by
  have hβ : HeckeZeroSupremum.beta+8*(1/2000:ℝ)≤3 := by linarith [HeckeZeroSupremum.beta_le_one]
  have hi (q : ℝ) (hq : (17/50:ℝ)≤q) :
      Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ q) heightMeasure :=
    continuedPhysicalRowKernel_integrable (1/2000) 3 υ q (by norm_num) (by norm_num) (by norm_num) hβ hυ hq
      S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  obtain ⟨_,hphysical⟩ := rowIntegral_w_shift (1/2) (by norm_num) (by norm_num) S hS (by norm_num;exact hfirst) hmax P hP hPS
    η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ υ hυ hυ3
  have hinner : (∫q : ℝ×ℝ,shiftedRowInner S hS hmax P hPS η u W0 W1 X Y Z υ q ∂(volume.prod volume))=
      ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ 2 p ∂heightMeasure :=
    (integral_prod _ (hi 2 (by norm_num))).symm
  have hz := continuedRowOnLines_z_transport (1/2000) 3 υ r 2 (by norm_num) (by norm_num)
    (by norm_num) hβ hυ hr hr2 S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ
  exact ⟨hi r hr,hphysical.trans (by rw [hinner,hz])⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI
