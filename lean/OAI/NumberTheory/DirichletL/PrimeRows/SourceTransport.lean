import OAI.NumberTheory.DirichletL.PrimeRows.WZTransport
import OAI.NumberTheory.DirichletL.PrimeRows.XShift

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

private lemma height_integral_wzx (f : HeightSpace→ℂ) (hf : Integrable f heightMeasure) :
    (∫p : HeightSpace,f p ∂heightMeasure)=∫w : ℝ,∫z : ℝ,∫x : ℝ,f ((x,z),w) := by
  rw [integral_prod_symm _ hf]
  apply integral_congr_ae
  filter_upwards [hf.prod_left_ae] with w hw
  exact integral_prod_symm _ hw

theorem continuedRowOnLines_x_transport {K : ℕ}
    (e l r υ ξ : ℝ) (he : 0<e) (he' : e<1/1000)
    (hl : (7/8:ℝ)≤l) (hlβ : HeckeZeroSupremum.beta+8*e≤l) (hlr : l≤r)
    (hυ : (1/2:ℝ)≤υ) (hξ : (17/50:ℝ)≤ξ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    (∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z l υ ξ p ∂heightMeasure)=
      ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z r υ ξ p ∂heightMeasure := by
  have hi (q : ℝ) (hq : l≤q) :
      Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z q υ ξ) heightMeasure :=
    continuedPhysicalRowKernel_integrable e q υ ξ he he' (hl.trans hq) (hlβ.trans hq) hυ hξ
      S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  rw [height_integral_wzx _ (hi l le_rfl),height_integral_wzx _ (hi r hlr)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tw
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tz
  exact first_x_integral_eq e (1/4) he he' (by norm_num) S hS
    (hfirst.of_ge_one_fiftieth (by norm_num)) hmax P hPS η u W0 W1 X Y Z hZ
    ((υ:ℂ)+tw*I) ((ξ:ℂ)+tz*I) l r hlr (by linarith) hlβ
    (by simp;linarith) (by simpa using hξ) (by simp;linarith)

theorem rowIntegral_source_lines {K : ℕ}
    (e σ υ r : ℝ) (he : 0<e) (he' : e<1/1000)
    (hσ : (7/8:ℝ)≤σ) (hσβ : HeckeZeroSupremum.beta+8*e≤σ) (hσ3 : σ≤3)
    (hυ : (1/2:ℝ)≤υ) (hυ3 : υ≤3) (hr : (17/50:ℝ)≤r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r) heightMeasure ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r p ∂heightMeasure := by
  have hi := continuedPhysicalRowKernel_integrable e σ υ r he he' hσ hσβ hυ hr
    S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  obtain ⟨_,hphysical⟩ := rowIntegral_wz_transport S hS hmax hfirst P hP hPS η u hu W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ υ 2 hυ hυ3 (by norm_num) le_rfl
  have hβ3 : HeckeZeroSupremum.beta+8*e≤3 := hσβ.trans hσ3
  have hz : (∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ r p ∂heightMeasure)=
      ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ 2 p ∂heightMeasure := by
    by_cases hr2 : r≤2
    · exact continuedRowOnLines_z_transport e 3 υ r 2 he he' (by norm_num) hβ3 hυ hr hr2
        S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
    · exact (continuedRowOnLines_z_transport e 3 υ 2 r he he' (by norm_num) hβ3 hυ (by norm_num) (le_of_not_ge hr2)
        S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ).symm
  have hx := continuedRowOnLines_x_transport e σ 3 υ r he he' hσ hσβ hσ3 hυ hr
    S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  exact ⟨hi,hphysical.trans (by rw [hx,hz])⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI
