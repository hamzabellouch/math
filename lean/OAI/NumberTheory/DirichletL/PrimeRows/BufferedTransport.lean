import OAI.NumberTheory.DirichletL.PrimeRows.BufferedIntegral
import OAI.NumberTheory.DirichletL.PrimeRows.FirstTransport

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma height_slab_integral_wzx (f : HeightSpace→ℂ) (H : ℝ) (hH : 0≤H)
    (hf : IntegrableOn f {t : HeightSpace | |t.1.1|≤H} heightMeasure) :
    (∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤H},f p ∂heightMeasure)=
      ∫w : ℝ,∫z : ℝ,∫x : ℝ in -H..H,f ((x,z),w) := by
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  have hi : Integrable (E.indicator f) heightMeasure := (integrable_indicator_iff hE).mpr hf
  rw [←integral_indicator hE,integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_left_ae] with w hw
  rw [integral_prod_symm _ hw]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  have heq : (fun x : ℝ=>(E.indicator f) ((x,z),w))=(Icc (-H) H).indicator (fun x=>f ((x,z),w)) := by
    funext x
    simp only [Set.indicator_apply,E,Set.mem_ofPred_eq,Set.mem_Icc,abs_le]
  dsimp only
  rw [heq,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by linarith)]

variable {ι : Type*} [Fintype ι]

theorem rowIntegral_buffered_transport {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH0 : 0≤H) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀j,(P j).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    let F := fun x w z=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z
    let E : Set HeightSpace := {t | |t.1.1|≤H}
    rowIntegral η S (calibrationForSet S hmax)
      (fun j=>CompletedGauss.primaryGenerator (P j).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3 *
        ((∫tw : ℝ,∫tz : ℝ,
          (∫tx : ℝ in -H..H,F ((((a+16*e):ℝ):ℂ)+tx*I) ((((1-a-6*e):ℝ):ℂ)+tw*I) ((17/50:ℂ)+tz*I))+
          I*((∫v : ℝ in (a+16*e)..2,F ((v:ℂ)+(-H)*I) ((((1-a-6*e):ℝ):ℂ)+tw*I) ((17/50:ℂ)+tz*I))-
            (∫v : ℝ in (a+16*e)..2,F ((v:ℂ)+H*I) ((((1-a-6*e):ℝ):ℂ)+tw*I) ((17/50:ℂ)+tz*I))))+
          ∫p : HeightSpace in Eᶜ,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 (1-a-6*e) (17/50) p ∂heightMeasure) := by
  dsimp only
  obtain ⟨hi,hrow⟩ := rowIntegral_central_start a e ha haTop he he' S hS hmax hfirst P hP hPS η u hu
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  rw [hrow,←integral_add_compl hE hi]
  congr 2
  rw [height_slab_integral_wzx _ H hH0 hi.integrableOn]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tw
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tz
  have hHT : H≤3*(i+1:ℕ)*B := by
    apply hH.trans
    have hn : (3*i+2:ℕ)≤3*(i+1) := by omega
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (by linarith)
  simpa only [continuedRowOnLines,Complex.ofReal_div,Complex.ofReal_ofNat] using source_buffered_x_rectangle S hS hmax P hPS η u ψ B a e i he he' ha haTop hfirst hbin W0 W1 X Y Z hZ
    ((((1-a-6*e):ℝ):ℂ)+tw*I) ((17/50:ℂ)+tz*I) (by simp) (by norm_num) 2 H (by linarith) hH0 hHT

end SevenEighths.ProbeHighRowFamily

end

end OAI
