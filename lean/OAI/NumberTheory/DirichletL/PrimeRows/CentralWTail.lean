import OAI.NumberTheory.DirichletL.PrimeRows.UniformError

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem uniform_central_w_height_tail (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) (r : ℝ) (hr : (17/50:ℝ)≤r) (hr1 : r≤1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → 0≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀σ∈Icc (a+16*e) 2,
      (∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤H ∧ H < |t.2|},
        ‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r p‖ ∂heightMeasure)≤
        C*contourArithmeticCost η u P*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨A0,hA0,hrow0⟩ := rowAmplitudeOnLines_buffered_polynomial (ι:=ι) K e he he' S hS hfirst hmax
  obtain ⟨D,hD,hprofile⟩ := source_profile_arithmetic_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (51/100) 2 r r (-(1/100)) (1/2) (by linarith) 2 (N+2)
  refine ⟨81*A0*D,by positivity,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin σ hσ
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  let R : Set HeightSpace := {t | |t.1.1|≤H ∧ H < |t.2|}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  have hR : MeasurableSet R := hE.inter (measurableSet_lt measurable_const (show Measurable (fun t : HeightSpace => |t.2|) by fun_prop))
  let A := A0*contourArithmeticCost η u P
  have hA : 0≤A := mul_nonneg hA0 (contourArithmeticCost_nonneg η u P)
  let G := E.indicator (rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r)
  have hG : Measurable G := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).indicator hE
  have hb (t : HeightSpace) : ‖G t‖≤(9*A*(3+|H|)^2)*jointHeight t.1.1 t.1.2 t.2^2 := by
    by_cases ht : t∈E
    · rw [show G t=rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r t by exact Set.indicator_of_mem ht _]
      have hh : 3+|t.2|≤3*jointHeight t.1.1 t.1.2 t.2 := by
        unfold jointHeight
        linarith [abs_nonneg t.1.1,abs_nonneg t.1.2,abs_nonneg t.2]
      apply (hrow0 η u hu P hP hPS ψ a B H i ha haTop hB hH hbin σ hσ r ⟨hr,hr1⟩ t ht).trans
      calc
        _ ≤ (A*(3+|H|)^2)*(3*jointHeight t.1.1 t.1.2 t.2)^2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hh 2) (by positivity)
        _ = _ := by ring
    · simp only [G,Set.indicator_of_notMem ht,norm_zero]
      positivity
  let F := fun t : HeightSpace=>sourceMellinWeight W0 W1 X Y Z
    ((σ:ℂ)+t.1.1*I) ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*G t
  have hp := hprofile σ ⟨by linarith [hσ.1],hσ.2⟩ r ⟨le_rfl,le_rfl⟩ (1-a-6*e)
    ⟨by linarith,by linarith⟩ (9*A*(3+|H|)^2) (by positivity)
    X Y Z hX hY hZ G hG.aestronglyMeasurable hb
  have hFR (t : HeightSpace) (ht : t∈R) : F t=continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r t := by
    dsimp only [F,G]
    rw [Set.indicator_of_mem (show t∈E from ht.1),continuedRowOnLines_eq_amplitude]
  have hb' : (∫t in R,‖F t‖ ∂heightMeasure)≤
      (9*A*(3+|H|)^2)*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/(1+H)^(N+2) := by
    apply le_trans _ (hp.2 H hH0)
    apply setIntegral_mono_set hp.1.norm.integrableOn (Filter.Eventually.of_forall (fun _=>norm_nonneg _))
    exact Filter.Eventually.of_forall (fun t ht=>Or.inr (Or.inr ht.2))
  have heq : (∫t in R,‖F t‖ ∂heightMeasure)=
      ∫t in R,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r t‖ ∂heightMeasure :=
    setIntegral_congr_fun hR (fun t ht=>congrArg norm (hFR t ht))
  rw [heq] at hb'
  apply hb'.trans
  have hpow : (3+|H|)^2≤9*(height H)^2 := by
    have hh : 3+|H|≤3*height H := by unfold height;linarith [abs_nonneg H]
    have hh' := pow_le_pow_left₀ (by positivity) hh 2
    norm_num [mul_pow] at hh'
    exact hh'
  have hheight : 1+H=height H := by simp [height,abs_of_nonneg hH0]
  have hden : 0<height H := height_pos H
  rw [hheight]
  calc
    _ ≤ (9*A*(9*height H^2))*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^(N+2) := by
      gcongr
    _ = _ := by dsimp [A];rw [pow_add];field_simp;ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
