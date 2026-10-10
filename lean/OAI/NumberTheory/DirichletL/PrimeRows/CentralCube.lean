import OAI.NumberTheory.DirichletL.PrimeRows.CentralRectangle
import OAI.NumberTheory.DirichletL.PrimeRows.CentralZTail

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

def centralCubeIntegral {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫p : HeightSpace in {t : HeightSpace | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H},
      continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50) p ∂heightMeasure

theorem central_rectangle_z_cutoff_error (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → 0≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖centralRectangleIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H-
        centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
        C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(a+16*e+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C,hC,hbound⟩ := uniform_central_z_height_tail (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N (17/50) le_rfl (by norm_num)
  let n : ℂ := ((1/(2*Real.pi):ℝ):ℂ)^3
  refine ⟨‖n‖*C,mul_nonneg (norm_nonneg _) hC,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  let E : Set HeightSpace := {t | |t.1.1|≤H ∧ |t.2|≤H}
  let T : Set HeightSpace := {t | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}
  let R : Set HeightSpace := {t | (|t.1.1|≤H ∧ |t.2|≤H) ∧ H < |t.1.2|}
  let f := continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50)
  have hE : MeasurableSet E := (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.1.1|) by fun_prop) measurable_const).inter
    (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.2|) by fun_prop) measurable_const)
  have hT : MeasurableSet T := hE.inter (measurableSet_le (show Measurable (fun t : HeightSpace => |t.1.2|) by fun_prop) measurable_const)
  have hi0 : IntegrableOn f {t : HeightSpace | |t.1.1|≤H} heightMeasure := continuedPhysicalRowKernel_buffered_integrable e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
    (a+16*e) (17/50) le_rfl (by linarith) le_rfl
  have hi : IntegrableOn f E heightMeasure := hi0.mono_set (fun t ht=>ht.1)
  have hdiff : E\T=R := by
    ext t
    change ((|t.1.1|≤H ∧ |t.2|≤H) ∧ ¬((|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H)) ↔ ((|t.1.1|≤H ∧ |t.2|≤H) ∧ H < |t.1.2|)
    constructor
    · rintro ⟨hx,hw⟩
      exact ⟨hx,lt_of_not_ge (fun h=>hw ⟨hx,h⟩)⟩
    · rintro ⟨hx,hw⟩
      exact ⟨hx,fun h=>not_le_of_gt hw h.2⟩
  have heq : centralRectangleIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H-
        centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H=
      n*(∫t in R,f t ∂heightMeasure) := by
    rw [← hdiff,setIntegral_sdiff hT hi (fun t ht=>ht.1)]
    dsimp [centralRectangleIntegral,centralCubeIntegral,n,E,T,f]
    ring
  have htail : (∫t in R,‖f t‖ ∂heightMeasure)≤
      C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(a+16*e+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
    apply le_trans _ (hbound η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
      (a+16*e) ⟨le_rfl,by linarith⟩)
    apply setIntegral_mono_set ((show IntegrableOn (fun t=>‖f t‖) {t : HeightSpace | |t.1.1|≤H} heightMeasure from hi0.norm).mono_set (fun t ht=>ht.1)) (Filter.Eventually.of_forall (fun _=>norm_nonneg _))
    exact Filter.Eventually.of_forall (fun t ht=>⟨ht.1.1,ht.2⟩)
  rw [heq,norm_mul]
  calc
    _ ≤ ‖n‖*(∫t in R,‖f t‖ ∂heightMeasure) := mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ ≤ ‖n‖*(C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(a+16*e+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N) :=
      mul_le_mul_of_nonneg_left htail (norm_nonneg _)
    _ = _ := by ring

theorem uniform_original_row_cube_error (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0<X → 0<Y → 1≤Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → 0≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val) W0 W1 X Y Z u-
        centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
        C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C0,hC0,h0⟩ := uniform_original_row_rectangle_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  obtain ⟨C1,hC1,h1⟩ := central_rectangle_z_cutoff_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C0+C1,add_nonneg hC0 hC1,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have h0' := h0 η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have h1' := h1 η u hu P hP hPS ψ X Y Z hX hY (by linarith) a B H i ha haTop hB hH0 hH hbin
  have hcost := contourArithmeticCost_nonneg η u P
  have hz : Z^(a+16*e+(17/50:ℝ)-1)≤Z^(2+(17/50:ℝ)-1) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h1'' : ‖centralRectangleIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H-
      centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
      C1*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
    apply h1'.trans
    gcongr
    exact pow_nonneg (height_pos _).le _
  apply (norm_sub_le_norm_sub_add_norm_sub _ (centralRectangleIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H) _).trans
  exact (add_le_add h0' h1'').trans_eq (by ring)

end SevenEighths.ProbeHighRowFamily

end

end OAI
