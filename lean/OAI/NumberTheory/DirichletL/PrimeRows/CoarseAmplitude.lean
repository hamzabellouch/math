import OAI.NumberTheory.DirichletL.PrimeRows.CoarsePhysical
import OAI.NumberTheory.DirichletL.PrimeRows.BufferedIntegral

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma coarsePrimeCost_image {K : ℕ} (P : Fin K→PrimeIdeal) (hP : Function.Injective P) :
    coarsePrimeCost (Finset.univ.image P)=(8192:ℝ)^K*(∏i,(P i).val.absNorm:ℝ)^3 := by
  unfold coarsePrimeCost
  rw [Finset.prod_image (by intro a ha b hb hab;exact hP hab)]
  rw [Finset.prod_mul_distrib,←Finset.prod_pow]
  simp

lemma prime_frequency_amplitude_le_one {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (P : Fin K→PrimeIdeal)
    (hPS : ∀i,(P i).val∉S) (u : FreeRow) (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (t : ℝ) :
    ‖(∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(((r:ℂ)+t*I)-1))*
      frequencyWeight ((r:ℂ)+t*I) ⟨u.val,u.property.1⟩‖≤1 := by
  have hp (i : Fin K) : 1≤elementNorm (CompletedGauss.primaryGenerator (P i).val) := by
    unfold elementNorm
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (by simpa only [Ideal.span_singleton_eq_bot] using
        (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero))
  have hu : 1≤elementNorm u.val := by
    unfold elementNorm
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (by simpa only [Ideal.span_singleton_eq_bot] using u.property.1))
  rw [norm_mul,norm_prod]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans ?_
  · apply Finset.prod_le_one₀ (fun _ _=>norm_nonneg _)
    intro i hi
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hp i])]
    simp only [sub_re,add_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,mul_zero,zero_mul,sub_zero,add_zero,one_re]
    simpa using Real.rpow_le_rpow_of_exponent_le (hp i) (by linarith : r-1≤0)
  · unfold frequencyWeight
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0<elementNorm u.val)]
    simp only [neg_re,add_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
    simpa using Real.rpow_le_rpow_of_exponent_le hu (by linarith : -r≤0)

def contourArithmeticCost {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→PrimeIdeal) : ℝ :=
  (η.modulus.absNorm:ℝ)^2*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^6*(∏i,(P i).val.absNorm:ℝ)^3

lemma contourArithmeticCost_nonneg {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→PrimeIdeal) :
    0≤contourArithmeticCost η u P := by unfold contourArithmeticCost;positivity

theorem rowAmplitudeOnLines_buffered_polynomial (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀σ∈Icc (a+16*e) 2,∀r∈Icc (17/50:ℝ) 1,∀t : HeightSpace,|t.1.1|≤H →
      ‖rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r t‖≤
        C*contourArithmeticCost η u P*(3+|H|)^2*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_buffered_polynomial_growth (ι:=ι) e he he' S hS hfirst hmax
  refine ⟨C*(8192:ℝ)^K,by positivity,?_⟩
  intro η u hu P hP hPS ψ a B H i ha haTop hB hH hbin σ hσ r hr t ht
  have hw := prime_frequency_amplitude_le_one S hS P hPS u r (by linarith [hr.1]) hr.2 t.1.2
  have hb := hbound η u hu (Finset.univ.image P) (contourTupleOutside S P hPS) ψ a B H i ha haTop hB hH hbin
    ((σ:ℂ)+t.1.1*I) ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simpa using hσ.1) (by simpa using hσ.2) (by simpa using ht) (by simp) (by simpa using hr.1)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hb
  unfold rowAmplitudeOnLines
  rw [norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) hw).trans
  apply hb.trans_eq
  rw [coarsePrimeCost_image P hP]
  unfold contourArithmeticCost
  ring

theorem rowAmplitudeOnLines_first_polynomial (K : ℕ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (1/4) S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀υ : ℝ,-(1/100:ℝ)≤υ → ∀r∈Icc (17/50:ℝ) 1,∀t : HeightSpace,
      ‖rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r t‖≤
        C*contourArithmeticCost η u P*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_first_joint_polynomial_growth S hS hfirst hmax
  refine ⟨C*(8192:ℝ)^K,by positivity,?_⟩
  intro η u hu P hP hPS υ hυ r hr t
  have hw := prime_frequency_amplitude_le_one S hS P hPS u r (by linarith [hr.1]) hr.2 t.1.2
  have hb := hbound η u hu (Finset.univ.image P) (contourTupleOutside S P hPS)
    ((2:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simp) (by simpa using hυ) (by simpa using hr.1)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hb
  have hN : (1:ℝ)≤(Ideal.span {u.val}:Ideal O).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (by simpa only [Ideal.span_singleton_eq_bot] using u.property.1))
  have hη := HeckeLogarithmicInput.modulus_norm_ge_one η
  have hN46 : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^4≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^6 :=
    pow_le_pow_right₀ hN (by norm_num)
  have hη2 : (1:ℝ)≤(η.modulus.absNorm:ℝ)^2 := by nlinarith
  have hlarge : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^4≤
      (η.modulus.absNorm:ℝ)^2*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^6 :=
    hN46.trans (le_mul_of_one_le_left (by positivity) hη2)
  unfold rowAmplitudeOnLines
  rw [norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) hw).trans
  apply hb.trans
  rw [coarsePrimeCost_image P hP]
  unfold contourArithmeticCost
  calc
    _ = (C*(8192:ℝ)^K)*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^4*(∏i,(P i).val.absNorm:ℝ)^3*(3+|t.2|)^2 := by ring
    _ ≤ (C*(8192:ℝ)^K)*((η.modulus.absNorm:ℝ)^2*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^6)*
        (∏i,(P i).val.absNorm:ℝ)^3*(3+|t.2|)^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlarge (mul_nonneg hC (pow_nonneg (by norm_num) _)))
        (pow_nonneg (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg (P i).val.absNorm)) _)) (sq_nonneg _)
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
