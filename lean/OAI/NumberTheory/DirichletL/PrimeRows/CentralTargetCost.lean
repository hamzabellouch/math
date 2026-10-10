import OAI.NumberTheory.DirichletL.PrimeRows.CentralCosts
import OAI.NumberTheory.DirichletL.PrimeRows.CentralRowCost

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical HeckeReciprocalGrowth HeckeDeletionBounds
open ProbeRowRadicalConductor
local notation "O" => HeckeFamily.O

lemma presentationComplexity_norm_bound (χ : Character) (H : ℝ) :
    presentationComplexity χ H≤2*(χ.modulus.absNorm:ℝ)^2*(3+|H|)^2 := by
  have hd : radical χ.modulus∣χ.modulus := by
    unfold radical SmoothMobiusCorrection.primeProduct
    rw [SmoothMobiusCorrection.prod_primeSet χ.modulus (fun J : Ideal O=>J)]
    exact IdealMobiusDivisorSum.support_product_dvd χ.modulus_ne_bot (Finset.Subset.refl _)
  have hn : ((radical χ.modulus).absNorm:ℝ)≤χ.modulus.absNorm := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)) (map_dvd Ideal.absNorm hd)
  unfold presentationComplexity HeckeLogarithmic.complexity
  calc
    _ ≤ (χ.modulus.absNorm:ℝ)*(2*χ.modulus.absNorm*(3+|H|)^2) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ = _ := by ring

lemma target_complexity_norm_bound (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (H : ℝ) (hH : 0≤H) :
    presentationComplexity ((targetRow η u).excludePrimes S hS) H≤
      2*((fixedConductorConstant S:ℝ)*η.modulus.absNorm*rowNorm u)^2*(3+H)^2 := by
  have hn : (((targetRow η u).excludePrimes S hS).modulus.absNorm:ℝ)≤
      (fixedConductorConstant S:ℝ)*η.modulus.absNorm*rowNorm u := by
    unfold rowNorm
    exact_mod_cast (by simpa only [fixedConductorConstant,mul_assoc,mul_comm,mul_left_comm] using
      targetRow_excluded_conductor S hS η u)
  apply (presentationComplexity_norm_bound _ H).trans
  rw [abs_of_nonneg hH]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (by positivity) (by unfold rowNorm;positivity)).mpr hn) (by norm_num)

lemma target_complexity_power_bound (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (H eps : ℝ) (hH : 0≤H) (heps : 0≤eps) :
    (presentationComplexity ((targetRow η u).excludePrimes S hS) H)^eps≤
      (2*(fixedConductorConstant S:ℝ)^2)^eps*(η.modulus.absNorm:ℝ)^(2*eps)*
        rowNorm u^(2*eps)*(3+H)^(2*eps) := by
  have hb := Real.rpow_le_rpow (show 0≤presentationComplexity ((targetRow η u).excludePrimes S hS) H by
    unfold presentationComplexity HeckeLogarithmic.complexity;positivity)
    (target_complexity_norm_bound S hS η u H hH) heps
  apply hb.trans_eq
  rw [show 2*((fixedConductorConstant S:ℝ)*η.modulus.absNorm*rowNorm u)^2*(3+H)^2=
    (2*(fixedConductorConstant S:ℝ)^2)*(η.modulus.absNorm:ℝ)^2*rowNorm u^2*(3+H)^2 by ring]
  rw [Real.mul_rpow (by unfold rowNorm;positivity) (by positivity),
    Real.mul_rpow (by positivity) (by unfold rowNorm;positivity),Real.mul_rpow (by positivity) (by positivity)]
  rw [←Real.rpow_two (η.modulus.absNorm:ℝ),←Real.rpow_two (rowNorm u),←Real.rpow_two (3+H),
    ←Real.rpow_mul (by positivity : (0:ℝ)≤η.modulus.absNorm),
    ←Real.rpow_mul (rowNorm_ge_one u |>.trans' (by norm_num : (0:ℝ)≤1)),
    ←Real.rpow_mul (by linarith : 0≤3+H)]

theorem centralRemainingScalar_arithmetic_bound (e eps : ℝ)
    (he : 0<e) (he' : e<1/1000) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) {ι : Type*} [Fintype ι] (ψ : ι→Character)
      (B a H : ℝ) (i : ℕ),2<B → 51/100≤a → a≤1 → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |x.im|≤H →
      ‖centralRemainingScalar S hS η u x w z‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(3*eps)*(3+H)^(2*eps) := by
  obtain ⟨C,hC,hbound⟩ := centralRemainingScalar_bound e eps he he' heps
  have hF : 0<(fixedConductorConstant S:ℝ) := by exact_mod_cast fixedConductorConstant_pos S hS.prime
  refine ⟨C*(2*(fixedConductorConstant S:ℝ)^2)^eps,by positivity,?_⟩
  intro η u ι _ ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  have hh : 0≤H := (abs_nonneg _).trans hxi
  have hb := hbound S hS hfirst η u ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  apply hb.trans
  have hc := target_complexity_power_bound S hS.prime η u H eps hh heps.le
  have hn : 0<rowNorm u := zero_lt_one.trans_le (rowNorm_ge_one u)
  calc
    _ ≤ C*rowNorm u^eps*((2*(fixedConductorConstant S:ℝ)^2)^eps*(η.modulus.absNorm:ℝ)^(2*eps)*
        rowNorm u^(2*eps)*(3+H)^(2*eps)) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by
      rw [show 3*eps=eps+2*eps by ring,Real.rpow_add hn]
      ring

theorem central_remaining_rowCost_bound (e eps : ℝ)
    (he : 0<e) (he' : e<1/1000) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) {ι : Type*} [Fintype ι] (ψ : ι→Character)
      (B a H : ℝ) (i : ℕ),2<B → 51/100≤a → a≤1 → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |x.im|≤H →
      ‖centralRemainingScalar S hS η u x w z‖*ProbeCentralRepeatedProduct.rowCost S hS.prime u a e eps H≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+7*eps)*(3+H)^(2+4*eps) := by
  obtain ⟨C0,hC0,h0⟩ := centralRemainingScalar_arithmetic_bound e eps he he' heps S hS hfirst
  obtain ⟨C1,hC1,h1⟩ := central_rowCost_bound S hS.prime e eps he heps
  refine ⟨C0*C1,mul_pos hC0 hC1,?_⟩
  intro η u ι _ ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  have hh : 0≤H := (abs_nonneg _).trans hxi
  have hn : 0<rowNorm u := zero_lt_one.trans_le (rowNorm_ge_one u)
  have hL : 0<3+H := by linarith
  have h0' := h0 η u ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  have h1' := h1 u a H ha ha1 hh
  apply (mul_le_mul h0' h1' (ProbeCentralRepeatedProduct.rowCost_nonneg S hS.prime u a e eps H)
    (by positivity)).trans_eq
  have hnp : rowNorm u^(3*eps)*rowNorm u^(a-1/2+12*e+4*eps)=
      rowNorm u^(a-1/2+12*e+7*eps) := by rw [←Real.rpow_add hn];congr 1;ring
  have hlp : (3+H)^(2*eps)*(3+H)^(2+2*eps)=(3+H)^(2+4*eps) := by
    rw [←Real.rpow_add hL];congr 1;ring
  calc
    _ = C0*C1*(η.modulus.absNorm:ℝ)^(2*eps)*
        (rowNorm u^(3*eps)*rowNorm u^(a-1/2+12*e+4*eps))*
        ((3+H)^(2*eps)*(3+H)^(2+2*eps)) := by ring
    _ = _ := by rw [hnp,hlp]

end SevenEighths.ProbeHighRowFamily

end

end OAI
