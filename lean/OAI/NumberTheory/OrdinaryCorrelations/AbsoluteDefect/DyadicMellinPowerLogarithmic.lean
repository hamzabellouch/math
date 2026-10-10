import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicMellinExplicitParameters
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.QuadraticGeometricLimit

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction

namespace OrdinaryMellinModulus
open OrdinaryCorrelations SourcePrimeFactor OrdinaryNarrowGrid OrdinaryDirichletMeanSquare
open OrdinaryFrequencyChain OrdinaryChainScales Finset Filter

theorem dyadic_mellin_power_logarithmic :
    ∃ A : ℕ, ∀ m : ℕ,
    ∀ {f : ℕ→ℂ}, OneBounded f → Multiplicative f → UniformlyNonpretentious f →
    ∀ {d : ℕ}, 0<d → ∀χ : DirichletCharacter ℂ d,
    ∀ D : ℕ, 4*2^(2^(29*m+A))≤D →
      ∀ᶠ X : ℕ in atTop,∀S : Finset ℝ,
        (S : Set ℝ).Pairwise (fun t u=>1≤|t-u|) →
        (∀t∈S,|t|≤(X:ℝ)/(D:ℝ)) →
        (∑t∈S,‖dyadicCharacterPolynomial f χ X t‖^2)<(1/2:ℝ)^m := by
  classical
  obtain ⟨C,CT,hC,hCT,hParam⟩ := dyadic_mellin_explicit_parameters
  obtain ⟨c,hcC,hcP,hcRate⟩ := choose_initial_offset C CT (firstSampleConstant+2)
  have hpow := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)
  obtain ⟨k0,hkCoeff,hkTrans⟩ := ((hpow.eventually_ge_atTop
    (64*10816*(1+momentCoefficient))).and (hpow.eventually_ge_atTop
    (transitionConstant+Real.exp 1+10))).exists
  refine ⟨13*c+k0+134,?_⟩
  intro m f hf hm hNP d hd χ D hD
  let s := m+c
  let M := m+c
  let J := 2^(3*m+c)
  let r := 16*(576*J^2+96*J+4)
  let H := 6*m+2*c+20
  let Kr := 6*m+2*c+22
  let K := 6*m+2*c+k0
  let B := 28*m+12*c+k0+134
  have hJ : 0<J := by dsimp [J]; positivity
  have hR : r≤10816*J^2 := OrdinarySparseShell.polynomial_exponent_bound J hJ
  have hH : 16*(4*r)≤2^H := by
    calc
      _ = 64*r := by ring
      _ ≤ 64*(10816*J^2) := Nat.mul_le_mul_left 64 hR
      _ ≤ 2^20*J^2 := by
        rw [←Nat.mul_assoc]
        exact Nat.mul_le_mul_right (J^2) (by norm_num)
      _ = _ := by
        change 2^20*(2^(3*m+c))^2=2^(6*m+2*c+20)
        rw [←pow_mul,←pow_add]
        congr 1
        ring
  have hKr : 64*(4*r)≤2^Kr := by
    calc
      _ = 256*r := by ring
      _ ≤ 256*(10816*J^2) := Nat.mul_le_mul_left 256 hR
      _ ≤ 2^22*J^2 := by
        rw [←Nat.mul_assoc]
        exact Nat.mul_le_mul_right (J^2) (by norm_num)
      _ = _ := by
        change 2^22*(2^(3*m+c))^2=2^(6*m+2*c+22)
        rw [←pow_mul,←pow_add]
        congr 1
        ring
  have hRr : (r:ℝ)≤10816*(J:ℝ)^2 := by exact_mod_cast hR
  have hcoeff : 0≤1+momentCoefficient := by have := momentCoefficient_nonneg; linarith
  have hKterm : 16*((4*r:ℕ):ℝ)*(1+momentCoefficient)≤(2:ℝ)^K := by
    calc
      _ = 64*(r:ℝ)*(1+momentCoefficient) := by push_cast; ring
      _ ≤ 64*(10816*(J:ℝ)^2)*(1+momentCoefficient) := by gcongr
      _ = (64*10816*(1+momentCoefficient))*(J:ℝ)^2 := by ring
      _ ≤ (2:ℝ)^k0*(J:ℝ)^2 := mul_le_mul_of_nonneg_right hkCoeff (sq_nonneg _)
      _ = _ := by
        dsimp [J,K]
        push_cast
        rw [←pow_mul,←pow_add]
        congr 1
        ring
  have hKtrans : transitionConstant+Real.exp 1+10≤(2:ℝ)^K := by
    apply hkTrans.trans
    exact pow_le_pow_right₀ (by norm_num) (by dsimp [K]; omega)
  have hs0 : 6*C*(1/2:ℝ)^c<1/4 := by
    rw [one_div_pow,mul_one_div]
    apply (div_lt_iff₀ (by positivity : 0<(2:ℝ)^c)).mpr
    linarith only [hcC]
  have hM0 : 2*(firstSampleConstant+2)*(1/2:ℝ)^c<1/4 := by
    rw [one_div_pow,mul_one_div]
    apply (div_lt_iff₀ (by positivity : 0<(2:ℝ)^c)).mpr
    linarith only [hcP]
  have hs : 6*C*(1/2:ℝ)^s<(1/2:ℝ)^m/4 := by
    have hh := mul_lt_mul_of_pos_right hs0 (by positivity : 0<(1/2:ℝ)^m)
    dsimp [s]
    rw [pow_add]
    nlinarith only [hh]
  have hM : 2*(firstSampleConstant+2)*(1/2:ℝ)^M<(1/2:ℝ)^m/4 := by
    have hh := mul_lt_mul_of_pos_right hM0 (by positivity : 0<(1/2:ℝ)^m)
    dsimp [M]
    rw [pow_add]
    nlinarith only [hh]
  have hRate : 2120/(J:ℝ)≤((1/2:ℝ)^m/8)/(1+(CT+(s:ℝ)*Real.log 2)^2) :=
    powered_rate CT hCT c m hcRate
  have hF : F B s 0 = 2^(29*m+(13*c+k0+134)) := by
    dsimp [F,B,s]
    congr 1
    ring
  have hD0 : 4*2^(F B s 0)≤D := by
    calc
      _ = 4*2^(2^(29*m+(13*c+k0+134))) := congrArg (fun v : ℕ=>4*2^v) hF
      _ ≤ D := hD
  exact hParam (by positivity : 0<(1/2:ℝ)^m) s J M H Kr K B hJ hs hRate hM
    hH hKr hKterm hKtrans (by dsimp [H,s,Kr,K,B]; omega)
    (by dsimp [H,s,B]; omega) (by dsimp [H,s,B]; omega)
    (by dsimp [H,M,B]; omega) hf hm hNP hd χ D hD0

end OrdinaryMellinModulus

end

end OAI
