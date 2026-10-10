import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ExistsScaledGeometricLt
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicMellinPowerLogarithmic
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.IntegerGridSeparated
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicCoefficientSquareSum

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
open OrdinaryCorrelations SourcePrimeFactor OrdinaryDirichletMeanSquare OrdinaryChainScales
open Finset Filter MeasureTheory

theorem dyadic_gaussian_power_logarithmic :
    ∃ A c : ℕ, ∀ m : ℕ,
    ∀ {f : ℕ→ℂ}, OneBounded f → Multiplicative f → UniformlyNonpretentious f →
    ∀ {d : ℕ}, 0<d → ∀χ : DirichletCharacter ℂ d,
      ∀ᶠ X : ℕ in atTop,∀D : ℝ,
      ((16*(m+c+1)*2^(2^(29*(m+3)+A)):ℕ):ℝ)≤D →
      Integrable (fun t : ℝ=>gaussian (D*t/(2*(X:ℝ)))*‖dyadicCharacterPolynomial f χ X t‖^2) ∧
      (∫t : ℝ,gaussian (D*t/(2*(X:ℝ)))*‖dyadicCharacterPolynomial f χ X t‖^2)<(1/2:ℝ)^m := by
  obtain ⟨A,hA⟩ := dyadic_mellin_power_logarithmic
  obtain ⟨c,hc⟩ := exists_scaled_geometric_lt gaussianEnergyConstant_nonneg (by norm_num : (0:ℝ)<1/2)
  refine ⟨A,c,?_⟩
  intro m f hf hm hNP d hd χ
  let ε : ℝ := (1/2:ℝ)^m
  have hε : 0<ε := by dsimp [ε]; positivity
  let K := m+c
  have hK : gaussianEnergyConstant*(1/2:ℝ)^K<ε/2 := by
    have hh := mul_lt_mul_of_pos_right hc (by positivity : 0<(1/2:ℝ)^m)
    dsimp [K,ε]
    rw [pow_add]
    nlinarith only [hh]
  let D1 := 4*2^(2^(29*(m+3)+A))
  have hD1 : 0<D1 := by dsimp [D1]; positivity
  have hbase : ∀D : ℕ,D1≤D → ∀ᶠ X : ℕ in atTop,
    ∀S : Finset ℝ,(S : Set ℝ).Pairwise (fun t u=>1≤|t-u|) →
    (∀t∈S,|t|≤(X:ℝ)/(D:ℝ)) → (∑t∈S,‖dyadicCharacterPolynomial f χ X t‖^2)<ε/8 := by
    intro D hD
    have hh := hA (m+3) hf hm hNP hd χ D hD
    have he : (1/2:ℝ)^(m+3)=ε/8 := by dsimp [ε]; rw [pow_add]; norm_num; ring
    simpa only [he] using hh
  let D0 := 4*(K+1)*D1
  have hD0 : 0<D0 := by dsimp [D0]; positivity
  have hD0eq : D0=16*(m+c+1)*2^(2^(29*(m+3)+A)) := by dsimp [D0,D1,K]; ring
  filter_upwards [hbase D1 le_rfl,eventually_ge_atTop (1:ℕ)] with X hS hX
  intro D hDa
  have hD : (D0:ℝ)≤D := by simpa only [hD0eq] using hDa
  have hXp : 0<X := by omega
  have hXr : (0:ℝ)<X := by exact_mod_cast hXp
  have hD1r : (0:ℝ)<D1 := by exact_mod_cast hD1
  have hD01 : (1:ℝ)≤D0 := by exact_mod_cast hD0
  have hDge : 1≤D := hD01.trans hD
  have hcutD : 4*((K:ℝ)+1)*(D1:ℝ)≤D := by simpa only [D0,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hD
  let c := D/(2*(X:ℝ))
  let T := (X:ℝ)/(D1:ℝ)
  have hc : 0<c := div_pos (by linarith) (by positivity)
  have hT : 0≤T := (div_pos hXr hD1r).le
  have hcut : 2*((K:ℝ)+1)≤c*T := by
    have he : c*T=D/(2*(D1:ℝ)) := by dsimp [c,T]; field_simp
    rw [he]
    apply (le_div_iff₀ (by positivity : 0<2*(D1:ℝ))).2
    nlinarith only [hcutD]
  obtain ⟨hi,hg⟩ := dyadic_gaussian_uniform hf χ hXp hDge
  have he (t : ℝ) : D*t/(4*(X:ℝ))=c*t/2 := by dsimp [c]; ring
  simp_rw [he] at hi hg
  have hh := gaussian_split_bound (dyadicCharacterPolynomial f χ X) (dyadic_continuous f χ X)
    hc hT K hcut hi
  have hlow := OrdinaryReverseSampling.integral_le_samples
    (fun t=>‖dyadicCharacterPolynomial f χ X t‖^2)
    ((dyadic_continuous f χ X).norm.pow 2) hT (by positivity : 0≤ε/8)
    (fun S hsep hheight=>(hS S hsep hheight).le)
  have hh' := mul_le_mul_of_nonneg_left hg (pow_nonneg (by norm_num : (0:ℝ)≤1/2) K)
  have hsmall : (∫t : ℝ,gaussian (c*t)*‖dyadicCharacterPolynomial f χ X t‖^2)<ε := by
    nlinarith only [hh.2,hlow,hh',hK,hε]
  have he' (t : ℝ) : D*t/(2*(X:ℝ))=c*t := by dsimp [c]; ring
  simpa only [he'] using And.intro hh.1 hsmall

end OrdinaryMellinModulus

end

end OAI
