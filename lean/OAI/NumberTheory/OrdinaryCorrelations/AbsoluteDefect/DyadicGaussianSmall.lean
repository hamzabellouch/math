import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ExistsScaledGeometricLt
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

namespace OrdinaryChainScales
open OrdinaryCorrelations SourcePrimeFactor OrdinaryDirichletMeanSquare
open Finset Filter MeasureTheory

theorem dyadic_gaussian_small {f : ℕ→ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {d : ℕ} (hd : 0<d) (χ : DirichletCharacter ℂ d) {ε : ℝ} (hε : 0<ε) :
    ∃D0 : ℕ,0<D0 ∧ ∀ᶠ X : ℕ in atTop,∀D : ℝ,(D0:ℝ)≤D →
      Integrable (fun t : ℝ=>gaussian (D*t/(2*(X:ℝ)))*‖dyadicCharacterPolynomial f χ X t‖^2) ∧
      (∫t : ℝ,gaussian (D*t/(2*(X:ℝ)))*‖dyadicCharacterPolynomial f χ X t‖^2)<ε := by
  obtain ⟨K,hK⟩ := exists_scaled_geometric_lt gaussianEnergyConstant_nonneg (by positivity : 0<ε/2)
  obtain ⟨D1,hD1,hbase⟩ := dyadic_mellin_small hf hm hNP hd χ (by positivity : 0<ε/8)
  let D0 := 4*(K+1)*D1
  have hD0 : 0<D0 := by dsimp [D0]; positivity
  refine ⟨D0,hD0,?_⟩
  filter_upwards [hbase D1 le_rfl,eventually_ge_atTop (1:ℕ)] with X hS hX
  intro D hD
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

end OrdinaryChainScales

end

end OAI
