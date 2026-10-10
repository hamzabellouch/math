import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.WeightedRoughTwistCorrelation
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Cutoff
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.FourierMass

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
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff

namespace OrdinaryAnalyticCutoff
open OrdinaryCorrelations SourceRoughFourier OrdinaryTwistWidth Finset Filter

theorem smooth_rough_correlation (h : ℕ) (hh : 0<h) (phi : ℝ→ℝ)
    (hφ : ContDiff ℝ ∞ phi) (hφc : HasCompactSupport phi)
    (hφb : ∀x, 0≤phi x ∧ phi x≤1) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ B : ℝ in atTop,
    ∀ τ : ℝ, 1<τ → τ<2 → ∀ M : ℝ, Real.exp (B^(9999/10000:ℝ))/τ≤M →
    ∀ Z : Finset ℕ,
    (∀ z∈Z, M<z ∧ (z:ℝ)≤τ*M ∧ IsRough (Real.exp (B^(9999/10000:ℝ))) z) →
    ∀ f g : ℕ→ℂ, OneBounded f → OneBounded g → Multiplicative f → Multiplicative g →
    (UniformlyNonpretentious f ∨ UniformlyNonpretentious g) →
    ∀ P : Finset ℕ, (∀p∈P,Nat.Prime p) →
    ∀ c : ℕ→ℂ, (∀z∈Z,‖c z‖≤1) →
    ∀ᶠ X : ℝ in atTop, ∀ mu : ℝ,
      ‖∑v∈Finset.Icc 1 ⌊X⌋₊,∑z∈Z,(c z/(z:ℂ))*f v*g (v+h*z)*
         cutoff phi P mu v*cutoff phi P mu (v+h*z)‖
        ≤ C*B^(-10001/10000:ℝ)*X := by
  let ψ : SchwartzMap ℝ ℂ :=
    (hφc.comp_left (g:=Complex.ofRealCLM) (by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hφ)
  have hψ (x:ℝ) : ψ x=(phi x:ℂ) := rfl
  obtain ⟨C,hC,hMain⟩ := OrdinaryRoughTarget.weighted_rough_twist_correlation h hh
  have hφ0 : 0≤phi 0 := (hφb 0).1
  refine ⟨C*(1+phi 0+fourierMass ψ^2),by positivity,?_⟩
  filter_upwards [hMain,eventually_ge_atTop (1:ℝ)] with B hB hB1
  intro τ hτ1 hτ2 M hM Z hZ f g hf hg hfm hgm hNP P hP c hc
  have hτ0 : 0<τ := by linarith
  have hM0 : 0<M := lt_of_lt_of_le (div_pos (Real.exp_pos _) hτ0) hM
  let D : ℕ := ⌈M⌉₊
  have hMD : M≤(D:ℝ) := Nat.le_ceil M
  have hD : (1/2:ℝ)*Real.exp (B^(9999/10000:ℝ))≤D := by
    have he := (div_le_iff₀ hτ0).mp hM
    nlinarith
  have hZ' (z:ℕ) (hz:z∈Z) : D≤z ∧ z<2*D ∧
      IsRough (Real.exp (B^(199979/200000:ℝ))) z := by
    obtain ⟨hz1,hz2,hzr⟩ := hZ z hz
    refine ⟨Nat.ceil_le.mpr hz1.le,?_,?_⟩
    · have hz' : (z:ℝ)<2*D := by nlinarith
      exact_mod_cast hz'
    · intro p hp hpB
      exact hzr p hp (hpB.trans (Real.exp_le_exp.mpr
        (Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num))))
  have he := hB D hD Z hZ' f g hf hg hfm hgm hNP P hP c hc
  filter_upwards [tendsto_nat_floor_atTop.eventually he,eventually_ge_atTop (0:ℝ)] with X hX hX0
  intro mu
  have hb := bilinear_cutoff_bound ((Finset.Icc 1 ⌊X⌋₊)×ˢZ)
    (fun i : ℕ×ℕ=>(c i.2/(i.2:ℂ))*f i.1*g (i.1+h*i.2))
    (fun i : ℕ×ℕ=>(primeCount P i.1:ℝ))
    (fun i : ℕ×ℕ=>(primeCount P (i.1+h*i.2):ℝ)) ψ mu
    (C*B^(-10001/10000:ℝ)*(⌊X⌋₊:ℝ)) (fun s t=>by
      simpa only [sum_product,twist,mul_assoc,mul_left_comm,mul_comm] using hX s t)
  have hb' : ‖∑v∈Finset.Icc 1 ⌊X⌋₊,∑z∈Z,(c z/(z:ℂ))*f v*g (v+h*z)*
         cutoff phi P mu v*cutoff phi P mu (v+h*z)‖
      ≤fourierMass ψ^2*(C*B^(-10001/10000:ℝ)*(⌊X⌋₊:ℝ)) := by
    simpa only [sum_product,hψ,cutoff] using hb
  apply hb'.trans
  have hpow : 0≤B^(-10001/10000:ℝ) := Real.rpow_nonneg (by linarith) _
  calc
    _ ≤fourierMass ψ^2*(C*B^(-10001/10000:ℝ)*X) := by
      gcongr
      exact Nat.floor_le hX0
    _ ≤(C*(1+phi 0+fourierMass ψ^2))*B^(-10001/10000:ℝ)*X := by
      nlinarith [mul_nonneg (show 0≤1+phi 0 by positivity)
        (mul_nonneg (mul_nonneg hC.le hpow) hX0)]
end OrdinaryAnalyticCutoff

end

end OAI
