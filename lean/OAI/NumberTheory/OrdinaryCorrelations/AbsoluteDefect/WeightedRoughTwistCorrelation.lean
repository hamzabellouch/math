import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.EventualSourceLarge
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.EnergyComplexLe
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.EventualShortTwists
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ExponentBudget

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

namespace OrdinaryRoughTarget
open OrdinaryCorrelations SourceRoughFourier OrdinaryTwistWidth Finset Filter

theorem weighted_rough_twist_correlation (h : ℕ) (hh : 0<h) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ B : ℝ in atTop,
    ∀ D : ℕ, (1/2:ℝ)*Real.exp (B^(9999/10000:ℝ))≤D →
    ∀ Z : Finset ℕ,
    (∀ z∈Z, D≤z ∧ z<2*D ∧ IsRough (Real.exp (B^(199979/200000:ℝ))) z) →
    ∀ f g : ℕ→ℂ, OneBounded f → OneBounded g → Multiplicative f → Multiplicative g →
    (UniformlyNonpretentious f ∨ UniformlyNonpretentious g) →
    ∀ P : Finset ℕ, (∀p∈P,Nat.Prime p) →
    ∀ c : ℕ→ℂ, (∀z∈Z,‖c z‖≤1) →
    ∀ᶠ U : ℕ in atTop, ∀s t : ℝ,
      ‖∑v∈Icc 1 U,∑z∈Z,(c z/(z:ℂ))*twist f P s v*twist g P t (v+h*z)‖
        ≤ C*B^(-10001/10000:ℝ)*U := by
  obtain ⟨C₁,hC₁,hMass⟩ := OrdinaryRoughEnergy.eventual_real_mass
  obtain ⟨C₄,hC₄,hEnergy⟩ := OrdinaryRoughEnergy.eventual_real_energy
  let a : ℝ := 2*(h:ℝ)+1
  have ha : 1≤a := by dsimp [a];nlinarith [Nat.cast_nonneg (α:=ℝ) h]
  refine ⟨1+a+8016*C₄*C₁*a^2,by positivity,?_⟩
  filter_upwards [hMass,hEnergy,eventual_short_twists,OrdinaryRoughEnergy.eventual_source_D_large,
    eventually_ge_atTop (1:ℝ)] with B hM hE hShort hDlarge hB
  intro D hD Z hZ f g hf hg hfm hgm hNP P hP c hc
  have hDr : 0<(D:ℝ) := by linarith [hDlarge.trans hD]
  have hDn : 0<D := by exact_mod_cast hDr
  have hZr (z : ℕ) (hz : z∈Z) : (D:ℝ)≤z ∧ (z:ℝ)<2*D ∧
      IsRough (Real.exp (B^(199979/200000:ℝ))) z := by
    obtain ⟨hz1,hz2,hzr⟩ := hZ z hz
    exact ⟨by exact_mod_cast hz1,by exact_mod_cast hz2,hzr⟩
  have hMbound := hM D hD Z hZr
  have hEbound := hE D hD Z hZr
  let M : ℝ := ∑z∈Z,(z:ℝ)⁻¹
  have hM0 : 0≤M := sum_nonneg (fun z _=>by positivity)
  let A : ℕ := (2*h+1)*D
  have hDA : D≤A := by dsimp [A];nlinarith
  have hAr : (A:ℝ)=a*D := by simp [A,a]
  let τ : ℝ := B^(-10001/10000:ℝ)
  have hτ : 0<τ := by dsimp [τ];positivity
  let S : ℕ→ℝ := fun U=>8016*B^(-1/950:ℝ)*(A:ℝ)*U
  have hshort : ∀ᶠ U : ℕ in atTop, ∀s t : ℝ,
      (∀{N:ℕ} [NeZero N],∀k:ZMod N,∑v∈Icc 1 U,
        ‖poly (Icc 1 D) (fun m=>twist f P s (v+m)) (fun m=>(m:ZMod N)) k‖≤S U) ∨
      (∀{N:ℕ} [NeZero N],∀k:ZMod N,∑v∈Icc 1 U,
        ‖poly (Icc 1 A) (fun m=>twist g P t (v+m)) (fun m=> -(m:ZMod N)) k‖≤S U) := by
    rcases hNP with hNP|hNP
    · filter_upwards [hShort hf hfm hNP P hP,eventually_ge_atTop A] with U hU hAU
      intro s t
      left
      intro N hN k
      have hDU : (D:ℝ)≤(U:ℝ)+1 := by
        have hdU : (D:ℝ)≤U := by exact_mod_cast hDA.trans hAU
        linarith
      apply (hU D hD hDU s k).trans
      dsimp [S]
      have hDAR : (D:ℝ)≤A := by exact_mod_cast hDA
      gcongr
    · filter_upwards [hShort hg hgm hNP P hP,eventually_ge_atTop A] with U hU hAU
      intro s t
      right
      intro N hN k
      have hAd : (1/2:ℝ)*Real.exp (B^(9999/10000:ℝ))≤A :=
        hD.trans (by exact_mod_cast hDA)
      have hAU' : (A:ℝ)≤(U:ℝ)+1 := by
        have hAU'' : (A:ℝ)≤U := by exact_mod_cast hAU
        linarith
      simpa only [poly,neg_mul,mul_neg] using hU A hAd hAU' t (-k)
  have hboundary : ∀ᶠ U : ℕ in atTop, 2*(D:ℝ)*M≤τ*U := by
    have ht := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop ((2*D*M)/τ)
    filter_upwards [ht] with U hU
    have he := (div_le_iff₀ hτ).mp hU
    nlinarith only [he]
  filter_upwards [hshort,hboundary] with U hU hboundary
  intro s t
  let N : ℕ := 4*h*D+(2*h+1)*D+1
  have : NeZero N := ⟨by dsimp [N];omega⟩
  have hN₁ : (2*h+1)*D<N := by dsimp [N];omega
  have hN₂ : 4*h*D≤N := by dsimp [N];omega
  have hw (z : ℕ) (hz : z∈Z) : ‖c z/(z:ℂ)‖≤(z:ℝ)⁻¹ := by
    rw [norm_div,Complex.norm_natCast]
    simpa only [one_div] using div_le_div_of_nonneg_right (hc z hz) (Nat.cast_nonneg z)
  have hS0 : 0≤S U := by dsimp [S];positivity
  have hSU : (∀k:ZMod N,∑v∈Icc 1 U,
        ‖poly (Icc 1 D) (fun m=>twist f P s (v+m)) (fun m=>(m:ZMod N)) k‖≤S U) ∨
      (∀k:ZMod N,∑v∈Icc 1 U,
        ‖poly (Icc 1 ((2*h+1)*D)) (fun m=>twist g P t (v+m)) (fun m=> -(m:ZMod N)) k‖≤S U) := by
    rcases hU s t with h1|h2
    · exact Or.inl h1
    · exact Or.inr h2
  have hb := OrdinaryRoughWeighted.weighted_correlation_bound (N:=N) Z h D U
    (twist f P s) (twist g P t) (fun z=>c z/(z:ℂ)) hh hDn
    (fun z hz=>⟨(hZ z hz).1,(hZ z hz).2.1⟩) hN₁ hN₂
    (twist_oneBounded hf P s) (twist_oneBounded hg P t) hw (S U) τ hS0 hτ hSU
  have hn := numeric_budget hB hDr ha (Nat.cast_nonneg U) hM0
    (Nat.cast_nonneg (natAdditiveEnergy Z)) hC₁ hC₄ hMbound hEbound hboundary
  apply hb.trans
  simpa only [S,hAr,M,τ,a,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using hn
end OrdinaryRoughTarget

end

end OAI
