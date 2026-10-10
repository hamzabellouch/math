import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.AllFrequencyPowerLogarithmic
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.AeNotNatTranslate

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

namespace OrdinaryInitialWidth
open OrdinaryCorrelations OrdinaryLocalAdditive OrdinarySharpWindow Finset Filter MeasureTheory

theorem ordinary_short_power_logarithmic :
    ∃ v : ℕ, ∀ m : ℕ,
    ∀ {f : ℕ→ℂ}, OneBounded f → Multiplicative f → UniformlyNonpretentious f →
    ∀ᶠ X : ℝ in atTop,
    ∀ D : ℝ, ((2:ℕ)^(2^(1800*m+v)):ℝ)≤D → D≤X → ∀α : ℝ,
      (∫y in Set.Ioc 0 X,‖forwardSum f α D y‖)
      ≤1000*(1/2:ℝ)^(2*m)*D*X := by
  obtain ⟨v,hv⟩ := OrdinaryUniformWidth.all_frequency_power_logarithmic
  refine ⟨v,?_⟩
  intro m f hf hm hNP
  obtain ⟨K,hK⟩ := eventually_atTop.mp (hv m hf hm hNP)
  let ε : ℝ := (1/2:ℝ)^(2*m)
  have hε : 0<ε := by dsimp [ε];positivity
  refine eventually_atTop.mpr ⟨max 1 (2*((K:ℝ)+1)/ε),?_⟩
  intro X hX D hD hDX α
  have hX1 : 1≤X := (le_max_left _ _).trans hX
  have hXK : 2*((K:ℝ)+1)/ε≤X := (le_max_right _ _).trans hX
  have hD0 : 0<D := (by positivity : (0:ℝ)<((2:ℕ)^(2^(1800*m+v)):ℝ)).trans_le hD
  obtain ⟨k,hk1,hk2⟩ := exists_nat_pow_near (by linarith : (1:ℝ)≤2*X) (by norm_num : (1:ℝ)<2)
  have hP : ((2^(k+1):ℕ):ℝ)≤4*X := by
    push_cast
    rw [pow_succ]
    linarith
  have hPX : X+D≤((2^(k+1):ℕ):ℝ) := by
    push_cast
    linarith
  have ha : OneBounded (fun n=>f n*phase (α*n)) := by
    intro n
    rw [norm_mul,OrdinaryLocalAdditive.norm_phase,mul_one]
    exact hf n
  have hp := prefixEnergy_power_bound ha hD0.le (by positivity : 0≤100*ε) K
    (fun N hN=>hK N hN D hD α) (k+1)
  have hstart : (2*((K:ℝ)+1))*D≤ε*D*X := by
    have hcross := (div_le_iff₀ hε).mp hXK
    have ht := mul_le_mul_of_nonneg_right hcross hD0.le
    nlinarith only [ht]
  have hlast := mul_le_mul_of_nonneg_left hP (by positivity : 0≤100*ε*D)
  have ht := (forward_integral_le_prefix f α hD0.le hPX).trans hp
  push_cast at hlast
  change _≤1000*ε*D*X
  nlinarith [mul_nonneg (mul_nonneg hε.le hD0.le) (by linarith : 0≤X)]

end OrdinaryInitialWidth

end

end OAI
