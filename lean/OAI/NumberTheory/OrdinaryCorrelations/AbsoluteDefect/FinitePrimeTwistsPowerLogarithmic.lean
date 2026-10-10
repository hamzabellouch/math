import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OrdinaryShortPowerLogarithmic
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeCountLe
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.FinitePhaseGrid
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ForwardIntegrableOn

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

namespace OrdinaryTwistWidth
open OrdinaryCorrelations OrdinaryInitialWidth OrdinaryLocalAdditive Finset Filter MeasureTheory

theorem finite_prime_twists_power_logarithmic :
    ∃ v : ℕ, ∀ m : ℕ,
    ∀ {f : ℕ→ℂ}, OneBounded f → Multiplicative f → UniformlyNonpretentious f →
    ∀ (P : Finset ℕ), (∀ p∈P, Nat.Prime p) →
    ∀ᶠ X : ℝ in atTop,
    ∀ D : ℝ, ((2:ℕ)^(2^(1800*m+v)):ℝ)≤D → D≤X → ∀α t : ℝ,
      (∫y in Set.Ioc 0 X,‖forwardSum (twist f P t) α D y‖)
      ≤1002*(1/2:ℝ)^(2*m)*D*X := by
  obtain ⟨v,hv⟩ := ordinary_short_power_logarithmic
  refine ⟨v,?_⟩
  intro m f hf hm hNP P hP
  let ε : ℝ := (1/2:ℝ)^(2*m)
  have hε : 0<ε := by dsimp [ε];positivity
  obtain ⟨N,hN,hgrid⟩ := finite_phase_grid (2*Real.pi*P.card)
    (by positivity) (by positivity : (0:ℝ)<ε/2)
  have hevent : ∀ᶠ X : ℝ in atTop, ∀j : Fin N,
      ∀D : ℝ, ((2:ℕ)^(2^(1800*m+v)):ℝ)≤D → D≤X → ∀α : ℝ,
        (∫y in Set.Ioc 0 X,‖forwardSum (twist f P ((j:ℝ)/N)) α D y‖)
        ≤1000*ε*D*X := by
    apply eventually_all.mpr
    intro j
    exact hv m (twist_oneBounded hf P _) (twist_multiplicative hm P hP _)
      (twist_nonpretentious hf hNP P hP _)
  filter_upwards [hevent,eventually_ge_atTop (1:ℝ)] with X hXX hX
  intro D hD hDX α t
  have hD0 : 0<D := (by positivity : (0:ℝ)<((2:ℕ)^(2^(1800*m+v)):ℝ)).trans_le hD
  obtain ⟨j,hj⟩ := hgrid t
  have hfg (n : ℕ) : ‖twist f P t n-twist f P ((j:ℝ)/N) n‖≤ε/2 := by
    rw [twist_fract f P t]
    exact (twist_sub_le hf P (Int.fract t) ((j:ℝ)/N) n).trans hj
  have hb := hXX j D hD hDX α
  have hc := forward_integral_continuity hfg (by positivity : (0:ℝ)≤ε/2) hD0.le hX hDX α
  change _≤1002*ε*D*X
  nlinarith [mul_nonneg (mul_nonneg hε.le hD0.le) (by linarith : 0≤X)]

end OrdinaryTwistWidth

end

end OAI
