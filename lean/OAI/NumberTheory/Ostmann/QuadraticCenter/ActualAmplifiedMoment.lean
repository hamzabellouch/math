import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualAmplifierScales
import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualAmplifierSupport
import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplifiedMomentScales

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem eventually_actual_amplified_moment_lower (d : Decomposition)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z →
      Real.log z ≤ 2*T^auxiliaryExponent →
      ∀ (ι : Type*) [Fintype ι] (p : ι → ℕ)
        (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
        (hne : ∀ i, NeZero (p i)),
      Fintype.card ι = auxiliaryK Z z →
      (∀ i, BalancedResiduePrime d (p i)) → (∀ i,p i ≤ Z) →
      ∀ (P : Finset ℕ), 0 < P.card → ∀ ε t : ℕ → ℤ,
      (∀ r ∈ P, ε r = -1 ∨ ε r = 1) →
      (∀ r ∈ P, δ/4 ≤ (∑ a ∈ positiveIntegerWindow d.A (parameterX T),
        ((ε r * jacobiSym (a-t r) r : ℤ) : ℝ)) /
          (positiveIntegerWindow d.A (parameterX T)).card) →
      letI : ∀ i, NeZero (p i) := hne
      Real.sqrt (parameterX T:ℝ)*Real.exp ((2/125:ℝ)*auxiliaryK Z z) ≤
        ∑' n : ℤ, amplifiedMomentTerm p hcop (fun i => d.residueSupport (p i))
          (1/16) (parameterX T) P ε t (evenMomentParameter (parameterX T) Z) n := by
  obtain ⟨c,hc,hcard⟩ := actual_positiveIntegerWindow_card_lower d
  have hc' : 0 < cutoffLower*c := mul_pos cutoffLower_pos hc
  filter_upwards [parameterX_tendsto.eventually hcard,
    parameterX_tendsto.eventually (eventually_actual_amplifier_support_uniform d),
    eventually_prime_band_le_sqrt_parameterX,
    eventually_amplified_moment_scalar_lower (cutoffLower*c) (δ/4) hc' (by positivity),
    parameterX_tendsto.eventually_gt_atTop 0] with T hcard hsupport hscale hscalar hX
  intro Z z hZl hZu hz hzl hzu ι _ p hcop hne hK hbal hp P hP ε t hε hbias
  let : ∀ i, NeZero (p i) := hne
  have hpX : ∀ i,(p i:ℝ) ≤ Real.sqrt (parameterX T:ℝ) := by
    intro i
    have hh : (p i:ℝ) ≤ Z := by exact_mod_cast hp i
    exact hh.trans (hscale Z hZu)
  have hs := hsupport.2 ι p hcop hne hpX
  have hbalance : ∀ i, Supply.density (d.residueSupport (p i)) ≤ 1-(1/3:ℝ) := by
    intro i
    have hh := (actual_balanced_density d (p i) (hbal i)).2
    linarith
  have hm := amplified_moment_lower p hcop (fun i => d.residueSupport (p i))
    (lam := (1/16:ℝ)) (c := (1/3:ℝ)) (δ := δ/4)
    (by norm_num) (by norm_num) (by exact_mod_cast hX) (by norm_num) (by positivity)
    hbalance (positiveIntegerWindow d.A (parameterX T)) hcard.2 P hP ε t hε
    hsupport.1 hs hbias (evenMomentParameter_even (parameterX T) Z)
  rw [hK] at hm
  norm_num only at hm
  have hcutoff : 0 < cutoffLower := cutoffLower_pos
  have hbound := mul_le_mul_of_nonneg_right hcard.1
    (show 0 ≤ cutoffLower*(49/48:ℝ)^auxiliaryK Z z*(δ/4)^evenMomentParameter (parameterX T) Z by positivity)
  calc
    _ ≤ (cutoffLower*c)*Real.sqrt (parameterX T:ℝ)/(Real.log (parameterX T:ℝ))^3*
        (49/48:ℝ)^auxiliaryK Z z*(δ/4)^evenMomentParameter (parameterX T) Z :=
      hscalar Z z hZl hZu hz hzl hzu
    _ ≤ cutoffLower*(49/48:ℝ)^auxiliaryK Z z*(positiveIntegerWindow d.A (parameterX T)).card*
        (δ/4)^evenMomentParameter (parameterX T) Z := by
      convert hbound using 1 <;> ring
    _ ≤ _ := hm

end Ostmann.QuadraticCenter

end

end OAI
