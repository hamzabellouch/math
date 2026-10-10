import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceTypicalAlgebra
import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualBiasedPopulationsBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters
open Ostmann.Preliminaries Ostmann.Construction Filter
open scoped BigOperators

theorem eventually_higherSourceTypical_mass (d : Decomposition) (δ c₀ : ℝ)
    (hδ : 0 < δ) (hc₀ : 0 < c₀) :
    ∃ cA : ℝ,0 < cA ∧ ∀ᶠ X : ℕ in atTop,∀ (ι : Type) [Fintype ι],
      (Fintype.card ι:ℝ) ≤ Real.log (X:ℝ) →
      ∀ E : Finset (PrimeUpTo (collisionScale 10 X)),
      ∀ F : HigherBiasSourceFamily d (collisionScale 10 X) E δ,
      ∀ G : ι → Finset (PrimeUpTo (collisionScale 10 X)),
      (∀ i,G i ⊆ E) → ∀ hm : ∀ i,0 < primeShellMass (G i),
      (∀ i,c₀ ≤ primeShellMass (G i)) →
      (∀ i,∀ p∈G i,(Real.log (Real.log (X:ℝ)))^2 ≤ Real.log p.val) →
      ∃ H : Finset ℕ,H ⊆ upperWindow d.A X ∧
        cA*Real.sqrt X/(Real.log (X:ℝ))^3 ≤ H.card ∧
        ∀ a∈H,∀ i,δ/2 ≤
          ((primeShellPrior (G i) (hm i)).cmean (fun p => F.test p (a:ZMod p.val))).re := by
  classical
  obtain ⟨c,hc,hcard⟩ := QuadraticCenter.actual_integerWindows_card_lower d
  have hlog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  refine ⟨c/2,half_pos hc,?_⟩
  filter_upwards [hcard,eventually_higherSourceTypical_count d,
    hlog.eventually_ge_atTop 1,hlog.eventually_ge_atTop (2/c),
    hloglog.eventually_gt_atTop 0,
    hloglog.eventually_gt_atTop (4*collisionConstant 10/(c₀*δ^2))]
    with X hcard hcount ht htlarge he hesmall
  intro ι _ hι E F G hG hm hmass hscale
  let H := higherSourceTypicalEndpoints d X F G hm
  have herr : ∀ i,(primeShellMass (G i)*(Real.log (Real.log (X:ℝ)))^2)⁻¹ *
      (collisionConstant 10*Real.log (Real.log (X:ℝ))) < (δ/2)^2 := by
    intro i
    exact higherSource_error_small hc₀ hδ (collisionConstant_pos 10).le he
      (hmass i) le_rfl hesmall
  have hbad := hcount ι δ hδ E F G hG hm ((Real.log (Real.log (X:ℝ)))^2)
    (sq_pos_of_pos he) hscale herr
  have hloss := higherSource_typical_loss hc ht (Nat.cast_nonneg (Fintype.card ι))
    (Real.sqrt_nonneg (X:ℝ)) hι htlarge
  have hfull : c*Real.sqrt X/(Real.log (X:ℝ))^3 ≤ (upperWindow d.A X).card := by
    simpa only [QuadraticCenter.positiveIntegerWindow,Finset.card_map] using hcard.1
  refine ⟨H,Finset.filter_subset _ _,?_,?_⟩
  · change (upperWindow d.A X).card ≤ (H.card:ℝ)+_ at hbad
    have heq : c*Real.sqrt X/(Real.log (X:ℝ))^3 =
        2*((c/2)*Real.sqrt X/(Real.log (X:ℝ))^3) := by ring
    linarith
  · intro a ha
    exact (Finset.mem_filter.mp ha).2

end Ostmann.Characters

end

end OAI
