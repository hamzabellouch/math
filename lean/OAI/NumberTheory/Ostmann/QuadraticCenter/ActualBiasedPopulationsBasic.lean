import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualAmplifierSupport
import OAI.NumberTheory.Ostmann.QuadraticCenter.AffineKernelNumeratorBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter Ostmann.Preliminaries

lemma actual_negativeIntegerWindow_mem {S : Set ℕ} {X : ℕ} {a : ℤ}
    (ha : a ∈ negativeIntegerWindow S X) :
    ∃ n : ℕ, n ∈ S ∧ n ≤ X ∧ (X : ℝ)^(9/10:ℝ) ≤ n ∧ -(n:ℤ)=a := by
  obtain ⟨n,hn,hn'⟩ := Finset.mem_map.mp ha
  obtain ⟨hS,hX,hlarge⟩ := mem_upperWindow.mp hn
  exact ⟨n,hS,hX,hlarge,hn'⟩

theorem actual_integerWindows_card_lower (d : Decomposition) :
    ∃ c : ℝ,0 < c ∧ ∀ᶠ X : ℕ in atTop,
      c*Real.sqrt X/(Real.log (X:ℝ))^3 ≤ (positiveIntegerWindow d.A X).card ∧
      c*Real.sqrt X/(Real.log (X:ℝ))^3 ≤ (negativeIntegerWindow d.B X).card := by
  obtain ⟨c,C,hc,hC,hbounds⟩ := summand_sqrt_bounds d
  have hA := eventually_upperWindow_card_lower d.A hc hC
    (hbounds.mono fun X h => h.1) (hbounds.mono fun X h => h.2.2.1)
  have hB := eventually_upperWindow_card_lower d.B hc hC
    (hbounds.mono fun X h => h.2.1) (hbounds.mono fun X h => h.2.2.2)
  refine ⟨c/2,by positivity,?_⟩
  filter_upwards [hA,hB] with X hA hB
  simpa only [positiveIntegerWindow,negativeIntegerWindow,Finset.card_map] using And.intro hA hB

theorem eventually_actual_integerWindows_cross (d : Decomposition) :
    ∀ᶠ X : ℕ in atTop, ∀ x∈positiveIntegerWindow d.A X,
      ∀ y∈negativeIntegerWindow d.B X,
      Nat.Prime (x-y).natAbs ∧ (X:ℝ)^(9/10:ℝ) ≤ ((x-y).natAbs:ℝ) := by
  filter_upwards [eventually_upperWindow_large d.cutoff] with X hlarge
  intro x hx y hy
  obtain ⟨a,ha,haX,haL,rfl⟩ := actual_positiveIntegerWindow_mem hx
  obtain ⟨b,hb,hbX,hbL,rfl⟩ := actual_negativeIntegerWindow_mem hy
  have hcut : d.cutoff ≤ a+b := by
    have hr : (d.cutoff:ℝ) ≤ (a:ℝ)+b := by
      have := Real.sqrt_nonneg (X:ℝ)
      have := Nat.cast_nonneg (α:=ℝ) b
      linarith
    exact_mod_cast hr
  have hab : ((a:ℤ)-(-(b:ℤ))).natAbs=a+b := by
    rw [sub_neg_eq_add,← Nat.cast_add,Int.natAbs_natCast]
  rw [hab]
  exact ⟨d.sum_prime ha hb hcut,haL.trans (by exact_mod_cast Nat.le_add_right a b)⟩

end Ostmann.QuadraticCenter

end

end OAI
