import OAI.NumberTheory.Ostmann.Characters.SourceTemplateActualDisjoint
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowsCells
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSourceScalesBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSourceScales
open Construction Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate Template

def shortUpper {E : Finset ℕ} {L : ℝ} {k : ℕ} {α β ρ γ c₀ : ℝ}
    (s : SourceLocations E L k α β ρ γ c₀) (big : Bool) : ℝ :=
  if big then s.B+s.w else s.s+1

def longLower {E : Finset ℕ} {L : ℝ} {k : ℕ} {α β ρ γ c₀ : ℝ}
    (s : SourceLocations E L k α β ρ γ c₀) (big : Bool) : ℝ :=
  if big then s.u else s.B

theorem actual_location_gap {E : Finset ℕ} {L : ℝ} {k : ℕ} {α β ρ γ c₀ : ℝ}
    (s : SourceLocations E L k α β ρ γ c₀) (hγ : 0<γ) (hL : 0<L) (big : Bool) :
    0<shortUpper s big ∧ shortUpper s big≤β*L ∧
      shortUpper s big+γ*L≤longLower s big := by
  have hw : 0<s.w := (mul_pos hγ hL).trans_le s.width_lower
  cases big <;> simp only [shortUpper,longLower,Bool.false_eq_true,ite_false,ite_true]
  · constructor
    · linarith [s.small_start,s.A_nonneg]
    · constructor
      · linarith [s.small_end,s.lower_separation,s.upper_separation,s.upper_end]
      · linarith [s.small_end,s.lower_separation,s.width_lower]
  · constructor
    · linarith [s.lower_separation,s.A_nonneg]
    · constructor
      · linarith [s.upper_separation,s.upper_end]
      · linarith [s.bulk_gap]

theorem actual_location_grid {E : Finset ℕ} {L : ℝ} {k : ℕ} {α β ρ γ c₀ : ℝ}
    (s : SourceLocations E L k α β ρ γ c₀) (hγ : 0<γ) (hL : 0<L) (big : Bool) :
    ∃n : Fin (scaleCount β γ),0<n.val ∧
      shortUpper s big ≤ shortExponent γ n.val*L ∧
      (longExponent γ n.val+scaleStep γ)*L ≤ longLower s big := by
  have hg := actual_location_gap s hγ hL big
  exact exists_grid_of_gap hγ hL hg.1 hg.2.1 hg.2.2

theorem fixedConfiguration_anchor_log_bounds {d : Decomposition} {E : Finset ℕ}
    {δ L : ℝ} {k : ℕ} {α β ρ γ c₀ c BD : ℝ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀}
    (w : FixedConfigurationWitness s c BD) (a : Fin k) (big : Bool)
    (p : PrimeUpTo s.locations.Q)
    (hp : p∈boundedRawLogCell s.locations.primes (w.configuration.1 (anchorCoordinate a big))) :
    Real.exp (if big then s.locations.u else s.locations.s) ≤ Real.log p.val ∧
      Real.log p.val ≤ Real.exp ((if big then s.locations.u else s.locations.s)+1) := by
  obtain ⟨small,large,hcfg,hsl,hsh,hll,hlh⟩ := w.geometry.anchors
  have hp' := (Finset.mem_filter.mp hp).2
  have hsmall : w.configuration.1 (anchorCoordinate a false)=small := by
    rw [hcfg]
    change (if a.val<k then small else large)=small
    exact ite_eq_left a.isLt
  have hlarge : w.configuration.1 (anchorCoordinate a true)=large := by
    rw [hcfg]
    change (if k+a.val<k then small else large)=large
    exact ite_eq_right (by omega)
  cases big
  · rw [hsmall] at hp'
    exact ⟨hsl.le.trans hp'.1,hp'.2.le.trans hsh⟩
  · rw [hlarge] at hp'
    exact ⟨hll.le.trans hp'.1,hp'.2.le.trans hlh⟩

end Ostmann.Characters.TemplateOneSidedSourceScales

end

end OAI
