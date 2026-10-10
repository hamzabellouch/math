import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceAmplitudeData
import OAI.NumberTheory.Ostmann.Characters.SourceTemplateShellsDisjoint

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template HigherBiasSourceWord HigherBiasSourceRoleBounds InitialCharacterScale
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem boundedRawLogCell_disjoint_interval {Q : ℕ} (E : Finset (PrimeUpTo Q))
    (h : ℤ) (a b : ℝ) (hh : (h:ℝ)+1 ≤ Real.exp a ∨ Real.exp b < (h:ℝ)) :
    Disjoint (boundedRawLogCell E h) (boundedInterval E a b) := by
  apply Finset.disjoint_left.mpr
  intro p hp hb
  have hc := (Finset.mem_filter.mp hp).2
  have hi := boundedInterval_log_bounds E a b p hb
  rcases hh with hl | hu <;> linarith

theorem fixedConfiguration_cells_disjoint_bulk {d : Decomposition} {E : Finset ℕ}
    {δ L : ℝ} {k : ℕ} {α β ρ γ c₀ c BD : ℝ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀}
    (w : FixedConfigurationWitness s c BD) (hwidth : 0 < s.locations.w)
    (i : Fin (configCellCount w.configuration)) :
    Disjoint (w.cells i) (s.locations.base 0) := by
  have hsmall : Real.exp (s.locations.s+1) ≤ Real.exp s.locations.B := by
    apply Real.exp_le_exp.mpr
    linarith [s.locations.small_end,s.locations.lower_separation]
  have hlarge : Real.exp (s.locations.B+s.locations.w) < Real.exp s.locations.U := by
    apply Real.exp_lt_exp.mpr
    linarith [s.locations.upper_separation,s.locations.grid_start]
  have htop : Real.exp s.locations.U ≤ Real.exp s.locations.u :=
    Real.exp_le_exp.mpr s.locations.top_start
  obtain ⟨small,big,hanchors,hsl,hsh,hbl,hbh⟩ := w.geometry.anchors
  have ha : ∀ j,(w.configuration.1 j:ℝ)+1 ≤ Real.exp s.locations.B ∨
      Real.exp (s.locations.B+s.locations.w) < (w.configuration.1 j:ℝ) := by
    intro j
    rw [hanchors]
    unfold repeatedAnchors
    split_ifs
    · exact Or.inl (hsh.trans hsmall)
    · exact Or.inr (hlarge.trans_le htop |>.trans hbl)
  have hl : ∀ j,∀ a∈w.configuration.2 j,(a:ℝ)+1 ≤ Real.exp s.locations.B ∨
      Real.exp (s.locations.B+s.locations.w) < (a:ℝ) := by
    intro j a ha
    exact Or.inr (hlarge.trans_le (w.geometry.list_entry_lower j a ha))
  have hi := configCellIndices_property w.configuration
    (fun a=>(a:ℝ)+1 ≤ Real.exp s.locations.B ∨
      Real.exp (s.locations.B+s.locations.w) < (a:ℝ)) ha hl i
  exact boundedRawLogCell_disjoint_interval s.locations.primes
    (configCellIndices w.configuration i) s.locations.B (s.locations.B+s.locations.w) hi

theorem selectedSource_top_disjoint_bulk {d : Decomposition} {E : Finset ℕ}
    {δ L : ℝ} {k : ℕ} {α β ρ γ c₀ : ℝ}
    (s : SelectedWordSource d E δ L k α β ρ γ c₀) (hwidth : 0 < s.locations.w) :
    Disjoint (s.locations.base 2) (s.locations.base 0) := by
  apply Finset.disjoint_left.mpr
  intro p hp hb
  have hl : s.locations.B+s.locations.w < s.locations.u := by
    linarith [s.locations.upper_separation,s.locations.grid_start,s.locations.top_start]
  have hpl := (boundedInterval_log_bounds s.locations.primes s.locations.u
    (s.locations.u+1) p hp).1
  have hpu := (boundedInterval_log_bounds s.locations.primes s.locations.B
    (s.locations.B+s.locations.w) p hb).2
  have hh := Real.exp_lt_exp.mpr hl
  linarith

theorem fixedConfiguration_scheduled_nonbulk_disjoint {d : Decomposition} {E : Finset ℕ}
    {δ L : ℝ} {k : ℕ} {α β ρ γ c₀ c BD : ℝ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀}
    (w : FixedConfigurationWitness s c BD) (hwidth : 0 < s.locations.w) (j : ℕ)
    (i : (schedule k j).Constituent (sourceWidth w.configuration (wordSize k L)))
    (hi : (schedule k j).role i.1 ≠ .word ∨ wordSize k L ≤ i.2.val) :
    Disjoint (scheduledPrimeShells k (sourceWidth w.configuration (wordSize k L))
      (configurationPrimeShells w.configuration (wordSize k L)
        (s.locations.base 0) (s.locations.base 2) s.locations.primes) j i) (s.locations.base 0) :=
  scheduledPrimeShells_nonbulk_disjoint w.configuration (wordSize k L) j
    (s.locations.base 0) (s.locations.base 2) s.locations.primes
    (fixedConfiguration_cells_disjoint_bulk w hwidth) (selectedSource_top_disjoint_bulk s hwidth) i hi

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
