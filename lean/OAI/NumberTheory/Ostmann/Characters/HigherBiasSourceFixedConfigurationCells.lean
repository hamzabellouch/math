import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceFixedConfigurationDefs
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceTargetCells

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Construction Preliminaries

theorem bounded_cell_index_upper {Q : ℕ} {E : Finset ℕ} {h : ℤ} {B : ℝ}
    (hband : ∀ p∈E,Real.log (Real.log p) ≤ B)
    (hm : 0 < primeShellMass (boundedRawLogCell (boundedPrimeSet Q E) h)) :
    (h:ℝ) ≤ Real.exp B := by
  classical
  have hne : (boundedRawLogCell (boundedPrimeSet Q E) h).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    simp only [primeShellMass,he,Finset.sum_empty] at hm
    exact lt_irrefl _ hm
  obtain ⟨p,hp⟩ := hne
  obtain ⟨hp,hlo,_⟩ := Finset.mem_filter.mp hp
  have hup := Real.exp_le_exp.mpr (hband p.val (mem_boundedPrimeSet.mp hp))
  have hlog : 0 < Real.log (p.val:ℝ) := Real.log_pos (by
    exact_mod_cast (primeUpTo_prime p).one_lt)
  rw [Real.exp_log hlog] at hup
  exact hlo.trans hup

theorem good_cell_uniform {d : Decomposition} {Q : ℕ} {E : Finset ℕ}
    {δ c a B : ℝ} (F : HigherBiasSourceFamily d Q (boundedPrimeSet Q E) δ)
    (hc : 0<c) (hband : ∀ p∈E,Real.log (Real.log p) ≤ B)
    {n h : ℤ} (hlo : Real.exp a < (h:ℝ))
    (hm : c/Real.exp a ≤ primeShellMass (boundedRawLogCell (boundedPrimeSet Q E) h))
    (ht : ∃ hp : 0 < primeShellMass (boundedRawLogCell (boundedPrimeSet Q E) h),
      δ/4 ≤ ((primeShellPrior (boundedRawLogCell (boundedPrimeSet Q E) h) hp).cmean
        (fun p => F.test p (n:ZMod p.val))).re) :
    0 ≤ h ∧ (h:ℝ) ≤ Real.exp B ∧
    c/Real.exp B ≤ primeShellMass (boundedRawLogCell (boundedPrimeSet Q E) h) ∧
    ∃ hp : 0 < primeShellMass (boundedRawLogCell (boundedPrimeSet Q E) h),
      δ/4 ≤ ((primeShellPrior (boundedRawLogCell (boundedPrimeSet Q E) h) hp).cmean
        (fun p => F.test p (n:ZMod p.val))).re := by
  have hpos : 0 < (h:ℝ) := (Real.exp_pos a).trans hlo
  have hu := bounded_cell_index_upper hband ht.choose
  refine ⟨by exact_mod_cast hpos.le,hu,?_,ht⟩
  exact (div_le_div_of_nonneg_left hc.le (Real.exp_pos a) (hlo.le.trans hu)).trans hm

theorem configuration_bounded_of_good {d : Decomposition} {E : Finset ℕ} {δ L : ℝ}
    {k : ℕ} {α β ρ γ c0 c BD : ℝ}
    {s : SelectedWordSource d E δ L k α β ρ γ c0}
    {cfg : SourceConfiguration k} {n : ℤ}
    (hg : ConfigurationGoodAt s c cfg n) (hgeom : ConfigurationGeometry s c BD cfg) :
    cfg.Bounded ⌊Real.exp (β*L)⌋₊ ⌈2*Real.exp (2*((1/10000:ℝ)*k))⌉₊ := by
  have hb (h : ℤ) (hh : ∃ i,configCellIndices cfg i=h) :
      |h| ≤ (⌊Real.exp (β*L)⌋₊:ℤ)+1 := by
    obtain ⟨i,rfl⟩ := hh
    have hi := hg i
    rw [abs_of_nonneg hi.1]
    have hf := Nat.lt_floor_add_one (Real.exp (β*L))
    have hh' : (configCellIndices cfg i:ℝ) ≤ (⌊Real.exp (β*L)⌋₊:ℝ)+1 := by
      linarith [hi.2.1]
    exact_mod_cast hh'
  refine ⟨fun i => hb _ (configCellIndices_anchor cfg i),?_⟩
  intro j
  refine ⟨?_,fun h hh => hb h ((configCellIndices_range cfg h).mpr (Or.inr ⟨j,hh⟩))⟩
  exact_mod_cast (hgeom.length_upper j).trans (Nat.le_ceil _)

end Ostmann.Characters.HigherBiasSource

end

end OAI
