import OAI.NumberTheory.Ostmann.Construction.SourceFrequencyBoundsFamily
import OAI.NumberTheory.Ostmann.Construction.SourceFrequencyBoundsNumeric
import OAI.NumberTheory.Ostmann.Construction.SourceRangeSeparationPriors
import OAI.NumberTheory.Ostmann.Construction.SourceRangeSeparationScales

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter

theorem initial_sources_above_frequencies_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀j : ℕ,j≤k →
        C.giant.AboveFrequency (Conclusion.frequencyBound Bs BD Bz k L j) ∧
        ∀origin,(C.sources origin).AboveFrequency (Conclusion.frequencyBound Bs BD Bz k L j) := by
  filter_upwards [SourceFrequencyBounds.frequency_lt_of_log_lower_eventually Bs BD Bz hk
      (by norm_num : (0:ℝ)<1/250),
    SourceRangeSeparation.broad_range_gaps_eventually k,
    nominalTotals_eventually Bs BD Bz hk] with L hfreq hgap hnom
  intro E C hG hc hcu hb hd j hj
  have hG0 : 0≤C.blockBase := (Real.exp_pos _).le.trans hG
  have hnom := hnom C.blockBase C.giantCenter C.bulkBin C.spectatorBin hG0
    ⟨hc.le,hcu.le⟩ hb hd
  have hwidth : 1000≤favorableBlockWidth L := by linarith [hgap.2.1]
  have hsmall : Real.exp ((1/250:ℝ)*L)≤favorableBlockWidth L/200 := by
    apply le_trans _ hgap.2.2.2.1.le
    exact Real.exp_le_exp.mpr (by nlinarith [hgap.1])
  have hgiantlower : Real.exp ((1/250:ℝ)*L)≤Real.exp ((1/20:ℝ)*L)-3 := by
    have hp : (1:ℝ)≤2^k := one_le_pow₀ (by norm_num)
    have hw0 : 0≤favorableBlockWidth L := by linarith
    have hmul := mul_le_mul_of_nonneg_right hp hw0
    have hbig := hgap.2.2.2.2
    linarith
  have hbulk : C.bulk.AboveFrequency (Conclusion.frequencyBound Bs BD Bz k L j) := by
    intro p hp
    exact hfreq j hj (p:ℕ) (C.bulk.prime _ p.property).pos
      (harmonicBand_log_support C.bulkPositive p).1
  have haux : ∀i,(C.auxiliary i).AboveFrequency (Conclusion.frequencyBound Bs BD Bz k L j) := by
    intro i p hp
    apply hfreq j hj (p:ℕ) ((C.auxiliary i).prime _ p.property).pos
    have hlog := C.cells.auxSource_log_bounds hwidth hnom.2.1
      (fun a => hnom.2.2 a.val a.isLt) E C.deleted_card i p hp
    exact hsmall.trans hlog.1
  refine ⟨?_,C.sources_aboveFrequency _ hbulk haux⟩
  intro p hp
  apply hfreq j hj (p:ℕ) (C.giant.prime _ p.property).pos
  have hlog := (abs_lt.mp (logCellPrimeSource_log_support C.giantCenter ∅ C.giantPositive p hp)).1
  linarith

end Ostmann.Construction

end

end OAI
