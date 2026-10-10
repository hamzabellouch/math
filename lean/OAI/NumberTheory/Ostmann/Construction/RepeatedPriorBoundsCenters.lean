import OAI.NumberTheory.Ostmann.Construction.InitialSourceChoice
import OAI.NumberTheory.Ostmann.Construction.NominalCenterSelectionRanges
import OAI.NumberTheory.Ostmann.Construction.RepeatedPriorBoundsScales

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction.RepeatedPriorBounds
open Filter

def auxiliaryCenter {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ}
    {E : Finset ℕ} (C : InitialSourceChoice d Bs BD Bz k L E) : AuxiliaryIndex k → ℝ
  | .inl i => C.cells.top i
  | .inr ji => C.cells.comp ji.1 ji.2

theorem initial_cell_centers_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      (favorableBlockWidth L/100≤(C.giantCenter:ℝ) ∧ (C.giantCenter:ℝ)≤Real.exp L/2) ∧
      ∀i,favorableBlockWidth L/100≤auxiliaryCenter C i ∧ auxiliaryCenter C i≤Real.exp L/2 := by
  filter_upwards [cell_center_ranges_eventually hk,
    SourceRangeSeparation.broad_range_gaps_eventually k,
    nominalTotals_eventually Bs BD Bz hk] with L hr hg ht
  intro E C hG hGu hc hcu hb hd
  have h0 : 0≤C.blockBase := (Real.exp_pos _).le.trans hG
  have ht := ht C.blockBase C.giantCenter C.bulkBin C.spectatorBin h0 ⟨hc.le,hcu.le⟩ hb hd
  have hwidth : 1000≤favorableBlockWidth L := by linarith [hg.2.1]
  have hp : (1:ℝ)≤2^k := one_le_pow₀ (by norm_num)
  have hw0 : 0≤favorableBlockWidth L := by linarith
  refine ⟨⟨by linarith [hr.2.1],by linarith [hr.2.2.1]⟩,?_⟩
  intro i
  cases i with
  | inl i =>
    have h := C.cells.top_bounds hwidth ht.2.1 i
    change _≤(C.cells.top i:ℝ) ∧ (C.cells.top i:ℝ)≤_
    refine ⟨h.1,h.2.trans ?_⟩
    have hmul := mul_le_mul_of_nonneg_right hp hw0
    linarith [hr.2.2.2.1]
  | inr ji =>
    have h := C.cells.comp_bounds hwidth ji.1 (ht.2.2 ji.1.val ji.1.isLt) ji.2
    exact ⟨h.1,h.2.trans hr.2.2.2.1⟩

end Ostmann.Construction.RepeatedPriorBounds

end

end OAI
