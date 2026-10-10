import OAI.NumberTheory.Ostmann.Construction.SourceRangeSeparationPriors
import OAI.NumberTheory.Ostmann.Construction.SourceRangeSeparationScales

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter

namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}

structure CrossRoleSeparation (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource) : Prop where
  spectator_bulk : spectator.DisjointMass C.bulk
  spectator_giant : spectator.DisjointMass C.giant
  spectator_aux : ∀ i, spectator.DisjointMass (C.auxiliary i)
  bulk_giant : C.bulk.DisjointMass C.giant
  bulk_aux : ∀ i, C.bulk.DisjointMass (C.auxiliary i)
  giant_aux : ∀ i, C.giant.DisjointMass (C.auxiliary i)
  top_comp : ∀ i j r, (C.auxiliary (Sum.inl i)).DisjointMass (C.auxiliary (Sum.inr (j,r)))
  comp_comp : ∀ a b, a≠b → ∀ i r,
    (C.auxiliary (Sum.inr (a,i))).DisjointMass (C.auxiliary (Sum.inr (b,r)))

end InitialSourceChoice

theorem initial_source_cross_role_separation_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀ spectator : PrimeSource,
        (∀p : spectator.Sample, Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
          Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
        C.CrossRoleSeparation spectator := by
  filter_upwards [SourceRangeSeparation.broad_range_gaps_eventually k,
    nominalTotals_eventually Bs BD Bz hk,
    nominalCompensation_relative_eventually Bs BD Bz hk (by norm_num : (0:ℝ)<1/100)] with L hgap htotal hrelative
  intro E C hGlo hclo hchi htb htd spectator hspec
  let J := nominalJ Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin
  have hG : 0≤C.blockBase := (Real.exp_pos _).le.trans hGlo
  have hcenters := htotal C.blockBase C.giantCenter C.bulkBin C.spectatorBin hG ⟨hclo.le,hchi.le⟩ htb htd
  have hwidth : 4000≤favorableBlockWidth L := hgap.2.1
  have hh : 1000≤favorableBlockWidth L := by linarith
  have hJ : 1000≤J := by dsimp only [J]; linarith [hcenters.1.1]
  have hhJ : favorableBlockWidth L≤2*J := by dsimp only [J]; linarith [hcenters.1.1]
  have hw : ∀ j : Fin k, |nominalCompensation Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin j-
      (2:ℝ)^(k-1-j.val)*J|≤J/100 := by
    intro j
    simpa only [J,one_div,div_eq_mul_inv,one_mul,mul_comm] using
      hrelative C.blockBase C.giantCenter C.spectatorBin hG ⟨hclo.le,hchi.le⟩ htd j.val j.isLt
  have hbulk : ∀ p : C.bulk.Sample, Real.exp ((1/250:ℝ)*L)≤Real.log (p:ℕ) ∧
      Real.log (p:ℕ)≤Real.exp ((3/500:ℝ)*L) := harmonicBand_log_support C.bulkPositive
  have haux : ∀ i, ∀ p : (C.auxiliary i).Sample, (C.auxiliary i).law.mass p≠0 →
      favorableBlockWidth L/200≤Real.log (p:ℕ) ∧ Real.log (p:ℕ)≤3*(2:ℝ)^k*favorableBlockWidth L := by
    intro i p hp
    exact C.cells.auxSource_log_bounds hh hcenters.2.1 (fun j => hcenters.2.2 j.val j.isLt)
      E C.deleted_card i p hp
  have hgiant : ∀ p : C.giant.Sample, C.giant.law.mass p≠0 →
      Real.exp ((1/20:ℝ)*L)-3<Real.log (p:ℕ) := by
    intro p hp
    have he := (abs_lt.mp (logCellPrimeSource_log_support C.giantCenter ∅ C.giantPositive p hp)).1
    linarith
  have hspbulk := hgap.2.2.1
  have hbulkaux := hgap.2.2.2.1
  have hauxgiant := hgap.2.2.2.2
  have hbb : Real.exp ((1/250:ℝ)*L)≤Real.exp ((3/500:ℝ)*L) :=
    Real.exp_le_exp.mpr (by nlinarith [hgap.1])
  have hmiddle : favorableBlockWidth L/200≤3*(2:ℝ)^k*favorableBlockWidth L := by
    have hp : (1:ℝ)≤2^k := one_le_pow₀ (by norm_num)
    have hn : 0≤favorableBlockWidth L := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hp hn]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · apply PrimeSource.disjointMass_of_log_lt
    intro p q hp hq
    exact (hspec p).2.trans_lt (hspbulk.trans_le (hbulk q).1)
  · apply PrimeSource.disjointMass_of_log_lt
    intro p q hp hq
    exact (hspec p).2.trans_lt (hspbulk.trans_le hbb |>.trans hbulkaux |>.trans_le hmiddle |>.trans hauxgiant |>.trans (hgiant q hq))
  · intro i
    apply PrimeSource.disjointMass_of_log_lt
    intro p q hp hq
    exact (hspec p).2.trans_lt (hspbulk.trans_le hbb |>.trans hbulkaux |>.trans_le (haux i q hq).1)
  · apply PrimeSource.disjointMass_of_log_lt
    intro p q hp hq
    exact (hbulk p).2.trans_lt (hbulkaux.trans_le hmiddle |>.trans hauxgiant |>.trans (hgiant q hq))
  · intro i
    apply PrimeSource.disjointMass_of_log_lt
    intro p q hp hq
    exact (hbulk p).2.trans_lt (hbulkaux.trans_le (haux i q hq).1)
  · intro i
    apply PrimeSource.DisjointMass.symm
    apply PrimeSource.disjointMass_of_log_lt
    intro p q hp hq
    exact (haux i p hp).2.trans_lt (hauxgiant.trans (hgiant q hq))
  · intro i j r
    exact C.cells.topSource_compSource_disjoint hh hJ hhJ htb hw E C.deleted_card i j r
  · intro a b hab i r
    exact C.cells.compSource_compSource_disjoint hh hJ hhJ hw E C.deleted_card a b hab i r

end Ostmann.Construction

end

end OAI
