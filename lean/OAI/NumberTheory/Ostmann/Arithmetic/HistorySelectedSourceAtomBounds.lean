import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationMomentSelected
import OAI.NumberTheory.Ostmann.Construction.SourceRangeSeparationPriors

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedSourceAtomBounds
open Filter Construction CounterpartNormalizationBound RepeatedPriorBounds

theorem initialSourceValue_property {α : Type*} (b k : ℕ) (bulk : α)
    (top : Fin 3 → α) (comp : Fin k → Fin 2 → α) (P : α → Prop)
    (hb : P bulk) (ht : ∀ i, P (top i)) (hc : ∀ j i, P (comp j i)) (q : ℕ) :
    P (initialSourceValue b k bulk top comp q) := by
  unfold initialSourceValue
  split_ifs
  · exact hb
  · exact ht _
  · exact hc _ _
  · exact hb

theorem mass_le_exp_of_log_lower {L mass p : ℝ} (hp : 0 < p)
    (hcap : mass * p ≤ Real.exp L)
    (hlog : Real.exp ((39/10000 : ℝ)*L) ≤ Real.log p) :
    mass ≤ Real.exp (L-Real.exp ((39/10000 : ℝ)*L)) := by
  calc
    mass ≤ Real.exp L / p := (le_div_iff₀ hp).mpr hcap
    _ = Real.exp (L-Real.log p) := by rw [Real.exp_sub, Real.exp_log hp]
    _ ≤ Real.exp (L-Real.exp ((39/10000 : ℝ)*L)) :=
      Real.exp_le_exp.mpr (by linarith)

theorem selected_source_atom_bounds_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20 : ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10 : ℝ)*L) →
      C.blockBase-2 < (C.giantCenter : ℝ) →
      (C.giantCenter : ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin : ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin : ℝ)| ≤ favorableBlockWidth L/16 →
      (∀ q : ℕ, C.sourceNormalization q ≤ Real.exp L) ∧
      (∀ q : ℕ, ∀ p : (C.sources q).Sample, (C.sources q).law.mass p ≠ 0 →
        Real.exp ((39/10000 : ℝ)*L) ≤ Real.log (p : ℕ)) ∧
      (∀ q : ℕ, ∀ p : (C.sources q).Sample,
        (C.sources q).law.mass p ≤ Real.exp (L-Real.exp ((39/10000 : ℝ)*L))) ∧
      (logCellMass C.giantCenter ∅)⁻¹ ≤ Real.exp L ∧
      (∀ p : C.giant.Sample, C.giant.law.mass p ≠ 0 →
        Real.exp ((39/10000 : ℝ)*L) ≤ Real.log (p : ℕ)) ∧
      (∀ p : C.giant.Sample,
        C.giant.law.mass p ≤ Real.exp (L-Real.exp ((39/10000 : ℝ)*L))) := by
  filter_upwards [initial_cell_centers_eventually d Bs BD Bz hk,
    cell_inverse_exp_bound_eventually, bulk_mass_lower_eventually,
    SourceRangeSeparation.broad_range_gaps_eventually k,
    eventually_ge_atTop (1000 : ℝ)] with L hcenters hcell hbulk hgap hL
  intro E C hG hGu hcl hcu hb hd
  have hLpos : 0 < L := by linarith
  have hc := hcenters E C hG hGu hcl hcu hb hd
  have hbulkInv : (harmonicPrimeMass (bulkPrimeBand L E))⁻¹ ≤ Real.exp L := by
    have hi := one_div_le_one_div_of_le (by positivity : 0 < L/(1000 : ℝ))
      (hbulk E C.deleted_card)
    have hi' : (harmonicPrimeMass (bulkPrimeBand L E))⁻¹ ≤ 1000/L := by
      simpa only [one_div, inv_div] using hi
    exact hi'.trans ((div_le_one hLpos).mpr hL |>.trans (Real.one_le_exp hLpos.le))
  have ht (i : Fin 3) : (logCellMass (C.cells.top i) E)⁻¹ ≤ Real.exp L :=
    hcell _ (hc.2 (.inl i)).1 (hc.2 (.inl i)).2 E C.deleted_card
  have ha (j : Fin k) (i : Fin 2) : (logCellMass (C.cells.comp j i) E)⁻¹ ≤ Real.exp L :=
    hcell _ (hc.2 (.inr (j,i))).1 (hc.2 (.inr (j,i))).2 E C.deleted_card
  have hn (q : ℕ) : C.sourceNormalization q ≤ Real.exp L :=
    initialSourceValue_property _ _ _ _ _ (fun x => x ≤ Real.exp L) hbulkInv ht ha q
  have hsmall : Real.exp ((39/10000 : ℝ)*L) ≤ favorableBlockWidth L/200 :=
    (Real.exp_le_exp.mpr (by linarith : (39/10000 : ℝ)*L ≤ (3/500)*L)).trans
      hgap.2.2.2.1.le
  have hlogCell {c p : ℝ} (hcenter : favorableBlockWidth L/100 ≤ c)
      (hs : |Real.log p-c| < 1) : Real.exp ((39/10000 : ℝ)*L) ≤ Real.log p := by
    have hleft := (abs_lt.mp hs).1
    linarith [hgap.2.1]
  have hbLog (p : C.bulk.Sample) (_hp : C.bulk.law.mass p ≠ 0) :
      Real.exp ((39/10000 : ℝ)*L) ≤ Real.log (p : ℕ) :=
    (Real.exp_le_exp.mpr (by linarith : (39/10000 : ℝ)*L ≤ (1/250)*L)).trans
      (harmonicBand_log_support C.bulkPositive p).1
  have htLog (i : Fin 3) (p : (C.cells.topSource E C.deleted_card i).Sample)
      (hp : (C.cells.topSource E C.deleted_card i).law.mass p ≠ 0) :
      Real.exp ((39/10000 : ℝ)*L) ≤ Real.log (p : ℕ) :=
    hlogCell (hc.2 (.inl i)).1 (C.cells.topSource_cell_support E C.deleted_card i p hp)
  have haLog (j : Fin k) (i : Fin 2)
      (p : (C.cells.compSource E C.deleted_card j i).Sample)
      (hp : (C.cells.compSource E C.deleted_card j i).law.mass p ≠ 0) :
      Real.exp ((39/10000 : ℝ)*L) ≤ Real.log (p : ℕ) :=
    hlogCell (hc.2 (.inr (j,i))).1 (C.cells.compSource_cell_support E C.deleted_card j i p hp)
  have hs (q : ℕ) : ∀ p : (C.sources q).Sample, (C.sources q).law.mass p ≠ 0 →
      Real.exp ((39/10000 : ℝ)*L) ≤ Real.log (p : ℕ) :=
    initialSourceValue_property _ _ _ _ _
      (fun S : PrimeSource => ∀ p : S.Sample, S.law.mass p ≠ 0 →
        Real.exp ((39/10000 : ℝ)*L) ≤ Real.log (p : ℕ)) hbLog htLog haLog q
  have hgNorm : (logCellMass C.giantCenter ∅)⁻¹ ≤ Real.exp L :=
    hcell _ hc.1.1 hc.1.2 ∅ (by simp)
  have hgLog (p : C.giant.Sample) (hp : C.giant.law.mass p ≠ 0) :
      Real.exp ((39/10000 : ℝ)*L) ≤ Real.log (p : ℕ) :=
    hlogCell hc.1.1 (logCellPrimeSource_log_support _ ∅ C.giantPositive p hp)
  refine ⟨hn, hs, ?_, hgNorm, hgLog, ?_⟩
  · intro q p
    by_cases hp : (C.sources q).law.mass p = 0
    · rw [hp]; exact (Real.exp_pos _).le
    · exact mass_le_exp_of_log_lower
        (by exact_mod_cast ((C.sources q).prime p.val p.property).pos)
        ((HistoryCompensationMoment.selected_source_mass_mul_le C q p).trans (hn q))
        (hs q p hp)
  · intro p
    by_cases hp : C.giant.law.mass p = 0
    · rw [hp]; exact (Real.exp_pos _).le
    · apply mass_le_exp_of_log_lower
        (by exact_mod_cast (C.giant.prime p.val p.property).pos) _ (hgLog p hp)
      exact (le_div_iff₀ (by exact_mod_cast (C.giant.prime p.val p.property).pos)).mp
        (cell_mass_le C.giantPositive hgNorm p)

end Ostmann.Arithmetic.HistorySelectedSourceAtomBounds

end

end OAI
