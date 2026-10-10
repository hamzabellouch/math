import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightCounts
import OAI.NumberTheory.Ostmann.Construction.SourceAssignmentSupportCells
import OAI.NumberTheory.Ostmann.Construction.SourceRangeSeparation

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Conclusion
open Filter
open Ostmann.Construction

theorem initial_source_regular_ranges_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀ l≤k, ∀ x : SourceAssignment C.sources
        (Template.current (Template.initial (2*(bulkSize k L/2)) k) l),
      (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)).mass x≠0 →
      let small := assignedSlots C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) x
      (small.length:ℝ)≤Real.exp ((1/1000:ℝ)*L) ∧
      ∀ z∈small, Real.exp ((1/250:ℝ)*L)≤Real.log (z.value:ℝ) ∧
        Real.log (z.value:ℝ)≤Real.exp ((11/1000:ℝ)*L) := by
  have hlen : ∀ᶠ L : ℝ in atTop,
      (2:ℝ)^k*(bulkScale k*L+6+4*k)≤Real.exp ((1/1000:ℝ)*L) := by
    have hh := (tendsto_exp_mul_div_rpow_atTop 1 (1/1000) (by norm_num)).eventually_ge_atTop
      ((2:ℝ)^k*(bulkScale k+6+4*k))
    filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with L h hL
    simp only [Real.rpow_one] at h
    have hLp : 0<L := by linarith
    have hh := (le_div_iff₀ hLp).mp h
    have hpow : 0≤(2:ℝ)^k := by positivity
    nlinarith [mul_nonneg hpow (show 0≤(6+4*(k:ℝ))*(L-1) by positivity)]
  filter_upwards [nominalTotals_eventually Bs BD Bz hk,
    SourceRangeSeparation.broad_range_gaps_eventually k,hlen,
    (exp_mul_tendsto (by norm_num : (0:ℝ)<1/1000)).eventually_ge_atTop (3*(2:ℝ)^k)]
    with L htotal hgap hlen hupper
  intro E C hGlo hclo hchi htb htd l hl x hx
  have hG : 0≤C.blockBase := (Real.exp_pos _).le.trans hGlo
  have hc := htotal C.blockBase C.giantCenter C.bulkBin C.spectatorBin hG ⟨hclo.le,hchi.le⟩ htb htd
  have haux : ∀ i, ∀ p : (C.auxiliary i).Sample, (C.auxiliary i).law.mass p≠0 →
      Real.exp ((1/250:ℝ)*L)≤Real.log (p:ℕ) ∧ Real.log (p:ℕ)≤Real.exp ((11/1000:ℝ)*L) := by
    intro i p hp
    have ha := C.cells.auxSource_log_bounds (by linarith [hgap.2.1]) hc.2.1
      (fun j => hc.2.2 j.val j.isLt) E C.deleted_card i p hp
    have hb : Real.exp ((1/250:ℝ)*L)≤favorableBlockWidth L/200 :=
      (Real.exp_le_exp.mpr (by nlinarith [hgap.1])).trans hgap.2.2.2.1.le
    have hu := mul_le_mul_of_nonneg_right hupper (Real.exp_pos ((1/100:ℝ)*L)).le
    rw [←Real.exp_add,show (1/1000:ℝ)*L+(1/100)*L=(11/1000)*L by ring] at hu
    exact ⟨hb.trans ha.1,ha.2.trans hu⟩
  have hsource : ∀ origin<2*(bulkSize k L/2)+6+4*k, ∀ p : (C.sources origin).Sample,
      (C.sources origin).law.mass p≠0 →
      Real.exp ((1/250:ℝ)*L)≤Real.log (p:ℕ) ∧ Real.log (p:ℕ)≤Real.exp ((11/1000:ℝ)*L) := by
    intro origin horigin
    by_cases hb : origin<2*(bulkSize k L/2)
    · have heq : C.sources origin=C.bulk := initialSourceValue_bulk _ _ _ _ _ hb
      rw [heq]
      intro p hp
      have hh := harmonicBand_log_support C.bulkPositive p
      exact ⟨hh.1,hh.2.trans (Real.exp_le_exp.mpr (by nlinarith [hgap.1]))⟩
    · have hh := initialSourceValue_rel_nonbulk (bulkSize k L/2) k C.bulk ()
        (C.cells.topSource E C.deleted_card) (fun _ => ())
        (C.cells.compSource E C.deleted_card) (fun _ _ => ())
        (fun (S : PrimeSource) (_ : Unit) => ∀p:S.Sample,S.law.mass p≠0 →
          Real.exp ((1/250:ℝ)*L)≤Real.log (p:ℕ) ∧ Real.log (p:ℕ)≤Real.exp ((11/1000:ℝ)*L))
        (fun i => haux (Sum.inl i)) (fun j i => haux (Sum.inr (j,i)))
        origin (by omega) horigin
      exact hh
  constructor
  · rw [assignedSlots_length]
    have hn := Arithmetic.HistorySymbolicEncoding.template_current_length_le
      (Template.initial (2*(bulkSize k L/2)) k) l
    have hseed : (Template.initial (2*(bulkSize k L/2)) k).length=2*(bulkSize k L/2)+6+4*k := by
      simp [Template.initial,InitialCoordinatesTemplate.initialRoles_length]
    rw [hseed] at hn
    have hn' : ((Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length:ℝ)≤
        (2:ℝ)^k*((bulkSize k L:ℝ)+6+4*k) := by
      exact_mod_cast hn.trans (Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hl)
        (by omega : 2*(bulkSize k L/2)+6+4*k≤bulkSize k L+6+4*k))
    exact hn'.trans ((mul_le_mul_of_nonneg_left (by linarith [(bulkSize_bounds k hgap.1.le).2])
      (by positivity : 0≤(2:ℝ)^k)).trans hlen)
  · intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    have hs := Template.mem_current_mem_seed
      (List.getElem_mem (l := Template.current (Template.initial (2*(bulkSize k L/2)) k) l) i.isLt)
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hs
    have ho : (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)[i].origin <
        2*(bulkSize k L/2)+6+4*k := by
      have he := congrArg SourceSlot.origin hj
      change j.val=(Template.current (Template.initial (2*(bulkSize k L/2)) k) l)[i].origin at he
      rw [←he]
      simpa only [InitialCoordinatesTemplate.initialRoles_length] using j.isLt
    exact hsource _ ho (x i) (assignmentPrior_component_mass_ne_zero C.sources _ x hx i)

end Ostmann.Conclusion

end

end OAI
