import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellJointReplacementPrior
import OAI.NumberTheory.Ostmann.Construction.InitialSourceChoice
import OAI.NumberTheory.Ostmann.Construction.LogLogPrimeBandSupport

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPriorGrid
open Construction PrimeProgression PrimeCellReplacement
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def bulkLogLower (L : ℝ) : ℝ := Real.exp ((1/250 : ℝ)*L)
def bulkLogUpper (L : ℝ) : ℝ := Real.exp ((3/500 : ℝ)*L)
def bulkPrimeCutoff (L : ℝ) : ℕ := ⌈Real.exp (bulkLogUpper L)⌉₊
def bulkClosedSupport (L : ℝ) : Finset ℕ :=
  logPrimeSupport (bulkPrimeCutoff L) (bulkLogLower L) (bulkLogUpper L)
def bulkBoundary (L : ℝ) : Finset ℕ :=
  (bulkClosedSupport L).filter (fun p => Real.log (p : ℝ) = bulkLogLower L)
def bulkRemoved (L : ℝ) (E : Finset ℕ) : Finset ℕ := E ∪ bulkBoundary L

theorem mem_bulkPrimeBand (L : ℝ) (E : Finset ℕ) (p : ℕ) :
    p ∈ bulkPrimeBand L E ↔ p.Prime ∧ bulkLogLower L < Real.log (p : ℝ) ∧
      Real.log (p : ℝ) ≤ bulkLogUpper L ∧ p ∉ E := by
  rw [bulkPrimeBand, Finset.mem_sdiff, logLogPrimeBand_mem_iff]
  constructor
  · rintro ⟨⟨hp, hlo, hhi⟩, he⟩
    have hlp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
    have h₁ := Real.exp_lt_exp.mpr hlo
    have h₂ := Real.exp_le_exp.mpr hhi
    rw [Real.exp_log hlp] at h₁ h₂
    exact ⟨hp, h₁, h₂, he⟩
  · rintro ⟨hp, hlo, hhi, he⟩
    have hlp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
    have h₁ := Real.log_lt_log (Real.exp_pos ((1/250 : ℝ)*L)) hlo
    have h₂ := Real.log_le_log hlp hhi
    simp only [bulkLogUpper, Real.log_exp] at h₁ h₂
    exact ⟨⟨hp, h₁, h₂⟩, he⟩

theorem mem_bulkClosedSupport (L : ℝ) (p : ℕ) :
    p ∈ bulkClosedSupport L ↔ p.Prime ∧ bulkLogLower L ≤ Real.log (p : ℝ) ∧
      Real.log (p : ℝ) ≤ bulkLogUpper L := by
  rw [bulkClosedSupport, mem_logPrimeSupport]
  constructor
  · exact fun h => h.2
  · rintro ⟨hp, hlo, hhi⟩
    refine ⟨?_, hp, hlo, hhi⟩
    have hu := Real.exp_le_exp.mpr hhi
    rw [Real.exp_log (by exact_mod_cast hp.pos : (0 : ℝ) < p)] at hu
    exact_mod_cast hu.trans (Nat.le_ceil (Real.exp (bulkLogUpper L)))

theorem bulkBoundary_card_le_one (L : ℝ) : (bulkBoundary L).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  have ep := (Finset.mem_filter.mp hp).2
  have eq := (Finset.mem_filter.mp hq).2
  have hpp := (mem_bulkClosedSupport L p).mp (Finset.mem_filter.mp hp).1
  have hqp := (mem_bulkClosedSupport L q).mp (Finset.mem_filter.mp hq).1
  have he := congrArg Real.exp (ep.trans eq.symm)
  rw [Real.exp_log (by exact_mod_cast hpp.1.pos : (0 : ℝ) < p),
    Real.exp_log (by exact_mod_cast hqp.1.pos : (0 : ℝ) < q)] at he
  exact_mod_cast he

theorem bulkRemoved_card_le (L : ℝ) (E : Finset ℕ) :
    (bulkRemoved L E).card ≤ E.card+1 :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add_left (bulkBoundary_card_le_one L) _)

theorem bulkPrimeBand_eq_closed_sdiff (L : ℝ) (E : Finset ℕ) :
    bulkPrimeBand L E = bulkClosedSupport L \ bulkRemoved L E := by
  ext p
  rw [mem_bulkPrimeBand, Finset.mem_sdiff, mem_bulkClosedSupport]
  constructor
  · rintro ⟨hp, hlo, hhi, he⟩
    refine ⟨⟨hp, hlo.le, hhi⟩, ?_⟩
    intro hm
    rcases Finset.mem_union.mp hm with he' | hb
    · exact he he'
    · exact (ne_of_gt hlo) (Finset.mem_filter.mp hb).2
  · rintro ⟨⟨hp, hlo, hhi⟩, hm⟩
    have he : p ∉ E := fun he => hm (Finset.mem_union.mpr (Or.inl he))
    have hn : Real.log (p : ℝ) ≠ bulkLogLower L := by
      intro hz
      apply hm
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨(mem_bulkClosedSupport L p).mpr ⟨hp, hlo, hhi⟩, hz⟩))
    exact ⟨hp, lt_of_le_of_ne hlo hn.symm, hhi, he⟩

theorem bulkPrimeBand_subset_closed (L : ℝ) (E : Finset ℕ) :
    bulkPrimeBand L E ⊆ bulkClosedSupport L := by
  rw [bulkPrimeBand_eq_closed_sdiff]
  exact Finset.sdiff_subset

end Ostmann.Arithmetic.HistoryBulkPriorGrid

end

end OAI
