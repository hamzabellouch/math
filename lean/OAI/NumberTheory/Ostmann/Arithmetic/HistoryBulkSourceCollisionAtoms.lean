import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPriorGridMass
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedSourceAtomBounds

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSourceCollision
open Construction RepeatedPriorBounds HistoryBulkPriorGrid Filter

theorem bulk_mass_le_pointCap (L : ℝ) (E : Finset ℕ)
    (hZ : 0 < harmonicPrimeMass (bulkPrimeBand L E))
    (p : (bulkPrimeSource L E hZ).Sample) :
    (bulkPrimeSource L E hZ).law.mass p ≤ bulkPointCap L E := by
  rw [bulkSource_mass]
  apply bulkWeight_le_pointCap L E hZ
  have hp := (mem_bulkPrimeBand L E p.val).mp p.property
  exact (mem_bulkClosedSupport L p.val).mpr ⟨hp.1,hp.2.1.le,hp.2.2.1⟩

theorem bulk_atom_bound_eventually :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ), E.card ≤ 2 →
      ∀ (hZ : 0 < harmonicPrimeMass (bulkPrimeBand L E)),
      ∀ p : (bulkPrimeSource L E hZ).Sample,
      (bulkPrimeSource L E hZ).law.mass p ≤ Real.exp (L-Real.exp ((39/10000 : ℝ)*L)) := by
  filter_upwards [bulk_mass_lower_eventually, eventually_ge_atTop (1000:ℝ)] with L hmass hL
  intro E hE hZ p
  have hLpos : 0 < L := by linarith
  have hi : (bulkNormalizer L E)⁻¹ ≤ Real.exp L := by
    have h := one_div_le_one_div_of_le (by positivity : 0 < L/(1000:ℝ)) (hmass E hE)
    have h' : (bulkNormalizer L E)⁻¹ ≤ 1000/L := by
      simpa only [bulkNormalizer, one_div, inv_div] using h
    exact h'.trans ((div_le_one hLpos).mpr hL |>.trans (Real.one_le_exp hLpos.le))
  apply (bulk_mass_le_pointCap L E hZ p).trans
  calc
    bulkPointCap L E ≤ Real.exp (-bulkLogLower L)*Real.exp L := by
      unfold bulkPointCap
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hi (Real.exp_nonneg _)
    _ ≤ Real.exp (L-Real.exp ((39/10000:ℝ)*L)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh : Real.exp ((39/10000:ℝ)*L) ≤ bulkLogLower L :=
        Real.exp_le_exp.mpr (by nlinarith)
      linarith

end Ostmann.Arithmetic.HistoryBulkSourceCollision

end

end OAI
