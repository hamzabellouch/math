import OAI.NumberTheory.Ostmann.Arithmetic.ResidueIntervals
import OAI.NumberTheory.Ostmann.Arithmetic.CRTLineAverage

namespace OAI

/-! # Natural residue representatives and the Haar unit averages used by CRT -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def unitReducedResidueEquiv (q : ℕ) [NeZero q] :
    (ZMod q)ˣ ≃ {a : ℕ // a ∈ reducedResidues q} where
  toFun u := ⟨(u : ZMod q).val, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (ZMod.val_lt _), ZMod.val_coe_unit_coprime u⟩⟩
  invFun a := ZMod.unitOfCoprime a.val (Finset.mem_filter.mp a.property).2
  left_inv u := Units.ext (ZMod.natCast_zmod_val _)
  right_inv a := by
    apply Subtype.ext
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp a.property).1)

theorem sum_reducedResidues_eq_units (q : ℕ) [NeZero q] (f : ℕ → ℂ) :
    (∑ a ∈ reducedResidues q, f a) = ∑ a : (ZMod q)ˣ, f (a : ZMod q).val := by
  rw [← Finset.sum_coe_sort]
  exact ((unitReducedResidueEquiv q).sum_comp (fun a => f a.val)).symm

theorem sum_range_eq_zmod (q : ℕ) [NeZero q] (f : ℕ → ℂ) :
    (∑ a ∈ Finset.range q, f a) = ∑ a : ZMod q, f a.val := by
  rw [← Fin.sum_univ_eq_sum_range]
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q => rfl

end Ostmann

end OAI
