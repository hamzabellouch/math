import OAI.Geometry.EinsteinFour.CP2UnitGeometry

namespace OAI

/-! Unit representatives with nonnegative real overlap, including orthogonal pairs. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

theorem cp2_aligned_unit_representative (p q : ComplexProjective2) :
    ∃ v : CP2Vector, ∃ hv : v ≠ 0, ‖v‖ = 1 ∧ Projectivization.mk ℂ v hv = q ∧
      inner ℂ (cp2UnitRep p) v = (cp2Overlap p q : ℂ) := by
  by_cases hpos : 0 < cp2Overlap p q
  · exact cp2_unit_aligned p q hpos
  have hz : cp2Overlap p q = 0 := le_antisymm (le_of_not_gt hpos) (cp2Overlap_nonneg p q)
  refine ⟨cp2UnitRep q,cp2UnitRep_ne_zero q,cp2UnitRep_norm q,cp2UnitRep_mk q,?_⟩
  have hi : inner ℂ (cp2UnitRep p) (cp2UnitRep q) = 0 := norm_eq_zero.mp hz
  rw [hi,hz,Complex.ofReal_zero]

end
end PositiveEinsteinFour.Geometry

end OAI
