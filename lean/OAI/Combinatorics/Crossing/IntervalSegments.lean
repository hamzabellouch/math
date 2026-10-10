import OAI.Combinatorics.Crossing.DrawingDefinition
import Mathlib.Tactic.Linarith

namespace OAI

namespace Zarankiewicz

def intervalSegment (a b t : unitInterval) : unitInterval :=
  ⟨(1-t.val)*a.val+t.val*b.val,by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) a.property.1)
        (mul_nonneg t.property.1 b.property.1)
    · have h₀ := mul_le_mul_of_nonneg_left a.property.2 (sub_nonneg.mpr t.property.2)
      have h₁ := mul_le_mul_of_nonneg_left b.property.2 t.property.1
      linarith⟩

theorem intervalSegment_between (a b t : unitInterval) (hab : a ≤ b) :
    a ≤ intervalSegment a b t ∧ intervalSegment a b t ≤ b := by
  have hab' : a.val ≤ b.val := hab
  have h₀ := mul_nonneg t.property.1 (sub_nonneg.mpr hab')
  have h₁ := mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr hab')
  change a.val ≤ (1-t.val)*a.val+t.val*b.val ∧ (1-t.val)*a.val+t.val*b.val ≤ b.val
  constructor <;> nlinarith

end Zarankiewicz

end OAI
