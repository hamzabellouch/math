import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.UnitInterval

namespace OAI

/-! Extend a map on the open unit interval by prescribed endpoint
values. Continuity in the interior is independent of endpoint limits. -/
noncomputable section
open Set Topology unitInterval
attribute [local instance] Classical.propDecidable
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*}

def intervalInteriorPoint (t : I) (h0 : t ≠ 0) (h1 : t ≠ 1) : Ioo (0:ℝ) 1 :=
  ⟨t.val,by
    constructor
    · apply lt_of_le_of_ne t.property.1
      intro h
      exact h0 (Subtype.ext h.symm)
    · apply lt_of_le_of_ne t.property.2
      intro h
      exact h1 (Subtype.ext h)⟩

def openIntervalExtension (F : Ioo (0:ℝ) 1 → X) (x y : X) (t : I) : X :=
  if h0 : t = 0 then x else if h1 : t = 1 then y else F (intervalInteriorPoint t h0 h1)

@[simp] lemma openIntervalExtension_zero (F : Ioo (0:ℝ) 1 → X) (x y : X) :
    openIntervalExtension F x y 0 = x := by simp [openIntervalExtension]

@[simp] lemma openIntervalExtension_one (F : Ioo (0:ℝ) 1 → X) (x y : X) :
    openIntervalExtension F x y 1 = y := by simp [openIntervalExtension]

lemma openIntervalExtension_interior (F : Ioo (0:ℝ) 1 → X) (x y : X)
    (t : I) (ht : 0 < (t:ℝ) ∧ (t:ℝ) < 1) :
    openIntervalExtension F x y t = F ⟨t.val,ht⟩ := by
  have h0 : t ≠ 0 := by intro h; subst t; norm_num at ht
  have h1 : t ≠ 1 := by intro h; subst t; norm_num at ht
  simp only [openIntervalExtension,h0,h1,↓reduceDIte]
  rfl

variable [TopologicalSpace X]

lemma openIntervalExtension_continuousOn (F : Ioo (0:ℝ) 1 → X) (hF : Continuous F)
    (x y : X) : ContinuousOn (openIntervalExtension F x y) {t : I | 0 < (t:ℝ) ∧ (t:ℝ) < 1} := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  let k : {t : I | 0 < (t:ℝ) ∧ (t:ℝ) < 1} → Ioo (0:ℝ) 1 :=
    fun t => ⟨t.val.val,t.property⟩
  have hk : Continuous k :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have he : {t : I | 0 < (t:ℝ) ∧ (t:ℝ) < 1}.domRestrict (openIntervalExtension F x y) = F ∘ k := by
    funext t
    exact openIntervalExtension_interior F x y t.val t.property
  rw [he]
  exact hF.comp hk

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
