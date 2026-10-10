import OAI.GroupTheory.PolycyclicRecognition.Analysis.LinearSupportSymmetries
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportTemplates

namespace OAI

/-! # The finite template-preserving group from the manuscript

Preserving the support exponent of every compact convex template is stronger
than preserving only its values on segments. This file keeps those groups
distinct and proves the required inclusion and finiteness.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]

/-- The group in equation (support-symmetry-group) of `boxes.tex`. -/
def templateSymmetryGroup (D : SupportDatum W I B) : Subgroup (W ≃ₗ[ℝ] W) where
  carrier := {A | ∀ E : Set W, IsCompact E → E.Nonempty → Convex ℝ E →
    D.templateSupport (A '' E) = D.templateSupport E}
  one_mem' := by
    intro E _ _ _
    simp
  mul_mem' := by
    intro A C hA hC E hc hn hv
    have hh := hA (C '' E) (hc.image C.continuous_of_finiteDimensional)
      (hn.image C) (hv.linear_image C.toLinearMap)
    change D.templateSupport ((fun x => A (C x)) '' E) = _
    simpa only [Set.image_image, Function.comp_def] using hh.trans (hC E hc hn hv)
  inv_mem' := by
    intro A hA E hc hn hv
    have hh := hA (A.symm '' E) (hc.image A.symm.continuous_of_finiteDimensional)
      (hn.image A.symm) (hv.linear_image A.symm.toLinearMap)
    change D.templateSupport (A.symm '' E) = _
    simpa only [Set.image_image, Function.comp_def, LinearEquiv.apply_symm_apply,
      Set.image_id'] using hh.symm

/-- Every template symmetry is an isometry of the segment norm. -/
theorem templateSymmetry_mem_linearSupportSymmetry
    (D : SupportDatum W I B) (A : templateSymmetryGroup D) :
    A.val ∈ linearSupportSymmetryGroup D := by
  intro w
  have hc : IsCompact (segment ℝ (0 : W) w) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image ((continuous_const.sub continuous_id).smul continuous_const |>.add
      (continuous_id.smul continuous_const))
  have hn : (segment ℝ (0 : W) w).Nonempty := ⟨0, left_mem_segment ℝ 0 w⟩
  have him : A.val '' segment ℝ (0 : W) w = segment ℝ (0 : W) (A.val w) := by
    change A.val.toLinearMap.toAffineMap '' segment ℝ (0 : W) w = _
    rw [image_segment]
    simp
  have hh := A.property (segment ℝ (0 : W) w) hc hn (convex_segment 0 w)
  rw [him, D.templateSupport_segment, D.templateSupport_segment] at hh
  exact hh

instance finite_templateSymmetryGroup (D : SupportDatum W I B) :
    Finite (templateSymmetryGroup D) := by
  let f : templateSymmetryGroup D → linearSupportSymmetryGroup D :=
    fun A => ⟨A.val, templateSymmetry_mem_linearSupportSymmetry D A⟩
  apply Finite.of_injective f
  intro A C h
  apply Subtype.ext
  exact congrArg (fun x : linearSupportSymmetryGroup D => x.val) h

end PolycyclicRecognition

end

end OAI
