import OAI.GroupTheory.PolycyclicRecognition.Algebra.TemplateSymmetries

namespace OAI

/-! # Removing the choice of origin from template comparison -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open Set

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (P : PolycyclicRecognition.SupportDatum W I B)

/-- Translation invariance extends the comparison for templates containing
zero to every nonempty compact convex template. -/
theorem templateSupport_le_of_zero_mem (A : W →L[ℝ] W)
    (h : ∀ C : Set W, IsCompact C → Convex ℝ C → (0 : W) ∈ C →
      P.templateSupport C ≤ P.templateSupport (A '' C))
    (C : Set W) (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C) :
    P.templateSupport C ≤ P.templateSupport (A '' C) := by
  obtain ⟨x, hx⟩ := hne
  let D := (fun y => y + -x) '' C
  have hD : IsCompact D := hC.image (continuous_id.add_const _)
  have hDv : Convex ℝ D := by
    simpa only [add_comm] using hconv.translate (-x)
  have hD0 : (0 : W) ∈ D := ⟨x, hx, add_neg_cancel x⟩
  have hle := h D hD hDv hD0
  have hne : C.Nonempty := ⟨x, hx⟩
  have hPD : P.templateSupport D = P.templateSupport C :=
    P.templateSupport_translate hC hne (-x)
  have himage : A '' D = (fun y => y + -(A x)) '' (A '' C) := by
    simp only [D, image_image, map_add, map_neg]
  rw [hPD, himage, P.templateSupport_translate (hC.image A.continuous) (hne.image A)] at hle
  exact hle

/-- Forward and inverse comparisons force preservation of the full
template functional, using only comparisons for templates through zero. -/
theorem template_symmetry_of_zero_mem_comparisons (A : W ≃L[ℝ] W)
    (hf : ∀ C : Set W, IsCompact C → Convex ℝ C → (0 : W) ∈ C →
      P.templateSupport C ≤ P.templateSupport (A '' C))
    (hi : ∀ C : Set W, IsCompact C → Convex ℝ C → (0 : W) ∈ C →
      P.templateSupport C ≤ P.templateSupport (A.symm '' C)) :
    A.toLinearEquiv ∈ templateSymmetryGroup P := by
  intro C hc hn hv
  have hf' := P.templateSupport_le_of_zero_mem A.toContinuousLinearMap hf C hc hn hv
  have hi' := P.templateSupport_le_of_zero_mem A.symm.toContinuousLinearMap hi
    (A '' C) (hc.image A.continuous) (hn.image A) (hv.linear_image A.toLinearMap)
  have he : A.symm '' (A '' C) = C := by
    simp only [image_image, ContinuousLinearEquiv.symm_apply_apply, image_id']
  change P.templateSupport (A '' C) ≤ P.templateSupport (A.symm '' (A '' C)) at hi'
  rw [he] at hi'
  exact le_antisymm hi' hf'

end PolycyclicRecognition.SupportDatum

end

end OAI
