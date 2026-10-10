import Mathlib

namespace OAI

open Set MeasureTheory
namespace BorsukNine
section Sard
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma exists_regular_value (f : E → E) (hf : Differentiable ℝ f)
    {U : Set E} (hU : IsOpen U) (hUn : U.Nonempty) :
    ∃ y ∈ U, ∀ x, f x = y → (fderiv ℝ f x).det ≠ 0 := by
  let μ := (Module.finBasis ℝ E).addHaar
  let C : Set E := {x | (fderiv ℝ f x).det = 0}
  have hz : μ (f '' C) = 0 := addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    (fun x _ => (hf x).hasFDerivAt.hasFDerivWithinAt) (fun _ h => h)
  have hUp : 0 < μ U := hU.measure_pos μ hUn
  have hns : ¬ U ⊆ f '' C := by
    intro hs
    have hh : μ U ≤ μ (f '' C) := measure_mono hs
    rw [hz] at hh
    exact (not_le_of_gt hUp) hh
  obtain ⟨y,hy,hny⟩ := Set.not_subset.mp hns
  refine ⟨y,hy,?_⟩
  intro x hx hc
  exact hny ⟨x,hc,hx⟩

omit [MeasurableSpace E] [BorelSpace E] in
lemma compact_regular_level_finite (f : E → E) (hf : ContDiff ℝ 1 f) {y : E}
    {K : Set E} (hc : IsCompact K) (hK : ∀ x ∈ K, f x = y) (hr : ∀ x, f x = y → (fderiv ℝ f x).det ≠ 0) :
    K.Finite := by
  apply hc.finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  have hdet := hr x (hK x hx)
  let e : E ≃L[ℝ] E := (LinearMap.equivOfIsUnitDet
    (f := (fderiv ℝ f x).toLinearMap) (isUnit_iff_ne_zero.mpr hdet)).toContinuousLinearEquiv
  have he : e.toContinuousLinearMap = fderiv ℝ f x := by
    ext z
    exact LinearMap.equivOfIsUnitDet_apply _ z
  have hd : HasStrictFDerivAt f e.toContinuousLinearMap x := by
    rw [he]
    exact hf.hasStrictFDerivAt one_ne_zero
  let p := hd.toOpenPartialHomeomorph f
  refine ⟨p.source, p.open_source,?_⟩
  ext z
  constructor
  · intro hz
    exact Set.mem_singleton_iff.mpr (p.injOn hz.1 hd.mem_toOpenPartialHomeomorph_source
      ((hK z hz.2).trans (hK x hx).symm))
  · rintro rfl
    exact ⟨hd.mem_toOpenPartialHomeomorph_source,hx⟩
end Sard
end BorsukNine

end OAI
