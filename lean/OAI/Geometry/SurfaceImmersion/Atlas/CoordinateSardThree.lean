import OAI.Geometry.SurfaceImmersion.Geometry.PublishedInputs
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace OAI

/-! The exact three-dimensional coordinate Sard and regular-fiber facts
needed for generic projections of a surface from four-space to three-space. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PublishedInputs

abbrev SurfaceDirectionParameters := (Fin 2 → ℝ) × ℝ

theorem smooth_coordinate_critical_values_null
    (f : SurfaceDirectionParameters → ThreeSpace)
    (U : Set SurfaceDirectionParameters) (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    volume (f '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  have : ContinuousSMul ℝ SurfaceDirectionParameters := Prod.continuousSMul
  let L : ThreeSpace ≃L[ℝ] SurfaceDirectionParameters :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let C : Set SurfaceDirectionParameters :=
    {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}
  let g : ThreeSpace → ThreeSpace := f ∘ L
  have hg (x : ThreeSpace) (hx : L x ∈ U) :
      HasFDerivAt g ((fderiv ℝ f (L x)).comp L.toContinuousLinearMap) x :=
    ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.comp x
      L.hasFDerivAt
  have hnull : volume (g '' (L ⁻¹' C)) = 0 := by
    apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun x => (fderiv ℝ f (L x)).comp L.toContinuousLinearMap)
    · intro x hx
      exact (hg x hx.1).hasFDerivWithinAt
    · intro x hx
      rw [LinearMap.det_eq_zero_iff_ker_ne_bot,ne_eq,LinearMap.ker_eq_bot]
      intro hinj
      have hsurj := LinearMap.injective_iff_surjective.mp hinj
      apply hx.2
      intro y
      obtain ⟨z,hz⟩ := hsurj y
      exact ⟨L z,hz⟩
  have he : g '' (L ⁻¹' C) = f '' C := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨L x,hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨L.symm x,by simpa using hx,by simp [g]⟩
  rwa [he] at hnull

lemma regular_coordinate_point_locally_injective
    {f : SurfaceDirectionParameters → ThreeSpace}
    {U : Set SurfaceDirectionParameters} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {x : SurfaceDirectionParameters} (hx : x ∈ U)
    (hreg : Function.Surjective (fderiv ℝ f x)) :
    ∃ V : Set SurfaceDirectionParameters, IsOpen V ∧ x ∈ V ∧ V.InjOn f := by
  have : ContinuousSMul ℝ SurfaceDirectionParameters := Prod.continuousSMul
  have hdim : Module.finrank ℝ SurfaceDirectionParameters = Module.finrank ℝ ThreeSpace := by simp
  have hinj : Function.Injective (fderiv ℝ f x) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hreg
  let L : SurfaceDirectionParameters ≃L[ℝ] ThreeSpace :=
    ContinuousLinearEquiv.ofBijective (fderiv ℝ f x)
      (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hreg)
  have hfx : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hU.mem_nhds hx)
  have hd : HasFDerivAt f L.toContinuousLinearMap x :=
    (hfx.differentiableAt (by simp)).hasFDerivAt
  let e := hfx.toOpenPartialHomeomorph f hd (by simp)
  exact ⟨e.source,e.open_source,hfx.mem_toOpenPartialHomeomorph_source hd (by simp),e.injOn⟩

theorem finite_compact_coordinate_regular_fiber
    {f : SurfaceDirectionParameters → ThreeSpace}
    {U : Set SurfaceDirectionParameters} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {K : Set SurfaceDirectionParameters} (hK : IsCompact K) (hKU : K ⊆ U) (y : ThreeSpace)
    (hreg : ∀ x ∈ K, f x = y → Function.Surjective (fderiv ℝ f x)) :
    (K ∩ {x | f x = y}).Finite := by
  have hcompact : IsCompact (K ∩ {x | f x = y}) :=
    hK.of_isClosed_subset
      ((hf.continuousOn.mono hKU).preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton)
      inter_subset_left
  apply hcompact.finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  obtain ⟨V,hV,hxV,hVinj⟩ := regular_coordinate_point_locally_injective hU hf
    (hKU hx.1) (hreg x hx.1 hx.2)
  refine ⟨V,hV,?_⟩
  ext z
  constructor
  · rintro ⟨hzV,hzK,hzy⟩
    exact mem_singleton_iff.mpr (hVinj hzV hxV (hzy.trans hx.2.symm))
  · rintro rfl
    exact ⟨hxV,hx⟩

end ClosedSurfaceR4.PublishedInputs

end

end OAI
