import OAI.Geometry.SurfaceImmersion.Whitney.RelativeImmersionHPrinciple

namespace OAI

/-! Compact relative realization of a constructed smooth formal immersion.
This only removes singularities where an injective formal field is supplied. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing.HPrincipleBridge

/-- A compact formal correction is integrated without changing exterior germs. -/
theorem supported_formal_immersion {f : Plane → Vec} {A : Plane → Plane →L[ℝ] Vec}
    (hf : ContDiff ℝ ∞ f) (hA : ContDiff ℝ ∞ A)
    {K₀ K₁ : Set Plane} (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁)
    (h01 : K₀ ⊆ interior K₁)
    (hs : tsupport (A-fderiv ℝ f) ⊆ interior K₀)
    (hAI : ∀ x ∈ K₁, Function.Injective (A x)) :
    ∃ g : Plane → Vec, ContDiff ℝ ∞ g ∧ tsupport (g-f) ⊆ K₁ ∧
      (∀ x ∈ K₁, Function.Injective (fderiv ℝ g x)) ∧
      (∀ x ∉ interior K₀, g =ᶠ[𝓝 x] f) ∧
      ∀ x ∉ K₁, Function.Injective (fderiv ℝ g x) ↔
        Function.Injective (fderiv ℝ f x) := by
  let L : Landscape Plane :=
    { C := (interior K₀)ᶜ, K₀ := K₀, K₁ := K₁,
      hC := isOpen_interior.isClosed_compl, hK₀ := hK₀, hK₁ := hK₁, h₀₁ := h01 }
  have hcover : L.K₀ ∪ L.C = univ := by
    ext x
    simp only [L, mem_union, mem_compl_iff, mem_univ, iff_true]
    by_cases hx : x ∈ K₀
    · exact Or.inl hx
    · exact Or.inr (fun h => hx (interior_subset h))
  have hhol : ∀ᶠ x in 𝓝ˢ L.C, fderiv ℝ f x = A x := by
    have hC : L.C ⊆ (tsupport (A-fderiv ℝ f))ᶜ := by
      intro x hx hxs
      exact hx (hs hxs)
    have hN : (tsupport (A-fderiv ℝ f))ᶜ ∈ 𝓝ˢ L.C :=
      (isClosed_tsupport _).isOpen_compl.mem_nhdsSet.mpr hC
    filter_upwards [hN] with x hx
    have hz : (A-fderiv ℝ f) x = 0 := image_eq_zero_of_notMem_tsupport hx
    exact (sub_eq_zero.mp hz).symm
  obtain ⟨g,hg,hsupp,_hclose,hgI,hgC⟩ :=
    realize_relative_frame hf hA L hcover hAI hhol (by norm_num : (0:ℝ)<1)
  refine ⟨g,hg,hsupp,hgI,hgC,?_⟩
  intro x hx
  have hxC : x ∉ interior K₀ := by
    intro hi
    exact hx (interior_subset (h01 (interior_subset hi)))
  rw [(hgC x hxC).fderiv_eq]

end ClosedSurfaceR4.FiniteOrderSmoothing.HPrincipleBridge

end

end OAI
