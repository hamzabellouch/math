import OAI.Geometry.SurfaceImmersion.Whitney.SupportedFormalImmersion
import OAI.Geometry.SurfaceImmersion.Geometry.C1ImmersionJets
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs

namespace OAI

/-! A continuous compact relative frame can be smoothed while retaining
injectivity and the exact prescribed derivative near its exterior. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing.HPrincipleBridge

theorem smooth_relative_frame {f : Plane → Vec} {A : Plane → Plane →L[ℝ] Vec}
    (hf : ContDiff ℝ ∞ f) (hA : Continuous A)
    {K₀ K₁ : Set Plane} (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁)
    (hs : tsupport (A-fderiv ℝ f) ⊆ interior K₀)
    (hAI : ∀ x ∈ K₁, Function.Injective (A x)) :
    ∃ B : Plane → Plane →L[ℝ] Vec, ContDiff ℝ ∞ B ∧
      tsupport (B-fderiv ℝ f) ⊆ interior K₀ ∧
      ∀ x ∈ K₁, Function.Injective (B x) := by
  let S := tsupport (A-fderiv ℝ f)
  have hS : IsCompact S := hK₀.of_isClosed_subset (isClosed_tsupport _)
    (hs.trans interior_subset)
  obtain ⟨U,hU,hSU,_hUc,hUK⟩ :=
    CollarVelocity.compact_open_thickening hS isOpen_interior hs
  have hclosed : IsClosed Uᶜ := hU.isClosed_compl
  have hEq : EqOn A (fderiv ℝ f) Sᶜ := by
    intro x hx
    have hz : (A-fderiv ℝ f) x = 0 := image_eq_zero_of_notMem_tsupport hx
    exact sub_eq_zero.mp hz
  have hSopen : IsOpen Sᶜ := (isClosed_tsupport _).isOpen_compl
  have hDS : ContDiffOn ℝ ∞ A Sᶜ :=
    (hf.fderiv_right (m := ∞) (by simp)).contDiffOn.congr hEq
  have hC : Sᶜ ∈ 𝓝ˢ Uᶜ := hSopen.mem_nhdsSet.mpr (compl_subset_compl.mpr hSU)
  obtain ⟨ε,hε,hεI⟩ := compact_injective_stability (hK₁.image hA)
    (by rintro _ ⟨x,hx,rfl⟩; exact hAI x hx)
  obtain ⟨B,hB,hBA,hBEq⟩ := exists_smooth_and_eqOn hA continuous_const
    (fun _ => hε) hclosed ⟨Sᶜ,hC,hDS⟩
  refine ⟨B,hB,?_,?_⟩
  · apply (closure_minimal (s := Function.support (B-fderiv ℝ f))
      (t := closure U) ?_ isClosed_closure).trans hUK
    intro x hx
    apply subset_closure
    by_contra hxu
    have hAs : A x = fderiv ℝ f x := hEq (fun h => hxu (hSU h))
    exact hx (by simp only [Pi.sub_apply,hBEq hxu,hAs,sub_self])
  · intro x hx
    apply hεI (A x) ⟨x,hx,rfl⟩ (B x)
    simpa only [dist_eq_norm] using hBA x

/-- The formal field in the relative h-principle may be merely continuous;
its exact exterior equality is retained in the smooth realization. -/
theorem realize_continuous_relative_frame {f : Plane → Vec}
    {A : Plane → Plane →L[ℝ] Vec} (hf : ContDiff ℝ ∞ f) (hA : Continuous A)
    {K₀ K₁ : Set Plane} (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁)
    (h01 : K₀ ⊆ interior K₁)
    (hs : tsupport (A-fderiv ℝ f) ⊆ interior K₀)
    (hAI : ∀ x ∈ K₁, Function.Injective (A x)) :
    ∃ g : Plane → Vec, ContDiff ℝ ∞ g ∧ tsupport (g-f) ⊆ K₁ ∧
      (∀ x ∈ K₁, Function.Injective (fderiv ℝ g x)) ∧
      (∀ x ∉ interior K₀, g =ᶠ[𝓝 x] f) ∧
      ∀ x ∉ K₁, Function.Injective (fderiv ℝ g x) ↔
        Function.Injective (fderiv ℝ f x) := by
  obtain ⟨B,hB,hBs,hBI⟩ := smooth_relative_frame hf hA hK₀ hK₁ hs hAI
  exact supported_formal_immersion hf hB hK₀ hK₁ h01 hBs hBI

end ClosedSurfaceR4.FiniteOrderSmoothing.HPrincipleBridge

end

end OAI
