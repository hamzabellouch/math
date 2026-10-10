import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapFormalPair
import OAI.Geometry.SurfaceImmersion.Whitney.SurfaceFormalImmersion

namespace OAI

/-! Actual supported cancellation of the two singularities on a crosscap
connecting arc, obtained from the constructed relative differential. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem cancel_crosscap_pair {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {p q : M} (A : CrosscapConnectingArc f p q) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      (∀ x, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x) ↔
        x = p ∨ x = q ∨ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)) ∧
      ∀ x, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x) →
        x ≠ p → x ≠ q → g =ᶠ[𝓝 x] f := by
  obtain ⟨S⟩ := exists_crosscap_coordinate_strip hf A
  obtain ⟨V,B,K,hV,hVD,hAV,hB,hK,hKV,hBs,hBI,hregV⟩ := S.formal_pair hf
  let Z := crosscapAxis '' Icc A.arc.start A.arc.finish
  have hZ : IsCompact Z := isCompact_Icc.image crosscapAxis.continuous
  have hZV : Z ⊆ V := by rintro x ⟨t,ht,rfl⟩; exact hAV t ht
  obtain ⟨U₀,hU₀,hKU₀,hK₀,hK₀V⟩ :=
    CollarVelocity.compact_open_thickening (hK.union hZ) hV (union_subset hKV hZV)
  obtain ⟨U₁,hU₁,hK₀U₁,hK₁,hK₁V⟩ := CollarVelocity.compact_open_thickening hK₀ hV hK₀V
  have hU₀i : U₀ ⊆ interior (closure U₀) := hU₀.subset_interior_iff.mpr subset_closure
  have hU₁i : U₁ ⊆ interior (closure U₁) := hU₁.subset_interior_iff.mpr subset_closure
  have h01 : closure U₀ ⊆ interior (closure U₁) := hK₀U₁.trans hU₁i
  have hsup : tsupport (B-fderiv ℝ S.model) ⊆ interior (closure U₀) :=
    hBs.trans ((subset_union_left.trans hKU₀).trans hU₀i)
  obtain ⟨g,hg,hout,hIg⟩ := surface_formal_immersion S.chart S.chart_smooth S.inverse_smooth hf
    S.model_smooth S.domain_open S.domain_target S.model_eq hB hK₀ hK₁ h01
    (hK₁V.trans hVD) hsup (fun x hx => hBI x (hK₁V hx))
  have hrec : ∀ t ∈ Icc A.arc.start A.arc.finish,
      S.chart.symm (crosscapAxis t) = A.arc.curve t := by
    intro t ht
    rw [crosscapAxis_apply,←(S.axis t ht).2,S.chart.left_inv (S.axis t ht).1]
  have hzK : Z ⊆ closure U₁ :=
    ((subset_union_right.trans hKU₀).trans subset_closure).trans (h01.trans interior_subset)
  have hpimage : p ∈ S.chart.symm '' closure U₁ := by
    refine ⟨crosscapAxis A.arc.start,hzK ⟨A.arc.start,left_mem_Icc.mpr A.arc.start_lt_finish.le,rfl⟩,?_⟩
    rw [hrec _ (left_mem_Icc.mpr A.arc.start_lt_finish.le),A.source]
  have hqimage : q ∈ S.chart.symm '' closure U₁ := by
    refine ⟨crosscapAxis A.arc.finish,hzK ⟨A.arc.finish,right_mem_Icc.mpr A.arc.start_lt_finish.le,rfl⟩,?_⟩
    rw [hrec _ (right_mem_Icc.mpr A.arc.start_lt_finish.le),A.target]
  have hbad : ∀ x ∈ S.chart.symm '' closure U₁,
      ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x) → x = p ∨ x = q := by
    rintro x ⟨z,hz,rfl⟩ hx
    have hzV := hK₁V hz
    have hn : ¬ Function.Injective (fderiv ℝ S.model z) := by
      intro hi
      exact hx ((coordinate_representative_immersion_iff S.chart S.chart_smooth S.inverse_smooth hf
        S.domain_open S.domain_target S.model_eq (hVD hzV)).mp hi)
    have he : z = crosscapAxis A.arc.start ∨ z = crosscapAxis A.arc.finish := by
      have hh : ¬ (z ≠ crosscapAxis A.arc.start ∧ z ≠ crosscapAxis A.arc.finish) :=
        fun hh => hn ((hregV z hzV).mpr hh)
      simpa only [not_and_or,not_not] using hh
    rcases he with rfl | rfl
    · left
      rw [hrec _ (left_mem_Icc.mpr A.arc.start_lt_finish.le),A.source]
    · right
      rw [hrec _ (right_mem_Icc.mpr A.arc.start_lt_finish.le),A.target]
  refine ⟨g,hg,?_,?_⟩
  · intro x
    rw [hIg x]
    constructor
    · rintro (hx | hx)
      · by_cases hr : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)
        · exact Or.inr (Or.inr hr)
        · rcases hbad x hx hr with he | he
          · exact Or.inl he
          · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr hx)
    · rintro (rfl | rfl | hx)
      · exact Or.inl hpimage
      · exact Or.inl hqimage
      · exact Or.inr hx
  · intro x hx hxp hxq
    apply hout x
    intro hi
    exact (hbad x hi hx).elim hxp hxq

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
