import OAI.Geometry.NodalSets.Elliptic.CompactSourceOperator
import OAI.Geometry.NodalSets.Elliptic.UniformSmoothBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma coordPartial_add (u v : Coord → ℂ) (hu : Differentiable ℝ u)
    (hv : Differentiable ℝ v) (i : Fin 4) :
    coordPartial i (fun z ↦ u z+v z) = fun z ↦ coordPartial i u z+coordPartial i v z := by
  funext x
  simp [coordPartial,fderiv_fun_add (hu x) (hv x)]

lemma smoothFluxOperator_add (v : Coord → ℂ) (F : Fin 4 → Fin 4 → Coord → ℂ)
    (hF : ∀ i j, ContDiff ℝ ∞ (F i j))
    (u t : Coord → ℂ) (hu : ContDiff ℝ ∞ u) (ht : ContDiff ℝ ∞ t) :
    smoothFluxOperator v F (fun z ↦ u z+t z) =
      fun z ↦ smoothFluxOperator v F u z+smoothFluxOperator v F t z := by
  have he (i : Fin 4) :
      (fun z ↦ ∑ j, F i j z*coordPartial j (fun z ↦ u z+t z) z) =
      (fun z ↦ (∑ j, F i j z*coordPartial j u z)+(∑ j, F i j z*coordPartial j t z)) := by
    funext z
    simp [coordPartial_add u t (hu.differentiable (by simp)) (ht.differentiable (by simp)),
      mul_add,Finset.sum_add_distrib]
  have hfu (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ ∑ j, F i j z*coordPartial j u z) :=
    ContDiff.sum (fun j _ ↦ (hF i j).mul (coordPartial_contDiff hu j))
  have hft (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ ∑ j, F i j z*coordPartial j t z) :=
    ContDiff.sum (fun j _ ↦ (hF i j).mul (coordPartial_contDiff ht j))
  funext x
  simp only [smoothFluxOperator,he,
    coordPartial_add _ _ ((hfu _).differentiable (by simp)) ((hft _).differentiable (by simp)),
    Finset.sum_add_distrib,mul_add]

lemma sourceOperator_add_germ {U : Set Coord} (hU : IsOpen U)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x)
    (u t : Coord → ℂ) (hu : ContDiff ℝ ∞ u) (ht : ContDiff ℝ ∞ t)
    {x : Coord} (hx : x ∈ U) :
    sourceWeightedOperator g w (fun z ↦ u z+t z) =ᶠ[𝓝 x]
      (fun z ↦ sourceWeightedOperator g w u z+sourceWeightedOperator g w t z) := by
  obtain ⟨v,F,hv,hF,he⟩ := compact_source_operator_coefficients (isCompact_singleton (x := x))
    hU (singleton_subset_iff.mpr hx) ⟨x,hx⟩ g hg hs hp w hw hwp
  filter_upwards [he x (mem_singleton x) u,he x (mem_singleton x) t,
    he x (mem_singleton x) (fun z ↦ u z+t z)] with z hzu hzt hzsum
  rw [hzsum,smoothFluxOperator_add v F hF u t hu ht]
  exact congrArg₂ (· + ·) hzu.symm hzt.symm

lemma sourceOperator_smoothAt {U : Set Coord} (hU : IsOpen U)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x)
    (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u) {x : Coord} (hx : x ∈ U) :
    ContDiffAt ℝ ∞ (sourceWeightedOperator g w u) x := by
  obtain ⟨v,F,hv,hF,he⟩ := compact_source_operator_coefficients (isCompact_singleton (x := x))
    hU (singleton_subset_iff.mpr hx) ⟨x,hx⟩ g hg hs hp w hw hwp
  exact (smoothFluxOperator_smooth v F hv hF u hu).contDiffAt.congr_of_eventuallyEq
    (he x (mem_singleton x) u)

theorem sourceOperator_add_supported {U : Set Coord} (hU : IsOpen U)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x)
    (u t : Coord → ℂ) (hu : ContDiff ℝ ∞ u) (ht : ContDiff ℝ ∞ t)
    (hsub : tsupport t ⊆ U) :
    sourceWeightedOperator g w (fun z ↦ u z+t z) =
      fun z ↦ sourceWeightedOperator g w u z+sourceWeightedOperator g w t z := by
  funext x
  by_cases hx : x ∈ U
  · exact (sourceOperator_add_germ hU g hg hs hp w hw hwp u t hu ht hx).self_of_nhds
  · have hz : t =ᶠ[𝓝 x] (fun _ ↦ 0) :=
      notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hx (hsub h))
    have hsum : (fun z ↦ u z+t z) =ᶠ[𝓝 x] u := by
      filter_upwards [hz] with z hz
      simp [hz]
    rw [(sourceOperator_eventuallyEq g w hsum).self_of_nhds,
      (sourceOperator_eventuallyEq g w hz).self_of_nhds,sourceWeightedOperator_zero]
    simp

end
end Yau.Geometry

end OAI
