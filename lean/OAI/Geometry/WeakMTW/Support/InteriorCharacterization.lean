import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.NonconjugateBranches
import OAI.Geometry.WeakMTW.Geodesics.MinimizerCompactness

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem unique_minimizer_neighborhood {x : M} {v : TangentSpace (model n) x}
    (huniq : ∀ w ∈ minimizingDomain x, exp x w = exp x v → w = v)
    {U : Set (TangentSpace (model n) x)} (hU : IsOpen U) (hvU : v ∈ U) :
    ∀ᶠ y in 𝓝 (exp x v), ∀ w ∈ minimizingDomain x, exp x w = y → w ∈ U := by
  let K := minimizingDomain (n := n) x \ U
  have hK : IsCompact K := (minimizingDomain_compact x).diff hU
  have hC := (hK.image (exp_fibre_smooth x).continuous).isClosed
  have hy : exp x v ∉ (exp x) '' K := by
    rintro ⟨w,hw,he⟩
    exact hw.2 ((huniq w hw.1 he).symm ▸ hvU)
  filter_upwards [hC.isOpen_compl.mem_nhds hy] with y hy
  intro w hw he
  by_contra hn
  exact hy ⟨w,⟨hw,hn⟩,he⟩

 theorem exp_local_inverse_nonconjugate {x : M} {v : TangentSpace (model n) x}
    (hn : Nonconjugate x v) :
    ∃ e : OpenPartialHomeomorph (TangentSpace (model n) x) (Model n),
      (∀ w, e w = chartAt (Model n) (exp x v) (exp x w)) ∧ v ∈ e.source := by
  let : FiniteDimensional ℝ (TangentSpace (model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  let y := exp x v
  let S : Set (TangentSpace (model n) x) := (exp (n := n) x) ⁻¹' (chartAt (Model n) y).source
  have hS : IsOpen S := (chartAt (Model n) y).open_source.preimage (exp_fibre_smooth x).continuous
  have hf : ContDiffOn ℝ ∞ (fun w => chartAt (Model n) y (exp x w)) S :=
    fun w hw => (exp_coordinates_smooth x y hw).contDiffWithinAt
  let A := fderiv ℝ (fun w => chartAt (Model n) y (exp x w)) v
  let e₀ : TangentSpace (model n) x ≃ₗ[ℝ] Model n :=
    LinearEquiv.ofInjectiveEndo A.toLinearMap hn
  let D : TangentSpace (model n) x ≃L[ℝ] Model n := e₀.toContinuousLinearEquiv
  have hD : HasFDerivAt (fun w => chartAt (Model n) y (exp x w))
      (D : TangentSpace (model n) x →L[ℝ] Model n) v :=
    by
      exact ((exp_coordinates_smooth x y (mem_chart_source (Model n) y)).differentiableAt (by simp)).hasFDerivAt
  obtain ⟨e,he,hev,_,_,_⟩ := NormalNeighborhood.exists_smooth_local_diffeomorph hS hf
    (mem_chart_source (Model n) y) hD
  exact ⟨e,fun w => congrFun he w,hev⟩

 theorem unique_nonconjugate_mem_injectivity {x : M} {v : TangentSpace (model n) x}
    (hn : Nonconjugate x v)
    (huniq : ∀ w ∈ minimizingDomain x, exp x w = exp x v → w = v) :
    v ∈ injectivityDomain x := by
  obtain ⟨e,he,hev⟩ := exp_local_inverse_nonconjugate hn
  have hnear := unique_minimizer_neighborhood huniq e.open_source hev
  have hvM : minimizingDomain x ∈ 𝓝 v := by
    filter_upwards [(exp_fibre_smooth x v).continuousAt.tendsto hnear,
      e.open_source.mem_nhds hev] with w hw hwe
    obtain ⟨u,heu,hnu⟩ := exists_minimizing_vector (n := n) x (exp x w)
    have hum : u ∈ minimizingDomain x := by change dist x (exp x u) = ‖u‖; rw [heu,hnu]
    have hue : u ∈ e.source := hw u hum heu
    have hwu : w = u := e.injOn hwe hue (by rw [he w,he u,heu])
    exact hwu ▸ hum
  have hevent : ∀ᶠ t : ℝ in 𝓝 (1 : ℝ), t • v ∈ minimizingDomain x := by
    have hc : ContinuousAt (fun t : ℝ => t • v) 1 := continuousAt_id.smul continuousAt_const
    have hvM' : minimizingDomain x ∈ 𝓝 ((1 : ℝ) • v) := by simpa only [one_smul] using hvM
    exact hc.preimage_mem_nhds hvM'
  obtain ⟨a,ha,haM⟩ : ∃ a : ℝ, 1 < a ∧ a • v ∈ minimizingDomain x := by
    obtain ⟨a,haM,ha⟩ := (hevent.filter_mono nhdsWithin_le_nhds |>.and
      (self_mem_nhdsWithin : ∀ᶠ a : ℝ in 𝓝[>] (1 : ℝ), a ∈ Ioi 1)).exists
    exact ⟨a,ha,haM⟩
  refine ⟨a,ha,?_⟩
  change dist x (exp x (a • v)) = ‖a • v‖ at haM
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos (zero_lt_one.trans ha)] using haM

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
