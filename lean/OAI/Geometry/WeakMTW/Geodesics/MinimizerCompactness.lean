import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.FibreNonfocal
import OAI.Geometry.WeakMTW.Geodesics.HopfRinow
import OAI.Geometry.WeakMTW.Geodesics.InjectivityUniqueness

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

 theorem minimizingDomain_closed (x : M) : IsClosed (minimizingDomain (n := n) x) :=
  isClosed_eq (continuous_const.dist (exp_fibre_smooth x).continuous) continuous_norm

 theorem minimizingDomain_compact (x : M) : IsCompact (minimizingDomain (n := n) x) := by
  let : FiniteDimensional ℝ (TangentSpace (model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  apply (isCompact_closedBall (0 : TangentSpace (model n) x) (Metric.diam (univ : Set M))).of_isClosed_subset
    (minimizingDomain_closed x)
  intro v hv
  rw [Metric.mem_closedBall,dist_zero_right]
  change dist x (exp x v) = ‖v‖ at hv
  rw [← hv]
  exact Metric.dist_le_diam_of_mem (isCompact_univ.isBounded) (mem_univ _) (mem_univ _)

 theorem minimizing_vectors_near_unique {x : M} {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) {U : Set (TangentSpace (model n) x)}
    (hU : IsOpen U) (hvU : v ∈ U) :
    ∀ᶠ y in 𝓝 (exp x v), ∀ w ∈ minimizingDomain x, exp x w = y → w ∈ U := by
  let K := minimizingDomain (n := n) x \ U
  have hK : IsCompact K := (minimizingDomain_compact x).diff hU
  have hC := (hK.image (exp_fibre_smooth x).continuous).isClosed
  have hy : exp x v ∉ (exp x) '' K := by
    rintro ⟨w,hw,he⟩
    have hh := minimizing_vector_unique_of_injectivity hv hw.1 he.symm
    exact hw.2 (hh ▸ hvU)
  filter_upwards [hC.isOpen_compl.mem_nhds hy] with y hy
  intro w hw he
  by_contra hn
  exact hy ⟨w,⟨hw,hn⟩,he⟩

 theorem injectivity_mem_interior_minimizing {x : M} {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) : v ∈ interior (minimizingDomain x) := by
  let y := exp x v
  obtain ⟨e,he,hev,hes,_⟩ := exp_coordinates_local_inverse x y hv (mem_chart_source (Model n) y)
  have hn := minimizing_vectors_near_unique hv e.open_source hev
  have hn' := (exp_fibre_smooth x v).continuousAt.tendsto hn
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hn',e.open_source.mem_nhds hev] with w hw hwe
  obtain ⟨u,heu,hnu⟩ := exists_minimizing_vector (n := n) x (exp x w)
  have hum : u ∈ minimizingDomain x := by change dist x (exp x u) = ‖u‖; rw [heu,hnu]
  have hue : u ∈ e.source := hw u hum heu
  have hwu : w = u := e.injOn hwe hue (by rw [he w,he u,heu])
  exact hwu ▸ hum

 theorem zero_mem_injectivity (x : M) : (0 : TangentSpace (model n) x) ∈ injectivityDomain x := by
  exact ⟨2,by norm_num,by simp [exp_zero]⟩

 theorem strict_radial_mem_injectivity {x : M} {v : TangentSpace (model n) x}
    (hv : v ∈ minimizingDomain x) {t : ℝ} (ht : 0 ≤ t) (ht₁ : t < 1) :
    t • v ∈ injectivityDomain x := by
  by_cases ht0 : t = 0
  · simpa only [ht0,zero_smul] using zero_mem_injectivity x
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  refine ⟨t⁻¹,(one_lt_inv₀ htp).mpr ht₁,?_⟩
  rw [smul_smul,inv_mul_cancel₀ ht0,one_smul]
  rw [show dist x (exp x v) = ‖v‖ from hv,norm_smul,Real.norm_eq_abs,abs_of_pos htp]
  field_simp

 theorem injectivity_extend {x : M} {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) : ∃ t : ℝ, 1 < t ∧ t • v ∈ injectivityDomain x := by
  obtain ⟨a,ha,he⟩ := hv
  have hap : 0 < a := lt_trans zero_lt_one ha
  obtain ⟨t,ht,hta⟩ := exists_between ha
  have ht₀ : 0 ≤ t/a := div_nonneg (zero_lt_one.trans ht).le hap.le
  have ht₁ : t/a < 1 := (div_lt_one hap).mpr hta
  have ham : a • v ∈ minimizingDomain x := by
    change dist x (exp x (a•v)) = ‖a•v‖
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hap]
  have hh := strict_radial_mem_injectivity ham ht₀ ht₁
  exact ⟨t,ht,by simpa only [smul_smul,div_mul_cancel₀ _ hap.ne'] using hh⟩

 theorem injectivityDomain_open (x : M) : IsOpen (injectivityDomain (n := n) x) := by
  rw [isOpen_iff_mem_nhds]
  intro v hv
  obtain ⟨t,ht,htv⟩ := injectivity_extend hv
  have hm := mem_interior_iff_mem_nhds.mp (injectivity_mem_interior_minimizing htv)
  have hn := (continuous_const_smul t).continuousAt.preimage_mem_nhds hm
  filter_upwards [hn] with w hw
  refine ⟨t,ht,?_⟩
  change dist x (exp x (t•w)) = ‖t•w‖ at hw
  rwa [norm_smul,Real.norm_eq_abs,abs_of_pos (zero_lt_one.trans ht)] at hw

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
