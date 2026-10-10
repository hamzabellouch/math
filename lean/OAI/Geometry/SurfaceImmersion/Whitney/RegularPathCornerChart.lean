import OAI.Geometry.SurfaceImmersion.Whitney.RegularPathCornerPieces
import OAI.Geometry.SurfaceImmersion.Whitney.FiniteRegularPathSmooth
import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceGraphParameter

namespace OAI

/-! Actual common graph charts at every corner of an embedded finite regular path. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

structure RegularPathCornerChart {x y : M} (γ : Path x y) (t : ℝ) where
  chart : OpenPartialHomeomorph M Base
  chart_smooth : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ chart chart.source
  inverse_smooth : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ chart.symm chart.target
  leftGraph : ℝ → ℝ
  rightGraph : ℝ → ℝ
  left_smooth : ContDiff ℝ ∞ leftGraph
  right_smooth : ContDiff ℝ ∞ rightGraph
  leftParameter : ℝ ≃ₜ ℝ
  rightParameter : ℝ ≃ₜ ℝ
  left_parameter_smooth : ContDiff ℝ ∞ leftParameter
  right_parameter_smooth : ContDiff ℝ ∞ rightParameter
  left_inverse_smooth : ContDiff ℝ ∞ leftParameter.symm
  right_inverse_smooth : ContDiff ℝ ∞ rightParameter.symm
  left_monotone : StrictMono leftParameter ∨ StrictAnti leftParameter
  right_monotone : StrictMono rightParameter ∨ StrictAnti rightParameter
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_lt : lower < t
  lt_upper : t < upper
  upper_lt_one : upper < 1
  left_chart : ∀ u ∈ Icc lower t, γ.extend u ∈ chart.source ∧
    chart (γ.extend u) = ![leftParameter u,leftGraph (leftParameter u)]
  right_chart : ∀ u ∈ Icc t upper, γ.extend u ∈ chart.source ∧
    chart (γ.extend u) = ![rightParameter u,rightGraph (rightParameter u)]
  parameter_match : leftParameter t = rightParameter t

theorem regular_path_corner_chart {x y : M} {γ : Path x y}
    (hγ : FiniteRegularPath planeModel γ) (hi : Function.Injective γ)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : Nonempty (RegularPathCornerChart γ t) := by
  obtain ⟨A,B,a,b,c,d,l,r,hlt,htr,ha,hc,hL,hR⟩ :=
    hγ.cover.some.one_sided_regular_pieces hi ht
  let F : ℝ → M := fun u => A.curve (a*u+b)
  let G : ℝ → M := fun u => B.curve (c*u+d)
  let U : Set ℝ := (fun u : ℝ => a*u+b) ⁻¹' A.domain
  let V : Set ℝ := (fun u : ℝ => c*u+d) ⁻¹' B.domain
  have hsF : ContDiff ℝ ∞ (fun u : ℝ => a*u+b) := by fun_prop
  have hsG : ContDiff ℝ ∞ (fun u : ℝ => c*u+d) := by fun_prop
  have hU : IsOpen U := A.domain_open.preimage hsF.continuous
  have hV : IsOpen V := B.domain_open.preimage hsG.continuous
  have htU : t ∈ U := (hL t ⟨hlt.le,le_rfl⟩).1
  have htV : t ∈ V := (hR t ⟨le_rfl,htr.le⟩).1
  have hF : ContMDiffOn 𝓘(ℝ) planeModel ∞ F U :=
    A.smooth.comp hsF.contMDiff.contMDiffOn (fun _ hu => hu)
  have hG : ContMDiffOn 𝓘(ℝ) planeModel ∞ G V :=
    B.smooth.comp hsG.contMDiff.contMDiffOn (fun _ hu => hu)
  have hFi : Function.Injective (mfderiv 𝓘(ℝ) planeModel F t) := by
    change Function.Injective (mfderiv 𝓘(ℝ) planeModel (A.curve ∘ fun u : ℝ => a*u+b) t)
    rw [mfderiv_comp t ((A.smooth.contMDiffAt (A.domain_open.mem_nhds htU)).mdifferentiableAt (by simp))
      (hsF.contMDiff.mdifferentiable (by simp) t)]
    exact (A.regular _ htU).comp (affine_parameter_regular ha t)
  have hGi : Function.Injective (mfderiv 𝓘(ℝ) planeModel G t) := by
    change Function.Injective (mfderiv 𝓘(ℝ) planeModel (B.curve ∘ fun u : ℝ => c*u+d) t)
    rw [mfderiv_comp t ((B.smooth.contMDiffAt (B.domain_open.mem_nhds htV)).mdifferentiableAt (by simp))
      (hsG.contMDiff.mdifferentiable (by simp) t)]
    exact (B.regular _ htV).comp (affine_parameter_regular hc t)
  have hmeet : F t = G t := (hL t ⟨hlt.le,le_rfl⟩).2.symm.trans (hR t ⟨le_rfl,htr.le⟩).2
  obtain ⟨q,f,g,U1,V1,hqs,hqi,hf,hg,hI,hJ,htI,htJ,hIU,hJV,hIF,hJG,hdF,hdG⟩ :=
    common_surface_curve_graphs hU hV hF hG htU htV hmeet hFi hGi
  obtain ⟨e,W,he,hei,hem,hW,htW,hWI,heW,_⟩ :=
    surface_graph_parameter hI (hF.mono hIU) q hqs f hIF htI hdF
  obtain ⟨e',W',he',hei',hem',hW',htW',hWJ,heW',_⟩ :=
    surface_graph_parameter hJ (hG.mono hJV) q hqs g hJG htJ hdG
  have hn : W ∩ W' ∩ Ioo l r ∩ Ioo (0:ℝ) 1 ∈ 𝓝 t :=
    by
      filter_upwards [hW.mem_nhds htW,hW'.mem_nhds htW',
        isOpen_Ioo.mem_nhds ⟨hlt,htr⟩,isOpen_Ioo.mem_nhds ht] with u hu hv hlr h01
      exact ⟨⟨⟨hu,hv⟩,hlr⟩,h01⟩
  obtain ⟨l₀,r₀,⟨hl₀,hr₀⟩,hsub₀⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  obtain ⟨l',hll₀,hlt'⟩ := exists_between hl₀
  obtain ⟨r',htr',hrr₀⟩ := exists_between hr₀
  have hsub : Icc l' r' ⊆ W ∩ W' ∩ Ioo l r ∩ Ioo (0:ℝ) 1 :=
    fun _ hu => hsub₀ ⟨hll₀.trans_le hu.1,hu.2.trans_lt hrr₀⟩
  have hll := hsub (left_mem_Icc.mpr (hlt'.trans htr').le)
  have hrr := hsub (right_mem_Icc.mpr (hlt'.trans htr').le)
  have hleft : ∀ u ∈ Icc l' t, γ.extend u ∈ q.source ∧
      q (γ.extend u) = ![e u,f (e u)] := by
    intro u hu
    have hum := hsub ⟨hu.1,hu.2.trans htr'.le⟩
    have hp := hL u ⟨hll.1.2.1.le.trans hu.1,hu.2⟩
    rw [hp.2]
    exact ⟨(hIF u (hWI hum.1.1.1)).1,by
      rw [heW u hum.1.1.1]
      exact (hIF u (hWI hum.1.1.1)).2⟩
  have hright : ∀ u ∈ Icc t r', γ.extend u ∈ q.source ∧
      q (γ.extend u) = ![e' u,g (e' u)] := by
    intro u hu
    have hum := hsub ⟨hlt'.le.trans hu.1,hu.2⟩
    have hp := hR u ⟨hu.1,hu.2.trans hrr.1.2.2.le⟩
    rw [hp.2]
    exact ⟨(hJG u (hWJ hum.1.1.2)).1,by
      rw [heW' u hum.1.1.2]
      exact (hJG u (hWJ hum.1.1.2)).2⟩
  refine ⟨⟨q,hqs,hqi,f,g,hf,hg,e,e',he,he',hei,hei',hem,hem',l',r',hll.2.1,
    hlt',htr',hrr.2.2,hleft,hright,?_⟩⟩
  have H := (hleft t ⟨hlt'.le,le_rfl⟩).2.symm.trans (hright t ⟨le_rfl,htr'.le⟩).2
  exact congrFun H 0

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
