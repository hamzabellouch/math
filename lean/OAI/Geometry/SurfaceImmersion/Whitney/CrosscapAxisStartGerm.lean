import OAI.Geometry.SurfaceImmersion.Whitney.SmoothCrosscapAxisTangent
import OAI.Geometry.SurfaceImmersion.Whitney.SmoothArcStartGerm
import OAI.Geometry.SurfaceImmersion.Geometry.NonzeroGermDiffeomorphism

namespace OAI

/-! Straighten the exterior start germ to the actual crosscap kernel
axis, without changing any point of the compact source arc. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}

theorem crosscap_axis_start_germ (c : SurfaceCrosscapCoordinates f p)
    (P : SmoothCompactArc planeModel M) (hPs : P.curve P.start = p)
    {V : Set M} (hV : IsOpen V) (hpV : p ∈ V)
    (haxis : ∀ u ∈ Icc P.start P.finish, P.curve u ∈ V →
      P.curve u ∈ c.source.source ∧ c.source (P.curve u) 0 = 0) :
    ∃ (R : SmoothCompactArc planeModel M) (e : ℝ ≃ₜ ℝ),
      R.start = P.start ∧ R.finish = P.finish ∧
      EqOn R.curve P.curve (Icc P.start P.finish) ∧
      ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧ e P.start = 0 ∧
      R.curve =ᶠ[𝓝 P.start] c.axisCurve ∘ e ∧
      R.curve =ᶠ[𝓝 P.finish] P.curve := by
  let g : ℝ → Base := c.source ∘ P.curve
  let h : ℝ → ℝ := fun t => g t 1
  let U := P.domain ∩ P.curve ⁻¹' c.source.source
  have hU : IsOpen U := P.smooth.continuousOn.isOpen_inter_preimage
    P.domain_open c.source.open_source
  have hsP := P.interval_subset (left_mem_Icc.mpr P.start_lt_finish.le)
  have hsU : P.start ∈ U := ⟨hsP,hPs ▸ c.source_mem⟩
  have hg : ContDiffOn ℝ ∞ g U := (c.source_smooth.comp
    (P.smooth.mono inter_subset_left) (fun _ ht => ht.2)).contDiffOn
  have hh : ContDiffOn ℝ ∞ h U := (contDiff_apply ℝ ℝ (1:Fin 2)).comp_contDiffOn hg
  have hgd := (hg.contDiffAt (hU.mem_nhds hsU)).differentiableAt (by simp)
  have hd1 : HasDerivAt h (deriv g P.start 1) P.start :=
    (ContinuousLinearMap.proj (1:Fin 2) : Base →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt P.start hgd.hasDerivAt
  have hn : deriv h P.start ≠ 0 := by
    rw [hd1.deriv]
    exact (smooth_crosscap_axis_tangent c P (left_mem_Icc.mpr P.start_lt_finish.le)
      hPs hV hpV haxis).2.1
  obtain ⟨e,hes,hei,_,he⟩ := nonzero_local_germ_diffeomorphism hU hh hsU hn
  have he0 : e P.start = 0 := by
    rw [he.eq_of_nhds]
    change c.source (P.curve P.start) 1 = 0
    rw [hPs,c.source_center]
    rfl
  obtain ⟨A,hA,h0A,hAs,hAr,_,_⟩ := c.axis_curve
  let G : ℝ → M := c.axisCurve ∘ e
  let B := e ⁻¹' A
  have hB : IsOpen B := hA.preimage e.continuous
  have hsB : P.start ∈ B := by change e P.start ∈ A; rwa [he0]
  have hGs : ContMDiffOn 𝓘(ℝ) planeModel ∞ G B :=
    hAs.comp hes.contMDiff.contMDiffOn (fun _ ht => ht)
  have hGr : ∀ t ∈ B, Function.Injective (mfderiv 𝓘(ℝ) planeModel G t) := by
    intro t ht
    exact regular_curve_reparameterization e hes hei
      (hAs.contMDiffAt (hA.mem_nhds ht)) (hAr _ ht)
  obtain ⟨W,hEq,hW,hsW⟩ := eventually_nhds_iff.mp he
  let D := P.domain ∩ P.curve ⁻¹' V
  have hD : IsOpen D := P.smooth.continuousOn.isOpen_inter_preimage P.domain_open hV
  have hsD : P.start ∈ D := ⟨hsP,by change P.curve P.start ∈ V; rwa [hPs]⟩
  let O := (B ∩ W) ∩ D
  have hO : IsOpen O := (hB.inter hW).inter hD
  have hsO : P.start ∈ O := ⟨⟨hsB,hsW⟩,hsD⟩
  have hGP : EqOn G P.curve (O ∩ Icc P.start P.finish) := by
    intro t ht
    change c.axisCurve (e t) = P.curve t
    rw [hEq t ht.1.1.2]
    exact c.axisCurve_coordinate (haxis t ht.2 ht.1.2.2).1 (haxis t ht.2 ht.1.2.2).2
  obtain ⟨R,hRs,hRf,hRP,hRG,hRPf⟩ := P.replace_start_germ hO hsO
    (hGs.mono (fun _ ht => ht.1.1)) (fun t ht => hGr t ht.1.1) hGP
  exact ⟨R,e,hRs,hRf,hRP,hes,hei,he0,hRG,hRPf⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
