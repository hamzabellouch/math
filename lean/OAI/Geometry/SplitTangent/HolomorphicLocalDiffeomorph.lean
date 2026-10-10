import Mathlib

namespace OAI

/-! Holomorphic Local Diffeomorph. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff

namespace HolomorphicLocalDiffeomorph
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace E M] [ChartedSpace F N]
  [IsManifold 𝓘(ℂ,E) ω M] [IsManifold 𝓘(ℂ,F) ω N]

 

theorem of_analytic_partial_homeomorph (φ : OpenPartialHomeomorph M N)
    {x : M} (hx : x∈φ.source)
    (hφ : ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,F) ω φ x)
    (hφs : ContMDiffAt 𝓘(ℂ,F) 𝓘(ℂ,E) ω φ.symm (φ x)) :
    IsLocalDiffeomorphAt 𝓘(ℂ,E) 𝓘(ℂ,F) ω φ x := by
  have he : ∀ᶠ y in 𝓝 x,
      ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,F) ω φ y ∧
      ContMDiffAt 𝓘(ℂ,F) 𝓘(ℂ,E) ω φ.symm (φ y) :=
    ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hφ).and
      (hφ.continuousAt.eventually ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hφs))
  obtain ⟨U,hUsub,hU,hxU⟩ := mem_nhds_iff.mp he
  let ψ := φ.restrOpen U hU
  let Φ : PartialDiffeomorph 𝓘(ℂ,E) 𝓘(ℂ,F) M N ω := {
    ψ.toPartialEquiv with
    open_source := ψ.open_source
    open_target := ψ.open_target
    contMDiffOn_toFun := by
      intro y hy
      exact (hUsub hy.2).1.contMDiffWithinAt
    contMDiffOn_invFun := by
      intro y hy
      have hz : φ.symm y∈ψ.source := ψ.map_target hy
      have hh := (hUsub hz.2).2
      change ContMDiffWithinAt 𝓘(ℂ,F) 𝓘(ℂ,E) ω φ.symm ψ.target y
      simpa only [φ.right_inv hy.1] using hh.contMDiffWithinAt }
  exact ⟨Φ,⟨hx,hxU⟩,fun _ _ => rfl⟩

 

theorem normed_ift [CompleteSpace E] [CompleteSpace F]
    {f : E → F} {x : E} (hf : ContDiffAt ℂ ω f x)
    (L : E ≃L[ℂ] F) (hL : HasFDerivAt f (L : E →L[ℂ] F) x) :
    IsLocalDiffeomorphAt 𝓘(ℂ,E) 𝓘(ℂ,F) ω f x := by
  let φ := hf.toOpenPartialHomeomorph f hL (by simp)
  exact of_analytic_partial_homeomorph φ
    (hf.mem_toOpenPartialHomeomorph_source hL (by simp))
    hf.contMDiffAt (hf.to_localInverse hL (by simp)).contMDiffAt

end HolomorphicLocalDiffeomorph

namespace HolomorphicLocalDiffeomorph
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace E M] [ChartedSpace F N]
  [IsManifold 𝓘(ℂ,E) ω M] [IsManifold 𝓘(ℂ,F) ω N]

omit [IsManifold 𝓘(ℂ,E) ω M] [IsManifold 𝓘(ℂ,F) ω N] in
theorem congr_eventually {f g : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt 𝓘(ℂ,E) 𝓘(ℂ,F) ω f x)
    (he : f=ᶠ[𝓝 x]g) : IsLocalDiffeomorphAt 𝓘(ℂ,E) 𝓘(ℂ,F) ω g x := by
  obtain ⟨φ,hx,hφ⟩ := hf
  obtain ⟨U,hUsub,hU,hxU⟩ := mem_nhds_iff.mp he
  let ψ := φ.toOpenPartialHomeomorph.restrOpen U hU
  let Φ : PartialDiffeomorph 𝓘(ℂ,E) 𝓘(ℂ,F) M N ω := {
    ψ.toPartialEquiv with
    open_source := ψ.open_source
    open_target := ψ.open_target
    contMDiffOn_toFun := φ.contMDiffOn_toFun.mono inter_subset_left
    contMDiffOn_invFun := φ.contMDiffOn_invFun.mono inter_subset_left }
  refine ⟨Φ,⟨hx,hxU⟩,?_⟩
  intro y hy
  exact (hUsub hy.2).symm.trans (hφ hy.1)

theorem chart_local {x y : M} (hy : y∈(chartAt E x).source) :
    IsLocalDiffeomorphAt 𝓘(ℂ,E) 𝓘(ℂ,E) ω (chartAt E x) y :=
  of_analytic_partial_homeomorph _ hy
    (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ,E))
      (n:=ω) x) hy)
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ,E))
      (n:=ω) x) ((chartAt E x).map_source hy))

theorem chart_symm_local {x : M} {y : E} (hy : y∈(chartAt E x).target) :
    IsLocalDiffeomorphAt 𝓘(ℂ,E) 𝓘(ℂ,E) ω (chartAt E x).symm y :=
  of_analytic_partial_homeomorph _ hy
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ,E))
      (n:=ω) x) hy)
    (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ,E))
      (n:=ω) x) ((chartAt E x).map_target hy))

 

theorem manifold_ift [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    {f : M → N} {x : M} (hf : ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,F) ω f x)
    (hb : Function.Bijective (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,F) f x)) :
    IsLocalDiffeomorphAt 𝓘(ℂ,E) 𝓘(ℂ,F) ω f x := by
  let c := chartAt E x
  let d := chartAt F (f x)
  have hc : x∈c.source := mem_chart_source E x
  have hd : f x∈d.source := mem_chart_source F (f x)
  have hcs : c.symm (c x)=x := c.left_inv hc
  have hdl := chart_local hd
  have hcsl := chart_symm_local (c.map_source hc)
  have hcl := chart_local hc
  let g : E → F := d ∘ f ∘ c.symm
  have hfcs : ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,F) ω f (c.symm (c x)) := by
    rwa [hcs]
  have hinner := hfcs.comp (c x) hcsl.contMDiffAt
  have hdcs : ContMDiffAt 𝓘(ℂ,F) 𝓘(ℂ,F) ω d (f (c.symm (c x))) := by
    simpa only [hcs] using hdl.contMDiffAt
  have hgM : ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,F) ω g (c x) := hdcs.comp (c x) hinner
  have hg : ContDiffAt ℂ ω g (c x) := hgM.contDiffAt
  have hbD : Function.Bijective
      (mfderiv 𝓘(ℂ,F) 𝓘(ℂ,F) d (f (c.symm (c x)))) := by
    rw [hcs]
    exact (hdl.mfderivToContinuousLinearEquiv (by simp)).bijective
  have hbF : Function.Bijective
      (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,F) f (c.symm (c x))) := by
    rw [hcs]
    exact hb
  have hbC : Function.Bijective (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,E) c.symm (c x)) :=
    (hcsl.mfderivToContinuousLinearEquiv (by simp)).bijective
  have hbg : Function.Bijective (fderiv ℂ g (c x)) := by
    rw [← mfderiv_eq_fderiv]
    change Function.Bijective (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,F) (d ∘ (f ∘ c.symm)) (c x))
    rw [mfderiv_comp (c x) (f := f ∘ c.symm) (g := d) (hdcs.mdifferentiableAt (by simp))
      (hinner.mdifferentiableAt (by simp)),
      mfderiv_comp (c x) (f := c.symm) (g := f) (hfcs.mdifferentiableAt (by simp))
        (hcsl.mdifferentiableAt (by simp))]
    exact hbD.comp (hbF.comp hbC)
  let L : E ≃L[ℂ] F :=
    (LinearEquiv.ofBijective (fderiv ℂ g (c x)).toLinearMap hbg).toContinuousLinearEquiv
  have hLg : HasFDerivAt g (L : E →L[ℂ] F) (c x) := hg.differentiableAt (by simp) |>.hasFDerivAt
  have hgl := normed_ift hg L hLg
  have hdsl : IsLocalDiffeomorphAt 𝓘(ℂ,F) 𝓘(ℂ,F) ω d.symm (g (c x)) := by
    simpa only [g,Function.comp_apply,hcs] using chart_symm_local (d.map_source hd)
  apply congr_eventually (hcl.comp 𝓘(ℂ,F) N (hgl.comp 𝓘(ℂ,F) N hdsl))
  filter_upwards [c.open_source.mem_nhds hc,
    hf.continuousAt.eventually (d.open_source.mem_nhds hd)] with y hy hfy
  change d.symm (d (f (c.symm (c y))))=f y
  rw [c.left_inv hy,d.left_inv hfy]

end HolomorphicLocalDiffeomorph

end

end OAI
