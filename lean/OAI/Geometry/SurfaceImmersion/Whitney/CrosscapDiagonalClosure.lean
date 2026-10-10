import OAI.Geometry.SurfaceImmersion.Whitney.CompactDoublePairs
import OAI.Geometry.SurfaceImmersion.Whitney.SurfaceQuadraticDoubleChart

namespace OAI

/-! A prepared crosscap is an actual endpoint of the compactified
unordered double curve: distinct double pairs approach its diagonal. -/
noncomputable section
open Set Filter Metric Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem crosscap_diagonal_mem_closure (F : M → ProjectionTarget 3) (p q : M)
    (hp : p ∈ (chart q).source) {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ)
    (he : F =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q)
    (b : Bool) (t : ℝ) (hz : surfaceDirection φ b (chart q p,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    (p,p) ∈ closure (surfaceDoublePairs F) := by
  obtain ⟨r,hr,hball,hformula,_hsing,_hdouble⟩ :=
    surface_quadratic_crosscap_chart F p q hp hφ he b t hz hreg
  let a := chart q p
  let w := tangentRay b t
  have haT : a ∈ (chart q).target := (chart q).map_source hp
  have hs := (chart q).symm.continuousAt haT
  have hplus : Tendsto (fun s : ℝ => a+s • w) (𝓝 0) (𝓝 a) := by
    have hc : ContinuousAt (fun s : ℝ => a+s • w) 0 := by fun_prop
    simpa only [zero_smul,add_zero] using hc.tendsto
  have hminus : Tendsto (fun s : ℝ => a-s • w) (𝓝 0) (𝓝 a) := by
    have hc : ContinuousAt (fun s : ℝ => a-s • w) 0 := by fun_prop
    simpa only [zero_smul,sub_zero] using hc.tendsto
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), a+s • w ∈ ball a r ∧ a-s • w ∈ ball a r :=
    (hplus.eventually (ball_mem_nhds a hr)).and (hminus.eventually (ball_mem_nhds a hr))
  obtain ⟨δ,hδ,hδnear⟩ := Metric.eventually_nhds_iff.mp hnear
  let σ : ℝ → M × M := fun s => ((chart q).symm (a+s • w),(chart q).symm (a-s • w))
  have hlim : Tendsto σ (𝓝 0) (𝓝 (p,p)) := by
    have h1 := hs.tendsto.comp hplus
    have h2 := hs.tendsto.comp hminus
    have h1' : Tendsto (fun s : ℝ => (chart q).symm (a+s • w)) (𝓝 0) (𝓝 p) := by
      simpa only [Function.comp_def,a,(chart q).left_inv hp] using h1
    have h2' : Tendsto (fun s : ℝ => (chart q).symm (a-s • w)) (𝓝 0) (𝓝 p) := by
      simpa only [Function.comp_def,a,(chart q).left_inv hp] using h2
    exact h1'.prodMk_nhds h2'
  have hσ0 : σ 0 = (p,p) := by simp [σ,a,(chart q).left_inv hp]
  have hσ : ContinuousAt σ 0 := by rw [ContinuousAt,hσ0]; exact hlim
  have h0 : (0 : ℝ) ∈ closure (Ioo 0 δ) := by
    rw [closure_Ioo hδ.ne]
    exact ⟨le_rfl,hδ.le⟩
  have himage : σ '' Ioo 0 δ ⊆ surfaceDoublePairs F := by
    rintro z ⟨s,hsδ,rfl⟩
    have hsabs : dist s 0 < δ := by rw [dist_zero_right,Real.norm_eq_abs,abs_of_pos hsδ.1]; exact hsδ.2
    obtain ⟨hsp,hsm⟩ := hδnear hsabs
    have hpT := hball (ball_subset_closedBall hsp)
    have hmT := hball (ball_subset_closedBall hsm)
    refine ⟨?_,?_⟩
    · intro hsame
      have hcoord : a+s • w = a-s • w := (chart q).symm.injOn hpT hmT hsame
      have htwo : (2 : ℝ) • (s • w) = 0 := by
        calc
          _ = (a+s • w)-(a-s • w) := by module
          _ = 0 := sub_eq_zero.mpr hcoord
      have hsw : s • w = 0 := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
      have hs0 : s = 0 := (smul_eq_zero.mp hsw).resolve_right (tangentRay_ne_zero b t)
      exact hsδ.1.ne' hs0
    · change F ((chart q).symm (a+s • w)) = F ((chart q).symm (a-s • w))
      rw [hformula _ hsp,hformula _ hsm]
      apply (centeredSurfaceTaylor_reflected_eq_iff hφ a (s • w)).mpr
      rw [map_smul]
      change s • surfaceDirection φ b (a,t) = 0
      rw [hz,smul_zero]
  have hcl := closure_mono himage (mem_closure_image hσ h0)
  rwa [hσ0] at hcl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
