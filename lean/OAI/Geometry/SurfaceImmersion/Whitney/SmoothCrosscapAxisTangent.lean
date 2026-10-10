import OAI.Geometry.SurfaceImmersion.Whitney.SmoothCrosscapSourceGeometry
import OAI.Geometry.SurfaceImmersion.Geometry.IntervalDerivativeZero

namespace OAI

/-! The actual smoothed source arc has a nonzero axial velocity and
zero image velocity at its singular endpoint. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}

theorem smooth_crosscap_axis_tangent (c : SurfaceCrosscapCoordinates f p)
    (P : SmoothCompactArc planeModel M) {t : ℝ} (ht : t ∈ Icc P.start P.finish)
    (hPt : P.curve t = p) {V : Set M} (hV : IsOpen V) (hpV : p ∈ V)
    (haxis : ∀ u ∈ Icc P.start P.finish, P.curve u ∈ V →
      P.curve u ∈ c.source.source ∧ c.source (P.curve u) 0 = 0) :
    deriv (c.source ∘ P.curve) t 0 = 0 ∧
      deriv (c.source ∘ P.curve) t 1 ≠ 0 ∧ deriv (f ∘ P.curve) t = 0 := by
  have hPtS : P.curve t ∈ c.source.source := hPt ▸ c.source_mem
  have hPc := P.smooth.contMDiffAt (P.domain_open.mem_nhds (P.interval_subset ht))
  have hcc := c.source_smooth.contMDiffAt (c.source.open_source.mem_nhds hPtS)
  let g : ℝ → Base := c.source ∘ P.curve
  have hgc : ContDiffAt ℝ ∞ g t := (hcc.comp t hPc).contDiffAt
  have hgd := hgc.differentiableAt (by simp)
  have hg0 : g t = 0 := by change c.source (P.curve t) = 0; rw [hPt,c.source_center]
  have hgi : Function.Injective (fderiv ℝ g t) := by
    have hd : c.source.MDifferentiable planeModel 𝓘(ℝ,Base) :=
      ⟨c.source_smooth.mdifferentiableOn (by simp),c.source_inverse_smooth.mdifferentiableOn (by simp)⟩
    rw [← mfderiv_eq_fderiv,mfderiv_comp t (hcc.mdifferentiableAt (by simp))
      (hPc.mdifferentiableAt (by simp))]
    exact (hd.mfderiv_injective hPtS).comp (P.regular t (P.interval_subset ht))
  have hnear : ∀ᶠ u in 𝓝 t, P.curve u ∈ V := hPc.continuousAt.eventually (hV.mem_nhds (hPt ▸ hpV))
  have he : (fun u => g u 0) =ᶠ[𝓝[Icc P.start P.finish] t] fun _ => (0:ℝ) := by
    filter_upwards [self_mem_nhdsWithin,hnear.filter_mono nhdsWithin_le_nhds] with u hu huV
    exact (haxis u hu huV).2
  have hd0 : HasDerivAt (fun u => g u 0) (deriv g t 0) t :=
    (ContinuousLinearMap.proj (0:Fin 2) : Base →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hgd.hasDerivAt
  have hz : deriv g t 0 = 0 := hd0.deriv.symm.trans
    (deriv_zero_of_interval_germ P.start_lt_finish ht hd0.differentiableAt he)
  have hn : deriv g t 1 ≠ 0 := by
    intro hn
    have hgz : deriv g t = 0 := by
      ext i
      fin_cases i
      · exact hz
      · exact hn
    have h01 : fderiv ℝ g t 1 = fderiv ℝ g t 0 := by
      rw [fderiv_apply_one_eq_deriv,hgz,map_zero]
    have h := hgi h01
    norm_num at h
  have hstd : HasDerivAt (standardCrosscap ∘ g) 0 t := by
    have hh := (standardCrosscap_hasFDerivAt (g t)).comp_hasDerivAt t hgd.hasDerivAt
    have hval : standardCrosscapDerivative (g t) (deriv g t) = 0 := by
      rw [hg0]
      apply Prod.ext
      · ext i
        fin_cases i <;> simp [standardCrosscapDerivative]
      · simpa [standardCrosscapDerivative] using hz
    exact hval ▸ hh
  have htarget := (c.target_smooth.differentiable (by simp) (standardCrosscap (g t))).hasFDerivAt.comp_hasDerivAt t hstd
  have hmatch : f ∘ P.curve =ᶠ[𝓝 t] c.target ∘ (standardCrosscap ∘ g) := by
    filter_upwards [hPc.continuousAt.eventually (c.source.open_source.mem_nhds hPtS)] with u hu
    exact c.model_eq (P.curve u) hu
  refine ⟨hz,hn,?_⟩
  rw [hmatch.deriv_eq,htarget.deriv,map_zero]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
