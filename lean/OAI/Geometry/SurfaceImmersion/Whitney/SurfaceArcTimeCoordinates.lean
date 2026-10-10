import OAI.Geometry.SurfaceImmersion.Atlas.TriangularTimeCoordinates
import OAI.Geometry.SurfaceImmersion.Whitney.SmoothArcTimeDerivative

namespace OAI

/-! Local surface coordinates with the fixed global arc-time function
as the second coordinate and with the arc as the zero transverse axis. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_arc_time_coordinates (P : SmoothCompactArc planeModel M)
    {F : M → ℝ} (hF : ContMDiff planeModel 𝓘(ℝ) ∞ F)
    (hFP : ∀ s ∈ Icc P.start P.finish, F (P.curve s) = s)
    {t : ℝ} (ht : t ∈ Icc P.start P.finish) :
    ∃ (d : OpenPartialHomeomorph M Base) (J : Set ℝ),
      IsOpen J ∧ t ∈ J ∧
      ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ d d.source ∧
      ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ d.symm d.target ∧
      (∀ x ∈ d.source, d x 1 = F x) ∧
      ∀ s ∈ J, P.curve s ∈ d.source ∧ d (P.curve s) = ![0,F (P.curve s)] := by
  obtain ⟨c,U,hU,htU,_,hcs,hci,hcoords⟩ := surface_curve_coordinates
    P.domain_open P.smooth (P.interval_subset ht) (P.regular t (P.interval_subset ht))
  have hct : c (P.curve t) = crosscapAxis t := (hcoords t htU).2.trans (crosscapAxis_apply t).symm
  have htc : crosscapAxis t ∈ c.target := hct ▸ c.map_source (hcoords t htU).1
  have hφlocal : ContDiffOn ℝ ∞ (F ∘ c.symm) c.target :=
    (hF.comp_contMDiffOn hci).contDiffOn
  obtain ⟨V,hV,htV,hVc,φ,hφ,hφEq⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := crosscapAxis t)) c.open_target
    (singleton_subset_iff.mpr htc) hφlocal
  have htV' : crosscapAxis t ∈ V := htV (mem_singleton _)
  have hφaxis : φ ∘ crosscapAxis =ᶠ[𝓝 t] F ∘ P.curve := by
    filter_upwards [hU.mem_nhds htU,crosscapAxis.continuous.continuousAt.eventually (hV.mem_nhds htV')] with s hsU hsV
    change φ (crosscapAxis s) = F (P.curve s)
    rw [hφEq hsV]
    change F (c.symm (crosscapAxis s)) = F (P.curve s)
    rw [crosscapAxis_apply,← (hcoords s hsU).2,c.left_inv (hcoords s hsU).1]
  have hdaxis := (hφ.differentiable (by simp) (crosscapAxis t)).hasFDerivAt.comp_hasDerivAt t
    crosscapAxis.hasFDerivAt.hasDerivAt
  have hvertical : fderiv ℝ φ (crosscapAxis t) (crosscapAxis 1) = 1 := by
    rw [← hdaxis.deriv,hφaxis.deriv_eq]
    exact (smooth_arc_time_derivative P hF hFP ht).1
  obtain ⟨e,hte,he,hei⟩ := triangular_time_coordinates hφ (crosscapAxis t) hvertical
  have hes : ContDiff ℝ ∞ e := he ▸ timeCoordinateMap_smooth hφ
  let d₀ := c.trans e
  let O := c.source ∩ c ⁻¹' V
  have hO : IsOpen O := c.isOpen_inter_preimage hV
  let d := d₀.restrOpen O hO
  have hds : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ d d.source :=
    (hes.contMDiff.comp_contMDiffOn (hcs.mono inter_subset_left)).mono (fun _ hx => hx.1)
  have hdi₀ : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ d₀.symm d₀.target := by
    apply hci.comp (hei.contMDiffOn.mono inter_subset_left)
    intro x hx
    exact hx.2
  have hdi : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ d.symm d.target :=
    hdi₀.mono (fun _ hx => hx.1)
  have htd : P.curve t ∈ d.source := by
    refine ⟨⟨(hcoords t htU).1,?_⟩,(hcoords t htU).1,?_⟩
    · change c (P.curve t) ∈ e.source
      rwa [hct]
    · change c (P.curve t) ∈ V
      rwa [hct]
  have hsecond : ∀ x ∈ d.source, d x 1 = F x := by
    intro x hx
    change e (c x) 1 = F x
    rw [he]
    change φ (c x) = F x
    rw [hφEq hx.2.2]
    change F (c.symm (c x)) = F x
    rw [c.left_inv hx.1.1]
  let J := U ∩ (P.domain ∩ P.curve ⁻¹' d.source)
  have hJ : IsOpen J := hU.inter
    (P.smooth.continuousOn.isOpen_inter_preimage P.domain_open d.open_source)
  refine ⟨d,J,hJ,⟨htU,P.interval_subset ht,htd⟩,hds,hdi,hsecond,?_⟩
  intro s hs
  refine ⟨hs.2.2,?_⟩
  ext i
  fin_cases i
  · change e (c (P.curve s)) 0 = 0
    rw [he]
    change c (P.curve s) 0 = 0
    rw [(hcoords s hs.1).2]
    rfl
  · simpa using hsecond (P.curve s) hs.2.2

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
