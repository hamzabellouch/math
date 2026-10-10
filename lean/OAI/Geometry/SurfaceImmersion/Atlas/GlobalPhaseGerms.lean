import OAI.Geometry.SurfaceImmersion.Atlas.UniformNearbyAtlasSmallIncrement
import OAI.Geometry.Immersion.ClosedSurface.PhaseDifferentials

namespace OAI

/-! On intersecting weight supports, restored global linear phases have
the same germs and covectors as the actual manifold coordinate phases. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
open JetPolynomial (planeCoordinateIsometry)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma linearAtlasPhase_eventually (Q : A.centers → PhaseBasis)
    (w : A.centers → Fin 3 → ℝ) (a : A.centers × Fin 3)
    (houter : ∀ x ∈ tsupport (A.weight a.1), A.outer a.1 =ᶠ[𝓝 x] (fun _ => 1))
    {p : M} (hp : p ∈ tsupport (A.weight a.1)) :
    A.linearAtlasPhase Q w a =ᶠ[𝓝 p]
      atlasPhase (a.1 : M) (w a.1 a.2 • (Q a.1).ξ a.2) := by
  filter_upwards [houter p hp,
    (chart (a.1 : M)).open_source.mem_nhds (A.weight_support a.1 hp)] with x ho hx
  rw [linearAtlasPhase, restore, indicator_of_mem hx, ho, one_smul]
  rfl

lemma vectorPlaneRead_eventually_comp_coordinateInverse
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : M → V) (k : A.centers)
    (houter : ∀ x ∈ tsupport (A.weight k), A.outer k =ᶠ[𝓝 x] (fun _ => 1))
    {p : M} (hp : p ∈ tsupport (A.weight k)) :
    A.vectorPlaneRead k F =ᶠ[𝓝 (coordinateChart (k : M) p)]
      F ∘ (coordinateChart (k : M)).symm := by
  let x := planeCoordinateIsometry (chart (k : M) p)
  let inv : SmallModes.Base → M := fun z => (chart (k : M)).symm (planeCoordinateIsometry.symm z)
  have hpS := A.weight_support k hp
  have hinv : inv x = p := by
    dsimp [inv,x]
    rw [LinearIsometryEquiv.symm_apply_apply,(chart (k : M)).left_inv hpS]
  have hc : ContinuousAt inv x := by
    apply ContinuousAt.comp
    · apply (chart (k : M)).continuousAt_symm
      simpa only [x,LinearIsometryEquiv.symm_apply_apply] using (chart (k : M)).map_source hpS
    · exact planeCoordinateIsometry.symm.continuous.continuousAt
  have ht : Tendsto inv (𝓝 x) (𝓝 p) := by simpa only [ContinuousAt,hinv] using hc
  have ho : ∀ᶠ z in 𝓝 x, A.outer k (inv z) = 1 := (houter p hp).comp_tendsto ht
  have htarget : ∀ᶠ z in 𝓝 x,
      planeCoordinateIsometry.symm z ∈ (chart (k : M)).target :=
    ((chart (k : M)).open_target.preimage planeCoordinateIsometry.symm.continuous).mem_nhds
      (by simpa only [Set.mem_preimage,x,LinearIsometryEquiv.symm_apply_apply] using
        (chart (k : M)).map_source hpS)
  change ∀ᶠ z in 𝓝 x, A.vectorPlaneRead k F z = F ((coordinateChart (k : M)).symm z)
  filter_upwards [ho,htarget] with z hz htgt
  change localize (k : M) (A.outer k) F (planeCoordinateIsometry.symm z) = _
  rw [localize,indicator_of_mem htgt]
  change A.outer k (inv z)^2 • F (inv z) = _
  rw [hz,one_pow,one_smul]
  rfl

/-- Both the original phase and its reading in another chart agree as
germs where the two actual compact supports meet. -/
lemma linearAtlasPhase_read_eventually (Q : A.centers → PhaseBasis)
    (w : A.centers → Fin 3 → ℝ) (a : A.centers × Fin 3) (k : A.centers)
    (houter : ∀ i x, x ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 x] (fun _ => 1))
    {p : M} (hpa : p ∈ tsupport (A.weight a.1)) (hpk : p ∈ tsupport (A.weight k)) :
    A.vectorPlaneRead k (A.linearAtlasPhase Q w a) =ᶠ[𝓝 (coordinateChart (k : M) p)]
      atlasPhase (a.1 : M) (w a.1 a.2 • (Q a.1).ξ a.2) ∘ (coordinateChart (k : M)).symm := by
  have hpK : p ∈ (coordinateChart (k : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support k hpk
  have hc := (coordinateChart (k : M)).continuousAt_symm
    ((coordinateChart (k : M)).map_source hpK)
  have ht : Tendsto (coordinateChart (k : M)).symm
      (𝓝 (coordinateChart (k : M) p)) (𝓝 p) := by
    simpa only [ContinuousAt,(coordinateChart (k : M)).left_inv hpK] using hc
  exact (A.vectorPlaneRead_eventually_comp_coordinateInverse
    (A.linearAtlasPhase Q w a) k (houter k) hpk).trans
    ((A.linearAtlasPhase_eventually Q w a (houter a.1) hpa).comp_tendsto ht)

lemma linearAtlasPhase_read_phaseDerivative (Q : A.centers → PhaseBasis)
    (w : A.centers → Fin 3 → ℝ) (a : A.centers × Fin 3) (k : A.centers)
    (houter : ∀ i x, x ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 x] (fun _ => 1))
    {p : M} (hpa : p ∈ tsupport (A.weight a.1)) (hpk : p ∈ tsupport (A.weight k)) :
    phaseDerivative (A.vectorPlaneRead k (A.linearAtlasPhase Q w a)) (coordinateChart (k : M) p) =
      w a.1 a.2 • atlasPhaseCovector (a.1 : M) (k : M) ((Q a.1).ξ a.2) p := by
  have he := A.linearAtlasPhase_read_eventually Q w a k houter hpa hpk
  have hd : phaseDerivative (A.vectorPlaneRead k (A.linearAtlasPhase Q w a))
      (coordinateChart (k : M) p) =
      phaseDerivative (atlasPhase (a.1 : M) (w a.1 a.2 • (Q a.1).ξ a.2) ∘
        (coordinateChart (k : M)).symm) (coordinateChart (k : M) p) := by
    unfold phaseDerivative
    rw [he.fderiv_eq (𝕜 := ℝ)]
  rw [hd]
  have hpK : p ∈ (coordinateChart (k : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support k hpk
  have hpA : p ∈ (coordinateChart (a.1 : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support a.1 hpa
  have hscale : atlasPhase (a.1 : M) (w a.1 a.2 • (Q a.1).ξ a.2) =
      w a.1 a.2 • atlasPhase (a.1 : M) ((Q a.1).ξ a.2) := by
    funext x
    simp only [atlasPhase,Function.comp_apply,phaseLinear_apply,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Pi.smul_apply]
    ring
  rw [hscale]
  change phaseDerivative (w a.1 a.2 •
    (atlasPhase (a.1 : M) ((Q a.1).ξ a.2) ∘ (coordinateChart (k : M)).symm))
      (coordinateChart (k : M) p) = _
  exact phaseDerivative_const_smul
    (atlasPhase_in_chart_differentiable (a.1 : M) (k : M) ((Q a.1).ξ a.2) hpK hpA) _

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
