import OAI.Geometry.Immersion.ClosedSurface.AtlasMargins

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]


def phaseLinear (ξ : SmallModes.Base) : SmallModes.Base →L[ℝ] ℝ :=
  ξ.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + ξ.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

lemma phaseLinear_apply (ξ x : SmallModes.Base) : phaseLinear ξ x = ξ.1*x.1+ξ.2*x.2 := rfl

def atlasPhase (p : M) (ξ : SmallModes.Base) : M → ℝ := phaseLinear ξ ∘ coordinateChart p

lemma atlasPhase_smoothOn (p : M) (ξ : SmallModes.Base) :
    ContMDiffOn planeModel 𝓘(ℝ) ∞ (atlasPhase p ξ) (coordinateChart p).source :=
  (phaseLinear ξ).contDiff.contMDiff.comp_contMDiffOn (coordinateChart_smoothOn p)


def phaseDerivative (f : SmallModes.Base → ℝ) (x : SmallModes.Base) : SmallModes.Base :=
  (fderiv ℝ f x dx,fderiv ℝ f x dy)

lemma phaseDerivative_linear_comp {φ : SmallModes.Base → SmallModes.Base}
    {x : SmallModes.Base} (hφ : DifferentiableAt ℝ φ x) (ξ : SmallModes.Base) :
    phaseDerivative (phaseLinear ξ ∘ φ) x = pullCovector (fderiv ℝ φ x) ξ := by
  have hd := ((phaseLinear ξ).hasFDerivAt.comp x hφ.hasFDerivAt).fderiv
  unfold phaseDerivative
  rw [hd]
  rfl



theorem actual_phase_differential (q p : M) (ξ : SmallModes.Base)
    {x : SmallModes.Base} (hx : x ∈ (coordinateTransition q p).source) :
    phaseDerivative (atlasPhase q ξ ∘ (coordinateChart p).symm) x =
      pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ := by
  change phaseDerivative (phaseLinear ξ ∘ coordinateTransition q p) x = _
  have hc := ((coordinateTransition_smoothOn q p) x hx).contDiffAt
    ((coordinateTransition q p).open_source.mem_nhds hx)
  exact phaseDerivative_linear_comp (hc.differentiableAt (by simp)) ξ

omit [IsManifold planeModel ∞ M] in
lemma coordinateTransition_apply_chart (q p : M) {a : M}
    (ha : a ∈ (coordinateChart p).source) :
    coordinateTransition q p (coordinateChart p a) = coordinateChart q a := by
  change coordinateChart q ((coordinateChart p).symm (coordinateChart p a)) = _
  rw [(coordinateChart p).left_inv ha]

omit [IsManifold planeModel ∞ M] in
lemma coordinateTransition_mem_chart (q p : M) {a : M}
    (hap : a ∈ (coordinateChart p).source) (haq : a ∈ (coordinateChart q).source) :
    coordinateChart p a ∈ (coordinateTransition q p).source := by
  constructor
  · exact (coordinateChart p).map_source hap
  · change (coordinateChart p).symm (coordinateChart p a) ∈ (coordinateChart q).source
    rwa [(coordinateChart p).left_inv hap]



def atlasPhaseCovector (q p : M) (ξ : SmallModes.Base) (a : M) : SmallModes.Base :=
  phaseDerivative (atlasPhase q ξ ∘ (coordinateChart p).symm) (coordinateChart p a)

theorem actual_phase_margin_at {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (q p : M) {a : M}
    (hap : a ∈ (coordinateChart p).source) (haq : a ∈ (coordinateChart q).source)
    (ξ : SmallModes.Base) {d L ε : ℝ} (hd : 0 < d) (hL : 0 < L) (hε : 0 < ε)
    (hD : NormalFrame.gramDet (coordDeriv dx (coordinateMap F q) (coordinateChart q a))
      (coordDeriv dy (coordinateMap F q) (coordinateChart q a)) ≠ 0)
    (hdet : d ≤ |coordDet (fderiv ℝ (coordinateTransition q p) (coordinateChart p a))|)
    (hA : ‖fderiv ℝ (coordinateTransition q p) (coordinateChart p a)‖ ≤ L)
    (hB : realSecondTensor (coordinateMap F q) (coordinateChart q a) ≠ 0)
    (hmargin : ε*‖realSecondTensor (coordinateMap F q) (coordinateChart q a)‖ ≤
      ‖secondQuadratic (realSecondTensor (coordinateMap F q) (coordinateChart q a)) (-ξ.2,ξ.1)‖) :
    ‖atlasPhaseCovector q p ξ a‖ ≤ 2*L*‖ξ‖ ∧
    d^2*ε/(4*L^2)*‖realSecondTensor (coordinateMap F p) (coordinateChart p a)‖ ≤
      ‖secondQuadratic (realSecondTensor (coordinateMap F p) (coordinateChart p a))
        (-(atlasPhaseCovector q p ξ a).2,(atlasPhaseCovector q p ξ a).1)‖ ∧
    Good (realSecondTensor (coordinateMap F p) (coordinateChart p a))
      (atlasPhaseCovector q p ξ a) ∧
    realSecondTensor (coordinateMap F p) (coordinateChart p a) ≠ 0 := by
  have hx := coordinateTransition_mem_chart q p hap haq
  have he := coordinateTransition_apply_chart q p hap
  have h := actual_chart_phase_margin hF q p hx ξ hd hL hε
    (by simpa only [he] using hD) hdet hA
    (by simpa only [he] using hB) (by simpa only [he] using hmargin)
  unfold atlasPhaseCovector
  rw [actual_phase_differential q p ξ hx]
  exact h

end ClosedSurfaceR4

end

end OAI
