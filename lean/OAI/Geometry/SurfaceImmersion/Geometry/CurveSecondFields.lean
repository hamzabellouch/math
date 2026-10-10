import OAI.Geometry.SurfaceImmersion.Atlas.PhaseMetricPositive
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseMetricRegularity
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseDiskNormalGluing

namespace OAI

/-! Smooth global representatives of second-form fields along a compact curve.
A cutoff in its own phase chart extends the field without choosing a normal frame. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.RealModes
open SmallModes NormalFrame

lemma realSecondForm_field_smoothAt {F : RField 4} {v w : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hv : ContDiff ℝ ∞ v) (hw : ContDiff ℝ ∞ w)
    {p : Base} (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => realSecondForm F (v q) (w q) q) p := by
  have hDF := hF.fderiv_right (m := ∞) (by simp)
  have hDDF := hDF.fderiv_right (m := ∞) (by simp)
  have heq : (fun q => realSecondForm F (v q) (w q) q) =
      fun q => realNormalPart (coordDeriv dx F q) (coordDeriv dy F q)
        (fderiv ℝ (fderiv ℝ F) q (v q) (w q)) := by
    funext q
    unfold realSecondForm
    rw [real_second_coordDeriv ((hDF.differentiable (by simp)) q)]
  rw [heq]
  exact contDiffAt_realNormalPart (contDiff_real_coordDeriv hF dx).contDiffAt
    (contDiff_real_coordDeriv hF dy).contDiffAt
    ((hDDF.clm_apply hv).clm_apply hw).contDiffAt hD

end ClosedSurfaceR4.RealModes
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SmallModes NormalFrame SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phase_gram_ne_zero (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    {p : SmallModes.Base} (hp : baseEquiv.symm p ∈ e.target)
    (ha : A.chartWeight i (e.symm (baseEquiv.symm p)) ≠ 0) :
    gramDet (coordDeriv dx (A.phaseRealChartMap i e.symm F) p)
      (coordDeriv dy (A.phaseRealChartMap i e.symm F) p) ≠ 0 := by
  rw [A.phaseMetricRead_isometry_det i hi hF ha]
  have hh := (A.phaseMetricRead_positive i g e he hi hp ha).2.ne'
  simpa only [baseEquiv.apply_symm_apply] using hh

/-- This cutoff is selected from the curve and phase chart before selecting
any later isometric immersion. -/
lemma phase_curve_cutoff (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm)
    {K : Set SmallModes.Base} (hK : IsCompact K)
    (hKt : ∀ p ∈ K, baseEquiv.symm p ∈ e.target)
    (hKa : ∀ p ∈ K, A.chartWeight i (e.symm (baseEquiv.symm p)) ≠ 0) :
    ∃ β : SmallModes.Base → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
      (∀ p ∈ K, β p = 1) ∧ ∀ p ∈ tsupport β,
        baseEquiv.symm p ∈ e.target ∧ A.chartWeight i (e.symm (baseEquiv.symm p)) ≠ 0 := by
  let U : Set SmallModes.Base := baseEquiv.symm ⁻¹' e.target ∩
    {p | A.chartWeight i (e.symm (baseEquiv.symm p)) ≠ 0}
  have hU : IsOpen U := (e.open_target.preimage baseEquiv.symm.continuous).inter
    (isOpen_ne.preimage ((A.chartWeight_smooth i).continuous.comp
      (hi.continuous.comp baseEquiv.symm.continuous)))
  obtain ⟨β,hβ,hβc,_,hβs,hβone⟩ := CollarVelocity.compact_cutoff hK hU
    (fun p hp => ⟨hKt p hp,hKa p hp⟩)
  exact ⟨β,hβ,hβc,hβone,fun p hp => hβs hp⟩

def phaseCurveSecondField (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (β : SmallModes.Base → ℝ) (F : M → Space) (v w : SmallModes.Base → SmallModes.Base) : M → Space :=
  restore (i : M) (A.outer i) (fun x => spaceCoordinates.symm
    (β (baseEquiv (e x)) • realSecondForm (A.phaseRealChartMap i e.symm F)
      (v (baseEquiv (e x))) (w (baseEquiv (e x))) (baseEquiv (e x))))

lemma phaseCurveSecondField_smooth (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    {β : SmallModes.Base → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hs : ∀ p ∈ tsupport β, baseEquiv.symm p ∈ e.target ∧
      A.chartWeight i (e.symm (baseEquiv.symm p)) ≠ 0)
    {v w : SmallModes.Base → SmallModes.Base} (hv : ContDiff ℝ ∞ v) (hw : ContDiff ℝ ∞ w) :
    ContMDiff planeModel spaceModel ∞ (A.phaseCurveSecondField i e β F v w) := by
  have hB : ContDiff ℝ ∞ (fun p => β p •
      realSecondForm (A.phaseRealChartMap i e.symm F) (v p) (w p) p) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p ∈ tsupport β
    · exact hβ.contDiffAt.smul (realSecondForm_field_smoothAt
        (A.phaseRealChartMap_smooth i hi hF.1) hv hw (A.phase_gram_ne_zero i e he hi hF
          (hs p hp).1 (hs p hp).2))
    · apply (contDiffAt_const (c := (0 : Vec))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
      simp only [Pi.zero_apply] at hq
      simp only [hq,zero_smul]
  exact restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
    (spaceCoordinates.symm.contDiff.comp (hB.comp (baseEquiv.contDiff.comp he)))

omit [CompactSpace M] in
lemma phaseCurveSecondField_eq (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (β : SmallModes.Base → ℝ) (F : M → Space) (v w : SmallModes.Base → SmallModes.Base)
    {p : M} (hp : p ∈ (chart (i : M)).source) (ho : A.outer i p = 1)
    (hβ : β (baseEquiv (e (chart (i : M) p))) = 1) :
    spaceCoordinates (A.phaseCurveSecondField i e β F v w p) =
      realSecondForm (A.phaseRealChartMap i e.symm F)
        (v (baseEquiv (e (chart (i : M) p)))) (w (baseEquiv (e (chart (i : M) p))))
        (baseEquiv (e (chart (i : M) p))) := by
  simp only [phaseCurveSecondField,restore,indicator_of_mem hp,ho,hβ,one_smul,
    spaceCoordinates.apply_symm_apply]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
