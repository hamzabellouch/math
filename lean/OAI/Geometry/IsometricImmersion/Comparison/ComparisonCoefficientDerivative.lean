import OAI.Geometry.IsometricImmersion.Comparison.ComparisonCoefficientSmooth
import OAI.Geometry.IsometricImmersion.Darboux.QLowActualBounds
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Analytic
open SmoothLocal.Geometry

theorem compactParameterIntegral_coordPartial
    {H : Coord × ℝ → ℝ} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContDiffOn ℝ ∞ H D) (hD : IsOpen D) (hU : IsOpen U)
    (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D) {p : Coord} (hp : p ∈ U) (j : Fin 2) :
    coordPartial j (compactParameterIntegral H) p =
      ∫ sigma in Icc (0 : ℝ) 1, compactParameterPartial H (p,sigma) (Pi.single j 1) := by
  have hH1 : ContDiffOn ℝ 1 H D := hH.of_le (by simp)
  have hd := compactParameterIntegral_hasFDerivAt hH1 hD hU hUD hp
  have hpart : ContinuousOn (compactParameterPartial H) D :=
    (compactParameterPartial_contDiffOn hD 0 hH1).continuousOn
  have hint : Integrable (fun sigma => compactParameterPartial H (p,sigma))
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (parameter_slice_continuousOn hpart hUD hp).integrableOn_compact isCompact_Icc
  change fderiv ℝ (compactParameterIntegral H) p (Pi.single j 1) = _
  rw [hd.fderiv]
  exact ContinuousLinearMap.integral_apply hint (Pi.single j 1)

end SmoothLocal.Analytic

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

theorem comparisonIntegrand_parameter_partial
    {g : MetricField} {P z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} {sigma : ℝ} (hp : p ∈ U)
    (hsegment : qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U)
    (i : Fin 6) (j : Fin 2) :
    compactParameterPartial (comparisonIntegrand g P z i) (p,sigma) (Pi.single j 1) =
      fderiv ℝ (qFirstCoefficient g i) (qHeightJetSegment P z sigma p)
        ((1-sigma) • coordPartial j (qSolutionJet P) p +
          sigma • coordPartial j (qSolutionJet z) p) := by
  have hJP := ((qSolutionJet_contDiffOn hU hP).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hJz := ((qSolutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hQ := ((qFirstCoefficient_contDiffOn hg hU i).contDiffAt
    ((darbouxQStateDomain_isOpen hg hU).mem_nhds hsegment)).differentiableAt (by simp)
  have hstate : HasFDerivAt (fun x => qHeightJetSegment P z sigma x)
      ((1-sigma) • fderiv ℝ (qSolutionJet P) p + sigma • fderiv ℝ (qSolutionJet z) p) p :=
    (hJP.hasFDerivAt.const_smul (1-sigma)).add (hJz.hasFDerivAt.const_smul sigma)
  have hchain := hQ.hasFDerivAt.comp p hstate
  have hparam := compactParameter_slice_hasFDerivAt
    ((comparisonIntegrand_contDiffOn hg hU hP hz i).of_le (by simp))
    (comparisonParameterDomain_isOpen hg hU hP hz)
    (show (p,sigma) ∈ comparisonParameterDomain g P z U from
      ⟨⟨hp,mem_univ _⟩,hsegment⟩)
  have he := hparam.unique hchain
  simpa only [ContinuousLinearMap.comp_apply,add_apply,
    smul_apply,coordPartial] using
      congrArg (fun A : Coord →L[ℝ] ℝ => A (Pi.single j 1)) he

theorem comparisonCoefficient_partial
    {g : MetricField} {P z : Coord → ℝ} {U W : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U)
    (hW : IsOpen W) (hWU : W ⊆ U)
    (hsegment : ∀ p ∈ W, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U)
    {p : Coord} (hp : p ∈ W) (i : Fin 6) (j : Fin 2) :
    coordPartial j (comparisonCoefficient g P z i) p =
      ∫ sigma in (0 : ℝ)..1,
        fderiv ℝ (qFirstCoefficient g i) (qHeightJetSegment P z sigma p)
          ((1-sigma) • coordPartial j (qSolutionJet P) p +
            sigma • coordPartial j (qSolutionJet z) p) := by
  rw [comparisonCoefficient_eq_parameterIntegral]
  have hUD : W ×ˢ Icc (0 : ℝ) 1 ⊆ comparisonParameterDomain g P z U := by
    intro q hq
    exact ⟨⟨hWU hq.1,mem_univ _⟩,hsegment q.1 hq.1 q.2 hq.2⟩
  rw [compactParameterIntegral_coordPartial (comparisonIntegrand_contDiffOn hg hU hP hz i)
    (comparisonParameterDomain_isOpen hg hU hP hz) hW hUD hp j,
    intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro sigma hs
  exact comparisonIntegrand_parameter_partial hg hU hP hz (hWU hp) (hsegment p hp sigma hs) i j

end SmoothLocal.HighEquation

end

end OAI
