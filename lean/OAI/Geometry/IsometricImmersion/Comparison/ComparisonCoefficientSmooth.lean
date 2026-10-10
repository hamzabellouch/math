import OAI.Geometry.IsometricImmersion.Comparison.ActualComparisonEquation
import OAI.Geometry.IsometricImmersion.Flows.CompactParameterIntegral
import OAI.Geometry.IsometricImmersion.Darboux.QSpatialJets
import Mathlib.Topology.Compactness.Compact

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

def comparisonStateMap (P z : Coord → ℝ) (q : Coord × ℝ) : DarbouxState :=
  qHeightJetSegment P z q.2 q.1

def comparisonIntegrand (g : MetricField) (P z : Coord → ℝ) (i : Fin 6)
    (q : Coord × ℝ) : ℝ := qFirstCoefficient g i (comparisonStateMap P z q)

def comparisonParameterDomain (g : MetricField) (P z : Coord → ℝ) (U : Set Coord) :
    Set (Coord × ℝ) :=
  (U ×ˢ (univ : Set ℝ)) ∩ comparisonStateMap P z ⁻¹' darbouxQStateDomain g U

theorem comparisonStateMap_contDiffOn {P z : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U) :
    ContDiffOn ℝ ∞ (comparisonStateMap P z) (U ×ˢ (univ : Set ℝ)) := by
  have h0 : ContDiffOn ℝ ∞ (fun q : Coord × ℝ => qSolutionJet P q.1)
      (U ×ˢ (univ : Set ℝ)) := (qSolutionJet_contDiffOn hU hP).comp contDiff_fst.contDiffOn
    (fun _ hq => hq.1)
  have h1 : ContDiffOn ℝ ∞ (fun q : Coord × ℝ => qSolutionJet z q.1)
      (U ×ˢ (univ : Set ℝ)) := (qSolutionJet_contDiffOn hU hz).comp contDiff_fst.contDiffOn
    (fun _ hq => hq.1)
  exact ((contDiffOn_const.sub contDiff_snd.contDiffOn).smul h0).add
    (contDiff_snd.contDiffOn.smul h1)

theorem comparisonParameterDomain_isOpen {g : MetricField} {P z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U) :
    IsOpen (comparisonParameterDomain g P z U) :=
  (comparisonStateMap_contDiffOn hU hP hz).continuousOn.isOpen_inter_preimage
    (hU.prod isOpen_univ) (darbouxQStateDomain_isOpen hg hU)

theorem comparisonIntegrand_contDiffOn {g : MetricField} {P z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U) (i : Fin 6) :
    ContDiffOn ℝ ∞ (comparisonIntegrand g P z i) (comparisonParameterDomain g P z U) :=
  (qFirstCoefficient_contDiffOn hg hU i).comp
    ((comparisonStateMap_contDiffOn hU hP hz).mono inter_subset_left) (fun _ hq => hq.2)

theorem comparisonCoefficient_eq_parameterIntegral (g : MetricField) (P z : Coord → ℝ)
    (i : Fin 6) :
    comparisonCoefficient g P z i = compactParameterIntegral (comparisonIntegrand g P z i) := by
  funext p
  change (∫ sigma in (0 : ℝ)..1, _) = ∫ sigma in Icc (0 : ℝ) 1, _
  simp only [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  rfl

theorem comparisonCoefficient_contDiffOn {g : MetricField} {P z : Coord → ℝ}
    {U W : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U)
    (hW : IsOpen W) (hWU : W ⊆ U)
    (hsegment : ∀ p ∈ W, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U) (i : Fin 6) :
    ContDiffOn ℝ ∞ (comparisonCoefficient g P z i) W := by
  rw [comparisonCoefficient_eq_parameterIntegral]
  apply compactParameterIntegral_contDiffOn (comparisonIntegrand_contDiffOn hg hU hP hz i)
    (comparisonParameterDomain_isOpen hg hU hP hz) hW
  intro q hq
  exact ⟨⟨hWU hq.1,mem_univ _⟩,hsegment q.1 hq.1 q.2 hq.2⟩

theorem exists_comparison_coefficient_neighborhood
    {g : MetricField} {P z : Coord → ℝ} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U)
    (hS : IsCompact S) (hSU : S ⊆ U)
    (hsegment : ∀ p ∈ S, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U) :
    ∃ W : Set Coord, IsOpen W ∧ S ⊆ W ∧ W ⊆ U ∧
      (∀ p ∈ W, ∀ sigma ∈ Icc (0 : ℝ) 1,
        qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U) ∧
      ∀ i : Fin 6, ContDiffOn ℝ ∞ (comparisonCoefficient g P z i) W := by
  have hprod : S ×ˢ Icc (0 : ℝ) 1 ⊆ comparisonParameterDomain g P z U := by
    intro q hq
    exact ⟨⟨hSU hq.1,mem_univ _⟩,hsegment q.1 hq.1 q.2 hq.2⟩
  obtain ⟨W,J,hW,_,hSW,hIJ,hWJ⟩ := generalized_tube_lemma hS isCompact_Icc
    (comparisonParameterDomain_isOpen hg hU hP hz) hprod
  have hWU : W ⊆ U := by
    intro p hp
    have hj : (0 : ℝ) ∈ J := hIJ (by norm_num)
    exact (hWJ (show (p, (0 : ℝ)) ∈ W ×ˢ J from ⟨hp,hj⟩)).1.1
  have hseg : ∀ p ∈ W, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U := by
    intro p hp sigma hs
    exact (hWJ (show (p, sigma) ∈ W ×ˢ J from ⟨hp,hIJ hs⟩)).2
  exact ⟨W,hW,hSW,hWU,hseg,fun i => comparisonCoefficient_contDiffOn hg hU hP hz hW hWU hseg i⟩

end SmoothLocal.HighEquation

end

end OAI
