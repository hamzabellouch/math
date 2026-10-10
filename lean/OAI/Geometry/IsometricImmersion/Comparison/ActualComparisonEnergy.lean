import OAI.Geometry.IsometricImmersion.Metrics.SmoothMetricRestriction
import OAI.Geometry.IsometricImmersion.Comparison.ComparisonCoefficientBounds
import OAI.Geometry.IsometricImmersion.Darboux.QContainingRectangle

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE
open SmoothLocal.Hyperbolic SmoothLocal.Taylor

def metricComparisonSource (g gRef : MetricField) (P z : Coord → ℝ) (p : Coord) : ℝ :=
  sixVariableQ g (qSolutionJet z p)-sixVariableQ gRef (qSolutionJet z p)-qResidual gRef P p

theorem metricComparisonSource_contDiffOn
    {g gRef : MetricField} {P z : Coord → ℝ} {V : Set Coord}
    (hg : SmoothPositiveOn g V) (hgRef : SmoothPositiveOn gRef V) (hV : IsOpen V)
    (hP : ContDiffOn ℝ ∞ P V) (hz : ContDiffOn ℝ ∞ z V)
    (hxx : ∀ p ∈ V, covHessian g z p 0 0 ≠ 0)
    (hrefz : ∀ p ∈ V, covHessian gRef z p 0 0 ≠ 0)
    (hrefP : ∀ p ∈ V, covHessian gRef P p 0 0 ≠ 0) :
    ContDiffOn ℝ ∞ (metricComparisonSource g gRef P z) V := by
  have hzJet := qSolutionJet_contDiffOn hV hz
  have hPJet := qSolutionJet_contDiffOn hV hP
  have hQ := (sixVariableQ_contDiffOn hg hV).comp hzJet
    (fun p hp => qSolutionJet_mem_domain hp (hxx p hp))
  have hQz := (sixVariableQ_contDiffOn hgRef hV).comp hzJet
    (fun p hp => qSolutionJet_mem_domain hp (hrefz p hp))
  have hQP := (sixVariableQ_contDiffOn hgRef hV).comp hPJet
    (fun p hp => qSolutionJet_mem_domain hp (hrefP p hp))
  exact (hQ.sub hQz).sub ((partial_contDiffOn (partial_contDiffOn hP hV 1) hV 1).sub hQP)

theorem metricComparisonSource_eq_actualSheared (gStar gTau : MetricField)
    (z P : Coord → ℝ) (q0 : ℝ) :
    metricComparisonSource (Pulse.metricInShearCoordinates gTau q0)
      (Pulse.metricInShearCoordinates gStar q0) P (Pulse.heightInShearCoordinates z q0) =
      Pulse.actualComparisonSource gStar gTau z q0 P := rfl

def comparisonEnergySpeed (C : ℝ) : ℝ := C+Real.sqrt C
def comparisonEnergyRate (C Z0 Z s0 : ℝ) : ℝ :=
  8*(C*(max 1 Z0+max 1 Z))*(1+1/s0)

theorem exists_actual_comparison_energy
    {gRef : MetricField} {U S : Set Coord}
    (hgRef : SmoothPositiveOn gRef U) (hU : IsOpen U)
    (hS : IsCompact S) (hSU : S ⊆ U)
    (R Z0 Z : ℝ) (hR : 0 ≤ R) {c s0 : ℝ} (hc : 0 < c) (hs0 : 0 < s0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (g : MetricField) (P z : Coord → ℝ) (V : Set Coord)
      (boxRadius width a b : ℝ),
      IsOpen V → V ⊆ U → SmoothPositiveOn g V →
      ContDiffOn ℝ ∞ P V → ContDiffOn ℝ ∞ z V →
      0 < width → width < boxRadius → a ≤ b →
      closedRectangle (-boxRadius) boxRadius a b ⊆ V →
      closedRectangle (-boxRadius) boxRadius a b ⊆ S →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, ‖p‖ ≤ R) →
      CoordinateBound P (closedRectangle (-boxRadius) boxRadius a b) 3 Z0 →
      CoordinateBound z (closedRectangle (-boxRadius) boxRadius a b) 3 Z →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b,
        (covHessian g z p).det = gaussianCurvature g p*heightEnergy g z p) →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, covHessian g z p 0 0 ≠ 0) →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, ∀ sigma ∈ Icc (0 : ℝ) 1,
        c ≤ |stateQDenominator gRef (qHeightJetSegment P z sigma p)| ∧
          s0 ≤ qFirstCoefficient gRef 5 (qHeightJetSegment P z sigma p)) →
      (∀ x ∈ Ioo (-boxRadius) boxRadius, P (boxPoint x a)=z (boxPoint x a)) →
      (∀ x ∈ Ioo (-boxRadius) boxRadius,
        coordPartial 1 P (boxPoint x a)=coordPartial 1 z (boxPoint x a)) →
      2*comparisonEnergySpeed C*(b-a)<2*width →
      Real.sqrt (movingEnergy (-width) width a (comparisonEnergySpeed C)
        (comparisonCoefficient gRef P z 5) (comparisonDifference P z) b) ≤
        Real.exp (comparisonEnergyRate C Z0 Z s0*(b-a))*
          ∫ t in a..b, movingSourceNorm (-width) width a (comparisonEnergySpeed C)
            (metricComparisonSource g gRef P z) t := by
  obtain ⟨C,hC,hbounds⟩ := exists_uniform_comparison_coefficient_bounds hgRef hU hS hSU R Z0 Z hR hc
  refine ⟨C,hC,?_⟩
  intro g P z V boxRadius width a b hV hVU hg hP hz hw hwR hab hboxV hboxS hpB hPZ hzZ
    hD hxx hmargin hvalue hvelocity hlength
  let T := closedRectangle (-boxRadius) boxRadius a b
  let speed := comparisonEnergySpeed C
  let MC := C*(max 1 Z0+max 1 Z)
  have hgRefV : SmoothPositiveOn gRef V := hgRef.mono hVU
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hs : 0 ≤ speed := add_nonneg hCp.le (Real.sqrt_nonneg _)
  have hMC : 0 ≤ MC := mul_nonneg hCp.le (by positivity)
  have hCmc : C ≤ MC := by
    have hsum : 1 ≤ max 1 Z0+max 1 Z := by
      linarith [le_max_left (1 : ℝ) Z0,le_max_left (1 : ℝ) Z]
    exact le_mul_of_one_le_right hCp.le hsum
  have hseg : ∀ p ∈ T, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain gRef V := by
    intro p hp sigma hsigma
    refine ⟨by simpa only [statePoint_qHeightJetSegment] using hboxV hp,?_⟩
    exact abs_pos.mp (hc.trans_le (hmargin p hp sigma hsigma).1)
  obtain ⟨W,hW,hTW,hWV,hWseg,hcoeffSmooth⟩ := exists_comparison_coefficient_neighborhood
    hgRefV hV hP hz (closedRectangle_compact _ _ _ _) hboxV hseg
  let V0 := W ∩ (fun p => covHessian g z p 0 0) ⁻¹' ({0}ᶜ : Set ℝ)
  have hV0 : IsOpen V0 := ((covHessian_contDiffOn hg hV hz 0 0).continuousOn.mono hWV).isOpen_inter_preimage
    hW isClosed_singleton.isOpen_compl
  have hTV0 : T ⊆ V0 := fun p hp => ⟨hTW hp,hxx p hp⟩
  obtain ⟨radius,lo,hi,hRad,hlo,hhi,hrect⟩ := exists_containing_coordinateRectangle hV0
    (hw.trans hwR) hab hTV0
  let Rect := coordinateRectangle radius lo hi
  have hRect : IsOpen Rect := coordinateRectangle_isOpen _ _ _
  have hRectW : Rect ⊆ W := fun p hp => (hrect hp).1
  have hRectV : Rect ⊆ V := hRectW.trans hWV
  have hgsR : SmoothPositiveOn gRef Rect := hgRefV.mono hRectV
  have hgR : SmoothPositiveOn g Rect := hg.mono hRectV
  have hPR := hP.mono hRectV
  have hzR := hz.mono hRectV
  have hxR : ∀ p ∈ Rect, covHessian g z p 0 0 ≠ 0 := fun p hp => (hrect hp).2
  have hsegR : ∀ p ∈ Rect, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain gRef Rect := by
    intro p hp sigma hsigma
    exact ⟨by simpa only [statePoint_qHeightJetSegment] using hp,(hWseg p (hRectW hp) sigma hsigma).2⟩
  have hrefP : ∀ p ∈ Rect, covHessian gRef P p 0 0 ≠ 0 := by
    intro p hp
    simpa only [qHeightJetSegment,stateSegment_zero,stateQDenominator_qSolutionJet] using
      (hsegR p hp 0 (by norm_num)).2
  have hrefz : ∀ p ∈ Rect, covHessian gRef z p 0 0 ≠ 0 := by
    intro p hp
    simpa only [qHeightJetSegment,stateSegment_one,stateQDenominator_qSolutionJet] using
      (hsegR p hp 1 (by norm_num)).2
  have hsource := metricComparisonSource_contDiffOn hgR hgsR hRect hPR hzR hxR hrefz hrefP
  have hcoeffR (i : Fin 6) : ContDiffOn ℝ ∞ (comparisonCoefficient gRef P z i) Rect :=
    (hcoeffSmooth i).mono hRectW
  have hnum := hbounds P z V T hV hVU hP hz hboxS hboxV hpB hPZ hzZ
    (fun p hp sigma hsigma => (hmargin p hp sigma hsigma).1)
  have hslabT : shrinkingSlab (-width) width a b speed ⊆ T := by
    intro p hp
    change p 1 ∈ Icc a b ∧ p 0 ∈ Icc (-width+speed*(p 1-a)) (width-speed*(p 1-a)) at hp
    have hinc : 0 ≤ speed*(p 1-a) := mul_nonneg hs (sub_nonneg.mpr hp.1.1)
    exact ⟨⟨by linarith [hp.2.1],
      by linarith [hp.2.2]⟩,hp.1⟩
  have hfloor (p : Coord) (hp : p ∈ shrinkingSlab (-width) width a b speed) :
      s0 ≤ comparisonCoefficient gRef P z 5 p :=
    averagedQCoefficient_lower hgRefV hV (hseg p (hslabT hp)) 5
      (fun sigma hsigma => (hmargin p (hslabT hp) sigma hsigma).2)
  have hchar (p : Coord) (hp : p ∈ shrinkingSlab (-width) width a b speed) :
      |comparisonCoefficient gRef P z 4 p|+Real.sqrt (comparisonCoefficient gRef P z 5 p) ≤ speed :=
    add_le_add (hnum 4 p (hslabT hp)).1
      (Real.sqrt_le_sqrt ((le_abs_self _).trans (hnum 5 p (hslabT hp)).1))
  have hEq (p : Coord) (hp : p ∈ shrinkingSlab (-width) width a b speed) :=
    comparison_equation_from_darboux hg hgRefV hV hz hP (hboxV (hslabT hp))
      (hD p (hslabT hp)) (hxx p (hslabT hp)) (hseg p (hslabT hp))
  have hprop := moving_slab_energy_propagation (hcoeffR 4) (hcoeffR 5) (hcoeffR 3) (hcoeffR 2)
    (hzR.sub hPR) hsource (hw.trans (hwR.trans hRad)) hab hs
    (by linarith) (by linarith) ⟨hlo,hab.trans_lt hhi⟩ ⟨hlo.trans_le hab,hhi⟩
    (by simpa only [sub_neg_eq_add,two_mul] using hlength) hs0 hMC hfloor
    (fun p hp => ⟨(hnum 3 p (hslabT hp)).1.trans hCmc,
      (hnum 2 p (hslabT hp)).1.trans hCmc,(hnum 4 p (hslabT hp)).2 0,
      (hnum 5 p (hslabT hp)).2 0,(hnum 5 p (hslabT hp)).2 1⟩) hchar hEq
  have hzero := comparison_initial_energy_zero (S := comparisonCoefficient gRef P z 5) hV hz hP
    (show -width ≤ width by linarith)
    (fun x hx => hboxV (by
      simpa [closedRectangle,boxPoint]
        using And.intro (And.intro hx.1.le hx.2.le) (And.intro (le_refl a) hab))) hvalue hvelocity
    (by linarith) hwR
  have hdiff : (fun x => z x-P x) = SmoothLocal.HighEquation.comparisonDifference P z := rfl
  rw [hdiff,hzero] at hprop
  simpa only [hzero,Real.sqrt_zero,zero_add,comparisonEnergyRate,MC] using hprop

end SmoothLocal.HighEquation

end

end OAI
