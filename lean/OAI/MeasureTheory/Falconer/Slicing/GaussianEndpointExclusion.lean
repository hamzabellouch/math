import OAI.MeasureTheory.Falconer.Geometry.EndpointChartObstruction
import OAI.MeasureTheory.Falconer.Geometry.EndpointChartSelection
import OAI.MeasureTheory.Falconer.Geometry.SelectedChartRelation
import OAI.MeasureTheory.Falconer.Slicing.UnnormalizedSliceBalls
import OAI.MeasureTheory.Falconer.Geometry.SelectedChartGeometry

namespace OAI

/-! # The endpoint obstruction on the actual pruned Gaussian slice laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n h N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem gaussian_endpoint_slice_exclusion
    (μ : Measure (Space (n+1))) (ν₀ : Measure (Space n))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν₀]
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) (hν₀ : ∀ᵐ p ∂ν₀, ‖p‖ ≤ 1)
    (A : Fin h → Space (n+1)) (z : Space h)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space 3)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    (J : Sphere (n+1) → Finset ι) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
    (v : ι → Space (n+1)) (TD : Fin (N+1) → ℝ≥0∞)
    (G : Set (Space n × Space n)) (hG : MeasurableSet G)
    {P M Mdir Mrow T a κ C s a₀ b : ℝ} {Bpair Btriple : ℝ≥0∞}
    (hP : 0 ≤ P) (hPM : P ≤ M) (hMdir : Mdir ≤ M) (hM : 0 < M) (hMrow : 0 ≤ Mrow)
    (hT : 0 ≤ T) (ha : 0 ≤ a) (hC : 0 ≤ C) (hs : 0 ≤ s) (hb : 0 < b)
    (ha₀ : 1 ≤ a₀) (haK : 4+4*(h:ℝ) ≤ a₀)
    (hA : ∀ i, ‖A i‖ ≤ Mrow)
    (hprojection : ∀ x : Space (n+1), ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ 2*‖gaussianRowMap A x‖)
    (hsmall : 2*(h:ℝ)*(1/(2:ℝ)^N) < 1)
    (hbounded : ∀ u ∈ E, ‖u.1‖ ≤ 1/4)
    (hanchor : ∀ w, ∀ i ∈ J w, ‖v i‖ ≤ 1/4)
    (hcover : ∀ u ∈ E, ∃ i ∈ J u.2,
      ‖perpendicularPart (u.2:Space (n+1)) (u.1-v i)‖ ≤ C*(1/(2:ℝ)^N))
    (hpair : ((gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N)).prod
      (gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N))) Gᶜ ≤ Bpair)
    (htriple : ((gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N)).prod
      ((gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N)).prod
        (gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N))))
      (badChartTriples G (2*(1/(2:ℝ)^N)^a)) ≤ Btriple)
    (hbad : Btriple+2*ENNReal.ofReal M*Bpair ≤ ENNReal.ofReal (b^3/(4*M^3)))
    (hmass : (1/(2:ℝ)^N)^κ ≤ b^3/(2*M^5))
    (hcount : T ≤ (1/(2:ℝ)^N)^(-1-κ))
    (hcoef : P*(4*a₀)^s ≤ (1/(2:ℝ)^N)^(-κ))
    (herror : 144*(h:ℝ)*(1/(2:ℝ)^N) ≤ 3*((1/(2:ℝ)^N)^a)^2)
    (hbudget : ((1/(2:ℝ)^N)^(-1-κ))^3*((6*C+35)/(1/(2:ℝ)^N)^a)^6*
      ((1/(2:ℝ)^N)^(-κ)*(6*(1/(2:ℝ)^N))^s)^2 < ((1/(2:ℝ)^N)^κ)^2) :
    gaussianPrunedPairMass μ (Measure.map gnomonicChart ν₀) (1/(2:ℝ)^N)
      (fun g : Fin (N+1) => (1/(2:ℝ)^g.val)/2)
      (fun g => ENNReal.ofReal (P*(1/(2:ℝ)^g.val)^s)) TD (ENNReal.ofReal Mdir)
      (gaussianActiveRelation E J v
        ((1/(2:ℝ)^N)+(2*(1/4))*(1/(2:ℝ)^N)+(C*(1/(2:ℝ)^N))*Mrow)
        (ENNReal.ofReal T) true) (A,z) < ENNReal.ofReal b := by
  classical
  let δ : ℝ := 1/(2:ℝ)^N
  let r : Fin (N+1) → ℝ := fun g => (1/(2:ℝ)^g.val)/2
  let TP : Fin (N+1) → ℝ≥0∞ := fun g => ENNReal.ofReal (P*(1/(2:ℝ)^g.val)^s)
  let α := (gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z))
  let D := gnomonicChart ⁻¹' gaussianDirectionGood (Measure.map gnomonicChart ν₀) δ r TD (ENNReal.ofReal Mdir) A
  let β := (gaussianChartSliceMeasure ν₀ A δ).restrict D
  let R := δ+(2*(1/4))*δ+(C*δ)*Mrow
  let F := selectedChartRelation A z δ E J v R T
  let L : Space n → Finset (Space (n+1)) := fun p =>
    (cappedActiveAnchors A z (J (gnomonicChart p)) v R T).image v
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1)
      (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) : (1:ℝ) ≤ (2:ℝ)^N)
  have hαP : α univ ≤ ENNReal.ofReal P := by
    have hh := gaussianPointGood_mass μ δ r TP (A,z) hμ 0 (by norm_num [r])
    simpa only [TP,Fin.val_zero,pow_zero,div_one,Real.one_rpow,mul_one] using hh
  have hα : α univ ≤ ENNReal.ofReal M := hαP.trans (ENNReal.ofReal_le_ofReal hPM)
  have hβ : β univ ≤ ENNReal.ofReal M :=
    (gnomonic_pruned_mass ν₀ A δ r TD (ENNReal.ofReal Mdir)).trans (ENNReal.ofReal_le_ofReal hMdir)
  have hF : MeasurableSet F := selectedChartRelation_measurable A z δ E hE J hJ v R T
  have hcost := restricted_chart_exceptional_triples ν₀ A δ D G (2*δ^a) hβ hpair htriple
  have hball := gaussian_point_endpoint_ball μ A z e N hP hs ha₀ haK hprojection hαP hcoef
  have hboundF := selectedChartRelation_point_bound A z δ E J v R T hbounded
  have hbandF := selectedChartRelation_kernel_band A z δ E J v R T hprojection
  have hcoverF := selectedChartRelation_original_cover A z δ E J v hMrow hT hA hbounded hanchor hcover
  have hcardL : ∀ p, ((L p).card:ℝ) ≤ δ^(-1-κ) := fun p =>
    (capped_original_cover_card A z (J (gnomonicChart p)) v R hT).trans hcount
  have hh := endpoint_chart_incidence_obstruction α β (gaussianRowMap A).ker e F hF G hG L
    hδ hδ1
    ha hC hsmall hM hb hα hβ (fun _ hu => hu.2) hboundF hbandF hball hcoverF hcardL
    (hcost.trans hbad) hmass (by nlinarith [herror]) hbudget
  rw [selected_chart_incidence_eq μ ν₀ hν₀ A z δ r TP TD (ENNReal.ofReal Mdir) E hE J hJ v R T] at hh
  exact hh

end Falconer

end OAI
