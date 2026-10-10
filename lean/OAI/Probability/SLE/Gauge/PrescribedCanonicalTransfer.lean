import OAI.Probability.SLE.Gauge.PrescribedApproachTransfer
import OAI.Probability.SLE.Gauge.PrescribedCanonicalTests

namespace OAI

/-! The original-law missed-cell estimate in terms of the finite centered
failure probability for the canonical tests. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (M : CanonicalMass P κ B hBm γ G)

theorem prescribed_missed_from_finite_failure
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (W : Target.WienerLaw) (n : ℕ) {J : ℕ} (e : Fin J → ℤ×ℕ)
    (C c R : ℝ) (K : Set ℂ) (ij : ℤ×ℤ)
    (hij : ij∈prescribedGridIndex R (Target.entryRadius κ W (n,none)) K)
    (hl : ∀ o, 0 ≤ Target.entryPhysicalLevel κ W (n,o) (2048*Real.pi)
      (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij))
    (u : ℝ) (hu : 0 ≤ u)
    (hgap : u+1 ≤ Target.entryPhysicalLevel κ W (n,none) (2048*Real.pi)
      (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij))
    (hend : ∀ i, Target.entryPhysicalLevel κ W (n,some (e i)) (2048*Real.pi)
      (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij)+
        2*Target.a κ*(Target.batchLevel κ W n:ℝ) ≤ u)
    (hsmall : 4*Target.entryRadius κ W (n,none) ≤
      (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij).im)
    (ε : ℝ) (hε : 0 ≤ ε) (hfailure :
      finiteCenteredLaw P κ B γ G (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij)
        (Target.entryPhysicalLevel κ W (n,none) (2048*Real.pi)
          (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij))
        (M.prescribedTestFailures W n e C c
          (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij)
          (fun i ω => radiusLevelTime (γ ω) (G ω)
            (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij)
            (Target.entryPhysicalLevel κ W (n,some (e i)) (2048*Real.pi)
              (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij)+
              2*Target.a κ*(Target.batchLevel κ W n:ℝ)))) ≤ ENNReal.ofReal ε) :
    P {ω | ij∈prescribedMissedIndices κ W n e C c R K (range (γ ω)∩K)
      (M.rational.physicalTerminal ω)} ≤
      ENNReal.ofReal ((uniformInverseAngleConstant κ 1*(2048*Real.pi)^codimension κ*
        (2:ℝ)^(-codimension κ))*
        (Target.entryRadius κ W (n,none))^codimension κ*
        (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij).im^(-codimension κ)*ε) := by
  let z := prescribedGridCenter (Target.entryRadius κ W (n,none)) ij
  have hz : 0<z.im := (prescribedGrid_center_height (Real.exp_pos _) hij).2
  let ℱ := Filtration.natural B (fun t =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B t)).stronglyMeasurable)
  let T (i : Fin J) (ω : Ω) : WithTop ℝ≥0 := radiusLevelTime (γ ω) (G ω) z
    (Target.entryPhysicalLevel κ W (n,some (e i)) (2048*Real.pi) z+
      2*Target.a κ*(Target.batchLevel κ W n:ℝ))
  have ht0 (i : Fin J) : 0 ≤ Target.entryPhysicalLevel κ W (n,some (e i)) (2048*Real.pi) z+
      2*Target.a κ*(Target.batchLevel κ W n:ℝ) := by
    have ha := Target.internal_a_pos hκ
    exact add_nonneg (hl _) (by positivity)
  have hT (i : Fin J) : IsStoppingTime ℱ (T i) :=
    actual_radiusLevelTime_stopping hB
      (fun t => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B t))) hBm hc h0 κ hκ hκ8 γ G F hw z hz _ (ht0 i)
  let S (ω : Ω) : WithTop ℝ≥0 := radiusLevelTime (γ ω) (G ω) z u
  have hS : IsStoppingTime ℱ S :=
    actual_radiusLevelTime_stopping hB
      (fun t => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B t))) hBm hc h0 κ hκ hκ8 γ G F hw z hz u hu
  have hTS (i : Fin J) (ω : Ω) : T i ω≤S ω :=
    radiusLevelTime_mono ((hc ω).const_mul _) (hw ω) z (ht0 i) (hend i)
  have hA := M.prescribedTestFailures_measurable_at_end W n e C c z T hT S hS hTS
  have hm := prescribed_missed_cell_bound_of_adapted_failure P κ hκ hκ8 B hB hBm hc h0
    γ G F hw hpublished M.rational.physicalTerminal W n e C c R K ij hij u hu hgap hsmall
    (M.prescribedTestFailures W n e C c z T) hA
    (M.prescribed_missed_implies_test_failures W n e C c R K ij T)
  have hr : 0<Target.entryRadius κ W (n,none) := Real.exp_pos _
  have hC := uniformInverseAngleConstant_pos κ 1 hκ hκ8 (by norm_num)
  have hG := initialGreen_pos κ z hz
  refine (hm.trans (mul_le_mul' le_rfl hfailure)).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ uniformInverseAngleConstant κ 1*
    (2048*Real.pi)^codimension κ*initialGreen κ z*(Target.entryRadius κ W (n,none))^codimension κ)]
  apply ENNReal.ofReal_le_ofReal
  have hh := mul_le_mul_of_nonneg_left (initialGreen_le_height κ hκ hκ8 z hz)
    (by positivity : 0 ≤ uniformInverseAngleConstant κ 1*(2048*Real.pi)^codimension κ)
  have hh' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh
    (Real.rpow_nonneg hr.le (codimension κ))) hε
  dsimp only [z] at hh'
  convert hh' using 1
  ring

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
