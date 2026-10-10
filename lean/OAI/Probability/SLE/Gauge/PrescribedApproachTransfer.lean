import OAI.Probability.SLE.Gauge.PrescribedRadiusLevels
import OAI.Probability.SLE.Gauge.PrescribedVisitBound
import OAI.Probability.SLE.Loewner.ActualApproachAtRadius
import OAI.Probability.SLE.Gauge.ActualMissedCell

namespace OAI

/-! Passing an adapted failure event through the final radius stop. The
  terminal candidate event is used only for set inclusion, outside the
  finite change of law. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

theorem prescribed_missed_cell_bound_of_adapted_failure
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (htrace : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (ν : Ω → Measure ℂ) (W : Target.WienerLaw) (n : ℕ)
    {J : ℕ} (e : Fin J → ℤ×ℕ) (C c R : ℝ) (K : Set ℂ)
    (ij : ℤ×ℤ) (hij : ij∈prescribedGridIndex R (Target.entryRadius κ W (n,none)) K)
    (u : ℝ) (hu : 0 ≤ u)
    (hgap : u+1 ≤ Target.entryPhysicalLevel κ W (n,none) (2048*Real.pi)
      (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij))
    (hsmall : 4*Target.entryRadius κ W (n,none) ≤
      (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij).im)
    (A : Set Ω)
    (hA : MeasurableSet[(actual_radiusLevelTime_stopping hB
      (fun _t => hBm.comp (measurable_const.prodMk measurable_id)) hBm hc h0
      κ hκ hκ8 γ G F hw _ (prescribedGrid_center_height (Real.exp_pos _) hij).2 u hu).measurableSpace] A)
    (hfailure : ∀ᵐ ω ∂P,
      ij∈prescribedMissedIndices κ W n e C c R K (range (γ ω)∩K) (ν ω) → ω∈A) :
    P {ω | ij∈prescribedMissedIndices κ W n e C c R K (range (γ ω)∩K) (ν ω)} ≤
      ENNReal.ofReal (uniformInverseAngleConstant κ 1*(2048*Real.pi)^codimension κ*
        initialGreen κ (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij)*
        (Target.entryRadius κ W (n,none))^codimension κ)*
      finiteCenteredLaw P κ B γ G (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij)
        (Target.entryPhysicalLevel κ W (n,none) (2048*Real.pi)
          (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij)) A := by
  classical
  let r := Target.entryRadius κ W (n,none)
  let z := prescribedGridCenter r ij
  let V := Target.entryPhysicalLevel κ W (n,none) (2048*Real.pi) z
  have hr : 0<r := Real.exp_pos _
  have hz : 0<z.im := (prescribedGrid_center_height hr hij).2
  have hgapV : u+1 ≤ V := hgap
  have hV : 0 ≤ V := by linarith
  let v : ℝ≥0 := ⟨V-u,by linarith⟩
  have hv : 1 ≤ (v:ℝ) := by change 1 ≤ V-u; linarith
  have huv : u+(v:ℝ)=V := by change u+(V-u)=V; ring
  have hrad : (2*z.im)*Real.exp (-V)=(2048*Real.pi)*r :=
    Target.entryPhysicalLevel_radius κ W _ (by positivity) hz
  have hbound := actual_conditional_approach_at_radius_stop P κ hκ hκ8 B hB hBm hc h0
    γ G F hw htrace z hz u hu v hv A hA
  rw [huv] at hbound
  have he : uniformInverseAngleConstant κ 1*Real.exp (-codimension κ*(v:ℝ))*
      ((2*z.im)*Real.exp (-u))^codimension κ*initialGreen κ z =
      uniformInverseAngleConstant κ 1*(2048*Real.pi)^codimension κ*
        initialGreen κ z*r^codimension κ := by
    calc
      _ = uniformInverseAngleConstant κ 1*
          (Real.exp (-codimension κ*(v:ℝ))*((2*z.im)*Real.exp (-u))^codimension κ)*
          initialGreen κ z := by ring
      _ = uniformInverseAngleConstant κ 1*((2*z.im)*Real.exp (-V))^codimension κ*
          initialGreen κ z := by
        rw [radius_gap_power _ u (v:ℝ) _ (by positivity),huv]
      _ = _ := by
        rw [hrad,Real.mul_rpow (by positivity) hr.le]
        ring
  rw [he] at hbound
  refine (measure_mono_ae ?_).trans hbound
  filter_upwards [hfailure] with ω hf hω
  refine ⟨hf hω,?_⟩
  obtain ⟨x,⟨⟨t,rfl⟩,_⟩,ht⟩ := (Finset.mem_filter.mp hω).2.1
  have ht' : dist (γ ω t) z < 4*r := by
    change dist (γ ω t) z ≤ 3*r at ht
    linarith
  obtain ⟨s,_,hsl,hsR⟩ := (hw ω).radius_approach_of_trace_approach
    ((hc ω).const_mul _) z (4*r) (by positivity) hsmall t ht'
  apply radiusLevelTime_finite_of_live_radius_lt ((hc ω).const_mul _) (hw ω) z V hV s hsl
  apply hsR.trans_le
  rw [hrad]
  have hp := Real.pi_pos
  nlinarith

end SLEExactGauge

end

end OAI
