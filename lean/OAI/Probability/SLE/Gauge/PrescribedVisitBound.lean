import OAI.Probability.SLE.Gauge.PrescribedCandidateCover
import OAI.Probability.SLE.SausagePointBound

namespace OAI

/-! The ordinary one-point estimate bounds every actual missed cell,
  including the bottom half-row of the shifted grid. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

theorem prescribed_missed_cell_visit_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {κ : ℝ} (hκ : 0<κ) (hκ8 : κ<8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (ν : Ω → Measure ℂ) (W : Target.WienerLaw) (n : ℕ)
    {J : ℕ} (e : Fin J → ℤ×ℕ) (C c R : ℝ) (K : Set ℂ)
    (ij : ℤ×ℤ) (hij : ij∈prescribedGridIndex R (Target.entryRadius κ W (n,none)) K) :
    P {ω | ij∈prescribedMissedIndices κ W n e C c R K (range (γ ω)∩K) (ν ω)} ≤
      ENNReal.ofReal ((sausagePointConstant κ*(4:ℝ)^codimension κ)*
        (Target.entryRadius κ W (n,none))^codimension κ*
        (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij).im^(-codimension κ)) := by
  classical
  let r := Target.entryRadius κ W (n,none)
  let z := prescribedGridCenter r ij
  have hr : 0<r := Real.exp_pos _
  have hz : 0<z.im := (prescribedGrid_center_height hr hij).2
  have hsub : {ω | ij∈prescribedMissedIndices κ W n e C c R K (range (γ ω)∩K) (ν ω)} ⊆
      {ω | ∃ t : ℝ≥0, dist (γ ω t) z < 4*r} := by
    intro ω hω
    obtain ⟨x,⟨⟨t,rfl⟩,_⟩,ht⟩ := (Finset.mem_filter.mp hω).2.1
    refine ⟨t,?_⟩
    change dist (γ ω t) z ≤ 3*r at ht
    linarith
  have hb := normalized_visit_bound hB κ hκ hκ8 γ G F hw z hz.ne' (4*r) (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hb
    (Real.rpow_nonneg (by positivity : 0 ≤ 4*r) (codimension κ))
  rw [← mul_assoc,← Real.rpow_add (by positivity : 0<4*r),add_neg_cancel,
    Real.rpow_zero,one_mul,abs_of_pos hz,
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hr.le] at hmul
  have hbound : (P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < 4*r}).toReal ≤
      (sausagePointConstant κ*(4:ℝ)^codimension κ)*r^codimension κ*z.im^(-codimension κ) := by
    convert hmul using 1
    ring
  exact (measure_mono hsub).trans ((ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
    (by have hC := sausagePointConstant_pos κ hκ hκ8; positivity)).mpr hbound)

end SLEExactGauge

end

end OAI
