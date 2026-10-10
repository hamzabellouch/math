import OAI.Probability.SLE.Gauge.PrescribedCoverExpectation
import OAI.Probability.SLE.Gauge.CoverNumerics

namespace OAI

/-! Expected cleanup cost is the finite sum of the actual missed-cell
probabilities. Terminal candidate events remain outside the stopped-law
calculation that will bound these probabilities. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
local instance prescribedMissedPathMeasurable : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance prescribedMissedPathBorel : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩

lemma prescribed_missed_cost_eq_sum
    {Ω : Type*} (f : Ω → C(ℝ≥0,ℂ)) (ν : Ω → Measure ℂ)
    {J : ℕ} (κ : ℝ) (W : Target.WienerLaw) (n : ℕ) (e : Fin J → ℤ×ℕ)
    (C c R : ℝ) (K : Set ℂ) (ω : Ω) :
    prescribedMissedCost f ν κ W n e C c R K ω =
      ∑ ij∈prescribedGridIndex R (Target.entryRadius κ W (n,none)) K,
        {ω | ij∈prescribedMissedIndices κ W n e C c R K (range (f ω)∩K) (ν ω)}.indicator
          (fun _ => ENNReal.ofReal (36*(n:ℝ)*(Target.entryRadius κ W (n,none))^Target.d κ)) ω := by
  classical
  unfold prescribedMissedCost
  rw [← nsmul_eq_mul,← Finset.sum_const]
  rw [prescribedMissedIndices,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ij hij
  by_cases h : ω∈{ω | ij∈prescribedMissedIndices κ W n e C c R K (range (f ω)∩K) (ν ω)}
  · rw [indicator_of_mem h]
    rw [ite_eq_left]
    exact (Finset.mem_filter.mp h).2
  · rw [indicator_of_notMem h]
    rw [ite_eq_right]
    intro hp
    exact h (Finset.mem_filter.mpr ⟨hij,hp⟩)

theorem expected_prescribed_missed_cost_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → C(ℝ≥0,ℂ)) (hf : Measurable f)
    (ν : Ω → Measure ℂ) (hν : Measurable ν)
    {J : ℕ} (κ : ℝ) (W : Target.WienerLaw) (n : ℕ) (e : Fin J → ℤ×ℕ)
    (C c R : ℝ) (K : Set ℂ) (hK : IsClosed K) (bound : ℤ×ℤ → ℝ≥0∞)
    (hb : ∀ ij∈prescribedGridIndex R (Target.entryRadius κ W (n,none)) K,
      P {ω | ij∈prescribedMissedIndices κ W n e C c R K (range (f ω)∩K) (ν ω)} ≤ bound ij) :
    (∫⁻ ω,prescribedMissedCost f ν κ W n e C c R K ω ∂P) ≤
      ENNReal.ofReal (36*(n:ℝ)*(Target.entryRadius κ W (n,none))^Target.d κ) *
        ∑ ij∈prescribedGridIndex R (Target.entryRadius κ W (n,none)) K, bound ij := by
  simp_rw [prescribed_missed_cost_eq_sum f ν κ W n e C c R K]
  rw [Finset.mul_sum]
  exact expected_missed_cell_cost P _ _
    (fun ij _ => prescribedMissedIndices_measurable f hf ν hν κ W n e C c R K hK ij)
    (fun _ => _) bound hb

end SLEExactGauge

end

end OAI
