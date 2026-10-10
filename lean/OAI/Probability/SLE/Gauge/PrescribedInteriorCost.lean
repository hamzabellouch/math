import OAI.Probability.SLE.Gauge.PrescribedCostConvergence
import OAI.Probability.SLE.Gauge.PrescribedVisitBound

namespace OAI

/-! The interior adapted-failure estimate bounds the cleanup cost, while
the one-point theorem pays for the boundary rows. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
local instance prescribedInteriorPathMeasurable : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance prescribedInteriorPathBorel : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩

theorem prescribed_missed_cost_tendsto_zero_of_interior
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → C(ℝ≥0,ℂ)) (hf : Measurable f)
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {κ : ℝ} (hκ : 0<κ) (hκ8 : κ<8) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (f ω) (G ω) (F ω))
    (ν : Ω → Measure ℂ) (hν : Measurable ν) (W : Target.WienerLaw)
    (J : ℕ → ℕ) (e : ∀ n, Fin (J n) → ℤ×ℕ)
    (C c R : ℝ) (hR : 0 ≤ R) (K : Set ℂ) (hK : IsClosed K)
    (A : ℝ)
    (hinterior : ∀ᶠ n in atTop, ∀ ij∈prescribedGridIndex R (Target.entryRadius κ W (n,none)) K,
      Real.exp (-(n:ℝ)) ≤ (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij).im →
      P {ω | ij∈prescribedMissedIndices κ W n (e n) C c R K (range (f ω)∩K) (ν ω)} ≤
        ENNReal.ofReal (A*(Target.entryRadius κ W (n,none))^codimension κ*
          (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij).im^(-codimension κ)*
          Real.exp (-((2:ℝ)^n/16)))) :
    Tendsto (fun n => ∫⁻ ω,prescribedMissedCost f ν κ W n (e n) C c R K ω ∂P)
      atTop (𝓝 0) := by
  let A₀ := sausagePointConstant κ*(4:ℝ)^codimension κ
  have hA₀ : 0<A₀ := by
    have hC := sausagePointConstant_pos κ hκ hκ8
    dsimp only [A₀]
    positivity
  apply prescribed_missed_cost_tendsto_zero P f hf ν hν hκ hκ8 W J e C c R hR K hK
    (max A₀ A) (hA₀.le.trans (le_max_left _ _))
  filter_upwards [hinterior] with n hn
  intro ij hij
  let r := Target.entryRadius κ W (n,none)
  let z := prescribedGridCenter r ij
  have hr : 0<r := Real.exp_pos _
  have hz : 0<z.im := (prescribedGrid_center_height hr hij).2
  have hnon : 0 ≤ max A₀ A*r^codimension κ*z.im^(-codimension κ) := by
    have hh : 0 < max A₀ A := hA₀.trans_le (le_max_left _ _)
    positivity
  by_cases hlow : z.im<Real.exp (-(n:ℝ))
  · have hv := prescribed_missed_cell_visit_bound hB hκ hκ8 (fun ω => f ω) G F hw ν W n (e n) C c R K ij hij
    refine hv.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [ite_eq_left hlow]
    calc
      _ ≤ max A₀ A*r^codimension κ*z.im^(-codimension κ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hr.le _)
      _ ≤ _ := le_mul_of_one_le_right hnon (by linarith [Real.exp_pos (-((2:ℝ)^n/16))])
  · refine (hn ij hij (le_of_not_gt hlow)).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [ite_eq_right hlow,add_zero]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right A₀ A) (Real.rpow_nonneg hr.le _))
        (Real.rpow_nonneg hz.le _)) (Real.exp_pos _).le

end SLEExactGauge

end

end OAI
