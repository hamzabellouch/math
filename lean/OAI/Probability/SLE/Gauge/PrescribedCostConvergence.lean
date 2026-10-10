import OAI.Probability.SLE.Gauge.PrescribedGridError

namespace OAI

/-! The source's pointwise missed-cell bounds imply vanishing expected
  cleanup cost for the exact prescribed gauge. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
local instance prescribedCostPathMeasurable : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance prescribedCostPathBorel : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩

theorem expected_prescribed_missed_cost_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → C(ℝ≥0,ℂ)) (hf : Measurable f)
    (ν : Ω → Measure ℂ) (hν : Measurable ν)
    {κ : ℝ} (hκ : 0<κ) (hκ8 : κ<8) (W : Target.WienerLaw)
    (n : ℕ) {J : ℕ} (e : Fin J → ℤ×ℕ)
    (C c R : ℝ) (hR : 0 ≤ R) (K : Set ℂ) (hK : IsClosed K)
    (η ε A : ℝ) (hη : 0 ≤ η) (hε : 0 ≤ ε) (hA : 0 ≤ A)
    (hr1 : Target.entryRadius κ W (n,none) ≤ 1)
    (hb : ∀ ij∈prescribedGridIndex R (Target.entryRadius κ W (n,none)) K,
      P {ω | ij∈prescribedMissedIndices κ W n e C c R K (range (f ω)∩K) (ν ω)} ≤
        ENNReal.ofReal (A*(Target.entryRadius κ W (n,none))^codimension κ*
          (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij).im^(-codimension κ)*
          (ε + if (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij).im<η then 1 else 0))) :
    (∫⁻ ω,prescribedMissedCost f ν κ W n e C c R K ω ∂P) ≤
      ENNReal.ofReal ((36*A*((2*R+5)*((2:ℝ)^codimension κ/(1-codimension κ))))*
        ((R+3)^(1-codimension κ)*((n:ℝ)*ε)+(n:ℝ)*(η+Target.entryRadius κ W (n,none))^(1-codimension κ))) := by
  let r := Target.entryRadius κ W (n,none)
  let b := fun ij => A*r^codimension κ*(prescribedGridCenter r ij).im^(-codimension κ)*
    (ε + if (prescribedGridCenter r ij).im<η then 1 else 0)
  have hr : 0<r := Real.exp_pos _
  have hb0 (ij) (hij : ij∈prescribedGridIndex R r K) : 0 ≤ b ij := by
    dsimp only [b]
    have hy := (prescribedGrid_center_height hr hij).2
    split_ifs <;> positivity
  calc
    _ ≤ ENNReal.ofReal (36*(n:ℝ)*r^Target.d κ)*
        ∑ ij∈prescribedGridIndex R r K, ENNReal.ofReal (b ij) :=
      expected_prescribed_missed_cost_bound P f hf ν hν κ W n e C c R K hK _ hb
    _ = ENNReal.ofReal ((36*(n:ℝ)*r^Target.d κ)*∑ ij∈prescribedGridIndex R r K,b ij) := by
      rw [← ENNReal.ofReal_sum_of_nonneg hb0,← ENNReal.ofReal_mul (by positivity : 0 ≤ 36*(n:ℝ)*r^Target.d κ)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (prescribed_cleanup_error_bound κ hκ hκ8 hR hr hr1 hη hε hA K n)

theorem prescribed_missed_cost_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → C(ℝ≥0,ℂ)) (hf : Measurable f)
    (ν : Ω → Measure ℂ) (hν : Measurable ν)
    {κ : ℝ} (hκ : 0<κ) (hκ8 : κ<8) (W : Target.WienerLaw)
    (J : ℕ → ℕ) (e : ∀ n, Fin (J n) → ℤ×ℕ)
    (C c R : ℝ) (hR : 0 ≤ R) (K : Set ℂ) (hK : IsClosed K)
    (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ᶠ n in atTop, ∀ ij∈prescribedGridIndex R (Target.entryRadius κ W (n,none)) K,
      P {ω | ij∈prescribedMissedIndices κ W n (e n) C c R K (range (f ω)∩K) (ν ω)} ≤
        ENNReal.ofReal (A*(Target.entryRadius κ W (n,none))^codimension κ*
          (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij).im^(-codimension κ)*
          (Real.exp (-((2:ℝ)^n/16)) +
            if (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij).im<Real.exp (-(n:ℝ)) then 1 else 0))) :
    Tendsto (fun n => ∫⁻ ω,prescribedMissedCost f ν κ W n (e n) C c R K ω ∂P)
      atTop (𝓝 0) := by
  let D := 36*A*((2*R+5)*((2:ℝ)^codimension κ/(1-codimension κ)))
  let F := fun n : ℕ => D*((R+3)^(1-codimension κ)*((n:ℝ)*Real.exp (-((2:ℝ)^n/16)))+
    (n:ℝ)*(Real.exp (-(n:ℝ))+Target.entryRadius κ W (n,none))^(1-codimension κ))
  have ht : Tendsto F atTop (𝓝 0) := by
    have h := (prescribed_batch_failure_cost_tendsto_zero.const_mul ((R+3)^(1-codimension κ))).add
      (prescribed_boundary_cost_tendsto_zero hκ W)
    simpa only [mul_zero,add_zero,F] using h.const_mul D
  have he : Tendsto (fun n => ENNReal.ofReal (F n)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero,Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
  · exact Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [hb,eventually_ge_atTop 1] with n hn hn1
    have hr1 : Target.entryRadius κ W (n,none) ≤ 1 :=
      (Target.entryRadius_le_batch_exp hκ W _).trans
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
    exact expected_prescribed_missed_cost_le P f hf ν hν hκ hκ8 W n (e n) C c R hR K hK
      _ _ A (Real.exp_pos _).le (Real.exp_pos _).le hA hr1 hn

end SLEExactGauge

end

end OAI
