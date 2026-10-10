import OAI.Probability.SLE.Angle.TargetBrownianNormalization
import OAI.Probability.SLE.Stochastic.WienerRealSupport

namespace OAI

/-! Positive probability of a uniformly small real Brownian driver on any
fixed finite time interval, using its actual based path law. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance smallBallPathMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance smallBallPathBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

def driverUnitSmallBall (ε : ℝ) : Set Target.Driver :=
  {b | ∀ t : ℝ≥0, t ≤ 1 → |b t| < ε}

lemma isOpen_driverUnitSmallBall (ε : ℝ) : IsOpen (driverUnitSmallBall ε) := by
  have ho := ContinuousMap.isOpen_setOfPred_mapsTo
    (isCompact_Icc : IsCompact (Icc (0:ℝ≥0) 1))
    (isOpen_Ioo : IsOpen (Ioo (-ε) ε))
  have he : driverUnitSmallBall ε =
      (fun b : Target.Driver => b.toContinuousMap) ⁻¹'
        {p : C(ℝ≥0,ℝ) | MapsTo p (Icc 0 1) (Ioo (-ε) ε)} := by
    ext b
    simp only [driverUnitSmallBall,mem_ofPred_eq,mem_preimage,MapsTo,mem_Icc,mem_Ioo]
    constructor
    · intro hb t ht
      exact abs_lt.mp (hb t ht.2)
    · intro hb t ht
      exact abs_lt.mpr (hb ⟨zero_le,ht⟩)
  rw [he]
  exact ho.preimage ContinuousMapZero.isClosedEmbedding_toContinuousMap.continuous

lemma driverUnitSmallBall_positive (W : Target.WienerLaw) (hW : Target.IsWiener W)
    {ε : ℝ} (hε : 0 < ε) : 0 < W (driverUnitSmallBall ε) := by
  have hp := wienerReal_uniform_tube_pos W hW (fun _ => 0) continuous_const rfl ε hε
  apply hp.trans_le
  apply measure_mono
  intro b hb t ht
  convert! hb (⟨(t:ℝ),t.coe_nonneg,by exact_mod_cast ht⟩ : unitInterval) using 1
  simp only [sub_zero]
  exact congrArg (fun u : ℝ≥0 => |b u|) (Subtype.ext rfl)

theorem brownian_finite_smallBall_positive
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (T : ℝ≥0) (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) :
    0 < P {ω | ∀ t ∈ Icc 0 T, |B t ω| < ε} := by
  let C (t : ℝ≥0) (ω : Ω) := (Real.sqrt T)⁻¹*B (T*t) ω
  have hC : IsBrownianReal C P := hB.smul hT.ne'
  have hCm : ∀ t, Measurable (C t) := fun t => measurable_const.mul (hm _)
  have hCc : ∀ ω, Continuous (fun t => C t ω) :=
    fun ω => continuous_const.mul ((hc ω).comp (continuous_const.mul continuous_id))
  have hC0 : ∀ ω, C 0 ω=0 := by intro ω; simp [C,h0]
  let b := Target.normalizedDriver 1 C hCc hC0
  have hb : Measurable b := Target.normalizedDriver_measurable 1 C hCm hCc hC0
  have hW := Target.normalizedDriver_isWiener 1 (by norm_num) C hC hCm hCc hC0
  have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by exact_mod_cast hT)
  have hp := driverUnitSmallBall_positive (P.map b) hW (div_pos hε hsqrt)
  rw [Measure.map_apply hb (isOpen_driverUnitSmallBall _).measurableSet] at hp
  apply hp.trans_le (measure_mono ?_)
  intro ω hω t ht
  let q : ℝ≥0 := t/T
  have hq : q ≤ 1 := (div_le_one₀ hT).mpr ht.2
  have hbq := hω q hq
  change |Real.sqrt 1*C (q/(1:ℝ).toNNReal) ω| < ε/Real.sqrt T at hbq
  simp only [Real.sqrt_one,Real.toNNReal_one,div_one,one_mul] at hbq
  have htq : T*q=t := by dsimp [q]; exact mul_div_cancel₀ _ hT.ne'
  dsimp only [C] at hbq
  rw [htq,abs_mul,abs_inv,abs_of_pos hsqrt,← div_eq_inv_mul] at hbq
  exact (div_lt_div_iff_of_pos_right hsqrt).mp hbq

end SLEExactGauge

end

end OAI
