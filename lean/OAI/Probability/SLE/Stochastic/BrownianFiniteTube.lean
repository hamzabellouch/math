import OAI.Probability.SLE.Stochastic.BrownianFiniteSmallBall

namespace OAI

/-! Finite-window support around any prescribed continuous based real
driver, transported from the actual unit-window Wiener law. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance finiteTubePathMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance finiteTubePathBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

def driverUnitTube (f : C(ℝ≥0,ℝ)) (ε : ℝ) : Set Target.Driver :=
  {b | ∀ t : ℝ≥0, t ≤ 1 → |b t-f t| < ε}

lemma isOpen_driverUnitTube (f : C(ℝ≥0,ℝ)) (ε : ℝ) : IsOpen (driverUnitTube f ε) := by
  have ho := ContinuousMap.isOpen_setOfPred_mapsTo
    (isCompact_Icc : IsCompact (Icc (0:ℝ≥0) 1))
    (isOpen_Ioo : IsOpen (Ioo (-ε) ε))
  have he : driverUnitTube f ε =
      (fun b : Target.Driver => b.toContinuousMap-f) ⁻¹'
        {p : C(ℝ≥0,ℝ) | MapsTo p (Icc 0 1) (Ioo (-ε) ε)} := by
    ext b
    simp only [driverUnitTube,mem_ofPred_eq,mem_preimage,MapsTo,mem_Icc,mem_Ioo,
      ContinuousMap.sub_apply]
    constructor
    · intro hb t ht
      exact abs_lt.mp (hb t ht.2)
    · intro hb t ht
      exact abs_lt.mpr (hb ⟨zero_le,ht⟩)
  rw [he]
  exact ho.preimage (ContinuousMapZero.isClosedEmbedding_toContinuousMap.continuous.sub
    continuous_const)

lemma driverUnitTube_positive (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (f : C(ℝ≥0,ℝ)) (hf0 : f 0=0) {ε : ℝ} (hε : 0 < ε) :
    0 < W (driverUnitTube f ε) := by
  have hp := wienerReal_uniform_tube_pos W hW f f.continuous hf0 ε hε
  apply hp.trans_le (measure_mono ?_)
  intro b hb t ht
  convert! hb (⟨(t:ℝ),t.coe_nonneg,by exact_mod_cast ht⟩ : unitInterval) using 1

theorem brownian_finite_uniform_tube_positive
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (T : ℝ≥0) (hT : 0 < T)
    (f : C(ℝ≥0,ℝ)) (hf0 : f 0=0) {ε : ℝ} (hε : 0 < ε) :
    0 < P {ω | ∀ t ∈ Icc 0 T, |B t ω-f t| < ε} := by
  let C (t : ℝ≥0) (ω : Ω) := (Real.sqrt T)⁻¹*B (T*t) ω
  have hC : IsBrownianReal C P := hB.smul hT.ne'
  have hCm : ∀ t, Measurable (C t) := fun t => measurable_const.mul (hm _)
  have hCc : ∀ ω, Continuous (fun t => C t ω) :=
    fun ω => continuous_const.mul ((hc ω).comp (continuous_const.mul continuous_id))
  have hC0 : ∀ ω, C 0 ω=0 := by intro ω; simp [C,h0]
  let g : C(ℝ≥0,ℝ) := ⟨fun t => (Real.sqrt T)⁻¹*f (T*t),
    continuous_const.mul (f.continuous.comp (continuous_const.mul continuous_id))⟩
  have hg0 : g 0=0 := by simp [g,hf0]
  let b := Target.normalizedDriver 1 C hCc hC0
  have hb : Measurable b := Target.normalizedDriver_measurable 1 C hCm hCc hC0
  have hW := Target.normalizedDriver_isWiener 1 (by norm_num) C hC hCm hCc hC0
  have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by exact_mod_cast hT)
  have hp := driverUnitTube_positive (P.map b) hW g hg0 (div_pos hε hsqrt)
  rw [Measure.map_apply hb (isOpen_driverUnitTube _ _).measurableSet] at hp
  apply hp.trans_le (measure_mono ?_)
  intro ω hω t ht
  let q : ℝ≥0 := t/T
  have hq : q ≤ 1 := (div_le_one₀ hT).mpr ht.2
  have hbq := hω q hq
  change |Real.sqrt 1*C (q/(1:ℝ).toNNReal) ω-g q| < ε/Real.sqrt T at hbq
  simp only [Real.sqrt_one,Real.toNNReal_one,div_one,one_mul] at hbq
  have htq : T*q=t := by dsimp [q]; exact mul_div_cancel₀ _ hT.ne'
  change |(Real.sqrt T)⁻¹*B (T*q) ω-(Real.sqrt T)⁻¹*f (T*q)| < _ at hbq
  rw [htq,← mul_sub,abs_mul,abs_inv,abs_of_pos hsqrt,← div_eq_inv_mul] at hbq
  exact (div_lt_div_iff_of_pos_right hsqrt).mp hbq

end SLEExactGauge

end

end OAI
