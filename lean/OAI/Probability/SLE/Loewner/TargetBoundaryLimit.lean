import OAI.Probability.SLE.Loewner.TargetInverseContinuity
import OAI.Probability.SLE.Loewner.TargetTraceCandidate
import OAI.Probability.SLE.Geometry.RightLimitMeasurability

namespace OAI

/-! The complete vertical boundary limit of the raw inverse flow has a
measurable event, without a trace-generation assumption. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

def rawTipAt (κ : ℝ) (T : ℝ≥0) (y : ℝ) (b : Driver) : ℂ :=
  inverseFlow κ b (κ.toNNReal*T)
    ((b (κ.toNNReal*T):ℂ)+(y:ℂ)*Complex.I)

lemma joint_measurable_rawTipAt (κ : ℝ) (y : ℝ) :
    Measurable (fun q : ℝ≥0 × Driver => rawTipAt κ q.1 y q.2) := by
  have ht : Measurable (fun q : ℝ≥0 × Driver => κ.toNNReal*q.1) :=
    measurable_const.mul measurable_fst
  have hw : Measurable (fun q : ℝ≥0 × Driver =>
      (q.2 (κ.toNNReal*q.1):ℂ)+(y:ℂ)*Complex.I) :=
    ((continuous_eval.measurable.comp (measurable_snd.prodMk ht)).complex_ofReal).add_const _
  exact @Measurable.comp (ℝ≥0 × Driver) (ℝ≥0 × (Driver × ℂ)) ℂ
    inferInstance inferInstance inferInstance
    (fun q => inverseFlow κ q.2.1 q.1 q.2.2)
    (fun q => (κ.toNNReal*q.1,(q.2,(q.2 (κ.toNNReal*q.1):ℂ)+(y:ℂ)*Complex.I)))
    (measurable_inverseFlow κ) (ht.prodMk (measurable_snd.prodMk hw))

lemma measurable_rawTipAt (κ : ℝ) (T : ℝ≥0) (y : ℝ) :
    Measurable (rawTipAt κ T y) := by
  have hw : Measurable (fun b : Driver =>
      (b (κ.toNNReal*T):ℂ)+(y:ℂ)*Complex.I) :=
    (continuous_eval_const _).measurable.complex_ofReal.add_const _
  exact @Measurable.comp Driver (ℝ≥0 × (Driver × ℂ)) ℂ
    inferInstance inferInstance inferInstance
    (fun q => inverseFlow κ q.2.1 q.1 q.2.2)
    (fun b => (κ.toNNReal*T,(b,(b (κ.toNNReal*T):ℂ)+(y:ℂ)*Complex.I)))
    (measurable_inverseFlow κ) (measurable_const.prodMk (measurable_id.prodMk hw))

lemma continuousOn_rawTipAt (κ : ℝ) (hκ : 0 < κ) (T : ℝ≥0) (b : Driver) :
    ContinuousOn (fun y => rawTipAt κ T y b) (Ioi 0) := by
  apply (continuousOn_inverseFlow κ hκ b (κ.toNNReal*T)).comp
    ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn)
  intro y hy
  change 0 < ((b (κ.toNNReal*T):ℂ)+(y:ℂ)*Complex.I).im
  simpa using hy

lemma measurableSet_rawTipAt_tendsto (κ : ℝ) (hκ : 0 < κ) (T : ℝ≥0)
    (g : Driver → ℂ) (hg : Measurable g) :
    MeasurableSet {b : Driver |
      Tendsto (fun y => rawTipAt κ T y b) (𝓝[>] 0) (𝓝 (g b))} :=
  measurableSet_tendsto_right (rawTipAt κ T) g (measurable_rawTipAt κ T) hg
    (continuousOn_rawTipAt κ hκ T)

lemma joint_measurableSet_rawTipAt_tendsto (κ : ℝ) (hκ : 0 < κ)
    (g : ℝ≥0 × Driver → ℂ) (hg : Measurable g) :
    MeasurableSet {q : ℝ≥0 × Driver |
      Tendsto (fun y => rawTipAt κ q.1 y q.2) (𝓝[>] 0) (𝓝 (g q))} := by
  have hf : ∀ y : ℝ, Measurable (fun q : ℝ≥0 × Driver => rawTipAt κ q.1 y q.2) :=
    joint_measurable_rawTipAt κ
  have hc : ∀ q : ℝ≥0 × Driver,
      ContinuousOn (fun y : ℝ => rawTipAt κ q.1 y q.2) (Ioi 0) :=
    fun q => continuousOn_rawTipAt κ hκ q.1 q.2
  exact @measurableSet_tendsto_right (ℝ≥0 × Driver) inferInstance
    (fun y q => rawTipAt κ q.1 y q.2) g hf hg hc

lemma rawTipAt_eq_witness
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (T : ℝ≥0) (y : ℝ) (hy : 0 < y) :
    rawTipAt κ T y b=F T ((U T:ℂ)+(y:ℂ)*Complex.I) := by
  have heTime : (κ*(T:ℝ)).toNNReal=κ.toNNReal*T := by
    rw [Real.toNNReal_mul hκ.le,Real.toNNReal_coe]
  have hb : b (κ.toNNReal*T)=U T := by
    have h := hU T T.coe_nonneg
    simpa only [Real.toNNReal_coe,driverValue,heTime] using h.symm
  unfold rawTipAt
  rw [Real.coe_toNNReal _ hκ.le,hb]
  exact inverseFlow_eq_witness κ hκ b U γ G F hw hU T _ (by
    change 0 < ((U T:ℂ)+(y:ℂ)*Complex.I).im
    simpa using hy)

lemma rawTipAt_tendsto_witness
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (T : ℝ≥0) :
    Tendsto (fun y => rawTipAt κ T y b) (𝓝[>] 0) (𝓝 (γ T)) := by
  apply Tendsto.congr' _ (hw.2.2.2.2.2.2.2.2.2.2.2.2 T)
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (rawTipAt_eq_witness κ hκ b U γ G F hw hU T y hy).symm

end SLEExactGauge.Target

end

end OAI
