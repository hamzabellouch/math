import OAI.Probability.SLE.Loewner.TargetInverseMeasurability
import OAI.Probability.SLE.Angle.TargetFlowIdentification

namespace OAI

/-! A measurable trace candidate from the prescribed inverse flow.
It equals the actual trace whenever a capacity witness is present. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

def rawTipApprox (κ : ℝ) (n : ℕ) (T : ℝ≥0) (b : Driver) : ℂ :=
  inverseFlow κ b (κ.toNNReal*T)
    ((b (κ.toNNReal*T):ℂ)+((1/((n:ℝ)+1):ℝ):ℂ)*Complex.I)

def traceCandidate (κ : ℝ) (T : ℝ≥0) (b : Driver) : ℂ :=
  limUnder atTop (fun n => rawTipApprox κ n T b)

lemma measurable_rawTipApprox (κ : ℝ) (n : ℕ) :
    Measurable (fun q : ℝ≥0 × Driver => rawTipApprox κ n q.1 q.2) := by
  have ht : Measurable (fun q : ℝ≥0 × Driver => κ.toNNReal*q.1) := measurable_const.mul measurable_fst
  have hw : Measurable (fun q : ℝ≥0 × Driver =>
      (q.2 (κ.toNNReal*q.1):ℂ)+((1/((n:ℝ)+1):ℝ):ℂ)*Complex.I) :=
    ((continuous_eval.measurable.comp (measurable_snd.prodMk ht)).complex_ofReal).add_const _
  have hq : Measurable (fun q : ℝ≥0 × Driver =>
      (κ.toNNReal*q.1,(q.2,(q.2 (κ.toNNReal*q.1):ℂ)+((1/((n:ℝ)+1):ℝ):ℂ)*Complex.I))) :=
    ht.prodMk (measurable_snd.prodMk hw)
  exact @Measurable.comp (ℝ≥0 × Driver) (ℝ≥0 × (Driver × ℂ)) ℂ
    inferInstance inferInstance inferInstance
    (fun q => inverseFlow κ q.2.1 q.1 q.2.2)
    (fun q => (κ.toNNReal*q.1,(q.2,(q.2 (κ.toNNReal*q.1):ℂ)+((1/((n:ℝ)+1):ℝ):ℂ)*Complex.I)))
    (measurable_inverseFlow κ) hq

lemma measurable_traceCandidate (κ : ℝ) :
    Measurable (fun q : ℝ≥0 × Driver => traceCandidate κ q.1 q.2) := by
  exact (StronglyMeasurable.limUnder
    (fun n => (measurable_rawTipApprox κ n).stronglyMeasurable)).measurable

lemma rawTipApprox_eq_witness
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (T : ℝ≥0) (n : ℕ) :
    rawTipApprox κ n T b=F T ((U T:ℂ)+((1/((n:ℝ)+1):ℝ):ℂ)*Complex.I) := by
  have heTime : (κ*(T:ℝ)).toNNReal=κ.toNNReal*T := by
    rw [Real.toNNReal_mul hκ.le,Real.toNNReal_coe]
  have hb : b (κ.toNNReal*T)=U T := by
    have h := hU T T.coe_nonneg
    simpa only [Real.toNNReal_coe,driverValue,heTime] using h.symm
  unfold rawTipApprox
  rw [Real.coe_toNNReal _ hκ.le,hb]
  exact inverseFlow_eq_witness κ hκ b U γ G F hw hU T _ (by
    change 0 < ((U T:ℂ)+((1/((n:ℝ)+1):ℝ):ℂ)*Complex.I).im
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_im,Complex.I_re,mul_one,mul_zero,zero_add,add_zero]
    positivity)

lemma rawTipApprox_tendsto_witness
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (T : ℝ≥0) : Tendsto (fun n => rawTipApprox κ n T b) atTop (𝓝 (γ T)) := by
  have hseq : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall (fun n => by change 0 < (1:ℝ)/((n:ℝ)+1); positivity)⟩
  simpa only [rawTipApprox_eq_witness κ hκ b U γ G F hw hU T,Function.comp_def] using
    (hw.2.2.2.2.2.2.2.2.2.2.2.2 T).comp hseq

lemma traceCandidate_eq_witness
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (T : ℝ≥0) : traceCandidate κ T b=γ T :=
  (rawTipApprox_tendsto_witness κ hκ b U γ G F hw hU T).limUnder_eq

end SLEExactGauge.Target

end

end OAI
