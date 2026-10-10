import Mathlib
import OAI.Probability.SKSupport.Moments.Curvature

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma OrderParameter.continuousAt_of_constant {γ : OrderParameter} {a b c : ℝ}
    (hc : ∀ s ∈ Ioo a b, extend γ.val s=c) (t : Time) (ht : (t:ℝ) ∈ Ioo a b) :
    ContinuousAt γ.val t := by
  have hh : γ.val =ᶠ[𝓝 t] fun _ => c := by
    filter_upwards [(continuous_subtype_val.tendsto t).eventually (Ioo_mem_nhds ht.1 ht.2)] with s hs
    have he := hc s hs
    simpa only [extend,dite_eq_left s.property] using he
  exact continuousAt_const.congr_of_eventuallyEq hh

lemma compactCoeff_constant (γ : OrderParameter) (T : Time) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ T) (hc : ∀ s ∈ Ioo a b, extend γ.val s=c) :
    ∀ s ∈ Ioo a b, compactCoeff γ T s=c := by
  intro s hs
  rw [compactCoeff,stripClamp_eq ⟨ha.trans hs.1.le,hs.2.le.trans hb⟩]
  exact hc s hs

lemma curvatureMoment_hasDerivAt_on_constant (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time)
    {a b c t : ℝ} (ha : 0 ≤ a) (hbT : b ≤ T) (ht : t ∈ Ioo a b)
    (hc : ∀ s ∈ Ioo a b, extend γ.val s=c) :
    HasDerivAt (curvatureMoment W γ) (stripSecond W γ T c t) t := by
  have hd := stripA_hasDerivAt_on_constant W γ T ha hbT ht (compactCoeff_constant γ T ha hbT hc)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (ha.trans_lt ht.1) (ht.2.trans_le hbT)] with s hs
  exact (stripA_eq_curvatureMoment W γ T ⟨hs.1.le,hs.2.le⟩).symm

lemma curvatureMoment_deriv_hasDerivAt_on_constant (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time)
    {a b c t : ℝ} (ha : 0 ≤ a) (hbT : b ≤ T) (ht : t ∈ Ioo a b)
    (hc : ∀ s ∈ Ioo a b, extend γ.val s=c) :
    HasDerivAt (deriv (curvatureMoment W γ)) (stripThird W γ T c t) t := by
  have hd := stripSecond_hasDerivAt_on_constant W γ T ha hbT ht (compactCoeff_constant γ T ha hbT hc)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact (curvatureMoment_hasDerivAt_on_constant W γ T ha hbT hs hc).deriv

theorem positive_gap_curvature (W : BrownianSystem Ω) (γ : OrderParameter)
    {a b c : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) (hc0 : 0 < c)
    (hc : ∀ s ∈ Ioo a b, extend γ.val s=c) :
    ∀ t ∈ Ioo a b, 0 < (deriv^[2] (curvatureMoment W γ)) t := by
  intro t ht
  let T : Time := ⟨b,⟨ha.trans hab.le,hb⟩⟩
  have htt : t ∈ Ico (0:ℝ) 1 := ⟨ha.trans ht.1.le,ht.2.trans hb⟩
  let τ : Time := ⟨t,htt⟩
  have he : γ.val τ=c := by simpa only [extend,dite_eq_left htt] using hc t ht
  change 0 < deriv (deriv (curvatureMoment W γ)) t
  rw [(curvatureMoment_deriv_hasDerivAt_on_constant W γ T ha le_rfl ht hc).deriv]
  have hp := stripThird_pos W γ T τ (ha.trans_lt ht.1) ht.2.le
    (γ.continuousAt_of_constant hc τ ht) (by rw [he];exact hc0)
  simpa only [he] using hp

theorem zero_gap_curvature (W : BrownianSystem Ω) (γ : OrderParameter)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1)
    (hc : ∀ s ∈ Ioo a b, extend γ.val s=0) :
    ∀ t ∈ Ioo a b, 0 < deriv (curvatureMoment W γ) t := by
  intro t ht
  let T : Time := ⟨b,⟨ha.trans hab.le,hb⟩⟩
  let τ : Time := ⟨t,⟨ha.trans ht.1.le,ht.2.trans hb⟩⟩
  rw [(curvatureMoment_hasDerivAt_on_constant W γ T ha le_rfl ht hc).deriv]
  exact stripSecond_zero_pos W γ T τ (ha.trans_lt ht.1) ht.2.le

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

instance timeCompactIccSpace : CompactIccSpace Time where
  isCompact_Icc {a} {b} := by
    rw [Subtype.isCompact_iff]
    have he : Subtype.val '' Icc a b=Icc (a:ℝ) (b:ℝ) := by
      ext t
      constructor
      · rintro ⟨u,hu,rfl⟩
        exact hu
      · intro ht
        exact ⟨⟨t,⟨a.property.1.trans ht.1,ht.2.trans_lt b.property.2⟩⟩,ht,rfl⟩
    rw [he]
    exact isCompact_Icc

def parameterStieltjes (γ : OrderParameter) : StieltjesFunction Time where
  toFun := γ.val
  mono' := γ.monotone
  right_continuous' := γ.right_continuous

lemma parameterStieltjes_atBot (γ : OrderParameter) :
    Tendsto (parameterStieltjes γ) atBot (𝓝 (γ.val ⊥)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_le_atBot (⊥ : Time)] with t ht
  have he : t=⊥ := le_antisymm ht bot_le
  subst t
  rfl

def parameterMeasure (γ : OrderParameter) : Measure Time :=
  (parameterStieltjes γ).measure + ENNReal.ofReal (γ.val ⊥) • Measure.dirac ⊥

lemma parameterMeasure_isStieltjes (γ : OrderParameter) : IsStieltjesMeasure γ (parameterMeasure γ) := by
  intro t
  rw [parameterMeasure,Measure.add_apply,(parameterStieltjes γ).measure_Iic (parameterStieltjes_atBot γ),
    Measure.smul_apply,Measure.dirac_apply' _ measurableSet_Iic]
  have hbot : (⊥ : Time) ∈ Iic t := by change (⊥ : Time) ≤ t; exact bot_le
  simp only [Set.indicator_of_mem hbot,Pi.one_apply,smul_eq_mul,mul_one]
  change ENNReal.ofReal (γ.val t-γ.val ⊥)+ENNReal.ofReal (γ.val ⊥)=ENNReal.ofReal (γ.val t)
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr (γ.monotone bot_le)) (γ.nonneg ⊥),sub_add_cancel]

end ZeroTemperatureSK

end
end

end OAI
