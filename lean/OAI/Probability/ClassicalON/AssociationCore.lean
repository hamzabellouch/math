import OAI.Probability.ClassicalON.CoarseCodes

namespace OAI

universe uX uY

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace ClassicalON

section CompactIntegral
variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {μ : Measure X} [IsFiniteMeasure μ]

theorem compact_integrable {f : X → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem compact_integral_pos [IsProbabilityMeasure μ] {w : X → ℝ}
    (hw : Continuous w) (hp : ∀ x,0<w x) : 0<∫ x,w x ∂μ := by
  apply (integral_pos_iff_support_of_nonneg (fun x => (hp x).le) (compact_integrable hw)).2
  have he : Function.support w=univ := by ext x; simp [Function.mem_support,(hp x).ne']
  rw [he,measure_univ]
  exact zero_lt_one

omit [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] in
theorem compact_parametric_integral [FirstCountableTopology Y] [LocallyCompactSpace Y]
    (f : Y → X → ℝ) (hf : Continuous f.uncurry) : Continuous (fun y => ∫ x,f y x ∂μ) := by
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous hf (isCompact_univ : IsCompact (univ : Set X)))

end CompactIntegral

def weightedMean {X : Type uX} [MeasurableSpace X] (μ : Measure X) (w f : X → ℝ) : ℝ :=
  (∫ x,w x*f x ∂μ)/(∫ x,w x ∂μ)

def ContinuousAssociated {X : Type uX} [MeasurableSpace X] [TopologicalSpace X]
    [Preorder X] (μ : Measure X) (w : X → ℝ) : Prop :=
  ∀ f g : X → ℝ, Continuous f → Continuous g → (∀ x,0≤f x) → (∀ x,0≤g x) →
    Monotone f → Monotone g →
    weightedMean μ w f * weightedMean μ w g ≤ weightedMean μ w (fun x => f x*g x)

section Weighted
variable {X : Type uX} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X]
  [BorelSpace X] {μ : Measure X} [IsProbabilityMeasure μ] {w : X → ℝ}
  (hw : Continuous w) (hp : ∀ x,0<w x)

include hw hp

theorem weightedMean_nonneg {f : X → ℝ} (hf : ∀ x,0≤f x) : 0≤weightedMean μ w f := by
  exact div_nonneg (integral_nonneg (fun x => mul_nonneg (hp x).le (hf x)))
    (compact_integral_pos hw hp).le

theorem weightedMean_mono {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x,f x≤g x) : weightedMean μ w f ≤ weightedMean μ w g := by
  exact div_le_div_of_nonneg_right
    (integral_mono (compact_integrable (hw.mul hf)) (compact_integrable (hw.mul hg))
      (fun x => mul_le_mul_of_nonneg_left (hfg x) (hp x).le)) (compact_integral_pos hw hp).le

theorem weightedMean_inequality_iff {f g : X → ℝ} :
    weightedMean μ w f * weightedMean μ w g ≤ weightedMean μ w (fun x => f x*g x) ↔
    (∫ x,w x*f x ∂μ)*(∫ x,w x*g x ∂μ) ≤ (∫ x,w x ∂μ)*(∫ x,w x*(f x*g x) ∂μ) := by
  unfold weightedMean
  have hm := compact_integral_pos (μ := μ) hw hp
  rw [div_mul_div_comm,div_le_div_iff₀ (mul_pos hm hm) hm]
  constructor <;> intro h <;> nlinarith

end Weighted

theorem continuousAssociated_chain {X : Type uX} [LinearOrder X] [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsProbabilityMeasure μ] (w : X → ℝ)
    (hw : Continuous w) (hp : ∀ x,0<w x) : ContinuousAssociated μ w := by
  intro f g hf hg _ _ hfm hgm
  apply (weightedMean_inequality_iff hw hp).2
  have hc : ∀ x y,w x*f x*(w y*g y)+w x*g x*(w y*f y) ≤
      w x*(f x*g x)*w y+w x*(w y*(f y*g y)) := by
    intro x y
    have hdiff : 0≤(f x-f y)*(g x-g y) := by
      rcases le_total x y with h | h
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hfm h)) (sub_nonpos.mpr (hgm h))
      · exact mul_nonneg (sub_nonneg.mpr (hfm h)) (sub_nonneg.mpr (hgm h))
    have ht := mul_nonneg (mul_nonneg (hp x).le (hp y).le) hdiff
    nlinarith
  have hint := integral_mono
    (compact_integrable (μ := μ.prod μ) (show Continuous (fun p : X×X =>
      w p.1*f p.1*(w p.2*g p.2)+w p.1*g p.1*(w p.2*f p.2)) from by fun_prop))
    (compact_integrable (μ := μ.prod μ) (show Continuous (fun p : X×X =>
      w p.1*(f p.1*g p.1)*w p.2+w p.1*(w p.2*(f p.2*g p.2))) from by fun_prop))
    (fun p => hc p.1 p.2)
  rw [integral_add (compact_integrable (by fun_prop)) (compact_integrable (by fun_prop)),
    integral_add (compact_integrable (by fun_prop)) (compact_integrable (by fun_prop))] at hint
  rw [integral_prod_mul (fun x => w x*f x) (fun x => w x*g x),
    integral_prod_mul (fun x => w x*g x) (fun x => w x*f x),
    integral_prod_mul (fun x => w x*(f x*g x)) w,
    integral_prod_mul w (fun x => w x*(f x*g x))] at hint
  nlinarith

end ClassicalON

end

end OAI
