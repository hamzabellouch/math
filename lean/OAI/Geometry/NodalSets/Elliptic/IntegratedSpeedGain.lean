import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace Yau.Geometry
open Set MeasureTheory
noncomputable section
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma integrated_speed_gain {Q A : Set X} (hQ : MeasurableSet Q) (hA : MeasurableSet A)
    (hAQ : A ⊆ Q) (hfin : μ Q ≠ ⊤) (f : X → ℝ) (hf : IntegrableOn f Q μ)
    (a b : ℝ) (hbase : ∀ x ∈ Q, a ≤ f x) (hgain : ∀ x ∈ A, a+b ≤ f x) :
    a*μ.real Q+b*μ.real A ≤ ∫ x in Q, f x ∂μ := by
  have ha : IntegrableOn (fun _ : X ↦ a) Q μ := integrableOn_const hfin
  have hb : IntegrableOn (fun _ : X ↦ b) Q μ := integrableOn_const hfin
  have hi : IntegrableOn (A.indicator (fun _ : X ↦ b)) Q μ := hb.indicator hA
  have hle : ∫ x in Q, a+A.indicator (fun _ : X ↦ b) x ∂μ ≤ ∫ x in Q, f x ∂μ := by
    apply setIntegral_mono_on (ha.add hi) hf hQ
    intro x hx
    by_cases hxA : x ∈ A
    · simpa only [Pi.add_apply,Set.indicator_of_mem hxA] using hgain x hxA
    · simpa only [Pi.add_apply,Set.indicator_of_notMem hxA,add_zero] using hbase x hx
  rw [integral_add ha hi,setIntegral_indicator hA,Set.inter_eq_right.mpr hAQ,
    setIntegral_const,setIntegral_const] at hle
  simpa only [smul_eq_mul,mul_comm] using hle

lemma integrated_speed_factor {Q A : Set X} (hQ : MeasurableSet Q) (hA : MeasurableSet A)
    (hAQ : A ⊆ Q) (hfin : μ Q ≠ ⊤) (f old : X → ℝ)
    (hf : IntegrableOn f Q μ) (ho : IntegrableOn old Q μ)
    {s δ q ε : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hq : 1 < q)
    (hfrac : δ*μ.real Q ≤ μ.real A)
    (hbudget : ε*(2+δ*(q-1)/2) ≤ δ*(q-1)/2)
    (hbase : ∀ x ∈ Q, s*(1-ε) ≤ f x)
    (hgain : ∀ x ∈ A, s*(q-ε) ≤ f x)
    (hold : ∀ x ∈ Q, old x ≤ s*(1+ε)) :
    (1+δ*(q-1)/2)*(∫ x in Q, old x ∂μ) ≤ ∫ x in Q, f x ∂μ := by
  have hh := integrated_speed_gain hQ hA hAQ hfin f hf (s*(1-ε)) (s*(q-1)) hbase
    (fun x hx ↦ by convert hgain x hx using 1; ring)
  have hupper : ∫ x in Q, old x ∂μ ≤ s*(1+ε)*μ.real Q := by
    have h := setIntegral_mono_on ho (integrableOn_const hfin) hQ hold
    simpa only [setIntegral_const,smul_eq_mul,mul_comm] using h
  have hv : 0 ≤ μ.real Q := measureReal_nonneg
  have hco : 0 ≤ 1+δ*(q-1)/2 := by positivity
  have hb := mul_le_mul_of_nonneg_left hbudget (mul_nonneg hs.le hv)
  have hm := mul_le_mul_of_nonneg_left hfrac (mul_nonneg hs.le (sub_nonneg.mpr hq.le))
  calc
    _ ≤ (1+δ*(q-1)/2)*(s*(1+ε)*μ.real Q) := mul_le_mul_of_nonneg_left hupper hco
    _ ≤ s*(1-ε)*μ.real Q+s*(q-1)*(δ*μ.real Q) := by nlinarith only [hb]
    _ ≤ s*(1-ε)*μ.real Q+s*(q-1)*μ.real A := add_le_add le_rfl hm
    _ ≤ _ := hh

end
end Yau.Geometry

end OAI
