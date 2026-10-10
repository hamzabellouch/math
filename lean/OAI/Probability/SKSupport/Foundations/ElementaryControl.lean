import Mathlib
import OAI.Probability.SKSupport.Model

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def elementaryControl (h : ℝ≥0) (a : ℕ → Ω → ℝ) : ℕ → ℝ≥0 → Ω → ℝ
  | 0, _, _ => 0
  | n+1, t, ω => if (n:ℝ≥0)*h ≤ t ∧ t < ((n+1:ℕ):ℝ≥0)*h then a n ω
      else elementaryControl h a n t ω

omit mΩ in
lemma elementaryControl_bound (h : ℝ≥0) {a : ℕ → Ω → ℝ}
    (ha : ∀ n ω, |a n ω| ≤ 1) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    |elementaryControl h a n t ω| ≤ 1 := by
  induction n with
  | zero => simp [elementaryControl]
  | succ n IH => simp only [elementaryControl]; split_ifs <;> first | exact ha n ω | exact IH

lemma elementaryControl_progressive (ℱ : Filtration ℝ≥0 mΩ) (h : ℝ≥0)
    {a : ℕ → Ω → ℝ} (ha : ∀ n : ℕ, Measurable[ℱ ((n:ℝ≥0)*h)] (a n)) (n : ℕ) :
    IsProgressive ℱ (elementaryControl h a n) := by
  induction n with
  | zero => exact isProgressive_const ℱ 0
  | succ n IH =>
    intro s
    by_cases hns : (n:ℝ≥0)*h ≤ s
    · have ham : Measurable[ℱ s] (a n) := (ha n).mono (ℱ.mono hns) le_rfl
      let : MeasurableSpace Ω := ℱ s
      have htime : Measurable (fun p : Set.Iic s × Ω => (p.1:ℝ≥0)) :=
        measurable_subtype_coe.comp measurable_fst
      have hset : MeasurableSet {p : Set.Iic s × Ω |
          (n:ℝ≥0)*h ≤ (p.1:ℝ≥0) ∧ (p.1:ℝ≥0) < ((n+1:ℕ):ℝ≥0)*h} :=
        (measurableSet_le (measurable_const : Measurable (fun _ : Set.Iic s × Ω => (n:ℝ≥0)*h)) htime).inter
          (measurableSet_lt (α := ℝ≥0) (f := fun p : Set.Iic s × Ω => (p.1:ℝ≥0))
            (g := fun _ : Set.Iic s × Ω => ((n+1:ℕ):ℝ≥0)*h) htime measurable_const)
      exact (ham.comp measurable_snd).ite hset (IH s)
    · convert IH s using 1
      funext p
      have hn : ¬(n:ℝ≥0)*h ≤ (p.1:ℝ≥0) := fun ht => hns (ht.trans p.1.property)
      simp only [elementaryControl, hn, false_and, ↓reduceIte]

lemma progressive_joint_measurable (ℱ : Filtration ℝ≥0 mΩ)
    {α : ℝ≥0 → Ω → ℝ} (hα : IsProgressive ℱ α) :
    Measurable (fun p : ℝ≥0 × Ω => α p.1 p.2) := by
  have hclip (n : ℕ) : Measurable (fun p : ℝ≥0 × Ω => α (min p.1 n) p.2) := by
    have hs : Measurable[inferInstance, ℱ (n:ℝ≥0)] (fun p : ℝ≥0 × Ω => p.2) :=
      measurable_snd.mono le_rfl (ℱ.le n)
    exact (hα n).comp (((measurable_fst.min measurable_const).subtype_mk
      (h := fun p : ℝ≥0 × Ω => min_le_right p.1 (n:ℝ≥0))).prodMk hs)
  apply measurable_of_tendsto_metrizable hclip
  apply tendsto_pi_nhds.mpr
  intro p
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ≥0)) atTop atTop).eventually
    (eventually_ge_atTop p.1)] with n hn
  simp only [min_eq_left hn]

omit mΩ in
lemma elementaryControl_on_step (h : ℝ≥0) (a : ℕ → Ω → ℝ) (n k : ℕ) (hk : k < n)
    (t : ℝ≥0) (ht : (k:ℝ≥0)*h ≤ t ∧ t < ((k+1:ℕ):ℝ≥0)*h) (ω : Ω) :
    elementaryControl h a n t ω = a k ω := by
  induction n with
  | zero => omega
  | succ n IH =>
    by_cases hkn : k = n
    · subst k
      simp only [elementaryControl, ht, and_self, ↓reduceIte]
    · have hkn' : k < n := by omega
      have hlt : t < (n:ℝ≥0)*h := ht.2.trans_le
        (mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : k+1 ≤ n)) (by positivity))
      simp only [elementaryControl, not_le.mpr hlt, false_and, ↓reduceIte]
      exact IH hkn'

omit mΩ in
lemma elementaryControl_integral_on_step (h : ℝ≥0) (a : ℕ → Ω → ℝ)
    (n k : ℕ) (hk : k < n) (φ : ℝ → ℝ) (ω : Ω) :
    (∫ r in ((k:ℝ≥0)*h:ℝ)..((k:ℝ≥0)*h:ℝ)+(h:ℝ),
      φ (elementaryControl h a n (Real.toNNReal r) ω)) = (h:ℝ)*φ (a k ω) := by
  have he : (∫ r in ((k:ℝ≥0)*h:ℝ)..((k:ℝ≥0)*h:ℝ)+(h:ℝ),
      φ (elementaryControl h a n (Real.toNNReal r) ω)) =
      ∫ _r in ((k:ℝ≥0)*h:ℝ)..((k:ℝ≥0)*h:ℝ)+(h:ℝ), φ (a k ω) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by linarith [h.coe_nonneg])
    intro r hr
    have hr0 : 0 ≤ r := le_trans ((k:ℝ≥0)*h).coe_nonneg hr.1.le
    have hr' : (k:ℝ≥0)*h ≤ Real.toNNReal r ∧ Real.toNNReal r < ((k+1:ℕ):ℝ≥0)*h := by
      constructor
      · apply NNReal.coe_le_coe.mp
        rw [Real.coe_toNNReal _ hr0]
        exact hr.1.le
      · apply NNReal.coe_lt_coe.mp
        rw [Real.coe_toNNReal _ hr0]
        simpa only [NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_add, Nat.cast_one, add_mul, one_mul, NNReal.coe_add] using hr.2
    change φ (elementaryControl h a n (Real.toNNReal r) ω) = φ (a k ω)
    rw [elementaryControl_on_step h a n k hk (Real.toNNReal r) hr' ω]
  rw [he, intervalIntegral.integral_const]
  simp only [add_sub_cancel_left, smul_eq_mul]

def feedbackEuler (B : ℝ≥0 → Ω → ℝ) (h c : ℝ≥0) (u : ℝ → ℝ → ℝ) (x : ℝ) :
    ℕ → Ω → ℝ
  | 0, _ => x
  | n+1, ω => feedbackEuler B h c u x n ω + (B (((n+1:ℕ):ℝ≥0)*h) ω-B ((n:ℝ≥0)*h) ω) +
      (c:ℝ)*(h:ℝ)*u ((n:ℝ≥0)*h) (feedbackEuler B h c u x n ω)

lemma feedbackEuler_adapted {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t))
    (h c : ℝ≥0) {u : ℝ → ℝ → ℝ} (hum : ∀ t, Measurable (u t)) (x : ℝ) (n : ℕ) :
    Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) ((n:ℝ≥0)*h)]
      (feedbackEuler B h c u x n) := by
  induction n with
  | zero => exact measurable_const
  | succ n IH =>
    have hle : (n:ℝ≥0)*h ≤ ((n+1:ℕ):ℝ≥0)*h := by gcongr; exact_mod_cast Nat.le_succ n
    have hYm := IH.mono ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).mono hle) le_rfl
    have hBs := (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) ((n:ℝ≥0)*h)).measurable.mono
      ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).mono hle) le_rfl
    have hBt := (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) (((n+1:ℕ):ℝ≥0)*h)).measurable
    exact (hYm.add (hBt.sub hBs)).add (((hum _).comp hYm).const_mul ((c:ℝ)*(h:ℝ)))

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
