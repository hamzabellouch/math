import Mathlib
import OAI.Probability.SKSupport.Foundations.FiniteValue

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma finiteValue_tail_of_le {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) {t : ℝ}
    (ht : (h:ℝ) ≤ t) : finiteValue c h f (N+1) i t = finiteValue c h f N (i+1) (t-h) := by
  rcases lt_or_eq_of_le ht with ht|rfl
  · exact finiteValue_tail f c h N i ht
  · rw [finiteValue_head f c h N i le_rfl,sub_self,finiteValue_zero hf hLip]
    funext x
    exact backward_terminal _ _ _ _

def finiteSource (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N i : ℕ) (t x : ℝ) : ℝ :=
  finiteCoeff c h N i t*(deriv (finiteValue c h f N i t) x)^2

lemma measurable_finiteSource {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    Measurable (fun p : ℝ × ℝ => finiteSource c h f N i p.1 p.2) := by
  exact ((measurable_finiteCoeff c h N i).comp measurable_fst).mul
    ((measurable_spatial_deriv (measurable_finiteValue hf hLip c h N i)
      (fun r => (finiteValue_regular hf hLip c h N i r).smooth.differentiable (by simp))).pow_const 2)

lemma finiteSource_bounded {f : ℝ → ℝ} (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    ∃ C : ℝ≥0, ∀ t x, |finiteSource c h f N i t x| ≤ C := by
  obtain ⟨C,hC⟩ := finiteCoeff_bounds c h N i
  refine ⟨C,fun t x => ?_⟩
  have hd : |deriv (finiteValue c h f N i t) x| ≤ 1 := by
    simpa only [Real.norm_eq_abs,NNReal.coe_one] using
      norm_deriv_le_of_lipschitz (x₀ := x) (finiteValue_lipschitz hLip c h N i t)
  rw [finiteSource,abs_mul,abs_pow,abs_of_nonneg (hC t).1]
  have hs : |deriv (finiteValue c h f N i t) x|^2 ≤ 1 := by
    nlinarith [abs_nonneg (deriv (finiteValue c h f N i t) x)]
  nlinarith [(hC t).1,(hC t).2]

lemma intervalIntegrable_heat_finiteSource {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) (p a b x : ℝ) :
    IntervalIntegrable (fun r => varianceHeat (r-p) (finiteSource c h f N i r) x) volume a b := by
  obtain ⟨C,hC⟩ := finiteSource_bounded hLip c h N i
  have hm := measurable_varianceHeat_family (measurable_finiteSource hf hLip c h N i)
    (measurable_id.sub_const p)
  apply (intervalIntegrable_const (c := (C:ℝ))).mono_fun
    (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  filter_upwards [] with r
  simpa only [Function.comp_def,id_eq,Real.norm_eq_abs,abs_of_nonneg C.coe_nonneg] using varianceHeat_abs_le (hC r) (r-p) x

lemma finiteSource_head (f : ℝ → ℝ) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) {t : ℝ}
    (ht : t ≤ h) : finiteSource c h f (N+1) i t =
      fun x => (c i:ℝ)*(deriv (backward (c i) h (cascade c h f N (i+1)) t) x)^2 := by
  funext x
  rw [finiteSource,finiteValue_head f c h N i ht]
  simp only [finiteCoeff,ite_eq_left ht]

lemma finiteSource_tail (f : ℝ → ℝ) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) {t : ℝ}
    (ht : (h:ℝ) < t) : finiteSource c h f (N+1) i t = finiteSource c h f N (i+1) (t-h) := by
  funext x
  rw [finiteSource,finiteValue_tail f c h N i ht]
  simp only [finiteCoeff,ite_eq_right (not_le.mpr ht),finiteSource]

lemma integral_heat_finiteSource_tail (f : ℝ → ℝ) (c : ℕ → ℝ≥0) (h : ℝ≥0)
    (N i : ℕ) {a b : ℝ} (ha : (h:ℝ) ≤ a) (hab : a ≤ b) (p x : ℝ) :
    (∫ r in a..b, varianceHeat (r-p) (finiteSource c h f (N+1) i r) x) =
      ∫ r in a-h..b-h, varianceHeat (r-(p-h)) (finiteSource c h f N (i+1) r) x := by
  rw [← intervalIntegral.integral_comp_sub_right (f := fun r => varianceHeat (r-(p-h))
    (finiteSource c h f N (i+1) r) x) (h:ℝ)]
  apply intervalIntegral.integral_congr_Ioo_of_le hab
  intro r hr
  dsimp only
  rw [finiteSource_tail f c h N i (ha.trans_lt hr.1)]
  rw [show r-(h:ℝ)-(p-h) = r-p by ring]

lemma finiteValue_heat_dual {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ)
    {p a b : ℝ} (ha : 0 ≤ a) (hpa : p ≤ a) (hab : a ≤ b) (hb : b ≤ (N:ℝ)*h) (x : ℝ) :
    varianceHeat (b-p) (finiteValue c h f N i b) x =
      varianceHeat (a-p) (finiteValue c h f N i a) x-
        (1/2)*(∫ r in a..b, varianceHeat (r-p) (finiteSource c h f N i r) x) := by
  induction N generalizing i p a b with
  | zero =>
    have hb0 : b = 0 := by simp only [Nat.cast_zero,zero_mul] at hb; linarith
    have ha0 : a = 0 := by linarith
    simp only [ha0,hb0,intervalIntegral.integral_same,mul_zero,sub_zero]
  | succ N ih =>
    by_cases hbh : b ≤ h
    · rw [finiteValue_head f c h N i hbh,finiteValue_head f c h N i (hab.trans hbh)]
      have hi : (∫ r in a..b, varianceHeat (r-p) (finiteSource c h f (N+1) i r) x) =
          (c i:ℝ)*(∫ r in a..b, varianceHeat (r-p)
            (fun z => (deriv (backward (c i) h (cascade c h f N (i+1)) r) z)^2) x) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr_Ioo_of_le hab
        intro r hr
        dsimp only
        rw [finiteSource_head f c h N i (hr.2.le.trans hbh),varianceHeat_const_mul]
      rw [hi]
      have he := backward_heat_dual (cascade_regular hf hLip c h N (i+1))
        (cascade_lipschitz hLip c h N (i+1)) (c i).coe_nonneg ha hpa hab hbh x
      linarith
    · have hhb : (h:ℝ) < b := lt_of_not_ge hbh
      have hbn : b-h ≤ (N:ℝ)*h := by
        push_cast at hb
        nlinarith
      by_cases hah : (h:ℝ) ≤ a
      · rw [finiteValue_tail_of_le hf hLip c h N i hhb.le,
          finiteValue_tail_of_le hf hLip c h N i hah,
          integral_heat_finiteSource_tail f c h N i hah hab]
        have he := ih (i+1) (p := p-h) (a := a-h) (b := b-h)
          (sub_nonneg.mpr hah) (by linarith) (by linarith) hbn
        rw [show b-(h:ℝ)-(p-h) = b-p by ring,
          show a-(h:ℝ)-(p-h) = a-p by ring] at he
        exact he
      · have hah' : a ≤ h := (lt_of_not_ge hah).le
        have hjoin := intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_heat_finiteSource hf hLip c h (N+1) i p a h x)
          (intervalIntegrable_heat_finiteSource hf hLip c h (N+1) i p h b x)
        have hhead := backward_heat_dual (cascade_regular hf hLip c h N (i+1))
          (cascade_lipschitz hLip c h N (i+1)) (c i).coe_nonneg ha hpa hah' le_rfl x
        have hihead : (∫ r in a..(h:ℝ), varianceHeat (r-p) (finiteSource c h f (N+1) i r) x) =
            (c i:ℝ)*(∫ r in a..(h:ℝ), varianceHeat (r-p)
              (fun z => (deriv (backward (c i) h (cascade c h f N (i+1)) r) z)^2) x) := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr_Ioo_of_le hah'
          intro r hr
          dsimp only
          rw [finiteSource_head f c h N i hr.2.le,varianceHeat_const_mul]
        have htail := ih (i+1) (p := p-h) (a := 0) (b := b-h)
          le_rfl (by linarith) (sub_nonneg.mpr hhb.le) hbn
        rw [finiteValue_zero hf hLip] at htail
        have hseam : backward (c i) h (cascade c h f N (i+1)) h = cascade c h f N (i+1) := by
          funext z; exact backward_terminal _ _ _ _
        rw [hseam] at hhead
        rw [finiteValue_tail_of_le hf hLip c h N i hhb.le,
          finiteValue_head f c h N i hah',← hjoin,hihead,
          integral_heat_finiteSource_tail f c h N i le_rfl hhb.le]
        simp only [sub_self] at *
        have he1 : b-(h:ℝ)-(p-h) = b-p := by ring
        have he2 : 0-(p-(h:ℝ)) = h-p := by ring
        rw [he1,he2] at htail
        linarith

lemma finiteValue_mild {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ (N:ℝ)*h) (x : ℝ) :
    finiteValue c h f N i a x = varianceHeat (b-a) (finiteValue c h f N i b) x+
      (1/2)*(∫ r in a..b, varianceHeat (r-a) (finiteSource c h f N i r) x) := by
  have he := finiteValue_heat_dual hf hLip c h N i ha le_rfl hab hb x
  rw [sub_self,varianceHeat_zero] at he
  linarith

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
