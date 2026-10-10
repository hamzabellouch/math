import Mathlib
import OAI.Probability.SKSupport.Regularity.BoundedSmoothFamily

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma finiteValue_time_bound {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    ∃ L : ℝ≥0, ∀ r ∈ Icc (0:ℝ) ((N:ℝ)*h), ∀ s ∈ Icc (0:ℝ) ((N:ℝ)*h), ∀ x,
      |finiteValue c h f N i r x-finiteValue c h f N i s x| ≤ (L:ℝ)*|r-s| := by
  induction N generalizing i with
  | zero => exact ⟨0,by simp [finiteValue]⟩
  | succ N ih =>
    obtain ⟨K,hK⟩ := ih (i+1)
    obtain ⟨L,hL⟩ := backward_joint_bound (cascade_regular hf hLip c h N (i+1))
      (cascade_lipschitz hLip c h N (i+1)) (c i).coe_nonneg (h:ℝ)
    have hhead (r s : ℝ) (hr : r ∈ Icc 0 (h:ℝ)) (hs : s ∈ Icc 0 (h:ℝ)) (x : ℝ) :
        |finiteValue c h f (N+1) i r x-finiteValue c h f (N+1) i s x| ≤ (L:ℝ)*|r-s| := by
      rw [finiteValue_head f c h N i hr.2,finiteValue_head f c h N i hs.2]
      simpa only [sub_self,abs_zero,add_zero] using hL r hr s hs x x
    have htail (r s : ℝ) (hr : r ∈ Icc (h:ℝ) (((N+1:ℕ):ℝ)*h))
        (hs : s ∈ Icc (h:ℝ) (((N+1:ℕ):ℝ)*h)) (x : ℝ) :
        |finiteValue c h f (N+1) i r x-finiteValue c h f (N+1) i s x| ≤ (K:ℝ)*|r-s| := by
      rw [finiteValue_tail_of_le hf hLip c h N i hr.1,finiteValue_tail_of_le hf hLip c h N i hs.1]
      have hr' : r-h ∈ Icc (0:ℝ) ((N:ℝ)*h) := by
        constructor
        · exact sub_nonneg.mpr hr.1
        · have hh := hr.2; push_cast at hh; nlinarith
      have hs' : s-h ∈ Icc (0:ℝ) ((N:ℝ)*h) := by
        constructor
        · exact sub_nonneg.mpr hs.1
        · have hh := hs.2; push_cast at hh; nlinarith
      simpa only [sub_sub_sub_cancel_right] using hK (r-h) hr' (s-h) hs' x
    refine ⟨L+K,?_⟩
    have hsum (A : ℝ) (hA : 0 ≤ A) : (L:ℝ)*A ≤ ((L+K:ℝ≥0):ℝ)*A ∧
        (K:ℝ)*A ≤ ((L+K:ℝ≥0):ℝ)*A := by
      simp only [NNReal.coe_add]
      constructor <;> nlinarith [L.coe_nonneg,K.coe_nonneg]
    have hhN : (h:ℝ) ≤ ((N+1:ℕ):ℝ)*h := by
      push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) h.coe_nonneg]
    have hord (r s : ℝ) (hr : r ∈ Icc (0:ℝ) (((N+1:ℕ):ℝ)*h))
        (hs : s ∈ Icc (0:ℝ) (((N+1:ℕ):ℝ)*h)) (hrs : r ≤ s) (x : ℝ) :
        |finiteValue c h f (N+1) i r x-finiteValue c h f (N+1) i s x| ≤ ((L+K:ℝ≥0):ℝ)*|r-s| := by
      by_cases hsh : s ≤ h
      · exact (hhead r s ⟨hr.1,hrs.trans hsh⟩ ⟨hs.1,hsh⟩ x).trans (hsum _ (abs_nonneg _)).1
      by_cases hhr : (h:ℝ) ≤ r
      · exact (htail r s ⟨hhr,hr.2⟩ ⟨hhr.trans hrs,hs.2⟩ x).trans (hsum _ (abs_nonneg _)).2
      have hrh : r ≤ h := (lt_of_not_ge hhr).le
      have hhs : (h:ℝ) ≤ s := (lt_of_not_ge hsh).le
      have ha := hhead r h ⟨hr.1,hrh⟩ ⟨h.coe_nonneg,le_rfl⟩ x
      have hb := htail h s ⟨le_rfl,hhN⟩ ⟨hhs,hs.2⟩ x
      have ht := abs_sub_le (finiteValue c h f (N+1) i r x)
        (finiteValue c h f (N+1) i h x) (finiteValue c h f (N+1) i s x)
      rw [abs_of_nonpos (sub_nonpos.mpr hrh)] at ha
      rw [abs_of_nonpos (sub_nonpos.mpr hhs)] at hb
      rw [abs_of_nonpos (sub_nonpos.mpr hrs),NNReal.coe_add]
      nlinarith [mul_nonneg L.coe_nonneg (sub_nonneg.mpr hhs),
        mul_nonneg K.coe_nonneg (sub_nonneg.mpr hrh)]
    intro r hr s hs x
    rcases le_total r s with hrs|hsr
    · exact hord r s hr hs hrs x
    · simpa only [abs_sub_comm] using hord s r hs hr hsr x

lemma finiteValue_joint_bound {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    ∃ L : ℝ≥0, ∀ r ∈ Icc (0:ℝ) ((N:ℝ)*h), ∀ s ∈ Icc (0:ℝ) ((N:ℝ)*h), ∀ x y,
      |finiteValue c h f N i r x-finiteValue c h f N i s y| ≤ (L:ℝ)*(|r-s|+|x-y|) := by
  obtain ⟨L,hL⟩ := finiteValue_time_bound hf hLip c h N i
  refine ⟨L+1,fun r hr s hs x y => ?_⟩
  have ht := hL r hr s hs x
  have hl := (finiteValue_lipschitz hLip c h N i s).dist_le_mul x y
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hl
  have htri := abs_sub_le (finiteValue c h f N i r x) (finiteValue c h f N i s x)
    (finiteValue c h f N i s y)
  simp only [NNReal.coe_add,NNReal.coe_one]
  nlinarith [mul_nonneg L.coe_nonneg (abs_nonneg (x-y)),abs_nonneg (r-s)]

lemma finiteValue_continuousOn {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => finiteValue c h f N i p.1 p.2)
      (Icc (0:ℝ) ((N:ℝ)*h) ×ˢ Set.univ) := by
  obtain ⟨L,hL⟩ := finiteValue_joint_bound hf hLip c h N i
  exact continuousOn_of_joint_bound hL

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def finiteRate (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N i : ℕ) (t x : ℝ) : ℝ :=
  -(1/2:ℝ)*deriv (deriv (finiteValue c h f N i t)) x-(1/2:ℝ)*finiteSource c h f N i t x

lemma measurable_finiteRate {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    Measurable (fun p : ℝ × ℝ => finiteRate c h f N i p.1 p.2) := by
  exact (measurable_const.mul (finiteGradient_family hf hLip c h N i).deriv.measurable).sub
    (measurable_const.mul (measurable_finiteSource hf hLip c h N i))

lemma finiteRate_bounded {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    ∃ C : ℝ≥0, ∀ t x, |finiteRate c h f N i t x| ≤ C := by
  obtain ⟨A,hA⟩ := (finiteGradient_family hf hLip c h N i).deriv.bound
  obtain ⟨B,hB⟩ := finiteSource_bounded hLip c h N i
  refine ⟨A+B,fun t x => ?_⟩
  have ha := hA t x
  have hb := hB t x
  unfold finiteRate
  refine (abs_sub _ _).trans ?_
  simp only [abs_mul,abs_neg,abs_of_nonneg (show (0:ℝ) ≤ 1/2 by norm_num),NNReal.coe_add]
  nlinarith [abs_nonneg (deriv (deriv (finiteValue c h f N i t)) x),
    abs_nonneg (finiteSource c h f N i t x)]

lemma intervalIntegrable_finiteRate {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) (a b x : ℝ) :
    IntervalIntegrable (fun t => finiteRate c h f N i t x) volume a b := by
  obtain ⟨C,hC⟩ := finiteRate_bounded hf hLip c h N i
  apply (intervalIntegrable_const (c := (C:ℝ))).mono_fun
    ((measurable_finiteRate hf hLip c h N i).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  filter_upwards [] with t
  simpa only [Function.comp_def,id_eq,Real.norm_eq_abs,abs_of_nonneg C.coe_nonneg] using hC t x

lemma finiteRate_head {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) h) :
    finiteRate c h f (N+1) i t = backwardRate (c i) h (cascade c h f N (i+1)) t := by
  funext x
  obtain ⟨C₂,C₃,Ct,L,h₂,h₃,hm,hCt,hd,hJ,hE⟩ :=
    (backward_verificationData (cascade_regular hf hLip c h N (i+1))
      (cascade_lipschitz hLip c h N (i+1)) (c i).coe_nonneg (h:ℝ)).bounds
  have he := hE t ht x
  rw [finiteRate,finiteSource_head f c h N i ht.2,finiteValue_head f c h N i ht.2]
  linarith

lemma finiteRate_tail (f : ℝ → ℝ) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) {t : ℝ}
    (ht : (h:ℝ) < t) : finiteRate c h f (N+1) i t = finiteRate c h f N (i+1) (t-h) := by
  funext x
  rw [finiteRate,finiteValue_tail f c h N i ht,finiteSource_tail f c h N i ht]
  rfl

lemma integral_finiteRate_tail (f : ℝ → ℝ) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ)
    {a b : ℝ} (ha : (h:ℝ) ≤ a) (hab : a ≤ b) (x : ℝ) :
    (∫ t in a..b, finiteRate c h f (N+1) i t x) =
      ∫ t in a-h..b-h, finiteRate c h f N (i+1) t x := by
  rw [← intervalIntegral.integral_comp_sub_right (f := fun t => finiteRate c h f N (i+1) t x) (h:ℝ)]
  apply intervalIntegral.integral_congr_Ioo_of_le hab
  intro t ht
  dsimp only
  rw [finiteRate_tail f c h N i (ha.trans_lt ht.1)]

lemma backward_integral_rate {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    {c : ℝ} (hc : 0 ≤ c) {a b T : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) (x : ℝ) :
    (∫ t in a..b, backwardRate c T f t x) = backward c T f b x-backward c T f a x := by
  obtain ⟨C₂,C₃,Ct,L,h₂,h₃,hm,hCt,hd,hJ,hE⟩ := (backward_verificationData hf hLip hc T).bounds
  have hcont : ContinuousOn (fun t => backward c T f t x) (Icc a b) := by
    intro t ht
    exact (hd t ⟨ha.trans ht.1,ht.2.trans hb⟩ x).continuousWithinAt.mono
      (Icc_subset_Icc ha hb)
  have hrate : ContinuousOn (fun t => backwardRate c T f t x) (Icc a b) := by
    apply ((continuousOn_of_joint_bound hJ).comp
      (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨ht,mem_univ _⟩)).mono
      (Icc_subset_Icc ha hb)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont _
    (hrate.intervalIntegrable_of_Icc hab)
  intro t ht
  exact (hd t ⟨ha.trans ht.1.le,ht.2.le.trans hb⟩ x).hasDerivAt
    (Icc_mem_nhds (ha.trans_lt ht.1) (ht.2.trans_le hb))

theorem finiteValue_integral_rate {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ (N:ℝ)*h) (x : ℝ) :
    (∫ t in a..b, finiteRate c h f N i t x) = finiteValue c h f N i b x-finiteValue c h f N i a x := by
  induction N generalizing i a b with
  | zero =>
    have hb0 : b = 0 := by simp only [Nat.cast_zero,zero_mul] at hb; linarith
    have ha0 : a = 0 := by linarith
    simp only [ha0,hb0,intervalIntegral.integral_same,sub_self]
  | succ N ih =>
    have hhead {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ h) :
        (∫ t in a..b, finiteRate c h f (N+1) i t x) =
          finiteValue c h f (N+1) i b x-finiteValue c h f (N+1) i a x := by
      rw [finiteValue_head f c h N i hb,finiteValue_head f c h N i (hab.trans hb)]
      have hi : (∫ t in a..b, finiteRate c h f (N+1) i t x) =
          (∫ t in a..b, backwardRate (c i) h (cascade c h f N (i+1)) t x) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hab
        intro t ht
        dsimp only
        rw [finiteRate_head hf hLip c h N i ⟨ha.trans ht.1.le,ht.2.le.trans hb⟩]
      rw [hi]
      exact backward_integral_rate (cascade_regular hf hLip c h N (i+1))
        (cascade_lipschitz hLip c h N (i+1)) (c i).coe_nonneg ha hab hb x
    have htail {a b : ℝ} (ha : (h:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (((N+1:ℕ):ℝ)*h)) :
        (∫ t in a..b, finiteRate c h f (N+1) i t x) =
          finiteValue c h f (N+1) i b x-finiteValue c h f (N+1) i a x := by
      rw [integral_finiteRate_tail f c h N i ha hab x,
        finiteValue_tail_of_le hf hLip c h N i (ha.trans hab),
        finiteValue_tail_of_le hf hLip c h N i ha]
      apply ih (i+1) (sub_nonneg.mpr ha) (by linarith)
      push_cast at hb
      nlinarith
    by_cases hbh : b ≤ h
    · exact hhead ha hab hbh
    by_cases hah : (h:ℝ) ≤ a
    · exact htail hah hab hb
    have hah' : a ≤ h := (lt_of_not_ge hah).le
    have hhb : (h:ℝ) ≤ b := (lt_of_not_ge hbh).le
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_finiteRate hf hLip c h (N+1) i a h x)
      (intervalIntegrable_finiteRate hf hLip c h (N+1) i h b x),
      hhead ha hah' le_rfl,htail le_rfl hhb hb]
    ring

end ZeroTemperatureSK.Heat

end
end

end OAI
