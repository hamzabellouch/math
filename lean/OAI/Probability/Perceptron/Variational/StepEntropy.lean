import Mathlib
import OAI.Probability.Perceptron.Variational.StepStationary

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def weightedStepTrial {I : Type*} [Fintype I] (w : I → ℝ) (q : I → Time)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) : Trial where
  toFun := fun t => ∑ i, if q i ≤ t then w i else 0
  monotone := by
    intro s t hst
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : q i ≤ s
    · simp only [ite_eq_left hi,ite_eq_left (hi.trans hst),le_refl]
    · rw [ite_eq_right hi]
      split_ifs <;> first | exact hw i | rfl
  measurable := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.ite (measurableSet_le measurable_const measurable_id) measurable_const
  nonneg := by
    intro t
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> first | exact hw i | rfl
  le_one := by
    intro t
    rw [← hw1]
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> first | rfl | exact hw i

lemma timeTail_atom_integral (q t : Time) (w : ℝ) :
    (∫ s in Ici t, (if q ≤ s then w else 0) ∂timeLaw) = w*(1-max (q:ℝ) (t:ℝ)) := by
  change (∫ s in Ici t, (Ici q).indicator (fun _ => w) s ∂timeLaw) = _
  rw [integral_indicator measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici]
  rw [Ici_inter_Ici]
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,timeLaw_eq_volume,
    unitInterval.volume_Ici,ENNReal.toReal_ofReal (sub_nonneg.mpr (max q t).2.2),smul_eq_mul]
  rcases le_total q t with h | h
  · rw [max_eq_right h,max_eq_right (show (q:ℝ) ≤ (t:ℝ) from h)]
    ring
  · rw [max_eq_left h,max_eq_left (show (t:ℝ) ≤ (q:ℝ) from h)]
    ring

lemma tailIntegral_weightedStepTrial {I : Type*} [Fintype I] (w : I → ℝ) (q : I → Time)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (t : Time) :
    tailIntegral (weightedStepTrial w q hw hw1) t = ∑ i, w i*(1-max (q i:ℝ) (t:ℝ)) := by
  unfold tailIntegral
  change (∫ s in Ici t, ∑ i, if q i ≤ s then w i else 0 ∂timeLaw) = _
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl (fun i _ => timeTail_atom_integral (q i) t (w i))
  · intro i _
    exact (integrable_const (w i)).indicator measurableSet_Ici

def weightedStepTail {I : Type*} [Fintype I] (w : I → ℝ) (q : I → ℝ) (t : ℝ) : ℝ :=
  ∑ i, w i*(1-max (q i) t)

lemma weightedStepTail_continuous {I : Type*} [Fintype I] (w q : I → ℝ) :
    Continuous (weightedStepTail w q) := by
  unfold weightedStepTail
  fun_prop

lemma weightedStepTail_lower {I : Type*} [Fintype I] (w q : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {B t : ℝ}
    (hq : ∀ i, q i ≤ B) (ht : t ≤ B) :
    1-B ≤ weightedStepTail w q t := by
  calc
    1-B = ∑ i, w i*(1-B) := by rw [← Finset.sum_mul,hw1,one_mul]
    _ ≤ _ := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (sub_le_sub_left (max_le (hq i) ht) 1) (hw i)

lemma weightedStepTail_upper {I : Type*} [Fintype I] (w q : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (t : ℝ) :
    weightedStepTail w q t ≤ 1-t := by
  calc
    _ ≤ ∑ i, w i*(1-t) := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (sub_le_sub_left (le_max_right (q i) t) 1) (hw i)
    _ = _ := by rw [← Finset.sum_mul,hw1,one_mul]

lemma weightedStepTail_of_le {I : Type*} [Fintype I] (w q : I → ℝ)
    (hw1 : ∑ i, w i = 1) {t : ℝ} (hq : ∀ i, q i ≤ t) :
    weightedStepTail w q t = 1-t := by
  simp only [weightedStepTail,max_eq_right (hq _)]
  rw [← Finset.sum_mul,hw1,one_mul]

lemma weightedStepTail_pos {I : Type*} [Fintype I] (w q : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {B t : ℝ}
    (hB : B < 1) (hq : ∀ i, q i ≤ B) (ht : t ≤ B) :
    0 < weightedStepTail w q t :=
  (sub_pos.mpr hB).trans_le (weightedStepTail_lower w q hw hw1 hq ht)

lemma weightedStepTail_inv_continuousOn {I : Type*} [Fintype I] (w q : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {B : ℝ}
    (hB : B < 1) (hq : ∀ i, q i ≤ B) :
    ContinuousOn (fun t => (weightedStepTail w q t)⁻¹) (Icc 0 B) :=
  (weightedStepTail_continuous w q).continuousOn.inv₀
    (fun _ ht => (weightedStepTail_pos w q hw hw1 hB hq ht.2).ne')

lemma integral_one_sub_inv {B : ℝ} (hB : B < 1) :
    (∫ t in (0:ℝ)..B, (1-t)⁻¹) = -Real.log (1-B) := by
  rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t⁻¹) 1]
  simp only [sub_zero]
  rw [integral_inv_of_pos (sub_pos.mpr hB) zero_lt_one,one_div,Real.log_inv]

theorem entropy_weightedStepTrial {I : Type*} [Fintype I] (w : I → ℝ) (q : I → Time)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B < 1)
    (hq : ∀ i, (q i : ℝ) ≤ B) :
    entropy (weightedStepTrial w q hw hw1) = ENNReal.ofReal
      (((∫ t in (0:ℝ)..B, (weightedStepTail w (fun i => (q i:ℝ)) t)⁻¹)+Real.log (1-B))/2) := by
  let D := weightedStepTail w (fun i => (q i:ℝ))
  let F : ℝ → ℝ := fun t => (D t)⁻¹-(1-t)⁻¹
  have hD (t : ℝ) (ht : t ≤ B) : 0 < D t := weightedStepTail_pos _ _ hw hw1 hB1 hq ht
  have hF : ContinuousOn F (Icc 0 B) :=
    (weightedStepTail_inv_continuousOn _ _ hw hw1 hB1 hq).sub
      ((continuous_const.sub continuous_id).continuousOn.inv₀ (fun t ht => by
        have : t < 1 := ht.2.trans_lt hB1
        exact (sub_pos.mpr this).ne'))
  have hF0 : ∀ t ∈ Icc 0 B, 0 ≤ F t := by
    intro t ht
    exact sub_nonneg.mpr (inv_le_inv₀ (sub_pos.mpr (ht.2.trans_lt hB1)) (hD t ht.2) |>.mpr
      (weightedStepTail_upper _ _ hw hw1 t))
  have he (t : Time) : (ENNReal.ofReal (tailIntegral (weightedStepTrial w q hw hw1) t))⁻¹-
      (ENNReal.ofReal (1-(t:ℝ)))⁻¹ = (Iic B).indicator (fun t => ENNReal.ofReal (F t)) (t:ℝ) := by
    rw [tailIntegral_weightedStepTrial]
    change (ENNReal.ofReal (D (t:ℝ)))⁻¹-_ = _
    by_cases ht : (t:ℝ) ≤ B
    · rw [Set.indicator_of_mem (show (t:ℝ) ∈ Iic B from ht)]
      dsimp [F]
      rw [ENNReal.ofReal_sub _ (inv_nonneg.mpr (sub_nonneg.mpr t.2.2)),
        ENNReal.ofReal_inv_of_pos (hD t ht),
        ENNReal.ofReal_inv_of_pos (sub_pos.mpr (ht.trans_lt hB1))]
    · rw [Set.indicator_of_notMem (show (t:ℝ) ∉ Iic B from ht)]
      have hd : D (t:ℝ) = 1-(t:ℝ) := weightedStepTail_of_le _ _ hw1
        (fun i => (hq i).trans (le_of_not_ge ht))
      rw [hd,tsub_self]
  have hset : Iic B ∩ Icc (0:ℝ) 1 = Icc 0 B := by
    ext t
    constructor
    · rintro ⟨ht,h0,h1⟩
      exact ⟨h0,ht⟩
    · rintro ⟨h0,ht⟩
      exact ⟨ht,h0,ht.trans hB1.le⟩
  have hel : (∫⁻ t : Time, (ENNReal.ofReal (tailIntegral (weightedStepTrial w q hw hw1) t))⁻¹-
      (ENNReal.ofReal (1-(t:ℝ)))⁻¹ ∂timeLaw) = ENNReal.ofReal (∫ t in Icc 0 B, F t) := by
    rw [lintegral_congr he]
    change (∫⁻ t : Icc (0:ℝ) 1, (Iic B).indicator (fun t => ENNReal.ofReal (F t)) t.val
      ∂Measure.comap Subtype.val volume) = _
    rw [lintegral_subtype_comap measurableSet_Icc,lintegral_indicator measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Iic,hset]
    exact (ofReal_integral_eq_lintegral_ofReal hF.integrableOn_Icc
      ((ae_restrict_mem measurableSet_Icc).mono (fun t ht => hF0 t ht))).symm
  have hInt : (∫ t in Icc 0 B, F t) = (∫ t in (0:ℝ)..B, (D t)⁻¹)+Real.log (1-B) := by
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hB0]
    have hiD : IntervalIntegrable (fun t => (D t)⁻¹) volume 0 B :=
      (weightedStepTail_inv_continuousOn _ _ hw hw1 hB1 hq).intervalIntegrable_of_Icc hB0
    have hiR : IntervalIntegrable (fun t : ℝ => (1-t)⁻¹) volume 0 B :=
      ((continuous_const.sub continuous_id).continuousOn.inv₀ (fun t (ht : t ∈ Icc (0:ℝ) B) =>
        (sub_pos.mpr (ht.2.trans_lt hB1)).ne')).intervalIntegrable_of_Icc hB0
    rw [show F = (fun t => (D t)⁻¹-(1-t)⁻¹) from rfl,
      intervalIntegral.integral_sub hiD hiR,integral_one_sub_inv hB1,sub_neg_eq_add]
  rw [entropy,hel,hInt,ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2)]
  norm_num
  rfl

def stepCumulative {k : ℕ} (w : Fin (k+1) → ℝ) (i : Fin k) : ℝ :=
  ∑ j : Fin (k+1), if j ≤ i.castSucc then w j else 0

lemma weightedStepTail_affine {k : ℕ} (w q : Fin (k+1) → ℝ) (hq : Monotone q)
    (i : Fin k) {t : ℝ} (ht : t ∈ Icc (q i.castSucc) (q i.succ)) :
    weightedStepTail w q t = weightedStepTail w q (q i.castSucc)-
      stepCumulative w i*(t-q i.castSucc) := by
  unfold weightedStepTail stepCumulative
  rw [Finset.sum_mul,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ≤ i.castSucc
  · rw [ite_eq_left hj,max_eq_right ((hq hj).trans ht.1),max_eq_right (hq hj)]
    ring
  · have hj' : i.succ ≤ j := by exact Fin.le_iff_val_le_val.mpr (by
      have hh := Fin.lt_def.mp (lt_of_not_ge hj)
      simp only [Fin.val_castSucc,Fin.val_succ] at *
      omega)
    rw [ite_eq_right hj,max_eq_left (ht.2.trans (hq hj')),max_eq_left
      ((hq (Fin.castSucc_le_succ i)).trans (hq hj'))]
    ring

lemma weightedStepTail_below_min {I : Type*} [Fintype I] (w q : I → ℝ)
    {a t : ℝ} (hq : ∀ i, a ≤ q i) (ht : t ≤ a) :
    weightedStepTail w q t = weightedStepTail w q a := by
  apply Finset.sum_congr rfl
  intro i _
  rw [max_eq_left (ht.trans (hq i)),max_eq_left (hq i)]

lemma affine_pos_on {A B a b z : ℝ} (_hab : a ≤ b) (hB : 0 < B) (hz : 0 < z)
    (hrel : A-z*(b-a)=B) {x : ℝ} (hx : x ∈ Icc a b) : 0 < A-z*(x-a) := by
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hx.2 a) hz.le
  linarith

lemma integral_positive_affine_inv {A B a b z : ℝ} (hab : a ≤ b) (_hA : 0 < A)
    (hB : 0 < B) (hz : 0 < z) (hrel : A-z*(b-a)=B) :
    (∫ x in a..b, (A-z*(x-a))⁻¹) = (Real.log A-Real.log B)/z := by
  have hd (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (fun x => -(Real.log (A-z*(x-a)))/z) (A-z*(x-a))⁻¹ x := by
    have hd := (((hasDerivAt_id x).sub_const a).const_mul z).const_sub A
    have he := ((hd.log (affine_pos_on hab hB hz hrel hx).ne').neg).div_const z
    have hv : -(-(z*1)/(A-z*(id x-a)))/z = (A-z*(x-a))⁻¹ := by
      dsimp only [id_eq]
      field_simp [hz.ne',(affine_pos_on hab hB hz hrel hx).ne']
    rw [hv] at he
    exact he
  have hi : IntervalIntegrable (fun x => (A-z*(x-a))⁻¹) volume a b :=
    ((continuous_const.sub (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn.inv₀
      (fun x hx => (affine_pos_on hab hB hz hrel hx).ne')).intervalIntegrable_of_Icc hab
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hd x (by simpa only [uIcc_of_le hab] using hx)) hi]
  rw [hrel]
  simp only [sub_self,mul_zero,sub_zero]
  ring

lemma integral_positive_affine_inv_sq {A B a b z : ℝ} (hab : a ≤ b) (hA : 0 < A)
    (hB : 0 < B) (hz : 0 < z) (hrel : A-z*(b-a)=B) :
    (∫ x in a..b, 1/(A-z*(x-a))^2) = (b-a)/(A*B) := by
  have hd (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (fun x => (A-z*(x-a))⁻¹/z) (1/(A-z*(x-a))^2) x := by
    have hd := (((hasDerivAt_id x).sub_const a).const_mul z).const_sub A
    have he := (hd.inv (affine_pos_on hab hB hz hrel hx).ne').div_const z
    have hv : (- -(z*1)/(A-z*(id x-a))^2)/z = 1/(A-z*(x-a))^2 := by
      dsimp only [id_eq]
      field_simp [hz.ne',(affine_pos_on hab hB hz hrel hx).ne']
    rw [hv] at he
    exact he
  have hi : IntervalIntegrable (fun x => 1/(A-z*(x-a))^2) volume a b := by
    have hc : ContinuousOn (fun x => (A-z*(x-a))⁻¹) (Icc a b) :=
      (continuous_const.sub (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn.inv₀
        (fun x hx => (affine_pos_on hab hB hz hrel hx).ne')
    have hh := (hc.pow 2).intervalIntegrable_of_Icc (μ := volume) hab
    change IntervalIntegrable (fun x => ((A-z*(x-a))⁻¹)^2) volume a b at hh
    simpa only [one_div,inv_pow] using hh
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hd x (by simpa only [uIcc_of_le hab] using hx)) hi]
  rw [hrel]
  simp only [sub_self,mul_zero,sub_zero]
  have hAn := hA.ne'
  have hBn := hB.ne'
  have hzn := hz.ne'
  field_simp
  nlinarith

lemma integral_eq_stepLogRatios (k : ℕ) (F : ℝ → ℝ) (q D : Fin (k+1) → ℝ)
    (z : Fin k → ℝ) (hq : Monotone q) (hc : ContinuousOn F (Icc (q 0) (q (Fin.last k))))
    (hseg : ∀ i : Fin k, (∫ x in q i.castSucc..q i.succ, F x) =
      (Real.log (D i.castSucc)-Real.log (D i.succ))/z i) :
    (∫ x in q 0..q (Fin.last k), F x) = 2*stepLogRatios k D z := by
  induction k with
  | zero => simp [stepLogRatios,Fin.fin_one_eq_zero]
  | succ k ih =>
    have h01 : q 0 ≤ q 1 := hq (Fin.zero_le _)
    have h1t : q 1 ≤ q (Fin.last (k+1)) := hq (Fin.le_last 1)
    have hct : ContinuousOn F (Icc ((fun i : Fin (k+1) => q i.succ) 0)
        ((fun i : Fin (k+1) => q i.succ) (Fin.last k))) := by
      exact hc.mono (Icc_subset_Icc h01 le_rfl)
    have ht := ih (fun i => q i.succ) (fun i => D i.succ) (fun i => z i.succ)
      (fun a b hab => hq (Fin.succ_le_succ_iff.mpr hab)) hct
      (fun i => by simpa only [Fin.castSucc_succ] using hseg i.succ)
    simp only [Fin.succ_zero_eq_one,Fin.succ_last] at ht
    have h0 := hseg 0
    simp only [Fin.castSucc_zero,Fin.succ_zero_eq_one] at h0
    rw [← intervalIntegral.integral_add_adjacent_intervals
      ((hc.mono (Icc_subset_Icc le_rfl h1t)).intervalIntegrable_of_Icc h01)
      ((hc.mono (Icc_subset_Icc h01 le_rfl)).intervalIntegrable_of_Icc h1t),h0,ht,
      stepLogRatios]
    ring

lemma weightedStep_integral_inv {k : ℕ} (w q : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hq : Monotone q)
    (hq0 : 0 ≤ q 0) (hq1 : q (Fin.last k) < 1) (hz : ∀ i, 0 < stepCumulative w i) :
    (∫ t in (0:ℝ)..q (Fin.last k), (weightedStepTail w q t)⁻¹) =
      q 0/weightedStepTail w q (q 0)+
        2*stepLogRatios k (fun i => weightedStepTail w q (q i)) (stepCumulative w) := by
  let D := weightedStepTail w q
  have hqi (i : Fin (k+1)) : q i ≤ q (Fin.last k) := hq (Fin.le_last i)
  have hD (i : Fin (k+1)) : 0 < D (q i) := weightedStepTail_pos _ _ hw hw1 hq1 hqi (hqi i)
  have hc := weightedStepTail_inv_continuousOn w q hw hw1 hq1 hqi
  have h0t : q 0 ≤ q (Fin.last k) := hqi 0
  have hseg (i : Fin k) : (∫ x in q i.castSucc..q i.succ, (D x)⁻¹) =
      (Real.log (D (q i.castSucc))-Real.log (D (q i.succ)))/stepCumulative w i := by
    have hab : q i.castSucc ≤ q i.succ := hq (Fin.castSucc_le_succ i)
    have he := weightedStepTail_affine w q hq i (t := q i.succ) ⟨hab,le_rfl⟩
    calc
      _ = ∫ x in q i.castSucc..q i.succ,
          (D (q i.castSucc)-stepCumulative w i*(x-q i.castSucc))⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hab] at ht
        dsimp only
        rw [show D t = _ from weightedStepTail_affine w q hq i ht]
      _ = _ := integral_positive_affine_inv hab (hD i.castSucc) (hD i.succ) (hz i) he.symm
  have htail := integral_eq_stepLogRatios k (fun t => (D t)⁻¹) q
    (fun i => D (q i)) (stepCumulative w) hq (hc.mono (Icc_subset_Icc hq0 le_rfl)) hseg
  have hroot : (∫ t in (0:ℝ)..q 0, (D t)⁻¹) = q 0/D (q 0) := by
    calc
      _ = ∫ _t in (0:ℝ)..q 0, (D (q 0))⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hq0] at ht
        dsimp only
        rw [show D t = D (q 0) from weightedStepTail_below_min w q (fun i => hq (Fin.zero_le i)) ht.2]
      _ = _ := by simp [div_eq_mul_inv]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((hc.mono (Icc_subset_Icc le_rfl h0t)).intervalIntegrable_of_Icc hq0)
    ((hc.mono (Icc_subset_Icc hq0 le_rfl)).intervalIntegrable_of_Icc h0t),hroot,htail]

theorem entropy_weightedStepTrial_finite_formula {k : ℕ} (w : Fin (k+1) → ℝ)
    (q : Fin (k+1) → Time) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hq : Monotone q) (hq1 : (q (Fin.last k):ℝ) < 1)
    (hz : ∀ i, 0 < stepCumulative w i) :
    entropy (weightedStepTrial w q hw hw1) = ENNReal.ofReal
      (Real.log (tailIntegral (weightedStepTrial w q hw hw1) (q (Fin.last k)))/2+
        stepLogRatios k (fun i => tailIntegral (weightedStepTrial w q hw hw1) (q i)) (stepCumulative w)+
        (q 0:ℝ)/(2*tailIntegral (weightedStepTrial w q hw hw1) (q 0))) := by
  have hqr : Monotone (fun i => (q i:ℝ)) := fun i j hij => hq hij
  have hqmax (i : Fin (k+1)) : (q i:ℝ) ≤ (q (Fin.last k):ℝ) := hqr (Fin.le_last i)
  rw [entropy_weightedStepTrial w q hw hw1 (q (Fin.last k)) (q (Fin.last k)).2.1 hq1 hqmax,
    weightedStep_integral_inv w (fun i => (q i:ℝ)) hw hw1 hqr (q 0).2.1 hq1 hz]
  simp only [tailIntegral_weightedStepTrial]
  change ENNReal.ofReal _ = ENNReal.ofReal
    (Real.log (weightedStepTail w (fun i => (q i:ℝ)) (q (Fin.last k)))/2+
      stepLogRatios k (fun i => weightedStepTail w (fun i => (q i:ℝ)) (q i)) (stepCumulative w)+
      (q 0:ℝ)/(2*weightedStepTail w (fun i => (q i:ℝ)) (q 0)))
  rw [weightedStepTail_of_le w (fun i => (q i:ℝ)) hw1 hqmax]
  congr 1
  ring

def weightedStepA {I : Type*} [Fintype I] (w q : I → ℝ) (r : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..r, 1/(weightedStepTail w q t)^2

lemma weightedStepA_root {k : ℕ} (w q : Fin (k+1) → ℝ)
    (hq : Monotone q) (hq0 : 0 ≤ q 0) :
    weightedStepA w q (q 0) = q 0/(weightedStepTail w q (q 0))^2 := by
  unfold weightedStepA
  calc
    _ = ∫ _t in (0:ℝ)..q 0, 1/(weightedStepTail w q (q 0))^2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hq0] at ht
      dsimp only
      rw [weightedStepTail_below_min w q (fun i => hq (Fin.zero_le i)) ht.2]
    _ = _ := by simp [div_eq_mul_inv]

lemma weightedStepA_increment {k : ℕ} (w q : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hq : Monotone q)
    (hq0 : 0 ≤ q 0) (hq1 : q (Fin.last k) < 1) (i : Fin k) (hz : 0 < stepCumulative w i) :
    weightedStepA w q (q i.succ)-weightedStepA w q (q i.castSucc) =
      (q i.succ-q i.castSucc)/(weightedStepTail w q (q i.castSucc)*weightedStepTail w q (q i.succ)) := by
  let D := weightedStepTail w q
  have hqi (i : Fin (k+1)) : q i ≤ q (Fin.last k) := hq (Fin.le_last i)
  have hD (i : Fin (k+1)) : 0 < D (q i) := weightedStepTail_pos _ _ hw hw1 hq1 hqi (hqi i)
  have hc : ContinuousOn (fun t => 1/(D t)^2) (Icc 0 (q (Fin.last k))) := by
    have hh := (weightedStepTail_inv_continuousOn w q hw hw1 hq1 hqi).pow 2
    change ContinuousOn (fun t => ((D t)⁻¹)^2) _ at hh
    simpa only [one_div,inv_pow] using hh
  have h0i : 0 ≤ q i.castSucc := hq0.trans (hq (Fin.zero_le _))
  have hij : q i.castSucc ≤ q i.succ := hq (Fin.castSucc_le_succ i)
  have hi := (hc.mono (Icc_subset_Icc le_rfl (hqi i.castSucc))).intervalIntegrable_of_Icc (μ := volume) h0i
  have hj := (hc.mono (Icc_subset_Icc h0i (hqi i.succ))).intervalIntegrable_of_Icc (μ := volume) hij
  have ha := intervalIntegral.integral_add_adjacent_intervals hi hj
  have hseg : (∫ t in q i.castSucc..q i.succ, 1/(D t)^2) =
      (q i.succ-q i.castSucc)/(D (q i.castSucc)*D (q i.succ)) := by
    have he := weightedStepTail_affine w q hq i (t := q i.succ) ⟨hij,le_rfl⟩
    calc
      _ = ∫ t in q i.castSucc..q i.succ,
          1/(D (q i.castSucc)-stepCumulative w i*(t-q i.castSucc))^2 := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hij] at ht
        dsimp only
        rw [show D t = _ from weightedStepTail_affine w q hq i ht]
      _ = _ := integral_positive_affine_inv_sq hij (hD i.castSucc) (hD i.succ) hz he.symm
  change (∫ t in (0:ℝ)..q i.succ, 1/(D t)^2)-
    (∫ t in (0:ℝ)..q i.castSucc, 1/(D t)^2) = _
  rw [← ha,hseg]
  ring

lemma weightedStep_truncated_entropy_nonneg {I : Type*} [Fintype I] (w q : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {B : ℝ} (hB0 : 0 ≤ B) (hB1 : B < 1)
    (hq : ∀ i, q i ≤ B) :
    0 ≤ ((∫ t in (0:ℝ)..B, (weightedStepTail w q t)⁻¹)+Real.log (1-B))/2 := by
  have hiD := (weightedStepTail_inv_continuousOn w q hw hw1 hB1 hq).intervalIntegrable_of_Icc (μ := volume) hB0
  have hiR : IntervalIntegrable (fun t : ℝ => (1-t)⁻¹) volume 0 B :=
    ((continuous_const.sub continuous_id).continuousOn.inv₀
      (fun t (ht : t ∈ Icc (0:ℝ) B) => (sub_pos.mpr (ht.2.trans_lt hB1)).ne')).intervalIntegrable_of_Icc hB0
  have hle := intervalIntegral.integral_mono_on hB0 hiR hiD (fun t ht =>
    (inv_le_inv₀ (sub_pos.mpr (ht.2.trans_lt hB1))
      (weightedStepTail_pos w q hw hw1 hB1 hq ht.2)).mpr
        (weightedStepTail_upper w q hw hw1 t))
  rw [integral_one_sub_inv hB1] at hle
  linarith

lemma entropy_weightedStepTrial_toReal {I : Type*} [Fintype I] (w : I → ℝ) (q : I → Time)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B < 1)
    (hq : ∀ i, (q i : ℝ) ≤ B) :
    (entropy (weightedStepTrial w q hw hw1)).toReal =
      ((∫ t in (0:ℝ)..B, (weightedStepTail w (fun i => (q i:ℝ)) t)⁻¹)+Real.log (1-B))/2 := by
  rw [entropy_weightedStepTrial w q hw hw1 B hB0 hB1 hq,ENNReal.toReal_ofReal
    (weightedStep_truncated_entropy_nonneg w (fun i => (q i:ℝ)) hw hw1 hB0 hB1 hq)]

lemma entropy_weightedStepTrial_toReal_finite_formula {k : ℕ} (w : Fin (k+1) → ℝ)
    (q : Fin (k+1) → Time) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hq : Monotone q) (hq1 : (q (Fin.last k):ℝ) < 1)
    (hz : ∀ i, 0 < stepCumulative w i) :
    (entropy (weightedStepTrial w q hw hw1)).toReal =
      Real.log (tailIntegral (weightedStepTrial w q hw hw1) (q (Fin.last k)))/2+
        stepLogRatios k (fun i => tailIntegral (weightedStepTrial w q hw hw1) (q i)) (stepCumulative w)+
        (q 0:ℝ)/(2*tailIntegral (weightedStepTrial w q hw hw1) (q 0)) := by
  have hqr : Monotone (fun i => (q i:ℝ)) := fun i j hij => hq hij
  have hqmax (i : Fin (k+1)) : (q i:ℝ) ≤ (q (Fin.last k):ℝ) := hqr (Fin.le_last i)
  rw [entropy_weightedStepTrial_toReal w q hw hw1 (q (Fin.last k)) (q (Fin.last k)).2.1 hq1 hqmax,
    weightedStep_integral_inv w (fun i => (q i:ℝ)) hw hw1 hqr (q 0).2.1 hq1 hz]
  simp only [tailIntegral_weightedStepTrial]
  change _ = Real.log (weightedStepTail w (fun i => (q i:ℝ)) (q (Fin.last k)))/2+
      stepLogRatios k (fun i => weightedStepTail w (fun i => (q i:ℝ)) (q i)) (stepCumulative w)+
      (q 0:ℝ)/(2*weightedStepTail w (fun i => (q i:ℝ)) (q 0))
  rw [weightedStepTail_of_le w (fun i => (q i:ℝ)) hw1 hqmax]
  ring

lemma stepCumulative_pos {k : ℕ} (w : Fin (k+1) → ℝ) (hw : ∀ i, 0 < w i) (i : Fin k) :
    0 < stepCumulative w i := by
  apply Finset.sum_pos'
  · intro j _
    split_ifs <;> first | exact (hw j).le | rfl
  · exact ⟨0,Finset.mem_univ _,by simpa only [ite_eq_left (Fin.zero_le _)] using hw 0⟩

lemma stepCumulative_lt_one {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (i : Fin k) :
    stepCumulative w i < 1 := by
  rw [← hw1]
  apply Finset.sum_lt_sum
  · intro j _
    split_ifs <;> first | rfl | exact (hw j).le
  · refine ⟨Fin.last k,Finset.mem_univ _,?_⟩
    have hnot : ¬Fin.last k ≤ i.castSucc := by
      simp only [Fin.le_iff_val_le_val,Fin.val_last,Fin.val_castSucc]
      omega
    simpa only [ite_eq_right hnot] using hw (Fin.last k)

lemma stepCumulative_strictMono {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) : StrictMono (stepCumulative w) := by
  intro i j hij
  apply Finset.sum_lt_sum
  · intro a _
    by_cases hai : a ≤ i.castSucc
    · have haj : a ≤ j.castSucc := hai.trans (Fin.castSucc_le_castSucc_iff.mpr hij.le)
      simp only [ite_eq_left hai,ite_eq_left haj,le_refl]
    · simp only [ite_eq_right hai]
      split_ifs <;> first | exact (hw a).le | rfl
  · refine ⟨j.castSucc,Finset.mem_univ _,?_⟩
    have hnot : ¬j.castSucc ≤ i.castSucc := by simpa only [Fin.castSucc_le_castSucc_iff] using not_le.mpr hij
    simpa only [ite_eq_right hnot,ite_eq_left le_rfl] using hw j.castSucc

end SphericalPerceptronFreeEnergy
end

end OAI
