import Mathlib
import OAI.Combinatorics.StripMass.LaguerreNormalization

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian
theorem laguerreExpectation_inverseSum (n : ℕ) {a : ℝ} (ha : 1 < a) :
    laguerreExpectation n a (fun r => ∑ i, (r i)⁻¹) =
      (n:ℝ)*(2*a+n-1)/(2*a*(a-1)) := by
  cases n with
  | zero => simp [laguerreExpectation]
  | succ n =>
    have ha0 : 0 < a := by linarith
    unfold laguerreExpectation
    rw [integral_laguerre_inverseSum_eq_gammaProduct ha,
      gammaSchurProduct_inverse n ha, laguerreNormalizer_succ_product n ha0,
      telescoping_inverse_product n (mul_pos (by norm_num : (0:ℝ)<2) ha0)]
    have hg := Real.Gamma_add_one (show a-1 ≠ 0 by linarith)
    rw [sub_add_cancel] at hg
    rw [hg]
    have hG : Real.Gamma (a-1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith : 0 < a-1)).ne'
    have hZ : laguerreNormalizer n (a+1) ≠ 0 := (laguerreNormalizer_pos n (by linarith)).ne'
    have hP : (∏ i : Fin n, ((i.val:ℝ)+1)/(2*a+i.val+1)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      positivity
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp
    ring


 


 
def minTilt (s r : ℝ) : ℝ := (max (1-s/r) 0)^2 / (1+s/r)
def minTiltProduct (n : ℕ) (s : ℝ) (r : Fin n → ℝ) : ℝ := ∏ i, minTilt s (r i)
def inverseSum (n : ℕ) (r : Fin n → ℝ) : ℝ := ∑ i, (r i)⁻¹

lemma minTilt_nonneg {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r) : 0 ≤ minTilt s r := by
  exact div_nonneg (sq_nonneg _) (by positivity)

lemma minTilt_le_one {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r) : minTilt s r ≤ 1 := by
  have ht : 0 ≤ s/r := div_nonneg hs hr.le
  have hm : 0 ≤ max (1-s/r) 0 := le_max_right _ _
  have hm1 : max (1-s/r) 0 ≤ 1 := max_le (by linarith) zero_le_one
  apply (div_le_one (by positivity : 0 < 1+s/r)).2
  nlinarith [mul_self_le_mul_self hm hm1]

lemma minTilt_eq_zero {s r : ℝ} (hr : 0 < r) (hrs : r ≤ s) : minTilt s r = 0 := by
  have ht : 1 ≤ s/r := (le_div_iff₀ hr).2 (by simpa using hrs)
  simp [minTilt, max_eq_right (by linarith : 1-s/r ≤ 0)]

lemma minTilt_eq_pair {s r : ℝ} (hs : 0 < s) (hrs : s < r) :
    minTilt s r = pairKernel s r / r := by
  have hr := hs.trans hrs
  rw [minTilt, max_eq_left (by rw [sub_nonneg]; exact (div_le_one hr).2 hrs.le)]
  unfold pairKernel
  field_simp

lemma one_sub_minTilt_le {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r) :
    1-minTilt s r ≤ 3*s/r := by
  by_cases hrs : r ≤ s
  · rw [minTilt_eq_zero hr hrs]
    have ht : 1 ≤ s/r := (le_div_iff₀ hr).2 (by simpa using hrs)
    have he : 3*s/r = 3*(s/r) := by ring
    rw [he]
    linarith
  · have ht : 0 ≤ s/r := div_nonneg hs hr.le
    have ht1 : s/r ≤ 1 := (div_le_one hr).2 (le_of_not_ge hrs)
    rw [minTilt, max_eq_left (by linarith : 0 ≤ 1-s/r)]
    have hd : 0 < 1+s/r := by positivity
    have he : 3*s/r = 3*(s/r) := by ring
    rw [he]
    have hh : 1-3*(s/r) ≤ (1-s/r)^2/(1+s/r) := by
      apply (le_div_iff₀ hd).2
      nlinarith [sq_nonneg (s/r)]
    linarith

lemma continuousOn_minTilt {s : ℝ} (hs : 0 ≤ s) : ContinuousOn (minTilt s) (Ioi 0) := by
  have hc : ContinuousOn (fun r : ℝ => s/r) (Ioi 0) :=
    continuousOn_const.div continuousOn_id (fun _ hr => ne_of_gt hr)
  unfold minTilt
  exact (((continuousOn_const.sub hc).sup continuousOn_const).pow 2).div
    (continuousOn_const.add hc) (fun r hr =>
      ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hs hr.le)))

lemma monotoneOn_minTilt {s : ℝ} (hs : 0 ≤ s) : MonotoneOn (minTilt s) (Ioi 0) := by
  intro r hr t ht hrt
  have hst : s/t ≤ s/r := div_le_div_of_nonneg_left hs hr hrt
  apply div_le_div₀
  · exact sq_nonneg _
  · exact pow_le_pow_left₀ (le_max_right _ _) (max_le_max_right 0 (by linarith)) 2
  · exact add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hs ht.le)
  · linarith

lemma measurable_minTilt (s : ℝ) : Measurable (minTilt s) := by unfold minTilt; fun_prop

lemma minTiltProduct_nonneg {n : ℕ} {s : ℝ} (hs : 0 ≤ s) {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) :
    0 ≤ minTiltProduct n s r := Finset.prod_nonneg fun i _ => minTilt_nonneg hs (hr i)

lemma minTiltProduct_le_one {n : ℕ} {s : ℝ} (hs : 0 ≤ s) {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) :
    minTiltProduct n s r ≤ 1 := Finset.prod_le_one₀ (fun i _ => minTilt_nonneg hs (hr i))
      (fun i _ => minTilt_le_one hs (hr i))

lemma minTiltProduct_eq_zero {n : ℕ} {s : ℝ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i)
    (h : ¬∀ i, s < r i) : minTiltProduct n s r = 0 := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (minTilt_eq_zero (hr i) (not_lt.mp hi))

lemma minTiltProduct_pair {n : ℕ} {s : ℝ} (hs : 0 < s) {r : Fin n → ℝ}
    (hr : ∀ i, s < r i) :
    (∏ i, r i) * minTiltProduct n s r = ∏ i, pairKernel s (r i) := by
  unfold minTiltProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [minTilt_eq_pair hs (hr i), mul_div_cancel₀ _ (hs.trans (hr i)).ne']

lemma laguerreDensity_cons_tilt {n : ℕ} {s : ℝ} (hs : 0 < s)
    {r : Fin n → ℝ} (hr : r ∈ laguerreDomain n) (hsr : ∀ i, s < r i) (a : ℝ) :
    laguerreDensity (n+1) a (Fin.cons s r) =
      laguerreWeight a s * minTiltProduct n s r * laguerreDensity n (a+1) r := by
  rw [laguerreDensity_cons, laguerreDensity_succ_parameter _ _ hr.2]
  calc
    _ = laguerreWeight a s * laguerreDensity n a r *
        ((∏ i, r i) * minTiltProduct n s r) := by rw [minTiltProduct_pair hs hsr]
    _ = _ := by ring

lemma continuousOn_minTiltProduct (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ContinuousOn (minTiltProduct n s) (coordinateBox (Fin n) (Ioi 0)) := by
  apply continuousOn_finsetProd
  intro i _
  exact (continuousOn_minTilt hs).comp (continuous_apply i).continuousOn (fun _ hr => hr i)

lemma monotoneOn_minTiltProduct (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    MonotoneOn (minTiltProduct n s) (coordinateBox (Fin n) (Ioi 0)) := by
  intro r hr t ht hrt
  apply Finset.prod_le_prod₀
  · intro i _
    exact minTilt_nonneg hs (hr i)
  · intro i _
    exact monotoneOn_minTilt hs (hr i) (ht i) (hrt i)

lemma measurable_minTiltProduct (n : ℕ) (s : ℝ) : Measurable (minTiltProduct n s) := by
  apply Finset.measurable_prod
  intro i _
  exact (measurable_minTilt s).comp (measurable_pi_apply i)

lemma inverseSum_nonneg {n : ℕ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) : 0 ≤ inverseSum n r :=
  Finset.sum_nonneg fun i _ => (inv_pos.mpr (hr i)).le

lemma continuousOn_inverseSum (n : ℕ) :
    ContinuousOn (inverseSum n) (coordinateBox (Fin n) (Ioi 0)) := by
  apply continuousOn_finsetSum
  intro i _
  exact (continuous_apply i).continuousOn.inv₀ fun _ hr => ne_of_gt (hr i)

lemma antitoneOn_inverseSum (n : ℕ) :
    AntitoneOn (inverseSum n) (coordinateBox (Fin n) (Ioi 0)) := by
  intro r hr t ht hrt
  exact Finset.sum_le_sum fun i _ => inv_anti₀ (hr i) (hrt i)

lemma measurable_inverseSum (n : ℕ) : Measurable (inverseSum n) := by unfold inverseSum; fun_prop

lemma integrable_laguerreLaw_inverseSum {n : ℕ} {a : ℝ} (ha : 1 < a) :
    Integrable (inverseSum n) (laguerreLaw n a) :=
  integrable_laguerreLaw (by linarith) (integrableOn_laguerre_inverseSum ha)

lemma integrable_laguerreLaw_minTiltProduct (n : ℕ) {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    Integrable (minTiltProduct n s) (laguerreLaw n a) := by
  let := laguerreLaw_isProbabilityMeasure n ha
  apply (integrable_const (1 : ℝ)).mono' (measurable_minTiltProduct n s).aestronglyMeasurable
  filter_upwards [ae_laguerreDomain n a] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (minTiltProduct_nonneg hs hr.2)]
  exact minTiltProduct_le_one hs hr.2

lemma integrable_laguerreLaw_inverseSum_minTilt {n : ℕ} {a s : ℝ} (ha : 1 < a) (hs : 0 ≤ s) :
    Integrable (fun r => inverseSum n r * minTiltProduct n s r) (laguerreLaw n a) := by
  apply (integrable_laguerreLaw_inverseSum ha).mono'
    ((measurable_inverseSum n).mul (measurable_minTiltProduct n s)).aestronglyMeasurable
  filter_upwards [ae_laguerreDomain n a] with r hr
  change ‖inverseSum n r * minTiltProduct n s r‖ ≤ inverseSum n r
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inverseSum_nonneg hr.2)
    (minTiltProduct_nonneg hs hr.2))]
  exact mul_le_of_le_one_right (inverseSum_nonneg hr.2) (minTiltProduct_le_one hs hr.2)

lemma laguerre_inverseSum_minTilt_le (n : ℕ) {a s : ℝ} (ha : 1 < a) (hs : 0 ≤ s) :
    (∫ r, inverseSum n r * minTiltProduct n s r ∂laguerreLaw n a) ≤
      ((n:ℝ)*(2*a+n-1)/(2*a*(a-1))) * (∫ r, minTiltProduct n s r ∂laguerreLaw n a) := by
  have h := laguerreLaw_reverse_covariance (by linarith : 0 < a) (inverseSum n) (minTiltProduct n s)
    (continuousOn_inverseSum n) (continuousOn_minTiltProduct n hs)
    (antitoneOn_inverseSum n) (monotoneOn_minTiltProduct n hs)
    (integrable_laguerreLaw_inverseSum ha) (integrable_laguerreLaw_minTiltProduct n (by linarith) hs)
    (integrable_laguerreLaw_inverseSum_minTilt ha hs)
  have he : (∫ r, inverseSum n r ∂laguerreLaw n a) = (n:ℝ)*(2*a+n-1)/(2*a*(a-1)) := by
    rw [integral_laguerreLaw n (by linarith)]
    exact laguerreExpectation_inverseSum n ha
  rw [he] at h
  exact h



lemma laguerre_indicator_cons_tilt (n : ℕ) (a : ℝ) (f : (Fin (n+1) → ℝ) → ℝ)
    (s : ℝ) (r : Fin n → ℝ) :
    (laguerreDomain (n+1)).indicator (fun x => f x * laguerreDensity (n+1) a x) (Fin.cons s r) =
      (Ioi 0).indicator (laguerreWeight a) s * (laguerreDomain n).indicator
        (fun r => f (Fin.cons s r) * minTiltProduct n s r * laguerreDensity n (a+1) r) r := by
  classical
  by_cases hs : 0 < s
  · rw [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs)]
    by_cases hr : r ∈ laguerreDomain n
    · rw [indicator_of_mem hr]
      by_cases hsr : ∀ i, s < r i
      · rw [indicator_of_mem ((laguerreDomain_cons_iff s r).2 ⟨hs,hr,hsr⟩),
          laguerreDensity_cons_tilt hs hr hsr a]
        ring
      · have hx : Fin.cons s r ∉ laguerreDomain (n+1) := by
          intro hx
          exact hsr ((laguerreDomain_cons_iff s r).1 hx).2.2
        rw [indicator_of_notMem hx, minTiltProduct_eq_zero hr.2 hsr]
        ring
    · have hx : Fin.cons s r ∉ laguerreDomain (n+1) := by
        intro hx
        exact hr ((laguerreDomain_cons_iff s r).1 hx).2.1
      simp only [indicator_of_notMem hx, indicator_of_notMem hr, mul_zero]
  · have hx : Fin.cons s r ∉ laguerreDomain (n+1) := by
      intro hx
      exact hs ((laguerreDomain_cons_iff s r).1 hx).1
    simp only [indicator_of_notMem hx, indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs), zero_mul]

lemma integral_laguerre_splitMin (n : ℕ) (a : ℝ) (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : IntegrableOn (fun x => f x * laguerreDensity (n+1) a x) (laguerreDomain (n+1))) :
    (∫ x in laguerreDomain (n+1), f x * laguerreDensity (n+1) a x) =
      ∫ s in Ioi 0, laguerreWeight a s *
        ∫ r in laguerreDomain n, f (Fin.cons s r) * minTiltProduct n s r * laguerreDensity n (a+1) r := by
  have hi := (integrable_indicator_iff (isOpen_laguerreDomain (n+1)).measurableSet).2 hf
  rw [← integral_indicator (isOpen_laguerreDomain (n+1)).measurableSet, integral_fin_cons_eq]
  calc
    _ = ∫ s, ∫ r : Fin n → ℝ, (laguerreDomain (n+1)).indicator
        (fun x => f x * laguerreDensity (n+1) a x) (Fin.cons s r) :=
      integral_prod _ (integrable_fin_cons hi)
    _ = _ := by
      simp_rw [laguerre_indicator_cons_tilt, integral_const_mul,
        integral_indicator (isOpen_laguerreDomain n).measurableSet]
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun s =>
        (indicator_mul_left (Ioi 0) (laguerreWeight a)
          (fun s => ∫ r in laguerreDomain n,
            f (Fin.cons s r) * minTiltProduct n s r * laguerreDensity n (a+1) r)).symm

lemma integrable_laguerre_splitMin (n : ℕ) (a : ℝ) (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : IntegrableOn (fun x => f x * laguerreDensity (n+1) a x) (laguerreDomain (n+1))) :
    IntegrableOn (fun s => laguerreWeight a s *
        ∫ r in laguerreDomain n, f (Fin.cons s r) * minTiltProduct n s r * laguerreDensity n (a+1) r)
      (Ioi 0) := by
  have hi := (integrable_indicator_iff (isOpen_laguerreDomain (n+1)).measurableSet).2 hf
  have hj := (integrable_fin_cons hi).integral_prod_left
  simp_rw [laguerre_indicator_cons_tilt, integral_const_mul,
    integral_indicator (isOpen_laguerreDomain n).measurableSet] at hj
  have he : (fun s => (Ioi 0).indicator (laguerreWeight a) s *
      ∫ r in laguerreDomain n, f (Fin.cons s r) * minTiltProduct n s r * laguerreDensity n (a+1) r) =
      (Ioi 0).indicator (fun s => laguerreWeight a s *
      ∫ r in laguerreDomain n, f (Fin.cons s r) * minTiltProduct n s r * laguerreDensity n (a+1) r) := by
    ext s
    exact (indicator_mul_left (Ioi 0) (laguerreWeight a)
      (fun s => ∫ r in laguerreDomain n,
        f (Fin.cons s r) * minTiltProduct n s r * laguerreDensity n (a+1) r)).symm
  rw [he] at hj
  exact (integrable_indicator_iff measurableSet_Ioi).1 hj

lemma integrableOn_laguerre_tailInverseSum {n : ℕ} {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun r : Fin (n+1) → ℝ => (∑ i : Fin n, (r i.succ)⁻¹) * laguerreDensity (n+1) a r)
      (laguerreDomain (n+1)) := by
  simp only [Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  simpa only [IntegrableOn, Real.rpow_neg_one] using integrableOn_laguerre_inverse_coordinate ha
    i.succ (p := 1) (by simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]; linarith [Nat.cast_nonneg (α := ℝ) i.val])

lemma weighted_integral_laguerre_inverseSum_minTilt_le (n : ℕ) {a s : ℝ} (ha : 1 < a) (hs : 0 ≤ s) :
    (∫ r in laguerreDomain n, inverseSum n r * minTiltProduct n s r * laguerreDensity n a r) ≤
      ((n:ℝ)*(2*a+n-1)/(2*a*(a-1))) *
        (∫ r in laguerreDomain n, minTiltProduct n s r * laguerreDensity n a r) := by
  have h := laguerre_inverseSum_minTilt_le n ha hs
  simp only [integral_laguerreLaw n (show 0 < a by linarith), laguerreExpectation,
    ← mul_div_assoc] at h
  exact (div_le_div_iff_of_pos_right (laguerreNormalizer_pos n (by linarith))).1 h

 

theorem laguerreExpectation_tailInverseSum_le (n : ℕ) {a : ℝ} (ha : 0 < a) :
    laguerreExpectation (n+1) a (fun r => ∑ i : Fin n, (r i.succ)⁻¹) ≤
      (n:ℝ)*(2*(a+1)+n-1)/(2*(a+1)*a) := by
  let T := (n:ℝ)*(2*(a+1)+n-1)/(2*(a+1)*a)
  have hi := integrableOn_laguerre_tailInverseSum (n := n) ha
  have h1 : IntegrableOn (fun x => (1:ℝ) * laguerreDensity (n+1) a x) (laguerreDomain (n+1)) := by
    simpa using integrableOn_laguerreDensity (n+1) ha
  have hb (s : ℝ) (hs : 0 < s) :
      (∫ r in laguerreDomain n, (∑ i : Fin n, (r i)⁻¹) * minTiltProduct n s r * laguerreDensity n (a+1) r) ≤
        T * ∫ r in laguerreDomain n, minTiltProduct n s r * laguerreDensity n (a+1) r := by
    simpa only [inverseSum, add_sub_cancel_right, T] using
      weighted_integral_laguerre_inverseSum_minTilt_le n (by linarith : 1 < a+1) hs.le
  have hm : (∫ x in laguerreDomain (n+1), (∑ i : Fin n, (x i.succ)⁻¹) * laguerreDensity (n+1) a x) ≤
      T * laguerreNormalizer (n+1) a := by
    rw [integral_laguerre_splitMin n a _ hi]
    change _ ≤ T * ∫ x in laguerreDomain (n+1), laguerreDensity (n+1) a x
    have he : (∫ x in laguerreDomain (n+1), laguerreDensity (n+1) a x) =
        ∫ x in laguerreDomain (n+1), (1:ℝ) * laguerreDensity (n+1) a x := by simp
    rw [he]
    rw [integral_laguerre_splitMin n a (fun _ => 1) h1, ← integral_const_mul]
    apply integral_mono_ae (integrable_laguerre_splitMin n a _ hi)
      ((integrable_laguerre_splitMin n a (fun _ => 1) h1).const_mul T)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    simp only [Fin.cons_succ, one_mul]
    have H := mul_le_mul_of_nonneg_left (hb s hs) (laguerreWeight_pos a hs).le
    simpa only [mul_left_comm] using H
  exact (div_le_iff₀ (laguerreNormalizer_pos (n+1) ha)).2 hm

end

 

noncomputable section
open scoped BigOperators
open Set MeasureTheory

lemma reciprocal_product_succ (n : ℕ) :
    (∏ i : Fin n, ((i.val:ℝ)+1)/(i.val+2)) = 1/(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
    rw [ih]
    have h1 : (n:ℝ)+1 ≠ 0 := by positivity
    have h2 : (n:ℝ)+2 ≠ 0 := by positivity
    field_simp
    ring

lemma laguerreNormalizer_half_step (n : ℕ) :
    laguerreNormalizer (n+1) (1/2) =
      Real.Gamma (1/2) / (n+1) * laguerreNormalizer n (3/2) := by
  rw [laguerreNormalizer_succ_product n (by norm_num : (0:ℝ)<1/2)]
  norm_num only at *
  have he : (fun i : Fin n => ((i.val:ℝ)+1)/(1+i.val+1)) =
      (fun i : Fin n => ((i.val:ℝ)+1)/(i.val+2)) := by ext i; congr 1; ring
  rw [he, reciprocal_product_succ]
  ring

lemma laguerreSmallCoefficient_half_one (n : ℕ) :
    laguerreSmallCoefficient (n+1) (1/2) 1 = 2*(n+1)/Real.Gamma (1/2) := by
  unfold laguerreSmallCoefficient
  simp only [Nat.add_sub_cancel, Fin.prod_univ_one, Fin.val_zero, Nat.cast_zero, add_zero]
  rw [laguerreNormalizer_half_step]
  have hZ : laguerreNormalizer n (3/2) ≠ 0 := (laguerreNormalizer_pos n (by norm_num)).ne'
  have hG : Real.Gamma (1/2) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num : (0:ℝ)<1/2)).ne'
  have hN : (n:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring_nf

lemma laguerre_least_inverseQuarter_upper (n : ℕ) :
    laguerreExpectation (n+1) (1/2) (fun r => (r 0)^(-(1/4:ℝ))) ≤
      (2*(2/Real.Gamma (1/2))^(1/2:ℝ)) * ((n:ℝ)+1)^(1/2:ℝ) := by
  have H := laguerre_inverse_bound_normalizer_ratio
    (by norm_num : (0:ℝ)<1/2) (0 : Fin (n+1)) (by norm_num : (0:ℝ)<1/4)
    (by norm_num [laguerreDimension] : (1/4:ℝ)<laguerreDimension (1/2) ((0:Fin (n+1)).val+1))
  norm_num only [Fin.val_zero, zero_add, laguerreDimension] at H
  rw [laguerreSmallCoefficient_half_one] at H
  convert H using 1
  have hg := (Real.Gamma_pos_of_pos (by norm_num : (0:ℝ)<1/2))
  rw [show 2*((n:ℝ)+1)/Real.Gamma (1/2) = (2/Real.Gamma (1/2))*((n:ℝ)+1) by ring,
    Real.mul_rpow (by positivity) (by positivity)]
  ring

lemma rpow_quarter_le_one_add {x : ℝ} (hx : 0 ≤ x) : x^(1/4:ℝ) ≤ 1+x := by
  by_cases h : x ≤ 1
  · have hp := Real.rpow_le_rpow hx h (by norm_num : (0:ℝ)≤1/4)
    rw [Real.one_rpow] at hp
    linarith
  · have h1 : 1 ≤ x := le_of_not_ge h
    have hp := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num : (1/4:ℝ)≤1)
    rw [Real.rpow_one] at hp
    linarith

lemma rpow_quarter_le_linear_scaled {x t : ℝ} (hx : 0 ≤ x) (ht : 0 < t) :
    x^(1/4:ℝ) ≤ t^(1/4:ℝ) * (1+x/t) := by
  have H := mul_le_mul_of_nonneg_left (rpow_quarter_le_one_add (div_nonneg hx ht.le))
    (Real.rpow_pos_of_pos ht (1/4)).le
  rw [← Real.mul_rpow ht.le (div_nonneg hx ht.le), mul_div_cancel₀ _ ht.ne'] at H
  exact H

lemma laguerre_tailInverseSum_half_upper (n : ℕ) :
    laguerreExpectation (n+1) (1/2) (fun r => ∑ i : Fin n, (r i.succ)⁻¹) ≤ ((n:ℝ)+1)^2 := by
  have H := laguerreExpectation_tailInverseSum_le n (by norm_num : (0:ℝ)<1/2)
  apply H.trans
  norm_num only
  have hn := Nat.cast_nonneg (α := ℝ) n
  nlinarith [sq_nonneg ((n:ℝ)+1)]

 

end
end CriticalStrip

end OAI
