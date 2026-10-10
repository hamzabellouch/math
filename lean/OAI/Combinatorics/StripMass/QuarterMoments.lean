import Mathlib
import OAI.Combinatorics.StripMass.InverseMoments

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory
theorem laguerre_inverseQuarterSum_upper (n : ℕ) :
    (∫ r, inverseQuarterStatistic (n+1) r ∂laguerreLaw (n+1) (1/2)) ≤
      (2*(2/Real.Gamma (1/2))^(1/2:ℝ)+2) * ((n:ℝ)+1)^(1/2:ℝ) := by
  let μ := laguerreLaw (n+1) (1/2)
  let S := fun r : Fin (n+1) → ℝ => ∑ i : Fin n, (r i.succ)⁻¹
  let T : ℝ := ((n:ℝ)+1)^2
  have ht : 0 < T := by dsimp [T]; positivity
  have he : T^(1/4:ℝ) = ((n:ℝ)+1)^(1/2:ℝ) := by
    dsimp only [T]
    rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ (n:ℝ)+1)]
    norm_num
  let : IsProbabilityMeasure μ := laguerreLaw_isProbabilityMeasure _ (by norm_num)
  have hi : Integrable S μ := integrable_laguerreLaw (by norm_num)
    (integrableOn_laguerre_tailInverseSum (by norm_num : (0:ℝ)<1/2))
  have hfirst : Integrable (fun r : Fin (n+1) → ℝ => (r 0)^(-(1/4:ℝ))) μ :=
    integrable_laguerreLaw_inverse_coordinate (by norm_num) 0 (by norm_num)
  have hmaj : Integrable (fun r => (r 0)^(-(1/4:ℝ)) + T^(1/4:ℝ)*(1+S r/T)) μ :=
    hfirst.add (((integrable_const 1).add (hi.div_const T)).const_mul _)
  have hpoint : inverseQuarterStatistic (n+1) ≤ᵐ[μ]
      (fun r => (r 0)^(-(1/4:ℝ)) + T^(1/4:ℝ)*(1+S r/T)) := by
    filter_upwards [ae_laguerreDomain (n+1) (1/2)] with r hr
    have hs : 0 ≤ S r := Finset.sum_nonneg fun i _ => (inv_pos.mpr (hr.2 i.succ)).le
    change (∑ i, (r i)⁻¹)^(1/4:ℝ) ≤ _
    rw [Fin.sum_univ_succ]
    apply (Real.rpow_add_le_add_rpow (inv_pos.mpr (hr.2 0)).le hs (by norm_num) (by norm_num)).trans
    rw [Real.inv_rpow (hr.2 0).le, ← Real.rpow_neg (hr.2 0).le]
    exact add_le_add_right (rpow_quarter_le_linear_scaled hs ht) _
  have H := integral_mono_ae (integrable_laguerreLaw_inverseQuarterSum (by norm_num : (1/4:ℝ)<1/2))
    hmaj hpoint
  have hs : (∫ r, S r ∂μ) ≤ T := by
    rw [show μ = laguerreLaw (n+1) (1/2) from rfl, integral_laguerreLaw _ (by norm_num)]
    exact laguerre_tailInverseSum_half_upper n
  have hf := laguerre_least_inverseQuarter_upper n
  rw [← integral_laguerreLaw _ (by norm_num : (0:ℝ)<1/2)] at hf
  have hroot : 0 ≤ T^(1/4:ℝ) := (Real.rpow_pos_of_pos ht _).le
  have hj : Integrable (fun r => 1+S r/T) μ := (integrable_const 1).add (hi.div_const T)
  have hk : Integrable (fun r => T^(1/4:ℝ)*(1+S r/T)) μ := hj.const_mul _
  change (∫ r, inverseQuarterStatistic (n+1) r ∂μ) ≤
    ∫ r, (r 0)^(-(1/4:ℝ)) + T^(1/4:ℝ)*(1+S r/T) ∂μ at H
  rw [integral_add hfirst hk, integral_const_mul,
    integral_add (integrable_const 1) (hi.div_const T), integral_div,
    integral_const, probReal_univ, one_smul] at H
  have hs' : (∫ r, S r ∂μ)/T ≤ 1 := (div_le_one ht).2 hs
  calc
    _ ≤ _ := H
    _ ≤ (2*(2/Real.Gamma (1/2))^(1/2:ℝ)) * ((n:ℝ)+1)^(1/2:ℝ) + T^(1/4:ℝ)*2 := by
      exact add_le_add hf (mul_le_mul_of_nonneg_left (by linarith) hroot)
    _ = _ := by rw [he]; ring


 


lemma reciprocal_product_two_succ (n : ℕ) :
    (∏ i : Fin n, ((i.val:ℝ)+1)/(i.val+3)) = 2/((n+1)*(n+2)) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
    rw [ih]
    have h1 : (n:ℝ)+1 ≠ 0 := by positivity
    have h2 : (n:ℝ)+2 ≠ 0 := by positivity
    have h3 : (n:ℝ)+3 ≠ 0 := by positivity
    field_simp
    ring

lemma laguerreNormalizer_one_step (n : ℕ) :
    laguerreNormalizer (n+1) 1 =
      2/((n+1)*(n+2)) * laguerreNormalizer n 2 := by
  rw [laguerreNormalizer_succ_product n (by norm_num : (0:ℝ)<1)]
  norm_num only [Real.Gamma_one]
  have he : (fun i : Fin n => ((i.val:ℝ)+1)/(2+i.val+1)) =
      (fun i : Fin n => ((i.val:ℝ)+1)/(i.val+3)) := by ext i; congr 1; ring
  rw [he, reciprocal_product_two_succ]
  ring

lemma laguerreNormalizer_one_ratio (n : ℕ) :
    laguerreNormalizer n 2 / laguerreNormalizer (n+1) 1 = ((n:ℝ)+1)*(n+2)/2 := by
  rw [laguerreNormalizer_one_step]
  have hz : laguerreNormalizer n 2 ≠ 0 := (laguerreNormalizer_pos n (by norm_num)).ne'
  have h1 : (n:ℝ)+1 ≠ 0 := by positivity
  have h2 : (n:ℝ)+2 ≠ 0 := by positivity
  field_simp

lemma minTiltProduct_lower {n : ℕ} {s : ℝ} (hs : 0 ≤ s) {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) :
    1-3*s*inverseSum n r ≤ minTiltProduct n s r := by
  have h := abs_one_sub_prod_le Finset.univ (fun i : Fin n => minTilt s (r i))
    (fun i _ => by rw [abs_of_nonneg (minTilt_nonneg hs (hr i))]; exact minTilt_le_one hs (hr i))
  have hp := minTiltProduct_le_one hs hr
  change |1-minTiltProduct n s r| ≤ ∑ i, |1-minTilt s (r i)| at h
  rw [abs_of_nonneg (by linarith)] at h
  have hsum : (∑ i, |1-minTilt s (r i)|) ≤ 3*s*inverseSum n r := by
    unfold inverseSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [abs_of_nonneg (sub_nonneg.mpr (minTilt_le_one hs (hr i))), ← div_eq_mul_inv]
    exact one_sub_minTilt_le hs (hr i)
  linarith

lemma laguerre_minTiltProduct_lower (n : ℕ) {a s : ℝ} (ha : 1 < a) (hs : 0 ≤ s) :
    1-3*s*((n:ℝ)*(2*a+n-1)/(2*a*(a-1))) ≤
      ∫ r, minTiltProduct n s r ∂laguerreLaw n a := by
  have ha0 : 0 < a := by linarith
  let := laguerreLaw_isProbabilityMeasure n ha0
  have hi := (integrable_laguerreLaw_inverseSum (n := n) ha).const_mul (3*s)
  have h := integral_mono_ae ((integrable_const 1).sub hi)
    (integrable_laguerreLaw_minTiltProduct n ha0 hs) (show
      (fun r => 1-3*s*inverseSum n r) ≤ᵐ[laguerreLaw n a] minTiltProduct n s from by
      filter_upwards [ae_laguerreDomain n a] with r hr
      exact minTiltProduct_lower hs hr.2)
  have he : (∫ r, inverseSum n r ∂laguerreLaw n a) = (n:ℝ)*(2*a+n-1)/(2*a*(a-1)) := by
    rw [integral_laguerreLaw n ha0]
    exact laguerreExpectation_inverseSum n ha
  change (∫ r, 1-3*s*inverseSum n r ∂laguerreLaw n a) ≤ _ at h
  rw [integral_sub (integrable_const 1) hi, integral_const_mul, he,
    integral_const, probReal_univ, one_smul] at h
  exact h

lemma laguerre_minTiltProduct_two_lower (n : ℕ) {s : ℝ} (hs : 0 ≤ s)
    (hs' : s ≤ 1/(12*((n:ℝ)+1)^2)) :
    laguerreNormalizer n 2 / 2 ≤
      ∫ r in laguerreDomain n, minTiltProduct n s r * laguerreDensity n 2 r := by
  have hn : 0 ≤ (n:ℝ) := by positivity
  have ht : 0 < ((n:ℝ)+1)^2 := by positivity
  have hs2 : s * ((n:ℝ)+1)^2 ≤ 1/12 := by
    have h := (le_div_iff₀ (by positivity : 0 < 12*((n:ℝ)+1)^2)).1 hs'
    nlinarith
  have he : (n:ℝ)*(2*2+n-1)/(2*2*(2-1)) ≤ ((n:ℝ)+1)^2 := by norm_num; nlinarith
  have h := laguerre_minTiltProduct_lower n (by norm_num : (1:ℝ)<2) hs
  have hh : (1/2:ℝ) ≤ ∫ r, minTiltProduct n s r ∂laguerreLaw n 2 := by
    have hm := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 3*s)
    nlinarith
  rw [integral_laguerreLaw _ (by norm_num), laguerreExpectation] at hh
  have H := (le_div_iff₀ (laguerreNormalizer_pos n (by norm_num))).1 hh
  linarith

lemma smallCoordinate_scale_lower (n : ℕ) {s : ℝ} (hs : 0 < s)
    (hs' : s ≤ 1/(12*((n:ℝ)+1)^2)) :
    ((n:ℝ)+1)^(1/2:ℝ) ≤ s^(-(1/4:ℝ)) := by
  have hn : 0 < (n:ℝ)+1 := by positivity
  have ht : 0 < ((n:ℝ)+1)^2 := by positivity
  have hle : s ≤ 1/((n:ℝ)+1)^2 := by
    exact hs'.trans (one_div_le_one_div_of_le ht (by nlinarith))
  have H := Real.rpow_le_rpow_of_nonpos hs hle (by norm_num : -(1/4:ℝ)≤0)
  rw [one_div, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le,
    neg_neg, ← Real.rpow_natCast_mul hn.le] at H
  norm_num only at H
  exact H

 

theorem laguerre_least_inverseQuarter_lower (n : ℕ) :
    (Real.exp (-1)/48) * ((n:ℝ)+1)^(1/2:ℝ) ≤
      laguerreExpectation (n+1) 1 (fun r => (r 0)^(-(1/4:ℝ))) := by
  let t : ℝ := 1/(12*((n:ℝ)+1)^2)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 12*((n:ℝ)+1)^2)).2
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  let F := fun s : ℝ => laguerreWeight 1 s *
    ∫ r in laguerreDomain n, s^(-(1/4:ℝ)) * minTiltProduct n s r * laguerreDensity n 2 r
  have hi := integrableOn_laguerre_inverse_coordinate (N := n+1) (by norm_num : (0:ℝ)<1)
    (0 : Fin (n+1)) (p := 1/4) (by norm_num)
  have hf : IntegrableOn F (Ioi 0) := by
    simpa only [Fin.cons_zero, one_add_one_eq_two] using integrable_laguerre_splitMin n 1
      (fun r => (r 0)^(-(1/4:ℝ))) hi
  have hnonneg (s : ℝ) (hs : 0 < s) : 0 ≤ F s := by
    apply mul_nonneg (laguerreWeight_pos 1 hs).le
    apply setIntegral_nonneg (isOpen_laguerreDomain n).measurableSet
    intro r hr
    exact mul_nonneg (mul_nonneg (Real.rpow_pos_of_pos hs _).le
      (minTiltProduct_nonneg hs.le hr.2)) (laguerreDensity_pos 2 hr).le
  have hbound (s : ℝ) (hs : s ∈ Ioo 0 t) :
      ((n:ℝ)+1)^(1/2:ℝ) * Real.exp (-1) * (laguerreNormalizer n 2 /2) ≤ F s := by
    have he : Real.exp (-1) ≤ laguerreWeight 1 s := by
      simp only [laguerreWeight, sub_self, Real.rpow_zero, one_mul]
      exact Real.exp_le_exp.2 (by have : s ≤ 1 := hs.2.le.trans ht1; linarith)
    have hp := smallCoordinate_scale_lower n hs.1 hs.2.le
    have hl := laguerre_minTiltProduct_two_lower n hs.1.le hs.2.le
    have hz : 0 < laguerreNormalizer n 2 := laguerreNormalizer_pos n (by norm_num)
    dsimp only [F]
    simp_rw [mul_assoc (s^(-(1/4:ℝ))) _ _]
    rw [integral_const_mul]
    calc
      _ ≤ Real.exp (-1) * (s^(-(1/4:ℝ))*(laguerreNormalizer n 2/2)) := by
        nlinarith [mul_le_mul_of_nonneg_right hp (mul_nonneg (Real.exp_nonneg (-1)) (by positivity : 0 ≤ laguerreNormalizer n 2/2))]
      _ ≤ laguerreWeight 1 s * (s^(-(1/4:ℝ)) *
          ∫ r in laguerreDomain n, minTiltProduct n s r * laguerreDensity n 2 r) := by
        exact mul_le_mul he (mul_le_mul_of_nonneg_left hl (Real.rpow_pos_of_pos hs.1 _).le)
          (mul_nonneg (Real.rpow_pos_of_pos hs.1 _).le (by positivity)) (laguerreWeight_pos 1 hs.1).le
  have hmass :
      t * (((n:ℝ)+1)^(1/2:ℝ) * Real.exp (-1) * (laguerreNormalizer n 2/2)) ≤ ∫ s in Ioi 0, F s := by
    calc
      _ = ∫ s in Ioo 0 t, ((n:ℝ)+1)^(1/2:ℝ) * Real.exp (-1) * (laguerreNormalizer n 2/2) := by
        rw [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
        simp
      _ ≤ ∫ s in Ioo 0 t, F s := by
        apply setIntegral_mono_on (integrableOn_const (by simp : volume (Ioo 0 t) ≠ ⊤))
          (hf.mono_set Ioo_subset_Ioi_self) measurableSet_Ioo hbound
      _ ≤ _ := setIntegral_mono_set hf (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact hnonneg s hs) (Filter.Eventually.of_forall Ioo_subset_Ioi_self)
  have hiEq : (∫ r in laguerreDomain (n+1), (r 0)^(-(1/4:ℝ))*laguerreDensity (n+1) 1 r) =
      ∫ s in Ioi 0, F s := by
    simpa only [Fin.cons_zero, one_add_one_eq_two] using integral_laguerre_splitMin n 1
      (fun r => (r 0)^(-(1/4:ℝ))) hi
  unfold laguerreExpectation
  rw [hiEq]
  apply (div_le_div_of_nonneg_right hmass (laguerreNormalizer_pos (n+1) (by norm_num)).le).trans'
  have hz : 0 < laguerreNormalizer (n+1) 1 := laguerreNormalizer_pos (n+1) (by norm_num)
  have he : t * (((n:ℝ)+1)^(1/2:ℝ) * Real.exp (-1) * (laguerreNormalizer n 2/2)) /
      laguerreNormalizer (n+1) 1 =
      (((n:ℝ)+1)^(1/2:ℝ) * Real.exp (-1)) * ((n:ℝ)+2)/(48*((n:ℝ)+1)) := by
    calc
      _ = (t * (((n:ℝ)+1)^(1/2:ℝ) * Real.exp (-1))/2) *
          (laguerreNormalizer n 2/laguerreNormalizer (n+1) 1) := by ring
      _ = _ := by
        rw [laguerreNormalizer_one_ratio]
        dsimp only [t]
        have hn : (n:ℝ)+1 ≠ 0 := by positivity
        field_simp
        ring
  rw [he]
  apply (le_div_iff₀ (by positivity : 0 < 48*((n:ℝ)+1))).2
  have hr : 0 ≤ ((n:ℝ)+1)^(1/2:ℝ) := Real.rpow_nonneg (by positivity) _
  nlinarith [mul_nonneg hr (Real.exp_nonneg (-1))]

end

 

noncomputable section
open scoped BigOperators
open Set MeasureTheory StripPfaffian

lemma orderedPairProduct_snoc {α M : Type*} [CommMonoid M] (k : α → α → M)
    {n : ℕ} (x : α) (r : Fin n → α) :
    (∏ i : Fin (n+1), ∏ j ∈ Finset.Ioi i, k ((Fin.snoc r x : Fin (n+1) → α) i) ((Fin.snoc r x : Fin (n+1) → α) j)) =
      (∏ i, ∏ j ∈ Finset.Ioi i, k (r i) (r j)) * ∏ i, k (r i) x := by
  classical
  have he {m : ℕ} (s : Fin m → α) :
      (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, k (s i) (s j)) =
        ∏ i : Fin m, ∏ j : Fin m, if i < j then k (s i) (s j) else 1 := by
    apply Finset.prod_congr rfl
    intro i _
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  rw [he, he]
  simp [Fin.prod_univ_castSucc, Finset.prod_mul_distrib, not_lt.mpr (Fin.le_last _)]

lemma gammaSchurProduct_snoc {n : ℕ} (r : ℝ) (q : Fin n → ℝ) :
    gammaSchurProduct (Fin.snoc q r) =
      gammaSchurProduct q * Real.Gamma r * (∏ i, (r-q i)/(q i+r)) := by
  unfold gammaSchurProduct
  rw [orderedPairProduct_snoc (fun r s : ℝ => (s-r)/(r+s))]
  simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  ring

lemma laguerreNormalizer_snoc_product (n : ℕ) {a : ℝ} (ha : 0 < a) :
    laguerreNormalizer (n+1) a = laguerreNormalizer n a * Real.Gamma (a+n) *
      (∏ i : Fin n, ((n:ℝ)-i.val)/(2*a+i.val+n)) := by
  rw [laguerreNormalizer_eq_product _ ha,
    ← gammaSchurProduct_laguerre, laguerreNormalizer_eq_product _ ha,
    ← gammaSchurProduct_laguerre]
  have hq : (fun i : Fin (n+1) => a+i.val) = Fin.snoc (fun i => a+i.val) (a+n) := by
    ext i
    refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
  rw [hq, gammaSchurProduct_snoc]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  congr 1 <;> ring

lemma prod_nat_sub (n : ℕ) : (∏ i : Fin n, ((n:ℝ)-i.val)) = n.factorial := by
  have he : (fun i : Fin n => (n:ℝ)-i.val) = (fun i => ((n-i.val:ℕ):ℝ)) := by
    ext i
    exact (Nat.cast_sub i.isLt.le).symm
  rw [he, ← Nat.cast_prod, Fin.prod_univ_eq_prod_range, ← Nat.descFactorial_eq_prod_range,
    Nat.descFactorial_self]

lemma prod_nat_add (n : ℕ) : (∏ i : Fin n, (1+(i.val:ℝ)+n)) = ((n+1).ascFactorial n:ℝ) := by
  have he : (fun i : Fin n => 1+(i.val:ℝ)+n) = (fun i => ((n+1+i.val:ℕ):ℝ)) := by
    ext i
    push_cast
    ring
  rw [he, ← Nat.cast_prod, Fin.prod_univ_eq_prod_range, ← Nat.ascFactorial_eq_prod_range]

lemma laguerreNormalizer_max_half_ratio (n : ℕ) :
    laguerreNormalizer n (1/2) / laguerreNormalizer (n+1) (1/2) * Real.Gamma (1/2+n) =
      ((n+n).choose n:ℝ) := by
  rw [laguerreNormalizer_snoc_product n (by norm_num : (0:ℝ)<1/2)]
  norm_num only
  rw [Finset.prod_div_distrib, prod_nat_sub, prod_nat_add, Nat.cast_add_choose ℝ]
  have he : (n.factorial:ℝ) * ((n+1).ascFactorial n:ℝ) = ((n+n).factorial:ℝ) := by
    exact_mod_cast Nat.factorial_mul_ascFactorial n n
  rw [← he]
  have hz : laguerreNormalizer n (1/2) ≠ 0 := (laguerreNormalizer_pos n (by norm_num)).ne'
  have hg : Real.Gamma (1/2+n) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity : (0:ℝ)<1/2+n)).ne'
  have hf : (n.factorial:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hF : ((n+1).ascFactorial n:ℝ) ≠ 0 := by
    have : 0 < (n+1).ascFactorial n := Nat.ascFactorial_pos n n
    exact_mod_cast this.ne'
  field_simp

lemma choose_double_le_four_pow (n : ℕ) : ((n+n).choose n:ℝ) ≤ (4:ℝ)^n := by
  have h := Nat.choose_le_two_pow (n+n) n
  have he : (2:ℕ)^(n+n) = 4^n := by rw [pow_add, ← mul_pow]; norm_num
  rw [he] at h
  exact_mod_cast h

lemma elementary_exp_half_bound (n : ℕ) :
    (4:ℝ)^n * (Real.exp (-(16*((n:ℝ)+1))/2) * 2^((1/2:ℝ)+n)) ≤ 1/4 := by
  have hh : (2:ℝ)^((1/2:ℝ)+n) ≤ (2:ℝ)^(n+1) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have he : Real.exp (-8) ≤ (1/8:ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ)<8)
      (by linarith [Real.add_one_le_exp (8:ℝ)] : 8 ≤ Real.exp 8)
  have hn : (Real.exp (-8))^(n+1) ≤ (1/8:ℝ)^(n+1) :=
    pow_le_pow_left₀ (Real.exp_nonneg _) he _
  have hexp : Real.exp (-(16*((n:ℝ)+1))/2) = (Real.exp (-8))^(n+1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc
    _ ≤ (4:ℝ)^n * ((1/8:ℝ)^(n+1) * (2:ℝ)^(n+1)) := by
      rw [hexp]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hn hh (by positivity) (by positivity)) (by positivity)
    _ = 1/4 := by
      rw [← mul_pow, pow_succ, ← mul_assoc, ← mul_pow]
      norm_num

 

theorem laguerreLaw_max_half_uniform (n : ℕ) :
    (laguerreLaw (n+1) (1/2)).real {r | 16*((n:ℝ)+1) < r (Fin.last n)} ≤ 1/4 := by
  have h := laguerreLaw_max_tail_exp_bound n (by norm_num : (0:ℝ)<1/2)
    (by positivity : 0 ≤ 16*((n:ℝ)+1))
  have he : (laguerreNormalizer n (1/2) / laguerreNormalizer (n+1) (1/2)) *
      (Real.exp (-(16*((n:ℝ)+1))/2) * (2^((1/2:ℝ)+n)*Real.Gamma (1/2+n))) =
      ((n+n).choose n:ℝ) * (Real.exp (-(16*((n:ℝ)+1))/2) * 2^((1/2:ℝ)+n)) := by
    rw [← laguerreNormalizer_max_half_ratio]
    ring
  rw [he] at h
  calc
    _ ≤ _ := h
    _ ≤ (4:ℝ)^n * (Real.exp (-(16*((n:ℝ)+1))/2) * 2^((1/2:ℝ)+n)) :=
      mul_le_mul_of_nonneg_right (choose_double_le_four_pow n) (by positivity)
    _ ≤ _ := elementary_exp_half_bound n

end

 

noncomputable section
open scoped BigOperators
open Set MeasureTheory

lemma laguerreLaw_cutoff_half_uniform (n : ℕ) :
    (1/2:ℝ) ≤ (laguerreLaw (n+1) (1/2)).real (cutoffEvent (n+1) (32*((n:ℝ)+1))) := by
  let μ := laguerreLaw (n+1) (1/2)
  have : IsProbabilityMeasure μ := laguerreLaw_isProbabilityMeasure _ (by norm_num)
  have hsubset : (cutoffEvent (n+1) (32*((n:ℝ)+1)))ᶜ ≤ᵐ[μ]
      {r | 16*((n:ℝ)+1) < r (Fin.last n)} := by
    filter_upwards [ae_laguerreDomain (n+1) (1/2)] with r hr
    intro h
    change r ∉ cutoffEvent (n+1) (32*((n:ℝ)+1)) at h
    have hh : ¬ r (Fin.last n) < 32*((n:ℝ)+1) := by
      simpa only [mem_compl_iff, mem_cutoffEvent_iff_last hr.1.monotone] using h
    have hn := Nat.cast_nonneg (α := ℝ) n
    change 16*((n:ℝ)+1) < r (Fin.last n)
    linarith [le_of_not_gt hh]
  have hreal : μ.real (cutoffEvent (n+1) (32*((n:ℝ)+1)))ᶜ ≤
      μ.real {r | 16*((n:ℝ)+1) < r (Fin.last n)} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsubset)
  rw [measureReal_compl (measurableSet_cutoffEvent _ _), probReal_univ] at hreal
  have H := laguerreLaw_max_half_uniform n
  change μ.real {r | 16*((n:ℝ)+1) < r (Fin.last n)} ≤ 1/4 at H
  change (1/2:ℝ) ≤ μ.real (cutoffEvent (n+1) (32*((n:ℝ)+1)))
  linarith

def referenceUpperConstant : ℝ := 2*(2/Real.Gamma (1/2))^(1/2:ℝ)+2

lemma referenceUpperConstant_pos : 0 < referenceUpperConstant := by
  have hg : 0 < Real.Gamma (1/2) := Real.Gamma_pos_of_pos (by norm_num)
  dsimp [referenceUpperConstant]
  positivity

 
end
end CriticalStrip

end OAI
