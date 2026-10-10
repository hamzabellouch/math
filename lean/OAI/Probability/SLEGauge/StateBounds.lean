import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.OptionalEstimates

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open scoped Topology
open Set
open MeasureTheory Filter
open scoped NNReal Topology
open MeasureTheory Filter Set Metric Function ODE
open MeasureTheory ProbabilityTheory Filter Set
open Filter
open Filter Set
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLECalculus ExactSLEFiniteTilt
noncomputable def regimeState {m : ℕ} (s : Finset (Fin m)) (a ε η : ℝ) (hη : 0<η) (N : ℝ≥0)
    (cap σ off : Fin m → ℝ) (z : Fin m → ℂ) (t : ℝ≥0) (b : Driver) : RegimeState m :=
  (vectorState a η hη z t b,
    ∫ u in (0:ℝ)..(t:ℝ), regimeDiscountCut s a ε η N cap σ off (vectorState a η hη z u.toNNReal b))
lemma regimeState_continuous {m : ℕ} (s : Finset (Fin m)) (a ε η : ℝ) (hη : 0<η) (N : ℝ≥0)
    (cap σ off : Fin m → ℝ) (z : Fin m → ℂ) (b : Driver) :
    Continuous (fun t => regimeState s a ε η hη N cap σ off z t b) := by
  have hc : Continuous (fun u : ℝ => regimeDiscountCut s a ε η N cap σ off
      (vectorState a η hη z u.toNNReal b)) :=
    (regimeDiscountCut_continuous s a ε η hη N cap σ off).comp
      ((vectorState_continuous a η hη z b).comp continuous_real_toNNReal)
  exact (vectorState_continuous a η hη z b).prodMk
    ((intervalIntegral.continuous_primitive hc.intervalIntegrable 0).comp continuous_subtype_val)
lemma regimeState_adapted {m : ℕ} (s : Finset (Fin m)) (a ε η : ℝ) (hη : 0<η) (N : ℝ≥0)
    (cap σ off : Fin m → ℝ) (z : Fin m → ℂ) (t : ℝ≥0) :
    Measurable[rawFiltration t] (regimeState s a ε η hη N cap σ off z t) := by
  apply (vectorState_adapted a η hη z t).prodMk
  apply adapted_intervalIntegral rawFiltration
    (fun u b => regimeDiscountCut s a ε η N cap σ off (vectorState a η hη z u b))
  · intro b
    exact (regimeDiscountCut_continuous s a ε η hη N cap σ off).comp
      (vectorState_continuous a η hη z b)
  · intro u
    exact (regimeDiscountCut_continuous s a ε η hη N cap σ off).measurable.comp
      (vectorState_adapted a η hη z u)
lemma regimeState_eq {m : ℕ} (s : Finset (Fin m)) (a ε η : ℝ) (hη : 0<η) (N : ℝ≥0)
    (cap σ off : Fin m → ℝ) (z : Fin m → ℂ) (u h : ℝ≥0) (b : Driver) :
    regimeState s a ε η hη N cap σ off z (u+h) b =
      regimeState s a ε η hη N cap σ off z u b+increment u h b • (multiNoise m,0)+
        ∫ t in (u:ℝ)..((u+h:ℝ≥0):ℝ), regimeDrift s a ε η N cap σ off
          (regimeState s a ε η hη N cap σ off z t.toNNReal b) := by
  let A := regimeDrift s a ε η N cap σ off
  let V := regimeState s a ε η hη N cap σ off z
  have hc : Continuous (fun t : ℝ => A (V t.toNNReal b)) :=
    (regimeDrift_continuous s a ε η hη N cap σ off).comp
      ((regimeState_continuous s a ε η hη N cap σ off z b).comp continuous_real_toNNReal)
  have hi := hc.intervalIntegrable (μ := volume) (u:ℝ) ((u+h:ℝ≥0):ℝ)
  apply Prod.ext
  · funext i
    let L : RegimeState m →L[ℝ] State := (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)
    have he := L.intervalIntegral_comp_comm hi
    change localState a η hη (z i) (u+h) b = localState a η hη (z i) u b+
      increment u h b • noise+L (∫ t in (u:ℝ)..((u+h:ℝ≥0):ℝ), A (V t.toNNReal b))
    rw [← he]
    exact localState_eq a η hη (z i) u h b
  · let L := ContinuousLinearMap.snd ℝ (Fin m → State) ℝ
    have he := L.intervalIntegral_comp_comm hi
    change (V (u+h) b).2 = (V u b).2+increment u h b • (0:ℝ)+L
      (∫ t in (u:ℝ)..((u+h:ℝ≥0):ℝ), A (V t.toNNReal b))
    rw [smul_zero,add_zero,← he]
    have hk : Continuous (fun t : ℝ => regimeDiscountCut s a ε η N cap σ off
        (vectorState a η hη z t.toNNReal b)) :=
      (regimeDiscountCut_continuous s a ε η hη N cap σ off).comp
        ((vectorState_continuous a η hη z b).comp continuous_real_toNNReal)
    exact (intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hk.intervalIntegrable 0 (u:ℝ))
      (hk.intervalIntegrable (u:ℝ) ((u+h:ℝ≥0):ℝ))).symm
end ExactSLEGreen
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEFiniteTilt ExactSLECalculus
lemma regimeDiscount_congr {m : ℕ} (s : Finset (Fin m)) (a ε : ℝ)
    (cap σ off : Fin m → ℝ) (v w : Fin m → State) (h : ∀ i∈s, v i=w i) :
    regimeDiscount s a ε cap σ off v=regimeDiscount s a ε cap σ off w := by
  unfold regimeDiscount
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [h i hi]
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [h i hi,h j (Finset.mem_of_mem_erase hj)]
 

theorem vector_regime_weighted_optional {m : ℕ} (s : Finset (Fin m)) {a ε η : ℝ}
    (ha : 1/4<a) (hε : 0<ε) (hη : 0<η) (hsize : ε*((s.card:ℝ)-1)≤regK a/2)
    (N : ℝ≥0) (cap σ off : Fin m → ℝ) (hσ : ∀ i∈s, |σ i|≤regBeta a)
    (z : Fin m → ℂ) (W : Measure Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W)
    (S T : Driver → ℝ≥0) (B : ℝ≥0)
    (hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0)))
    (hT : IsStoppingTime rawFiltration (fun b => (T b : WithTop ℝ≥0)))
    (hST : ∀ b, S b≤T b) (hTB : ∀ b, T b≤B)
    (E : Set Driver) (hE : MeasurableSet[hS.measurableSpace] E)
    (w : Driver → ℝ) (hw : StronglyMeasurable[hS.measurableSpace] w)
    (hw0 : ∀ b, 0≤w b) (C : ℝ) (hwb : ∀ b, ‖w b‖≤C)
    (hws : ∀ b∉E, w b=0)
    (hsafe : ∀ b∈E, ∀ t, S b≤t → t≤T b →
      ‖regimeState s a ε η hη N cap σ off z t b‖≤N ∧
      ∀ i∈s, η≤Y (vectorState a η hη z t b i) ∧
        physicalDelta a (cap i) (σ i) (off i) (vectorState a η hη z t b i)≤1) :
    ∫ b, w b*discountedProduct s a cap σ off
      (regimeState s a ε η hη N cap σ off z (T b) b) ∂W ≤
    ∫ b, w b*discountedProduct s a cap σ off
      (regimeState s a ε η hη N cap σ off z (S b) b) ∂W := by
  obtain ⟨K,hK,hKb⟩ := regimeDrift_bound s a ε η hη N cap σ off
  apply discounted_regime_weighted_optional s ha hε hsize cap σ off hσ W hW
    (regimeState s a ε η hη N cap σ off z)
    (regimeState_continuous s a ε η hη N cap σ off z)
    (regimeState_adapted s a ε η hη N cap σ off z)
    (regimeDrift s a ε η N cap σ off)
    (regimeDrift_continuous s a ε η hη N cap σ off) K hK hKb
    (regimeState_eq s a ε η hη N cap σ off z)
    S T B N η hη hS hT hST hTB E hE w hw hw0 C hwb hws hsafe
  intro b hb t hts htt
  have hn := (hsafe b hb t hts htt).1
  have hy := (hsafe b hb t hts htt).2
  constructor
  · change regimeDiscountCut s a ε η N cap σ off _ = _
    apply regimeDiscount_congr
    intro i hi
    apply regimeClamp_eq η N _ hη _ (hy i hi).1
    have hv : ‖vectorState a η hη z t b‖≤N :=
      (le_max_left _ _).trans hn
    exact (norm_le_pi_norm _ i).trans hv
  · intro i hi
    exact cutoffDrift_eq_physical a η _ (hy i hi).1
end ExactSLEGreen
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEFiniteTilt ExactSLECalculus
 

theorem vector_regime_weighted_optional_bounded {m : ℕ} (s : Finset (Fin m)) {a ε η : ℝ}
    (ha : 1/4<a) (hε : 0<ε) (hη : 0<η) (hsize : ε*((s.card:ℝ)-1)≤regK a/2)
    (M : ℝ≥0) (cap σ off : Fin m → ℝ) (hσ : ∀ i∈s, |σ i|≤regBeta a)
    (z : Fin m → ℂ) (W : Measure Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W)
    (S T : Driver → ℝ≥0) (B : ℝ≥0)
    (hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0)))
    (hT : IsStoppingTime rawFiltration (fun b => (T b : WithTop ℝ≥0)))
    (hST : ∀ b, S b≤T b) (hTB : ∀ b, T b≤B)
    (E : Set Driver) (hE : MeasurableSet[hS.measurableSpace] E)
    (w : Driver → ℝ) (hw : StronglyMeasurable[hS.measurableSpace] w)
    (hw0 : ∀ b, 0≤w b) (C : ℝ) (hwb : ∀ b, ‖w b‖≤C)
    (hws : ∀ b∉E, w b=0)
    (hsafe : ∀ b∈E, ∀ t, S b≤t → t≤T b →
      ‖vectorState a η hη z t b‖≤M ∧
      ∀ i∈s, η≤Y (vectorState a η hη z t b i) ∧
        physicalDelta a (cap i) (σ i) (off i) (vectorState a η hη z t b i)≤1) :
    ∫ b, w b*discountedProduct s a cap σ off
      (regimeState s a ε η hη M cap σ off z (T b) b) ∂W ≤
    ∫ b, w b*discountedProduct s a cap σ off
      (regimeState s a ε η hη M cap σ off z (S b) b) ∂W := by
  obtain ⟨K,hK,hKb⟩ := regimeDrift_bound s a ε η hη M cap σ off
  obtain ⟨L,hL,hLb⟩ := regimeDiscountCut_bound s a ε η hη M cap σ off
  let N : ℝ≥0 := ⟨max M (L*B),le_trans M.coe_nonneg (le_max_left _ _)⟩
  have hb (b : Driver) (t : ℝ≥0) (ht : t≤B) :
      ‖(regimeState s a ε η hη M cap σ off z t b).2‖≤L*B := by
    change ‖∫ u in (0:ℝ)..(t:ℝ), regimeDiscountCut s a ε η M cap σ off
      (vectorState a η hη z u.toNNReal b)‖≤_
    calc
      _ ≤ L*|(t:ℝ)-0| := intervalIntegral.norm_integral_le_of_norm_le_const fun u _ => hLb _
      _ ≤ L*B := by rw [sub_zero,abs_of_nonneg t.coe_nonneg]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast ht) hL
  apply discounted_regime_weighted_optional s ha hε hsize cap σ off hσ W hW
    (regimeState s a ε η hη M cap σ off z)
    (regimeState_continuous s a ε η hη M cap σ off z)
    (regimeState_adapted s a ε η hη M cap σ off z)
    (regimeDrift s a ε η M cap σ off)
    (regimeDrift_continuous s a ε η hη M cap σ off) K hK hKb
    (regimeState_eq s a ε η hη M cap σ off z)
    S T B N η hη hS hT hST hTB E hE w hw hw0 C hwb hws
  · intro b he t hst htt
    refine ⟨max_le ?_ ?_,(hsafe b he t hst htt).2⟩
    · exact (hsafe b he t hst htt).1.trans (le_max_left _ _)
    · exact (hb b t (htt.trans (hTB b))).trans (le_max_right _ _)
  · intro b he t hst htt
    have hs := hsafe b he t hst htt
    constructor
    · change regimeDiscountCut s a ε η M cap σ off _ = _
      apply regimeDiscount_congr
      intro i hi
      exact regimeClamp_eq η M _ hη ((norm_le_pi_norm _ i).trans hs.1) (hs.2 i hi).1
    · intro i hi
      exact cutoffDrift_eq_physical a η _ (hs.2 i hi).1
end ExactSLEGreen

namespace ExactSLEMain
open Set

lemma upper_pair_norm_sq (z w : ℂ) :
    ‖z-star w‖^2 = ‖z-w‖^2 + 4*z.im*w.im := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

lemma upper_pair_norm_lt {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    ‖z-w‖ < ‖z-star w‖ := by
  have h := upper_pair_norm_sq z w
  have hp : 0 < 4*z.im*w.im := by positivity
  nlinarith [norm_nonneg (z-w),norm_nonneg (z-star w)]

lemma upper_harnack {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    z.im * (‖z-star w‖ - ‖z-w‖) ≤ w.im * (‖z-star w‖ + ‖z-w‖) := by
  have hn : ‖z-w‖^2 = (z.re-w.re)^2+(z.im-w.im)^2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, pow_two]
  have hd := upper_pair_norm_sq z w
  have he : ((z.im+w.im)*‖z-w‖)^2 - ((z.im-w.im)*‖z-star w‖)^2 =
      4*z.im*w.im*(z.re-w.re)^2 := by
    rw [mul_pow, mul_pow, hd, hn]
    ring
  have hs : ((z.im-w.im)*‖z-star w‖)^2 ≤ ((z.im+w.im)*‖z-w‖)^2 := by
    have hp : 0 ≤ 4*z.im*w.im*(z.re-w.re)^2 := by positivity
    linarith
  have hh : (z.im-w.im)*‖z-star w‖ ≤ (z.im+w.im)*‖z-w‖ :=
    le_of_sq_le_sq hs (by positivity)
  nlinarith

lemma upper_velocity_harnack {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    (z.im/Complex.normSq z) * (‖z-star w‖ - ‖z-w‖) ≤
    (w.im/Complex.normSq w) * (‖z-star w‖ + ‖z-w‖) := by
  have hzn : z ≠ 0 := by intro h; simp [h] at hz
  have hwn : w ≠ 0 := by intro h; simp [h] at hw
  have hzN := Complex.normSq_pos.mpr hzn
  have hwN := Complex.normSq_pos.mpr hwn
  have hi : (-z⁻¹).im = z.im/Complex.normSq z := by simp only [Complex.neg_im, Complex.inv_im]; ring
  have hj : (-w⁻¹).im = w.im/Complex.normSq w := by simp only [Complex.neg_im, Complex.inv_im]; ring
  have hn : ‖-z⁻¹ - -w⁻¹‖ = ‖z-w‖ / (‖z‖*‖w‖) := by
    have he : -z⁻¹ - -w⁻¹ = (z-w)/(z*w) := by field_simp; ring
    rw [he,norm_div,norm_mul]
  have hd : ‖-z⁻¹ - star (-w⁻¹)‖ = ‖z-star w‖ / (‖z‖*‖w‖) := by
    have hwc : star w ≠ 0 := star_ne_zero.mpr hwn
    have he : -z⁻¹ - star (-w⁻¹) = (z-star w)/(z*star w) := by
      simp only [star_neg,star_inv₀]
      field_simp
      ring
    rw [he,norm_div,norm_mul,norm_star]
  have h := upper_harnack (z := -z⁻¹) (w := -w⁻¹)
    (by rw [hi]; positivity) (by rw [hj]; positivity)
  rw [hi,hj,hn,hd,← sub_div,← add_div,← mul_div_assoc,← mul_div_assoc] at h
  exact (div_le_div_iff_of_pos_right (mul_pos (norm_pos_iff.mpr hzn) (norm_pos_iff.mpr hwn))).mp h

lemma upper_initial_growth {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    ‖z-w‖ ≤ 2*z.im * (‖z-w‖/‖z-star w‖) / (1-‖z-w‖/‖z-star w‖)^2 := by
  have hnd := upper_pair_norm_lt hz hw
  have hd : 0 < ‖z-star w‖ := (norm_nonneg _).trans_lt hnd
  have hdiff : 0 < ‖z-star w‖ - ‖z-w‖ := sub_pos.mpr hnd
  have htri : ‖z-star w‖ ≤ ‖z-w‖+2*z.im := by
    have hh := norm_add_le (star z-w) (z-star z)
    have he : star z-w+(z-star z) = z-w := by ring
    have hh := norm_add_le (z-w) (w-star w)
    have hh' := norm_add_le (star (z-w)) (z-star z)
    have hnorm : ‖z-star z‖ = 2*z.im := by
      have he : z-star z = (2*z.im : ℝ)*Complex.I := by
        apply Complex.ext <;> simp
        ring
      rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,abs_of_pos (by positivity)]
    have he : star (z-w)+(z-star z) = z-star w := by simp only [star_sub]; ring
    rw [he,norm_star,hnorm] at hh'
    linarith
  have hs : (‖z-star w‖-‖z-w‖)^2 ≤ 2*z.im*‖z-star w‖ := by
    calc
      (‖z-star w‖-‖z-w‖)^2 ≤ (2*z.im)*(‖z-star w‖-‖z-w‖) := by
        nlinarith [mul_nonneg (show 0 ≤ 2*z.im-(‖z-star w‖-‖z-w‖) by linarith) hdiff.le]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sub_le_self _ (norm_nonneg _)) (by positivity)
  have he : 2*z.im * (‖z-w‖/‖z-star w‖) / (1-‖z-w‖/‖z-star w‖)^2 =
      ‖z-w‖ * (2*z.im*‖z-star w‖)/(‖z-star w‖-‖z-w‖)^2 := by
    field_simp
  rw [he]
  exact (le_div_iff₀ (sq_pos_of_pos hdiff)).mpr (mul_le_mul_of_nonneg_left hs (norm_nonneg _))

end ExactSLEMain

namespace ExactSLEMain
open Set

lemma complex_linear_norm_deriv {f : ℝ → ℂ} {c : ℂ} {D : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f (c*f t) D t) (hn : f t ≠ 0) :
    HasDerivWithinAt (fun t => ‖f t‖) (c.re*‖f t‖) D t := by
  have hN := norm_pos_iff.mpr hn
  have h := hf.norm_sq.sqrt (pow_ne_zero 2 hN.ne')
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  convert h using 1
  try rfl
  rw [Complex.inner, mul_assoc, Complex.mul_conj, Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,Complex.normSq_eq_norm_sq]
  field_simp

lemma loewner_pair_drift (A : ℝ) {z w : ℂ} (_hz : z ≠ 0) (_hw : w ≠ 0) :
    (-(A : ℂ)/(z*w)).re - (-(A : ℂ)/(z*star w)).re =
      2*A*(z.im/Complex.normSq z)*(w.im/Complex.normSq w) := by
  simp only [div_eq_mul_inv, mul_inv_rev, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.inv_re, Complex.inv_im, Complex.star_def, Complex.conj_re,Complex.conj_im,
    Complex.normSq_conj]
  ring

end ExactSLEMain

namespace ExactSLEMain
open Set

lemma growth_factor_deriv {D : Set ℝ} {t A v w : ℝ} {R r : ℝ → ℝ}
    (hR : HasDerivWithinAt R (-2*A*v^2*R t) D t)
    (hr : HasDerivWithinAt r (2*A*v*w*r t) D t) (hn : r t ≠ 1) :
    HasDerivWithinAt (fun t => R t*r t/(1-r t)^2)
      (2*A*R t*r t*v/(1-r t)^3 * (w*(1+r t)-v*(1-r t))) D t := by
  have h := (hR.mul hr).div ((hr.const_sub 1).pow 2) (pow_ne_zero 2 (sub_ne_zero.mpr hn.symm))
  convert h using 1
  try rfl
  simp only [Pi.pow_apply,Pi.mul_apply]
  field_simp
  ring

lemma odeUntil_pair_ne {A : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {z w : ℂ} {T : ℝ≥0} {f g : ℝ → ℂ}
    (hf : odeUntil A b z T f) (hg : odeUntil A b w T g) (hzw : z ≠ w)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) : f u-g u ≠ 0 := by
  have hsub : Icc (0 : ℝ) u.toNNReal ⊆ Icc (0 : ℝ) T := by
    rw [Real.coe_toNNReal _ hu.1]
    exact Icc_subset_Icc_right hu.2
  have hf' : odeUntil A b z u.toNNReal f := ⟨hf.1,fun s hs =>
    ⟨(hf.2 s (hsub hs)).1,((hf.2 s (hsub hs)).2).mono hsub⟩⟩
  have hg' : odeUntil A b w u.toNNReal g := ⟨hg.1,fun s hs =>
    ⟨(hg.2 s (hsub hs)).1,((hg.2 s (hsub hs)).2).mono hsub⟩⟩
  have he := loewner_solution_difference hb hf' hg'
  rw [Real.coe_toNNReal _ hu.1] at he
  rw [he]
  exact mul_ne_zero (sub_ne_zero.mpr hzw) (Complex.exp_ne_zero _)

lemma odeUntil_pair_ratio_deriv {A : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {z w : ℂ} {T : ℝ≥0} {f g : ℝ → ℂ}
    (hf : odeUntil A b z T f) (hg : odeUntil A b w T g) (hzw : z ≠ w)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun u => ‖f u-g u‖/‖f u-star (g u)‖)
      (2*A*((f u).im/Complex.normSq (f u-(b u.toNNReal : ℂ)))*
        ((g u).im/Complex.normSq (g u-(b u.toNNReal : ℂ)))*
        (‖f u-g u‖/‖f u-star (g u)‖)) (Icc (0 : ℝ) T) u := by
  let Z := f u-(b u.toNNReal : ℂ)
  let W := g u-(b u.toNNReal : ℂ)
  have hZ : Z ≠ 0 := odeUntil_center_ne_zero hf hu
  have hW : W ≠ 0 := odeUntil_center_ne_zero hg hu
  have hD : f u-star (g u) ≠ 0 := norm_pos_iff.mp
    ((norm_nonneg _).trans_lt (upper_pair_norm_lt (hf.2 u hu).1 (hg.2 u hu).1))
  have hd : HasDerivWithinAt (fun u => f u-g u)
      ((-(A : ℂ)/(Z*W))*(f u-g u)) (Icc (0 : ℝ) T) u := by
    convert (hf.2 u hu).2.sub (hg.2 u hu).2 using 1
    try rfl
    dsimp [Z,W]
    field_simp [odeUntil_center_ne_zero hf hu,odeUntil_center_ne_zero hg hu]
    ring
  have hc := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt u (hg.2 u hu).2
  change HasDerivWithinAt (fun s => star (g s)) (star ((A : ℂ)/W)) _ _ at hc
  have he : HasDerivWithinAt (fun u => f u-star (g u))
      ((-(A : ℂ)/(Z*star W))*(f u-star (g u))) (Icc (0 : ℝ) T) u := by
    convert (hf.2 u hu).2.sub hc using 1
    try rfl
    simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]
    change -(A : ℂ)/(Z*star W)*(f u-star (g u)) = (A : ℂ)/Z-(A : ℂ)/star W
    have he : f u-star (g u) = Z-star W := by simp [Z,W]
    rw [he]
    rw [div_sub_div _ _ hZ (star_ne_zero.mpr hW)]
    ring
  have hn := complex_linear_norm_deriv hd (odeUntil_pair_ne hb hf hg hzw hu)
  have hm := complex_linear_norm_deriv he hD
  have hh := hn.div hm (norm_ne_zero_iff.mpr hD)
  convert hh using 1
  try rfl
  have hi := loewner_pair_drift A hZ hW
  have hiz : Z.im = (f u).im := by simp [Z]
  have hiw : W.im = (g u).im := by simp [W]
  rw [hiz,hiw] at hi
  change (2*A*((f u).im/Complex.normSq Z)*((g u).im/Complex.normSq W))*
    (‖f u-g u‖/‖f u-star (g u)‖) = _
  rw [← hi]
  field_simp [norm_ne_zero_iff.mpr hD]

end ExactSLEMain

namespace ExactSLEMain
open Set

end ExactSLEMain
end

end OAI
