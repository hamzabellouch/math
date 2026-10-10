import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.ReverseFlow

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped NNReal ENNReal Topology
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
open scoped ContDiff Manifold
noncomputable section
open Filter Topology
noncomputable section
open Complex Real Set Filter
open scoped Topology
noncomputable section
open scoped Topology
open MeasureTheory
noncomputable section
open Set Filter Real
open scoped Topology
open Set MeasureTheory ProbabilityTheory Topology Function Filter
open scoped NNReal ENNReal ContinuousMapZero
noncomputable section
namespace SLEExactGauge.LiteralTrace
open ReverseDerivative MeasureTheory
lemma radial_length_moment {κ y T δ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (hy : 0 < y) (hδ : 0 < δ) (hT : δ ≤ T)
    {W : WienerLaw} (hW : IsWiener W) :
    (∫⁻ b : Driver, (radialLength κ b T y)^(lambda (a κ)) ∂W) ≤
      ENNReal.ofReal ((3/δ)^(zeta (a κ)/2)*y^(lambda (a κ)+zeta (a κ))) := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  have hT0 : 0 ≤ T := hδ.le.trans hT
  have ha : 1/4 < a κ := by unfold a; apply (lt_div_iff₀ hκ).mpr; linarith
  have hz := (parameters ha).1
  have hl := lambda_gt_one (show 0 < a κ by linarith)
  have hp0 : 0 < lambda (a κ) := by linarith
  let F : Driver → ℝ → ℝ≥0∞ := fun b u => ENNReal.ofReal ‖radialCoeff κ b T u‖
  have hm : Measurable (Function.uncurry F) :=
    (measurable_radial_norm hκ hT0).ennreal_ofReal.comp measurable_swap
  have hmass : (volume.restrict (Ioc (0:ℝ) y)) univ = ENNReal.ofReal y := by simp
  calc
    _ ≤ ∫⁻ b : Driver, (ENNReal.ofReal y)^(lambda (a κ)-1)*
        (∫⁻ u in Ioc (0:ℝ) y, (F b u)^(lambda (a κ))) ∂W := by
      apply lintegral_mono
      intro b
      simpa [radialLength,F,hmass,Function.uncurry] using lintegral_pow_le_mass
        (volume.restrict (Ioc (0:ℝ) y)) ((hm.comp (measurable_const.prodMk measurable_id)).aemeasurable) hl
    _ = (ENNReal.ofReal y)^(lambda (a κ)-1)*
        (∫⁻ u in Ioc (0:ℝ) y, ∫⁻ b : Driver, (F b u)^(lambda (a κ)) ∂W) := by
      rw [lintegral_const_mul' _ _ (by finiteness),
        lintegral_lintegral_swap (hm.pow_const _).aemeasurable]
    _ ≤ (ENNReal.ofReal y)^(lambda (a κ)-1)*
        (∫⁻ _u in Ioc (0:ℝ) y, ENNReal.ofReal ((3/δ)^(zeta (a κ)/2)*y^(zeta (a κ)))) := by
      apply mul_le_mul' le_rfl
      apply setLIntegral_mono' measurableSet_Ioc
      intro u hu
      have he : (∫⁻ b : Driver, (F b u)^(lambda (a κ)) ∂W) =
          ∫⁻ b : Driver, ENNReal.ofReal
            (‖deriv (inverseFlow κ b T) (driverValue b T+u*Complex.I)‖^(lambda (a κ))) ∂W := by
        congr 1
        funext b
        simp only [F,radialCoeff,ite_eq_left hu.1,norm_mul,Complex.norm_I,mul_one]
        exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le
      rw [he]
      apply (inverse_deriv_moment_away hκ hκ8 hu.1 hδ hT hW).trans
      apply ENNReal.ofReal_le_ofReal
      gcongr <;> linarith [hu.1,hu.2]
    _ = _ := by
      rw [lintegral_const,hmass,ENNReal.ofReal_rpow_of_nonneg hy.le (by linarith : 0 ≤ lambda (a κ)-1),
        ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
      congr 1
      calc
        y^(lambda (a κ)-1)*((3/δ)^(zeta (a κ)/2)*y^(zeta (a κ))*y) =
          (3/δ)^(zeta (a κ)/2)*(y^(lambda (a κ)-1)*y^(zeta (a κ))*y^((1:ℝ))) := by rw [Real.rpow_one]; ring
        _ = (3/δ)^(zeta (a κ)/2)*y^(lambda (a κ)+zeta (a κ)) := by
          rw [← Real.rpow_add hy,← Real.rpow_add hy]
          congr 2
          ring
end SLEExactGauge.LiteralTrace
namespace SLEExactGauge.LiteralTrace
open ReverseDerivative MeasureTheory

lemma measurable_radialLength {κ T : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T) (y : ℝ) :
    Measurable (fun b : Driver => radialLength κ b T y) :=
  ((measurable_radial_norm hκ hT).ennreal_ofReal.comp measurable_swap).lintegral_prod_right'

lemma radial_length_beta_tail {κ y T δ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (hy : 0 < y) (hδ : 0 < δ) (hT : δ ≤ T) {W : WienerLaw} (hW : IsWiener W) :
    W {b : Driver | ENNReal.ofReal (y^(traceBeta κ)) ≤ radialLength κ b T y} ≤
      ENNReal.ofReal ((3/δ)^(zeta (a κ)/2)*y^(2+traceEta κ)) := by
  have ha : 1/4 < a κ := by unfold a; apply (lt_div_iff₀ hκ).mpr; linarith
  have hp := trace_exponents hκ hκ8
  have hl := (parameters ha).2.1
  have hK : 0 < y^(traceBeta κ) := Real.rpow_pos_of_pos hy _
  have hKP : 0 < (y^(traceBeta κ))^(lambda (a κ)) := Real.rpow_pos_of_pos hK _
  have hm := (measurable_radialLength hκ (hδ.le.trans hT) y).pow_const (lambda (a κ))
  calc
    _ ≤ W {b : Driver | ENNReal.ofReal ((y^(traceBeta κ))^(lambda (a κ))) ≤
        (radialLength κ b T y)^(lambda (a κ))} := by
      apply measure_mono
      intro b hb
      rw [← ENNReal.ofReal_rpow_of_nonneg hK.le hl.le]
      exact ENNReal.rpow_le_rpow hb hl.le
    _ ≤ (∫⁻ b : Driver, (radialLength κ b T y)^(lambda (a κ)) ∂W)/
        ENNReal.ofReal ((y^(traceBeta κ))^(lambda (a κ))) :=
      meas_ge_le_lintegral_div hm.aemeasurable (ne_of_gt (ENNReal.ofReal_pos.mpr hKP)) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((3/δ)^(zeta (a κ)/2)*y^(lambda (a κ)+zeta (a κ)))/
        ENNReal.ofReal ((y^(traceBeta κ))^(lambda (a κ))) :=
      ENNReal.div_le_div_right (radial_length_moment hκ hκ8 hy hδ hT hW) _
    _ = _ := by
      rw [← ENNReal.ofReal_div_of_pos hKP,← Real.rpow_mul hy.le,mul_div_assoc,← Real.rpow_sub hy]
      congr 3
      linarith [hp.2.2.2]
end SLEExactGauge.LiteralTrace
namespace SLEExactGauge.LiteralTrace
open ReverseDerivative MeasureTheory
lemma refined_ratio (N : ℕ) (η : ℝ) :
    (2:ℝ)^(2*N+1)*(((1/2:ℝ)^N)^(2+η)) = (1/2:ℝ)^((N:ℝ)*η-1) := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 1/2)]
  have he : (2:ℝ)^(2*N+1) = (1/2:ℝ)^(-((2*N+1:ℕ):ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 1/2),Real.rpow_natCast,← inv_pow]
    norm_num
  rw [he,← Real.rpow_add (by norm_num : (0:ℝ) < 1/2)]
  congr 1
  push_cast
  ring
lemma refined_sum_term (M N n : ℕ) (C η : ℝ) :
    (((M*(2^(2*N+1))^n:ℕ):ℝ))*(C*(((1/2:ℝ)^N)^n)^(2+η)) =
      ((M:ℝ)*C)*(((1/2:ℝ)^((N:ℝ)*η-1))^n) := by
  rw [← refined_ratio N η,mul_pow]
  push_cast
  rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ (1/2:ℝ)^N),
    mul_comm (n:ℝ) (2+η),Real.rpow_mul_natCast (by positivity : 0 ≤ (1/2:ℝ)^N)]
  ring

def refinedHeight (N n : ℕ) : ℝ := ((1/2:ℝ)^N)^n

def refinedGridTime (δ : ℝ) (N n k : ℕ) : ℝ := δ+(k:ℝ)/((2:ℝ)^(2*N+1))^n

lemma refinedGridTime_ge (δ : ℝ) (N n k : ℕ) : δ ≤ refinedGridTime δ N n k := by
  unfold refinedGridTime
  exact le_add_of_nonneg_right (by positivity)

def radialGridBad (κ δ : ℝ) (M N n : ℕ) : Set Driver :=
  ⋃ k : Fin (M*(2^(2*N+1))^n), {b : Driver |
    ENNReal.ofReal ((refinedHeight N n)^(traceBeta κ)) ≤
      radialLength κ b (refinedGridTime δ N n k) (refinedHeight N n)}

lemma radialGridBad_measure {κ δ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (hδ : 0 < δ) {W : WienerLaw} (hW : IsWiener W) (M N n : ℕ) :
    W (radialGridBad κ δ M N n) ≤
      ENNReal.ofReal (((M:ℝ)*(3/δ)^(zeta (a κ)/2))*
        (((1/2:ℝ)^((N:ℝ)*traceEta κ-1))^n)) := by
  have hy : 0 < refinedHeight N n := by unfold refinedHeight; positivity
  calc
    _ ≤ ∑ k : Fin (M*(2^(2*N+1))^n), W {b : Driver |
        ENNReal.ofReal ((refinedHeight N n)^(traceBeta κ)) ≤
          radialLength κ b (refinedGridTime δ N n k) (refinedHeight N n)} :=
      measure_iUnion_fintype_le W _
    _ ≤ ∑ _k : Fin (M*(2^(2*N+1))^n), ENNReal.ofReal
        ((3/δ)^(zeta (a κ)/2)*(refinedHeight N n)^(2+traceEta κ)) := by
      apply Finset.sum_le_sum
      intro k _
      exact radial_length_beta_tail hκ hκ8 hy hδ (refinedGridTime_ge δ N n k) hW
    _ = ENNReal.ofReal (((M*(2^(2*N+1))^n:ℕ):ℝ)*
        ((3/δ)^(zeta (a κ)/2)*(refinedHeight N n)^(2+traceEta κ))) := by
      rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        ← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ = _ := by rw [refinedHeight,refined_sum_term]

lemma radialGridBad_summable {κ δ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (hδ : 0 < δ) {W : WienerLaw} (hW : IsWiener W) (M N : ℕ)
    (hN : 1 < (N:ℝ)*traceEta κ) :
    (∑' n : ℕ, W (radialGridBad κ δ M N n)) ≠ (∞:ℝ≥0∞) := by
  have hr : |(1/2:ℝ)^((N:ℝ)*traceEta κ-1)| < 1 := by
    rw [abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  apply ne_top_of_le_ne_top
    (((summable_geometric_of_abs_lt_one hr).mul_left
      ((M:ℝ)*(3/δ)^(zeta (a κ)/2))).tsum_ofReal_ne_top)
  exact ENNReal.tsum_le_tsum (radialGridBad_measure hκ hκ8 hδ hW M N)

 

theorem radial_length_refined_eventually {κ δ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (hδ : 0 < δ) {W : WienerLaw} (hW : IsWiener W) (M N : ℕ)
    (hN : 1 < (N:ℝ)*traceEta κ) :
    ∀ᵐ b ∂W, ∀ᶠ n : ℕ in atTop, ∀ k : Fin (M*(2^(2*N+1))^n),
      radialLength κ b (refinedGridTime δ N n k) (refinedHeight N n) <
        ENNReal.ofReal ((refinedHeight N n)^(traceBeta κ)) := by
  filter_upwards [ae_eventually_notMem (radialGridBad_summable hκ hκ8 hδ hW M N hN)] with b hb
  filter_upwards [hb] with n hn
  intro k
  apply lt_of_not_ge
  intro h
  exact hn (mem_iUnion.mpr ⟨k,h⟩)

 

theorem radial_length_all_refined_grids {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    {W : WienerLaw} (hW : IsWiener W) :
    ∃ N : ℕ, 0 < N ∧ 1 < (N:ℝ)*traceEta κ ∧
      ∀ᵐ b ∂W, ∀ m M : ℕ, ∀ᶠ n : ℕ in atTop, ∀ k : Fin (M*(2^(2*N+1))^n),
        radialLength κ b (refinedGridTime (1/((m:ℝ)+1)) N n k) (refinedHeight N n) <
          ENNReal.ofReal ((refinedHeight N n)^(traceBeta κ)) := by
  have hp := trace_exponents hκ hκ8
  obtain ⟨N,hN⟩ := exists_nat_gt (1/traceEta κ)
  have hN' : 1 < (N:ℝ)*traceEta κ := (div_lt_iff₀ hp.2.2.1).mp hN
  have hN0 : 0 < N := by
    by_contra hh
    have : N = 0 := Nat.eq_zero_of_not_pos hh
    subst N
    norm_num at hN'
  refine ⟨N,hN0,hN',?_⟩
  apply ae_all_iff.mpr
  intro m
  apply ae_all_iff.mpr
  intro M
  exact radial_length_refined_eventually hκ hκ8 (by positivity) hW M N hN'
end SLEExactGauge.LiteralTrace
namespace SLEExactGauge.LiteralTrace
open MeasureTheory

 

lemma radial_increment_le {κ T y z : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T)
    (hz : 0 < z) (hzy : z ≤ y) (b : Driver) :
    ENNReal.ofReal ‖inverseFlow κ b T (driverValue b T+y*Complex.I)-
      inverseFlow κ b T (driverValue b T+z*Complex.I)‖ ≤ radialLength κ b T y := by
  have hsub : Icc z y ⊆ Ioi (0:ℝ) := fun u hu => hz.trans_le hu.1
  have hc := (continuousOn_radialCoeff hκ hT b).mono hsub
  have hi : IntervalIntegrable (radialCoeff κ b T) volume z y :=
    hc.intervalIntegrable_of_Icc hzy
  have hd (u : ℝ) (hu : u ∈ uIcc z y) :
      HasDerivAt (fun v : ℝ => inverseFlow κ b T (driverValue b T+v*Complex.I))
        (radialCoeff κ b T u) u := by
    rw [uIcc_of_le hzy] at hu
    exact hasDerivAt_radial hκ hT (hsub hu) b
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi,
    intervalIntegral.integral_of_le hzy,ofReal_norm]
  apply (enorm_integral_le_lintegral_enorm _).trans
  change (∫⁻ u in Ioc z y, ‖radialCoeff κ b T u‖ₑ) ≤ radialLength κ b T y
  simp only [radialLength,ofReal_norm]
  exact lintegral_mono_set (Ioc_subset_Ioc hz.le le_rfl)
end SLEExactGauge.LiteralTrace
namespace SLEExactGauge.LiteralTrace
open Set Filter Metric
open scoped Topology

lemma halfPlane_sub_conj_ne_zero {w v : ℂ} (hw : 0 < w.im) (hv : 0 < v.im) :
    w-star v ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.sub_im,Complex.star_def,Complex.conj_im,Complex.zero_im] at hi
  linarith

lemma halfPlane_disk_norm_lt_one {w v : ℂ} (hw : 0 < w.im) (hv : 0 < v.im) :
    ‖(w-v)/(w-star v)‖ < 1 := by
  have hs : ‖w-v‖^2 < ‖w-star v‖^2 := by
    rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
      Complex.star_def,Complex.conj_re,Complex.conj_im]
    nlinarith [mul_pos hw hv]
  rw [norm_div,div_lt_one (norm_pos_iff.mpr (halfPlane_sub_conj_ne_zero hw hv))]
  nlinarith [norm_nonneg (w-v),norm_nonneg (w-star v)]

lemma halfPlane_self_sub_conj_norm {w : ℂ} (hw : 0 < w.im) :
    ‖w-star w‖ = 2*w.im := by
  have he : w-star w = (2*w.im:ℂ)*Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]; ring
  rw [he,norm_mul,Complex.norm_I,mul_one]
  norm_cast
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]

 

lemma ball_radius_le_conformal_radius {f : ℂ → ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball z r))
    (hH : ∀ w ∈ ball z r, 0 < (f w).im) (hd : deriv f z ≠ 0) :
    r ≤ 2*(f z).im / ‖deriv f z‖ := by
  have hz : z ∈ ball z r := by simpa using hr
  have hy := hH z hz
  let F (w : ℂ) : ℂ := (f w-f z)/(f w-star (f z))
  have hn (w : ℂ) (hw : w ∈ ball z r) : f w-star (f z) ≠ 0 :=
    halfPlane_sub_conj_ne_zero (hH w hw) hy
  have hF : DifferentiableOn ℂ F (ball z r) :=
    (hf.sub_const (f z)).div (hf.sub_const (star (f z))) hn
  have hFz : F z = 0 := by simp [F]
  have hm : MapsTo F (ball z r) (closedBall (F z) 1) := by
    intro w hw
    rw [hFz,mem_closedBall,dist_zero_right]
    exact (halfPlane_disk_norm_lt_one (hH w hw) hy).le
  have hh := Complex.norm_deriv_le_div_of_mapsTo_ball hF hm hr
  have hfd := (hf.differentiableAt (ball_mem_nhds z hr)).hasDerivAt
  have hFd : HasDerivAt F (deriv f z/(f z-star (f z))) z := by
    have h := (hfd.sub_const (f z)).div (hfd.sub_const (star (f z))) (hn z hz)
    convert! h using 1; first | rfl | (simp only [sub_self,zero_mul,sub_zero]; field_simp)
  rw [hFd.deriv,norm_div,halfPlane_self_sub_conj_norm hy] at hh
  have hi := (div_le_div_iff₀ (show 0 < 2*(f z).im by positivity) hr).mp hh
  apply (le_div_iff₀ (norm_pos_iff.mpr hd)).mpr
  nlinarith
end SLEExactGauge.LiteralTrace
namespace SLEExactGauge.LiteralTrace

lemma PositiveSolution.im_hasDeriv {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} {f : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun u => (f u).im)
      (-a κ*(f t).im/‖f t-driverValue b t‖^2) (Icc 0 T) t := by
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t (hf.2.2.2.2 t ht)
  convert! hi using 1; first | rfl |
    (simp only [Complex.imCLM_apply,Complex.div_im,Complex.ofReal_im,Complex.ofReal_re,
     Complex.sub_im,sub_zero,Complex.normSq_eq_norm_sq,zero_mul,zero_div,zero_sub]; ring)

lemma PositiveSolution.im_antitone {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} {f : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) (hκ : 0 < κ) :
    AntitoneOn (fun u => (f u).im) (Icc 0 T) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    (Complex.continuous_im.comp_continuousOn hf.2.1)
    (fun t ht => (hf.im_hasDeriv (interior_subset ht)).mono interior_subset)
  intro t ht
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  have ha : 0 < a κ := div_pos (by norm_num) hκ
  have hy := hf.2.2.2.1 t (interior_subset ht)
  nlinarith

lemma PositiveSolution.im_sq_bound {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} {f : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) (hκ : 0 < κ) {s t : ℝ}
    (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
    (f s).im^2 ≤ (f t).im^2+2*a κ*(t-s) := by
  have ha : 0 < a κ := div_pos (by norm_num) hκ
  have hm : MonotoneOn (fun u => (f u).im^2+2*a κ*u) (Icc 0 T) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      ((Complex.continuous_im.comp_continuousOn hf.2.1).pow 2 |>.add
        ((continuous_const.mul continuous_id).continuousOn))
      (fun u hu => (((hf.im_hasDeriv (interior_subset hu)).pow 2).add
        ((hasDerivAt_id u).const_mul (2*a κ)).hasDerivWithinAt).mono interior_subset)
    intro u hu
    have ht := interior_subset hu
    have hn := Complex.im_le_norm (f u-driverValue b u)
    simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at hn
    have hp := hf.2.2.2.1 u ht
    have hs : (f u).im^2 ≤ ‖f u-driverValue b u‖^2 := pow_le_pow_left₀ hp.le hn 2
    have hn0 : 0 < ‖f u-driverValue b u‖^2 := sq_pos_of_pos (hp.trans_le hn)
    norm_num only [Nat.cast_ofNat,pow_one,mul_one]
    convert! (div_nonneg (mul_nonneg (show 0 ≤ 2*a κ by positivity) (sub_nonneg.mpr hs)) hn0.le) using 1; field_simp [ne_of_gt (hp.trans_le hn)]; ring
  have hh := hm hs ht hst
  dsimp only at hh
  linarith

lemma inverseFlow_im_sq_bound {κ T : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T)
    (b : Driver) {w : ℂ} (hw : 0 < w.im) :
    (inverseFlow κ b T w).im^2 ≤ w.im^2+2*a κ*T := by
  have hf := surviving_flow_positiveSolution hT (inverseFlow_surviving hκ b hT hw)
  have hh := hf.im_sq_bound hκ (left_mem_Icc.mpr hT) (right_mem_Icc.mpr hT) hT
  simpa only [hf.2.2.1,flow_inverseFlow hκ b hT hw,sub_zero] using hh

lemma inverseFlow_im_pos {κ T : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T)
    (b : Driver) {w : ℂ} (hw : 0 < w.im) : 0 < (inverseFlow κ b T w).im := by
  have hf := surviving_flow_positiveSolution hT (inverseFlow_surviving hκ b hT hw)
  simpa only [hf.2.2.1] using hf.2.2.2.1 0 (left_mem_Icc.mpr hT)

lemma inverseFlow_deriv_absolute {κ T : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T)
    (b : Driver) {w : ℂ} (hw : 0 < w.im) :
    ‖deriv (inverseFlow κ b T) w‖ ≤ 2*(inverseFlow κ b T w).im/w.im := by
  have hs : ball w w.im ⊆ {u : ℂ | 0 < u.im} := by
    intro u hu
    rw [mem_ball,dist_eq_norm] at hu
    have hh := Complex.im_le_norm (w-u)
    rw [norm_sub_rev,Complex.sub_im] at hh
    change 0 < u.im
    linarith
  have hd : deriv (inverseFlow κ b T) w ≠ 0 := by
    rw [(inverseFlow_hasStrictDerivAt hκ b hT hw).hasDerivAt.deriv]
    exact inv_ne_zero (flow_deriv_ne_zero hT (inverseFlow_surviving hκ b hT hw))
  have hh := ball_radius_le_conformal_radius hw
    ((flow_conformal_bijection hκ b hT).2.2.2.mono hs)
    (fun u hu => inverseFlow_im_pos hκ hT b (hs hu)) hd
  have hh' := (le_div_iff₀ (norm_pos_iff.mpr hd)).mp hh
  apply (le_div_iff₀ hw).mpr
  nlinarith
end SLEExactGauge.LiteralTrace
namespace SLEExactGauge.LiteralTrace

lemma PositiveSolution.displacement_le {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} {f : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) (hκ : 0 < κ) {s t : ℝ}
    (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
    ‖f t-f s‖ ≤ (a κ/(f t).im)*(t-s) := by
  have ha : 0 < a κ := div_pos (by norm_num) hκ
  have hy := hf.2.2.2.1 t ht
  have hin : Icc s t ⊆ Icc 0 T := Icc_subset_Icc hs.1 ht.2
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (hf.2.2.2.2 u (hin hu)).mono hin)
    (show ∀ u ∈ Icc s t, ‖(a κ:ℂ)/(f u-driverValue b u)‖ ≤ a κ/(f t).im from by
      intro u hu
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha]
      apply div_le_div_of_nonneg_left ha.le hy
      apply (hf.im_antitone hκ (hin hu) ht hu.2).trans
      simpa using Complex.im_le_norm (f u-driverValue b u))
    (convex_Icc s t) (left_mem_Icc.mpr hst) (right_mem_Icc.mpr hst)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hst)] using hh

lemma inverseFlow_im_le {κ t T R : ℝ} (hκ : 0 < κ) (ht : 0 ≤ t) (htT : t ≤ T)
    (b : Driver) {w : ℂ} (hw : 0 < w.im) (hR : w.im ≤ R) :
    (inverseFlow κ b t w).im ≤ R+2*a κ*T+1 := by
  have ha : 0 < a κ := div_pos (by norm_num) hκ
  have hT : 0 ≤ T := ht.trans htT
  have hR0 : 0 ≤ R := hw.le.trans hR
  have hA : 0 ≤ 2*a κ*T := by positivity
  have him := inverseFlow_im_sq_bound hκ ht b hw
  have hnon := inverseFlow_im_pos hκ ht b hw
  have hup : w.im^2 ≤ R^2 := pow_le_pow_left₀ hw.le hR 2
  have hat : 2*a κ*t ≤ 2*a κ*T := mul_le_mul_of_nonneg_left htT (by positivity)
  nlinarith [sq_nonneg (2*a κ*T),mul_nonneg hR0 hA]

lemma inverseFlow_lipschitz_strip {κ t T y R : ℝ} (hκ : 0 < κ) (ht : 0 ≤ t)
    (htT : t ≤ T) (hy : 0 < y) (b : Driver) {v w : ℂ}
    (hv : y ≤ v.im ∧ v.im ≤ R) (hw : y ≤ w.im ∧ w.im ≤ R) :
    ‖inverseFlow κ b t v-inverseFlow κ b t w‖ ≤
      (2*(R+2*a κ*T+1)/y)*‖v-w‖ := by
  have hs : Convex ℝ {u : ℂ | y ≤ u.im ∧ u.im ≤ R} :=
    (convex_Icc y R).linear_preimage Complex.imCLM.toLinearMap
  apply Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ)
    (fun u hu => (inverseFlow_hasStrictDerivAt hκ b ht (hy.trans_le hu.1)).hasDerivAt.differentiableAt) _ hs hw hv
  intro u hu
  apply (inverseFlow_deriv_absolute hκ ht b (hy.trans_le hu.1)).trans
  calc
    _ ≤ 2*(R+2*a κ*T+1)/u.im := by
      apply div_le_div_of_nonneg_right _ (hy.le.trans hu.1)
      exact mul_le_mul_of_nonneg_left (inverseFlow_im_le hκ ht htT b (hy.trans_le hu.1) hu.2) (by norm_num)
    _ ≤ 2*(R+2*a κ*T+1)/y := by
      apply div_le_div_of_nonneg_left _ hy hu.1
      have ha : 0 < a κ := div_pos (by norm_num) hκ
      have hT : 0 ≤ T := ht.trans htT
      have hR0 : 0 < R := hy.trans_le (hu.1.trans hu.2)
      positivity

 

end SLEExactGauge.LiteralTrace
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
