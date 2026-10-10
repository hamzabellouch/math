import OAI.Analysis.IntegralMeans.Moments

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan

def circlePoint (r θ : ℝ) : ℂ := (r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)

def arcInterval : Set ℝ := Icc (-Real.pi/4) (Real.pi/4)

def arcD (r θ : ℝ) : ℝ := 1+2*r*Real.cos θ+r^2

def arcX (r θ : ℝ) : ℝ := 2*r*Real.sin θ/arcD r θ

def arcY (r θ : ℝ) : ℝ := (1-r^2)/arcD r θ

def arcXDeriv (r θ : ℝ) : ℝ := (4*r^2+2*r*(1+r^2)*Real.cos θ)/(arcD r θ)^2

lemma arc_cos_nonneg {θ : ℝ} (hθ : θ ∈ arcInterval) : 0 ≤ Real.cos θ := by
  apply Real.cos_nonneg_of_mem_Icc
  constructor <;> have hp := Real.pi_pos <;> dsimp [arcInterval] at hθ <;> linarith [hθ.1,hθ.2]

lemma arcD_bounds {r θ : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1) (hθ : θ ∈ arcInterval) :
    1 ≤ arcD r θ ∧ arcD r θ ≤ (1+r)^2 ∧ arcD r θ ≤ 4 := by
  have hc := arc_cos_nonneg hθ
  have hc1 := Real.cos_le_one θ
  have hr0 : 0 ≤ r := by linarith
  have hr2 : 0 ≤ 2*r := by positivity
  dsimp [arcD]
  have hm := mul_nonneg hr2 hc
  have hm1 := mul_le_mul_of_nonneg_left hc1 hr2
  constructor
  · nlinarith [sq_nonneg r]
  constructor <;> nlinarith

lemma arcX_bounds {r θ : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1) (hθ : θ ∈ arcInterval) :
    arcX r θ ∈ Icc (-1) 1 := by
  have hd := arcD_bounds hr hr1 hθ
  have hD : 0 < arcD r θ := by linarith [hd.1]
  have hc := arc_cos_nonneg hθ
  have hs := Real.neg_one_le_sin θ
  have hs1 := Real.sin_le_one θ
  have h2r : 0 ≤ 2*r := by linarith
  have hm1 := mul_le_mul_of_nonneg_left hs h2r
  have hm2 := mul_le_mul_of_nonneg_left hs1 h2r
  have hD2 : 2*r ≤ arcD r θ := by
    dsimp [arcD]
    nlinarith [mul_nonneg h2r hc,sq_nonneg (r-1)]
  constructor
  · exact (le_div_iff₀ hD).mpr (by nlinarith)
  · exact (div_le_iff₀ hD).mpr (by nlinarith)

lemma arcY_bounds {r θ : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1) (hθ : θ ∈ arcInterval) :
    (1-r)/2 ≤ arcY r θ ∧ arcY r θ ≤ 2*(1-r) := by
  have hd := arcD_bounds hr hr1 hθ
  have hD : 0 < arcD r θ := by linarith [hd.1]
  have hr0 : 0 ≤ r := by linarith
  have hd0 : 0 ≤ 1-r := by linarith
  constructor
  · apply (le_div_iff₀ hD).mpr
    have h := mul_le_mul_of_nonneg_left hd.2.1 (by positivity : 0 ≤ (1-r)/2)
    have hb : (1-r)/2*(1+r)^2 ≤ 1-r^2 := by nlinarith [mul_nonneg hd0 (sq_nonneg (1+r))]
    exact h.trans hb
  · apply (div_le_iff₀ hD).mpr
    have h := mul_le_mul_of_nonneg_left hd.1 (by positivity : 0 ≤ 2*(1-r))
    nlinarith [sq_nonneg (r-1)]

lemma arcX_hasDerivAt {r θ : ℝ} (hD : arcD r θ ≠ 0) :
    HasDerivAt (arcX r) (arcXDeriv r θ) θ := by
  have hn := (Real.hasDerivAt_sin θ).const_mul (2*r)
  have hd := (((Real.hasDerivAt_cos θ).const_mul (2*r)).const_add 1).add_const (r^2)
  have h := hn.div hd hD
  change HasDerivAt (arcX r) _ θ at h
  have he : arcXDeriv r θ =
      (2*r*Real.cos θ*arcD r θ-2*r*Real.sin θ*(2*r * -Real.sin θ))/(arcD r θ)^2 := by
    unfold arcXDeriv arcD
    congr 1
    have hc := Real.sin_sq_add_cos_sq θ
    nlinarith [sq_nonneg r]
  rw [he]
  exact h

lemma arcXDeriv_lower {r θ : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1) (hθ : θ ∈ arcInterval) :
    1/16 ≤ arcXDeriv r θ := by
  have hd := arcD_bounds hr hr1 hθ
  have hD : 0 < arcD r θ := by linarith [hd.1]
  have hc := arc_cos_nonneg hθ
  dsimp only [arcXDeriv]
  apply (le_div_iff₀ (sq_pos_of_pos hD)).mpr
  have hm : 0 ≤ 2*r*(1+r^2)*Real.cos θ := mul_nonneg (by positivity) hc
  have hsq : (arcD r θ)^2 ≤ 16 := by nlinarith [hd.2.2]
  nlinarith [sq_nonneg (r-1/2)]

lemma continuousOn_arcXDeriv {r : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1) :
    ContinuousOn (arcXDeriv r) arcInterval := by
  apply ContinuousOn.div
  · fun_prop
  · unfold arcD
    fun_prop
  · intro θ hθ
    exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one (arcD_bounds hr hr1 hθ).1))

lemma arcX_monotone {r : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1) : MonotoneOn (arcX r) arcInterval := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
  · intro θ hθ
    exact (arcX_hasDerivAt (ne_of_gt (lt_of_lt_of_le zero_lt_one (arcD_bounds hr hr1 hθ).1))).continuousAt.continuousWithinAt
  · intro θ hθ
    exact (arcX_hasDerivAt (ne_of_gt (lt_of_lt_of_le zero_lt_one (arcD_bounds hr hr1 (interior_subset hθ)).1))).hasDerivWithinAt
  · intro θ hθ
    exact le_trans (by norm_num) (arcXDeriv_lower hr hr1 (interior_subset hθ))

lemma circlePoint_norm (r θ : ℝ) : ‖circlePoint r θ‖ = |r| := by
  simp [circlePoint,Complex.norm_exp]

lemma circlePoint_re (r θ : ℝ) : (circlePoint r θ).re = r*Real.cos θ := by
  simp [circlePoint,Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin]

lemma circlePoint_im (r θ : ℝ) : (circlePoint r θ).im = r*Real.sin θ := by
  simp [circlePoint,Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin]

lemma one_add_circlePoint_norm_sq (r θ : ℝ) : ‖1+circlePoint r θ‖^2 = arcD r θ := by
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,circlePoint_re,circlePoint_im,zero_add]
  dsimp [arcD]
  nlinarith [Real.sin_sq_add_cos_sq θ,sq_nonneg r]

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan
attribute [local irreducible] classFun classWeight rerootClass

lemma circlePoint_mem_disk {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) : circlePoint r θ ∈ disk := by
  simpa [disk,circlePoint_norm,abs_of_nonneg hr] using hr1

lemma neg_circlePoint_mem_disk {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) : -circlePoint r θ ∈ disk := by
  simpa only [disk,Metric.mem_ball,dist_zero_right,norm_neg] using circlePoint_mem_disk hr hr1 θ

lemma halfCayley_re (z : ℂ) : (halfCayley z).re = -2*z.im/‖1-z‖^2 := by
  simp only [halfCayley,Complex.div_re,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.add_re,Complex.add_im,Complex.one_re,
    Complex.one_im,Complex.sub_re,Complex.sub_im,Complex.sq_norm,Complex.normSq_apply]
  ring

lemma halfCayley_neg_circlePoint {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    halfCayley (-circlePoint r θ) = (arcX r θ:ℂ)+(arcY r θ:ℂ)*Complex.I := by
  have hz := neg_circlePoint_mem_disk hr hr1 θ
  apply Complex.ext
  · rw [halfCayley_re]
    simp only [Complex.neg_im,circlePoint_im,sub_neg_eq_add,one_add_circlePoint_norm_sq,
      Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.ofReal_im,Complex.I_im]
    dsimp [arcX]
    ring
  · rw [halfCayley_im hz]
    simp only [norm_neg,circlePoint_norm,abs_of_nonneg hr,sub_neg_eq_add,one_add_circlePoint_norm_sq,
      Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.ofReal_re,Complex.I_im]
    simp [arcY]

lemma classWeight_vertical_bound (g : DiskClass) {η : ℝ} (hη : 1/2 ≤ η) (hη4 : η ≤ 4) :
    classWeight g (halfPoint 0 η (by linarith)) ≤ 1562500 := by
  let z := halfPoint 0 η (by linarith : 0 < η)
  have hb := classFun_reciprocal_bound g z
  have he : ‖z.val+Complex.I‖ = η+1 := by
    have hz : z.val+Complex.I = ((η+1:ℝ):ℂ)*Complex.I := by
      dsimp [z,halfPoint]
      push_cast
      ring
    rw [hz,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)]
  have hη0 : 0 < η := by linarith
  have ht : ‖reciprocalDeriv (classFun g) z‖ ≤ 1250 := by
    rw [he] at hb
    simp only [z,halfPoint,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] at hb
    have hp : (η+1)^4 ≤ (5:ℝ)^4 := pow_le_pow_left₀ (by linarith) (by linarith) _
    apply hb.trans
    apply (div_le_iff₀ hη0).mpr
    norm_num at hp
    linarith
  unfold classWeight
  change ‖reciprocalDeriv (classFun g) z‖^2 ≤ _
  nlinarith [norm_nonneg (reciprocalDeriv (classFun g) z)]

lemma classWeight_vertical_compare (g : DiskClass) (x v y : ℝ) (hv : 0 < v)
    (hy : v/2 ≤ y) (hy4 : y ≤ 4*v) :
    classWeight g (halfPoint x y (by linarith)) ≤
      1562500*classWeight g (halfPoint x v hv) := by
  have hη : 1/2 ≤ y/v := (le_div_iff₀ hv).mpr (by linarith)
  have hη4 : y/v ≤ 4 := (div_le_iff₀ hv).mpr hy4
  have hη0 : 0 < y/v := by linarith
  have he : halfMul (halfPoint x v hv) (halfPoint 0 (y/v) hη0) = halfPoint x y (by linarith) := by
    rw [halfPoint_mul]
    apply Subtype.ext
    dsimp [halfPoint]
    congr 2 <;> simp [mul_div_cancel₀ y hv.ne']
  have hc := classWeight_cocycle g (halfPoint x v hv) (halfPoint 0 (y/v) hη0)
  change _ = classWeight g (halfMul _ _) at hc
  rw [he] at hc
  rw [← hc,mul_comm (1562500:ℝ)]
  exact mul_le_mul_of_nonneg_left (classWeight_vertical_bound _ hη hη4) (classWeight_pos g _).le

lemma inverse_deriv_square_conversion {f : ℂ → ℂ} (hf : Schlicht f) {w : ℂ} (hw : w ∈ disk) :
    ‖deriv f w‖^(-2:ℝ) ≤ 16*classWeight (classOfHalf (diskToHalf f) (diskToHalf_schlicht hf))
      ⟨halfCayley w,halfCayley_maps hw⟩ := by
  let g := classOfHalf (diskToHalf f) (diskToHalf_schlicht hf)
  let z : halfPlane := ⟨halfCayley w,halfCayley_maps hw⟩
  have he := (classFun_classOfHalf (diskToHalf_schlicht hf)).deriv isOpen_halfPlane z.2
  have hfhe : EqOn (halfToDisk (diskToHalf f)) f disk := fun _ hz => halfToDisk_diskToHalf hz
  have hd := (hasDerivAt_halfToDisk (diskToHalf_schlicht hf).1.1 hw).deriv
  rw [hfhe.deriv Metric.isOpen_ball hw] at hd
  have hw1 : ‖w‖ < 1 := by simpa [disk] using hw
  have hb : ‖1-w‖ ≤ 2 := (norm_sub_le _ _).trans (by simpa using (show 1+‖w‖ ≤ 2 by linarith))
  have ha : 0 < ‖deriv (diskToHalf f) (halfCayley w)‖ := norm_pos_iff.mpr
    (univalent_deriv_ne_zero isOpen_halfPlane (diskToHalf_schlicht hf).1 z.2)
  rw [hd,norm_div,norm_pow,Real.rpow_neg (by positivity),Real.rpow_two]
  unfold classWeight
  change _ ≤ 16*‖reciprocalDeriv (classFun g) z‖^2
  rw [reciprocalDeriv,he,norm_inv]
  have hb4 : ‖1-w‖^4 ≤ (2:ℝ)^4 := pow_le_pow_left₀ (norm_nonneg _) hb _
  have hz0 : ‖1-w‖ ≠ 0 := norm_ne_zero_iff.mpr (halfCayley_den_ne_zero hw)
  dsimp only [z]
  field_simp [ha.ne',hz0]
  nlinarith

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan

attribute [local irreducible] classFun classWeight rerootClass

lemma continuous_weightAt : Continuous weightAt := by
  have he : weightAt = fun z => affineOperator z 1 := by
    funext z
    ext g
    simp only [affineOperator_apply,ContinuousMap.one_apply,mul_one]
    rfl
  rw [he]
  exact continuous_affineOperator_apply 1

def horizontalMass (v : ℝ) (hv : 0 < v) : C(DiskClass,ℝ) :=
  ∫ x in (-1:ℝ)..1, weightAt (halfPoint x v hv)

lemma horizontalMass_apply (v : ℝ) (hv : 0 < v) (g : DiskClass) :
    horizontalMass v hv g = ∫ x in (-1:ℝ)..1, classWeight g (halfPoint x v hv) := by
  exact ((ContinuousMap.evalCLM ℝ g).intervalIntegral_comp_comm
    ((continuous_weightAt.comp (continuous_halfPoint continuous_id continuous_const (fun _ => hv))).intervalIntegrable (μ := volume) _ _)).symm

lemma continuous_horizontalWeight (g : DiskClass) (v : ℝ) (hv : 0 < v) :
    Continuous (fun x => classWeight g (halfPoint x v hv)) :=
  continuous_classWeight.comp (continuous_const.prodMk
    (continuous_halfPoint continuous_id continuous_const (fun _ => hv)))

lemma horizontalMass_half (v : ℝ) (hv : 0 < v) :
    horizontalMass (v/2) (by positivity) = transferOperator (horizontalMass v hv) := by
  ext g
  rw [horizontalMass_apply]
  change _ = (1/2:ℝ)*(classWeight g dyadicLeft * horizontalMass v hv (rerootClass g dyadicLeft)+
    classWeight g dyadicRight * horizontalMass v hv (rerootClass g dyadicRight))
  rw [horizontalMass_apply,horizontalMass_apply,← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  have hL (x : ℝ) : classWeight g dyadicLeft * classWeight (rerootClass g dyadicLeft) (halfPoint x v hv) =
      classWeight g (halfPoint ((1/2)*x+(-(1/2))) (v/2) (by positivity)) := by
    rw [classWeight_cocycle]
    congr 1
    apply Subtype.ext
    apply Complex.ext <;> simp [dyadicLeft,halfPoint,affine] <;> ring
  have hR (x : ℝ) : classWeight g dyadicRight * classWeight (rerootClass g dyadicRight) (halfPoint x v hv) =
      classWeight g (halfPoint ((1/2)*x+1/2) (v/2) (by positivity)) := by
    rw [classWeight_cocycle]
    congr 1
    apply Subtype.ext
    apply Complex.ext <;> simp [dyadicRight,halfPoint,affine] <;> ring
  simp_rw [hL,hR]
  have hl := intervalIntegral.integral_comp_mul_add
    (f := fun x => classWeight g (halfPoint x (v/2) (by positivity)))
    (a := (-1:ℝ)) (b := 1) (by norm_num : (1/2:ℝ) ≠ 0) (-1/2)
  have hr := intervalIntegral.integral_comp_mul_add
    (f := fun x => classWeight g (halfPoint x (v/2) (by positivity)))
    (a := (-1:ℝ)) (b := 1) (by norm_num : (1/2:ℝ) ≠ 0) (1/2)
  norm_num at hl hr
  have hi := (continuous_horizontalWeight g (v/2) (by positivity)).intervalIntegrable (μ := volume)
  have hs := intervalIntegral.integral_add_adjacent_intervals (hi (-1) 0) (hi 0 1)
  rw [hl,hr]
  linarith [hs]

lemma horizontalMass_dyadic (n : ℕ) :
    horizontalMass ((1/2:ℝ)^n) (by positivity) = (transferOperator^n) (horizontalMass 1 zero_lt_one) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : (1/2:ℝ)^(n+1) = (1/2:ℝ)^n/2 := by rw [pow_succ]; ring
    have hm : horizontalMass ((1/2:ℝ)^(n+1)) (by positivity) = horizontalMass ((1/2:ℝ)^n/2) (by positivity) := by congr 1
    rw [hm,horizontalMass_half _ (by positivity),ih,pow_succ',mul_apply_eq_comp]

lemma horizontalMass_dyadic_le (n : ℕ) (g : DiskClass) :
    (∫ x in (-1:ℝ)..1, classWeight g (halfPoint x ((1/2:ℝ)^n) (by positivity))) ≤
      ‖horizontalMass 1 zero_lt_one‖*‖transferOperator^n‖ := by
  rw [← horizontalMass_apply,horizontalMass_dyadic,mul_comm]
  exact (le_abs_self _).trans ((ContinuousMap.norm_coe_le_norm _ _).trans ((transferOperator^n).le_opNorm _))

lemma transferOperator_uniform_growth {lam : ℝ} (hlam : 2 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖transferOperator^n‖ ≤ C*lam^n := by
  have hl : 0 < lam := by linarith
  obtain ⟨N,hN⟩ := eventually_atTop.mp (norm_pow_eventually_le transferOperator transferOperator_pow_norm_ge_one
    (lt_of_le_of_lt transferRho_le_two hlam))
  let C : ℝ := 1 + ∑ j ∈ Finset.range N, ‖transferOperator^j‖/lam^j
  have hC : 1 ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => div_nonneg (norm_nonneg (transferOperator^j)) (pow_pos hl j).le))
  refine ⟨C,zero_lt_one.trans_le hC,fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (le_mul_of_one_le_left (pow_pos hl n).le hC)
  · have hs : ‖transferOperator^n‖/lam^n ≤ ∑ j ∈ Finset.range N, ‖transferOperator^j‖/lam^j :=
      Finset.single_le_sum (fun j _ => div_nonneg (norm_nonneg (transferOperator^j)) (pow_pos hl j).le) (Finset.mem_range.mpr (lt_of_not_ge hn))
    apply (div_le_iff₀ (pow_pos hl n)).mp
    exact hs.trans (by dsimp [C]; linarith)

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan
attribute [local irreducible] classFun classWeight rerootClass

lemma continuous_circlePoint (r : ℝ) : Continuous (circlePoint r) := by
  unfold circlePoint
  fun_prop

lemma continuous_circle_deriv_rpow {f : ℂ → ℂ} (hf : UnivalentOn f disk)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    Continuous (fun θ => ‖deriv f (circlePoint r θ)‖^t) := by
  have hc : Continuous (fun θ => deriv f (circlePoint r θ)) :=
    ((hf.1.deriv Metric.isOpen_ball).continuousOn).comp_continuous (continuous_circlePoint r)
      (circlePoint_mem_disk hr hr1)
  exact hc.norm.rpow_const (fun θ => Or.inl (norm_ne_zero_iff.mpr
    (univalent_deriv_ne_zero Metric.isOpen_ball hf (circlePoint_mem_disk hr hr1 θ))))

lemma continuous_neg_circle_deriv_rpow {f : ℂ → ℂ} (hf : UnivalentOn f disk)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    Continuous (fun θ => ‖deriv f (-circlePoint r θ)‖^t) := by
  have hc : Continuous (fun θ => deriv f (-circlePoint r θ)) :=
    ((hf.1.deriv Metric.isOpen_ball).continuousOn).comp_continuous (continuous_circlePoint r).neg
      (neg_circlePoint_mem_disk hr hr1)
  exact hc.norm.rpow_const (fun θ => Or.inl (norm_ne_zero_iff.mpr
    (univalent_deriv_ne_zero Metric.isOpen_ball hf (neg_circlePoint_mem_disk hr hr1 θ))))

lemma arc_integral_bound {f : ℂ → ℂ} (hf : Schlicht f) {r v : ℝ}
    (hr : 1/2 ≤ r) (hr1 : r < 1) (hv : 0 < v) (hvδ : v ≤ 1-r) (hδv : 1-r ≤ 2*v) :
    (∫ θ in (-Real.pi/4)..(Real.pi/4), ‖deriv f (-circlePoint r θ)‖^(-2:ℝ)) ≤
      400000000 * horizontalMass v hv (classOfHalf (diskToHalf f) (diskToHalf_schlicht hf)) := by
  let g := classOfHalf (diskToHalf f) (diskToHalf_schlicht hf)
  let W : ℝ → ℝ := fun x => classWeight g (halfPoint x v hv)
  have hW : Continuous W := continuous_horizontalWeight g v hv
  have hab : -Real.pi/4 ≤ Real.pi/4 := by linarith [Real.pi_pos]
  have hu : uIcc (-Real.pi/4) (Real.pi/4) = arcInterval := uIcc_of_le hab
  have hX (θ : ℝ) (hθ : θ ∈ arcInterval) : HasDerivAt (arcX r) (arcXDeriv r θ) θ :=
    arcX_hasDerivAt (ne_of_gt (lt_of_lt_of_le zero_lt_one (arcD_bounds hr hr1 hθ).1))
  have hXc : ContinuousOn (arcX r) arcInterval := fun θ hθ => (hX θ hθ).continuousAt.continuousWithinAt
  have hprod : ContinuousOn (fun θ => W (arcX r θ)*arcXDeriv r θ) arcInterval :=
    (hW.comp_continuousOn hXc).mul (continuousOn_arcXDeriv hr hr1)
  have hi := intervalIntegral.integral_mono_on hab
    ((continuous_neg_circle_deriv_rpow hf.1 (by linarith) hr1 (-2)).intervalIntegrable (μ := volume) _ _)
    ((hprod.const_mul 400000000).intervalIntegrable_of_Icc hab)
    (fun θ hθ => show ‖deriv f (-circlePoint r θ)‖^(-2:ℝ) ≤
      400000000*(W (arcX r θ)*arcXDeriv r θ) from by
      have hθ' : θ ∈ arcInterval := hθ
      have hy := arcY_bounds hr hr1 hθ'
      have hz : (⟨halfCayley (-circlePoint r θ),halfCayley_maps (neg_circlePoint_mem_disk (by linarith) hr1 θ)⟩ : halfPlane) =
          halfPoint (arcX r θ) (arcY r θ) (by linarith) :=
        Subtype.ext (halfCayley_neg_circlePoint (by linarith) hr1 θ)
      have hc := inverse_deriv_square_conversion hf (neg_circlePoint_mem_disk (by linarith) hr1 θ)
      rw [hz] at hc
      have hb := classWeight_vertical_compare g (arcX r θ) v (arcY r θ) hv (by linarith) (by linarith)
      have hd := arcXDeriv_lower hr hr1 hθ'
      have hWp : 0 ≤ W (arcX r θ) := (classWeight_pos g _).le
      have hm := mul_nonneg hWp (sub_nonneg.mpr hd)
      change _ ≤ 16*classWeight g _ at hc
      change classWeight g _ ≤ 1562500*W (arcX r θ) at hb
      nlinarith)
  rw [intervalIntegral.integral_const_mul] at hi
  have hchange := intervalIntegral.integral_comp_mul_deriv
    (fun θ hθ => hX θ (hu ▸ hθ)) (hu ▸ continuousOn_arcXDeriv hr hr1) hW
  change (∫ θ in (-Real.pi/4)..(Real.pi/4), W (arcX r θ)*arcXDeriv r θ) = _ at hchange
  rw [hchange] at hi
  have hlo : -Real.pi/4 ∈ arcInterval := ⟨le_rfl,hab⟩
  have hhi : Real.pi/4 ∈ arcInterval := ⟨hab,le_rfl⟩
  have hm := arcX_monotone hr hr1 hlo hhi hab
  have hb := intervalIntegral.integral_mono_interval (arcX_bounds hr hr1 hlo).1 hm
    (arcX_bounds hr hr1 hhi).2
    (Eventually.of_forall (fun x => (classWeight_pos g (halfPoint x v hv)).le))
    (hW.intervalIntegrable (μ := volume) (-1) 1)
  rw [horizontalMass_apply]
  exact hi.trans (mul_le_mul_of_nonneg_left hb (by norm_num))

lemma arc_integral_dyadic_bound {f : ℂ → ℂ} (hf : Schlicht f) {r : ℝ}
    (hr : 1/2 ≤ r) (hr1 : r < 1) (n : ℕ)
    (hvδ : (1/2:ℝ)^n ≤ 1-r) (hδv : 1-r ≤ 2*(1/2:ℝ)^n) :
    (∫ θ in (-Real.pi/4)..(Real.pi/4), ‖deriv f (-circlePoint r θ)‖^(-2:ℝ)) ≤
      (400000000*‖horizontalMass 1 zero_lt_one‖)*‖transferOperator^n‖ := by
  have hb := arc_integral_bound hf hr hr1 (by positivity) hvδ hδv
  have hm := horizontalMass_dyadic_le n (classOfHalf (diskToHalf f) (diskToHalf_schlicht hf))
  rw [← horizontalMass_apply] at hm
  exact hb.trans ((mul_le_mul_of_nonneg_left hm (by norm_num)).trans_eq (by ring))

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan
attribute [local irreducible] classFun classWeight rerootClass

def rotateDisk (f : ℂ → ℂ) (α z : ℂ) : ℂ := f (α*z)/α

lemma rotateDisk_maps {α : ℂ} (hα : ‖α‖ = 1) : MapsTo (fun z => α*z) disk disk := by
  intro z hz
  simpa [disk,norm_mul,hα] using hz

lemma rotateDisk_hasDerivAt {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f disk)
    {α z : ℂ} (hα : ‖α‖ = 1) (hz : z ∈ disk) :
    HasDerivAt (rotateDisk f α) (deriv f (α*z)) z := by
  have hα0 : α ≠ 0 := by intro h; simp [h] at hα
  have hd := ((hf _ (rotateDisk_maps hα hz)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (rotateDisk_maps hα hz))).hasDerivAt
  convert (hd.comp z ((hasDerivAt_id z).const_mul α)).div_const α using 1 <;> try rfl
  simp [hα0]

lemma rotateDisk_schlicht {f : ℂ → ℂ} (hf : Schlicht f) {α : ℂ} (hα : ‖α‖ = 1) :
    Schlicht (rotateDisk f α) := by
  have hα0 : α ≠ 0 := by intro h; simp [h] at hα
  refine ⟨⟨fun z hz => (rotateDisk_hasDerivAt hf.1.1 hα hz).differentiableAt.differentiableWithinAt,?_⟩,?_,?_⟩
  · intro z hz w hw he
    exact mul_left_cancel₀ hα0 (hf.1.2 (rotateDisk_maps hα hz) (rotateDisk_maps hα hw)
      ((div_left_inj' hα0).mp he))
  · simp [rotateDisk,hf.2.1]
  · rw [(rotateDisk_hasDerivAt hf.1.1 hα (show (0:ℂ) ∈ disk by simp [disk])).deriv]
    simpa using hf.2.2

lemma circlePoint_shift (r θ c : ℝ) :
    (-Complex.exp ((c:ℂ)*Complex.I))*(-circlePoint r θ) = circlePoint r (θ+c) := by
  simp only [circlePoint,Complex.ofReal_add,add_mul,Complex.exp_add,neg_mul_neg]
  ring

lemma circle_arc_dyadic_bound {f : ℂ → ℂ} (hf : Schlicht f) {r : ℝ}
    (hr : 1/2 ≤ r) (hr1 : r < 1) (n : ℕ)
    (hvδ : (1/2:ℝ)^n ≤ 1-r) (hδv : 1-r ≤ 2*(1/2:ℝ)^n) (c : ℝ) :
    (∫ θ in (c-Real.pi/4)..(c+Real.pi/4), ‖deriv f (circlePoint r θ)‖^(-2:ℝ)) ≤
      (400000000*‖horizontalMass 1 zero_lt_one‖)*‖transferOperator^n‖ := by
  let α := -Complex.exp ((c:ℂ)*Complex.I)
  have hα : ‖α‖ = 1 := by simp [α,Complex.norm_exp]
  have hb := arc_integral_dyadic_bound (rotateDisk_schlicht hf hα) hr hr1 n hvδ hδv
  have he (θ : ℝ) : deriv (rotateDisk f α) (-circlePoint r θ) = deriv f (circlePoint r (θ+c)) := by
    rw [(rotateDisk_hasDerivAt hf.1.1 hα (neg_circlePoint_mem_disk (by linarith) hr1 θ)).deriv]
    rw [show α*(-circlePoint r θ) = circlePoint r (θ+c) from circlePoint_shift r θ c]
  simp_rw [he] at hb
  rw [intervalIntegral.integral_comp_add_right (f := fun θ => ‖deriv f (circlePoint r θ)‖^(-2:ℝ)) c] at hb
  convert hb using 1
  congr 1 <;> ring

lemma periodic_circlePoint (r : ℝ) : Periodic (circlePoint r) (2*Real.pi) := by
  simpa [circlePoint,circleMap] using periodic_circleMap (0:ℂ) r

lemma full_circle_dyadic_bound {f : ℂ → ℂ} (hf : Schlicht f) {r : ℝ}
    (hr : 1/2 ≤ r) (hr1 : r < 1) (n : ℕ)
    (hvδ : (1/2:ℝ)^n ≤ 1-r) (hδv : 1-r ≤ 2*(1/2:ℝ)^n) :
    (∫ θ in -Real.pi..Real.pi, ‖deriv f (circlePoint r θ)‖^(-2:ℝ)) ≤
      (1600000000*‖horizontalMass 1 zero_lt_one‖)*‖transferOperator^n‖ := by
  let F : ℝ → ℝ := fun θ => ‖deriv f (circlePoint r θ)‖^(-2:ℝ)
  have hF := (continuous_circle_deriv_rpow hf.1 (by linarith) hr1 (-2)).intervalIntegrable (μ := volume)
  have hper : Periodic F (2*Real.pi) := (periodic_circlePoint r).comp (fun z => ‖deriv f z‖^(-2:ℝ))
  have hshift := hper.intervalIntegral_add_eq (-Real.pi) (-Real.pi/4)
  have h1 := circle_arc_dyadic_bound hf hr hr1 n hvδ hδv 0
  have h2 := circle_arc_dyadic_bound hf hr hr1 n hvδ hδv (Real.pi/2)
  have h3 := circle_arc_dyadic_bound hf hr hr1 n hvδ hδv Real.pi
  have h4 := circle_arc_dyadic_bound hf hr hr1 n hvδ hδv (3*Real.pi/2)
  have e1 : (0:ℝ)-Real.pi/4 = -Real.pi/4 := by ring
  have e2 : (0:ℝ)+Real.pi/4 = Real.pi/4 := by ring
  have e3 : Real.pi/2-Real.pi/4 = Real.pi/4 := by ring
  have e4 : Real.pi/2+Real.pi/4 = 3*Real.pi/4 := by ring
  have e5 : Real.pi-Real.pi/4 = 3*Real.pi/4 := by ring
  have e6 : Real.pi+Real.pi/4 = 5*Real.pi/4 := by ring
  have e7 : 3*Real.pi/2-Real.pi/4 = 5*Real.pi/4 := by ring
  have e8 : 3*Real.pi/2+Real.pi/4 = 7*Real.pi/4 := by ring
  rw [e1,e2] at h1
  rw [e3,e4] at h2
  rw [e5,e6] at h3
  rw [e7,e8] at h4
  have ha := intervalIntegral.integral_add_adjacent_intervals (hF (-Real.pi/4) (Real.pi/4)) (hF (Real.pi/4) (3*Real.pi/4))
  have hb := intervalIntegral.integral_add_adjacent_intervals (hF (-Real.pi/4) (3*Real.pi/4)) (hF (3*Real.pi/4) (5*Real.pi/4))
  have hc := intervalIntegral.integral_add_adjacent_intervals (hF (-Real.pi/4) (5*Real.pi/4)) (hF (5*Real.pi/4) (7*Real.pi/4))
  have es1 : -Real.pi+2*Real.pi = Real.pi := by ring
  have es2 : -Real.pi/4+2*Real.pi = 7*Real.pi/4 := by ring
  rw [es1,es2] at hshift
  dsimp only [F] at hshift
  linarith

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan

lemma dyadic_growth_compare {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) {n : ℕ}
    (hn : δ ≤ 2*(1/2:ℝ)^n) :
    ((2:ℝ)^a)^n ≤ (2:ℝ)^a * δ^(-a) := by
  have hv : 0 < (1/2:ℝ)^n := by positivity
  have he : ((2:ℝ)^a)^n = ((1/2:ℝ)^n)^(-a) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num),← Real.rpow_natCast (1/2:ℝ),
      ← Real.rpow_mul (by norm_num)]
    rw [show (1/2:ℝ) = 2^(-1:ℝ) by norm_num,← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [he]
  have hb := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < δ/2)
    (show δ/2 ≤ (1/2:ℝ)^n by linarith) (neg_nonpos.mpr ha)
  refine hb.trans_eq ?_
  rw [Real.div_rpow hδ.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_inv_eq_mul,mul_comm]

lemma uniform_inverse_square_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℂ, Schlicht f → ∀ r : ℝ, 1/2 ≤ r → r < 1 →
      integralMean f (-2) r ≤ C*(1-r)^(-1-ε) := by
  have hlam : 2 < (2:ℝ)^(1+ε) := by
    calc
      (2:ℝ) = 2^(1:ℝ) := by rw [Real.rpow_one]
      _ < 2^(1+ε) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  obtain ⟨K,hK,hKn⟩ := transferOperator_uniform_growth hlam
  let A := (2*Real.pi)⁻¹*(1600000000*‖horizontalMass 1 zero_lt_one‖)*K*(2:ℝ)^(1+ε)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A+1,by linarith,fun f hf r hr hr1 => ?_⟩
  obtain ⟨n,hn1,hn2⟩ := exists_nat_pow_near_of_lt_one (by linarith : 0 < 1-r)
    (by linarith : 1-r ≤ 1) (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)
  have hn : 1-r ≤ 2*(1/2:ℝ)^(n+1) := by rw [pow_succ]; nlinarith
  have hb := full_circle_dyadic_bound hf hr hr1 (n+1) hn1.le hn
  have hc := dyadic_growth_compare (by linarith : 0 ≤ 1+ε) (by linarith : 0 < 1-r) hn
  have hx : 0 ≤ (2*Real.pi)⁻¹ := by positivity
  have hy : 0 ≤ 1600000000*‖horizontalMass 1 zero_lt_one‖ := by positivity
  have he : (-1-ε:ℝ) = -(1+ε) := by ring
  change (2*Real.pi)⁻¹*(∫ θ in -Real.pi..Real.pi, ‖deriv f (circlePoint r θ)‖^(-2:ℝ)) ≤ _
  calc
    _ ≤ (2*Real.pi)⁻¹*((1600000000*‖horizontalMass 1 zero_lt_one‖)*‖transferOperator^(n+1)‖) :=
      mul_le_mul_of_nonneg_left hb hx
    _ ≤ (2*Real.pi)⁻¹*((1600000000*‖horizontalMass 1 zero_lt_one‖)*(K*((2:ℝ)^(1+ε))^(n+1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hKn (n+1)) hy) hx
    _ ≤ (2*Real.pi)⁻¹*((1600000000*‖horizontalMass 1 zero_lt_one‖)*(K*((2:ℝ)^(1+ε)*(1-r)^(-(1+ε))))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc hK.le) hy) hx
    _ = A*(1-r)^(-1-ε) := by rw [he]; dsimp [A]; ring
    _ ≤ (A+1)*(1-r)^(-1-ε) := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by linarith) _)

end Brennan

end

end OAI
