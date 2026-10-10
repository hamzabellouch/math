import Mathlib
import OAI.Geometry.Cannon.Conformal.PreservesProducts

namespace OAI

section
section
section
section
section
section
section
section
section
section
noncomputable section
namespace CannonMetricQC
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

lemma image_ball_contains (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hf : WeakQS f H) (x y : ℂ) :
    ball (f x) (dist (f x) (f y)/H) ⊆ f '' closedBall x (dist x y) := by
  intro z hz
  refine ⟨f.symm z,?_,f.apply_symm_apply z⟩
  by_contra hh
  have hd : dist x y < dist x (f.symm z) := by
    simpa only [mem_closedBall,dist_comm,not_le] using hh
  have h := hf x y (f.symm z) hd.le
  rw [f.apply_symm_apply] at h
  have hz' : dist (f x) z < dist (f x) (f y)/H := by simpa only [mem_ball,dist_comm] using hz
  have hh' := (lt_div_iff₀ hH).mp hz'
  nlinarith

def imageArea (f : ℂ ≃ₜ ℂ) : Measure ℂ := volume.map f.symm

lemma imageArea_apply (f : ℂ ≃ₜ ℂ) {s : Set ℂ} (hs : MeasurableSet s) :
    imageArea f s=volume (f '' s) := by
  rw [imageArea,Measure.map_apply f.symm.continuous.measurable hs]
  congr 1
  exact (f.toEquiv.image_eq_preimage_symm s).symm

instance imageArea_locallyFinite (f : ℂ ≃ₜ ℂ) : IsLocallyFiniteMeasure (imageArea f) where
  finiteAtNhds x := by
    refine ⟨closedBall x 1,closedBall_mem_nhds x (by norm_num),?_⟩
    rw [imageArea_apply f isClosed_closedBall.measurableSet]
    exact ((isCompact_closedBall x 1).image f.continuous).measure_lt_top

lemma area_controls_dist (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hf : WeakQS f H) (x y : ℂ) :
    (dist (f x) (f y)/H)^2*Real.pi ≤
      (imageArea f (closedBall x (dist x y))).toReal := by
  have h := measure_mono (μ:=volume) (image_ball_contains f hH hf x y)
  rw [← imageArea_apply f isClosed_closedBall.measurableSet] at h
  have hm : imageArea f (closedBall x (dist x y)) ≠ ∞ :=
    (isCompact_closedBall x (dist x y)).measure_ne_top
  have hr := ENNReal.toReal_mono hm h
  simpa only [Complex.volume_ball,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (div_nonneg dist_nonneg hH.le),ENNReal.coe_toReal,
    NNReal.coe_real_pi] using hr

theorem weakQS_ae_pointwiseLip (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hf : WeakQS f H) : ∀ᵐ x ∂volume, PointwiseLip f x := by
  have hlim := Besicovitch.ae_tendsto_rnDeriv (imageArea f) volume
  filter_upwards [hlim,Measure.rnDeriv_lt_top (imageArea f) volume] with x hx hfin
  let c : ℝ≥0∞ := (imageArea f).rnDeriv volume x
  have hc : c ≠ ∞ := hfin.ne
  have ht : Tendsto (fun r =>
      ((imageArea f (closedBall x r))/(volume (closedBall x r))).toReal)
      (𝓝[>] (0:ℝ)) (𝓝 c.toReal) := ENNReal.tendsto_toReal hc |>.comp hx
  have hev := ht.eventually (gt_mem_nhds (show c.toReal < c.toReal+1 by linarith))
  obtain ⟨r,hr,hrb⟩ := Metric.mem_nhdsWithin_iff.mp hev
  let B := c.toReal+1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨H*(B+1),r,mul_nonneg hH.le (by positivity),hr,?_⟩
  intro y hy
  by_cases heq : x=y
  · subst y
    simp
  have hd : 0 < dist x y := dist_pos.mpr heq
  have hmem : dist x y ∈ ball (0:ℝ) r := by
    simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hd] using hy
  have hbound := hrb ⟨hmem,hd⟩
  change ((imageArea f (closedBall x (dist x y)))/(volume (closedBall x (dist x y)))).toReal < B at hbound
  have harea := area_controls_dist f hH hf x y
  have hv : (volume (closedBall x (dist x y))).toReal=(dist x y)^2*Real.pi := by
    simp only [Complex.volume_closedBall,ENNReal.toReal_mul,ENNReal.toReal_pow,
      ENNReal.toReal_ofReal dist_nonneg,ENNReal.coe_toReal,NNReal.coe_real_pi]
  rw [ENNReal.toReal_div,hv] at hbound
  have hp : 0 < (dist x y)^2*Real.pi := mul_pos (sq_pos_of_pos hd) Real.pi_pos
  have hm : (imageArea f (closedBall x (dist x y))).toReal < B*((dist x y)^2*Real.pi) :=
    (div_lt_iff₀ hp).mp hbound
  have hs : (dist (f x) (f y)/H)^2 < B*(dist x y)^2 := by
    nlinarith [Real.pi_pos]
  have hb : B ≤ (B+1)^2 := by nlinarith
  have hv' : dist (f x) (f y)/H ≤ (B+1)*dist x y := by
    have hpos : 0 ≤ (B+1)*dist x y := by positivity
    have hm' := mul_le_mul_of_nonneg_right hb (sq_nonneg (dist x y))
    nlinarith [sq_nonneg (dist (f x) (f y)/H+(B+1)*dist x y)]
  have h := (div_le_iff₀ hH).mp hv'
  nlinarith
end CannonMetricQC

namespace CannonMetricQC
open MeasureTheory

theorem weakQS_ae_differentiable (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hf : WeakQS f H) : ∀ᵐ x ∂volume, DifferentiableAt ℝ f x :=
  continuous_ae_differentiable_of_pointwiseLip f.continuous (weakQS_ae_pointwiseLip f hH hf)
end CannonMetricQC

noncomputable section
namespace CannonMetricQC
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal Topology

lemma measurable_ballArea (ν : Measure ℂ) [SFinite ν] (r : ℝ) :
    Measurable (fun x : ℂ => ν (closedBall x r)) := by
  let F : ℂ × ℂ → ℝ≥0∞ := {p | dist p.1 p.2 ≤ r}.indicator 1
  have hF : Measurable F := measurable_const.indicator
    (isClosed_le (continuous_fst.dist continuous_snd) continuous_const).measurableSet
  have h := hF.lintegral_prod_right' (ν:=ν)
  convert h using 1
  ext x
  have he : (fun y => F (x,y)) = (closedBall x r).indicator (fun _ => (1:ℝ≥0∞)) := by
    funext y
    by_cases h : dist x y ≤ r
    · simp [F, h, indicator_of_mem, show y ∈ closedBall x r by simpa [mem_closedBall, dist_comm] using h]
    · simp [F, h, indicator_of_notMem, show y ∉ closedBall x r by simpa [mem_closedBall, dist_comm] using h]
  rw [he,lintegral_indicator_const isClosed_closedBall.measurableSet]
  simp

theorem integrated_ballArea (ν : Measure ℂ) [SFinite ν] (c : ℂ) (R r : ℝ) :
    (∫⁻ x in closedBall c R, ν (closedBall x r)) ≤
      (volume (closedBall (0:ℂ) r))*ν (closedBall c (R+r)) := by
  let F : ℂ → ℂ → ℝ≥0∞ := fun x y => if dist x y ≤ r then 1 else 0
  have hF : Measurable (Function.uncurry F) := by
    exact measurable_const.ite (measurableSet_le
      (measurable_fst.dist measurable_snd) measurable_const) measurable_const
  have he (x : ℂ) : (∫⁻ y, F x y ∂ν)=ν (closedBall x r) := by
    have hh : F x = (closedBall x r).indicator (fun _ => (1:ℝ≥0∞)) := by
      funext y
      by_cases h : dist x y ≤ r
      · simp [F, h, show y ∈ closedBall x r by simpa [mem_closedBall, dist_comm] using h]
      · simp [F, h, show y ∉ closedBall x r by simpa [mem_closedBall, dist_comm] using h]
    rw [hh,lintegral_indicator_const isClosed_closedBall.measurableSet]
    simp
  simp_rw [← he]
  rw [lintegral_lintegral_swap hF.aemeasurable]
  calc
    _ ≤ ∫⁻ y, (closedBall c (R+r)).indicator
        (fun _ => volume (closedBall (0:ℂ) r)) y ∂ν := by
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ closedBall c (R+r)
      · rw [indicator_of_mem hy]
        have hh : (fun x => F x y)=(closedBall y r).indicator (fun _ => (1:ℝ≥0∞)) := by
          funext x
          by_cases h : dist x y ≤ r
          · simp [F, h, show x ∈ closedBall y r from h]
          · simp [F, h, show x ∉ closedBall y r from h]
        change (∫⁻ x in closedBall c R, F x y) ≤ _
        rw [hh,lintegral_indicator_const isClosed_closedBall.measurableSet,one_mul]
        calc
          (volume.restrict (closedBall c R)) (closedBall y r) ≤ volume (closedBall y r) :=
            Measure.restrict_apply_le _ _
          _ = volume (closedBall (0:ℂ) r) := by rw [Complex.volume_closedBall,Complex.volume_closedBall]
      · rw [indicator_of_notMem hy]
        apply le_of_eq
        apply lintegral_eq_zero_of_ae_eq_zero
        filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet] with x hx
        have hh : ¬ dist x y ≤ r := by
          intro hxy
          apply hy
          change dist y c ≤ R+r
          have hx' : dist x c ≤ R := hx
          calc
            dist y c ≤ dist y x + dist x c := dist_triangle _ _ _
            _ ≤ R+r := by rw [dist_comm y x]; linarith
        simp [F,hh]
    _ = _ := lintegral_indicator_const isClosed_closedBall.measurableSet _
end CannonMetricQC

namespace CannonMetricQC
open MeasureTheory Set Metric
open scoped ENNReal NNReal

lemma square_dist_le_area (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hf : WeakQS f H) (x y : ℂ) :
    ‖f y-f x‖ₑ^2 ≤ ENNReal.ofReal (H^2/Real.pi)*imageArea f (closedBall x (dist x y)) := by
  have hm : imageArea f (closedBall x (dist x y)) ≠ ∞ :=
    (isCompact_closedBall x (dist x y)).measure_ne_top
  have h := area_controls_dist f hH hf x y
  have hh : dist (f x) (f y)^2 ≤ (H^2/Real.pi)*(imageArea f (closedBall x (dist x y))).toReal := by
    have he : (dist (f x) (f y)/H)^2*H^2=dist (f x) (f y)^2 := by
      rw [←mul_pow,div_mul_cancel₀ _ hH.ne']
    have hmul := mul_le_mul_of_nonneg_right h (sq_nonneg H)
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ Real.pi_pos).mpr
    rw [mul_assoc, mul_comm Real.pi (H^2), ← mul_assoc, he] at hmul
    nlinarith
  have hr := ENNReal.ofReal_le_ofReal hh
  rw [ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) Real.pi_pos.le),ENNReal.ofReal_toReal hm] at hr
  simpa only [dist_comm (f x) (f y),dist_eq_norm,ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm] using hr

theorem weakQS_increment_energy (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hf : WeakQS f H) (c w : ℂ) (R : ℝ) :
    (∫⁻ x in closedBall c R, ‖f (x+w)-f x‖ₑ^2) ≤
      ENNReal.ofReal (H^2*‖w‖^2)*imageArea f (closedBall c (R+‖w‖)) := by
  have hpt (x : ℂ) := square_dist_le_area f hH hf x (x+w)
  have hd (x : ℂ) : dist x (x+w)=‖w‖ := by simp [dist_eq_norm]
  have harea := integrated_ballArea (imageArea f) c R ‖w‖
  calc
    _ ≤ ∫⁻ x in closedBall c R, ENNReal.ofReal (H^2/Real.pi)*
        imageArea f (closedBall x ‖w‖) := by
      apply lintegral_mono
      intro x
      simpa only [hd] using hpt x
    _ = ENNReal.ofReal (H^2/Real.pi)*(∫⁻ x in closedBall c R, imageArea f (closedBall x ‖w‖)) :=
      lintegral_const_mul _ (measurable_ballArea _ _)
    _ ≤ ENNReal.ofReal (H^2/Real.pi)*(volume (closedBall (0:ℂ) ‖w‖)*
        imageArea f (closedBall c (R+‖w‖))) := mul_le_mul le_rfl harea zero_le zero_le
    _ = _ := by
      rw [Complex.volume_closedBall,← mul_assoc]
      congr 1
      have hp : (NNReal.pi:ℝ≥0∞)=ENNReal.ofReal Real.pi := by rw [← NNReal.coe_real_pi]; exact ENNReal.ofReal_coe_nnreal.symm
      rw [hp,← ENNReal.ofReal_pow (norm_nonneg _),← ENNReal.ofReal_mul (sq_nonneg _),
        ← ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) Real.pi_pos.le)]
      congr 1
      field_simp
end CannonMetricQC

namespace CannonMetricQC
open MeasureTheory Set Metric
open scoped ENNReal NNReal

lemma eLpNorm_two_sq {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (g : X → E) (μ : Measure X) :
    (eLpNorm' g (2:ℝ) μ)^2=∫⁻ x, ‖g x‖ₑ^2 ∂μ := by
  simpa only [ENNReal.rpow_two] using
    (lintegral_rpow_enorm_eq_rpow_eLpNorm' (f:=g) (μ:=μ) (by norm_num : (0:ℝ) < 2)).symm

lemma continuous_memLp_compact {g : ℂ → ℂ}
    (hg : Continuous g) {S : Set ℂ} (hS : IsCompact S) : MemLp g 2 (volume.restrict S) := by
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_ne_top
  obtain ⟨B,hB⟩ := isBounded_iff_forall_norm_le.mp (hS.image hg).isBounded
  apply MemLp.of_bound hg.aestronglyMeasurable B
  filter_upwards [ae_restrict_mem hS.measurableSet] with z hz
  exact hB _ ⟨z,hz,rfl⟩

theorem weakQS_increment_lp (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hf : WeakQS f H) (c : ℂ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, ‖w‖ ≤ 1 →
      eLpNorm (fun x => f (x+w)-f x) 2 (volume.restrict (closedBall c R)) ≤
        ENNReal.ofReal (C*‖w‖) := by
  let T := imageArea f (closedBall c (R+1))
  have hT : T ≠ ∞ := (isCompact_closedBall c (R+1)).measure_ne_top
  let C := H*(Real.sqrt T.toReal)
  have hC : 0 ≤ C := mul_nonneg hH.le (Real.sqrt_nonneg _)
  refine ⟨C,hC,fun w hw => ?_⟩
  have he := weakQS_increment_energy f hH hf c w R
  have hm : imageArea f (closedBall c (R+‖w‖)) ≤ T :=
    measure_mono (closedBall_subset_closedBall (by linarith))
  have hb : (eLpNorm (fun x => f (x+w)-f x) 2 (volume.restrict (closedBall c R)))^2 ≤
      (ENNReal.ofReal (C*‖w‖))^2 := by
    have hincrement : Continuous (fun x : ℂ => f (x+w)-f x) :=
      (f.continuous.comp (continuous_id.add continuous_const)).sub f.continuous
    rw [eLpNorm_eq_eLpNorm' (by norm_num : (2:ℝ≥0∞) ≠ 0)
      (by norm_num : (2:ℝ≥0∞) ≠ ⊤) hincrement.aestronglyMeasurable,
      ENNReal.toReal_ofNat,eLpNorm_two_sq]
    apply he.trans
    calc
      _ ≤ ENNReal.ofReal (H^2*‖w‖^2)*T := mul_le_mul le_rfl hm zero_le zero_le
      _ = _ := by
        rw [← ENNReal.ofReal_toReal hT,← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
          ← ENNReal.ofReal_pow (mul_nonneg hC (norm_nonneg _))]
        congr 1
        dsimp only [C]
        rw [mul_pow,mul_pow,Real.sq_sqrt ENNReal.toReal_nonneg]
        ring
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0:ℝ) < 2)).mp (by simpa only [ENNReal.rpow_two] using hb)
end CannonMetricQC

namespace CannonMetricQC
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal Topology

theorem cutoff_increment_bound (f : ℂ → ℂ) (hf : Continuous f)
    (χ : ℂ → ℂ) {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hχb : ∀ x, ‖χ x‖ ≤ 1) {R : ℝ} (_hR : 0 ≤ R)
    (hs : ∀ x, R < ‖x‖ → χ x=0)
    (hi : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, ‖w‖ ≤ 1 →
      eLpNorm (fun x => f (x+w)-f x) 2 (volume.restrict (closedBall 0 (R+1))) ≤
        ENNReal.ofReal (C*‖w‖)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, ‖w‖ ≤ 1 →
      eLpNorm (fun x => χ (x+w)*f (x+w)-χ x*f x) 2 volume ≤
        ENNReal.ofReal (C*‖w‖) := by
  obtain ⟨E,hE,hi⟩ := hi
  let S : Set ℂ := closedBall 0 (R+1)
  let μ := volume.restrict S
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (isCompact_closedBall 0 (R+1)).measure_ne_top
  obtain ⟨B,hB0,hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ S, ‖f x‖ ≤ B := by
    obtain ⟨b,hb⟩ := (isCompact_closedBall (0:ℂ) (R+1)).exists_bound_of_continuousOn hf.continuousOn
    exact ⟨max b 0,le_max_right _ _,fun x hx => (hb x hx).trans (le_max_left _ _)⟩
  let K := eLpNorm (fun _ : ℂ => (1:ℂ)) 2 μ
  have hK : K ≠ ∞ := (memLp_const (1:ℂ) (p:=2) (μ:=μ)).ne
  let C := E + (L:ℝ)*B*K.toReal
  have hC : 0 ≤ C := add_nonneg hE (mul_nonneg (mul_nonneg L.coe_nonneg hB0) ENNReal.toReal_nonneg)
  refine ⟨C,hC,fun w hw => ?_⟩
  let A (x : ℂ) := χ (x+w)*(f (x+w)-f x)
  let D (x : ℂ) := (χ (x+w)-χ x)*f x
  have hA : Continuous A := (hχ.continuous.comp (continuous_id.add continuous_const)).mul
    ((hf.comp (continuous_id.add continuous_const)).sub hf)
  have hD : Continuous D := ((hχ.continuous.comp (continuous_id.add continuous_const)).sub hχ.continuous).mul hf
  have hsum : (fun x => χ (x+w)*f (x+w)-χ x*f x)=A+D := by
    funext x
    dsimp [A,D]
    ring
  have hzero (x : ℂ) (hx : x ∉ S) : (A+D) x=0 := by
    have hx' : R+1 < ‖x‖ := by simpa [S,mem_closedBall,dist_zero_right,not_le] using hx
    have hxw : R < ‖x+w‖ := by
      have hn : ‖x‖ ≤ ‖x+w‖+‖w‖ := by simpa using norm_sub_le (x+w) w
      linarith
    dsimp [A,D]
    rw [hs x (by linarith), hs (x+w) hxw]
    simp
  have hind : S.indicator (A+D)=A+D := by
    funext x
    by_cases hx : x ∈ S
    · simp [hx]
    · simp [hx,hzero x hx]
  have ha : eLpNorm A 2 μ ≤ ENNReal.ofReal (E*‖w‖) := by
    have he : eLpNorm A 2 μ ≤ eLpNorm (fun x => f (x+w)-f x) 2 μ :=
      eLpNorm_mono hA.aestronglyMeasurable (fun x => by
        dsimp [A]
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hχb _))
    exact he.trans (hi w hw)
  have hd : eLpNorm D 2 μ ≤ ENNReal.ofReal ((L:ℝ)*B*‖w‖)*K := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul hD.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (isClosed_closedBall.measurableSet)] with x hx
    have hl : ‖χ (x+w)-χ x‖ ≤ (L:ℝ)*‖w‖ := by
      simpa [dist_eq_norm] using hχ.dist_le_mul (x+w) x
    dsimp [D]
    simp only [norm_mul,norm_one,mul_one]
    calc
      _ ≤ ((L:ℝ)*‖w‖)*B := mul_le_mul hl (hB x hx) (norm_nonneg _) (mul_nonneg L.coe_nonneg (norm_nonneg _))
      _ = _ := by ring
  calc
    _ = eLpNorm (A+D) 2 μ := by
      rw [hsum]
      calc
        _ = eLpNorm (S.indicator (A+D)) 2 volume := congrArg (fun g => eLpNorm g 2 volume) hind.symm
        _ = _ := eLpNorm_indicator_eq_eLpNorm_restrict isClosed_closedBall.measurableSet
    _ ≤ eLpNorm A 2 μ+eLpNorm D 2 μ := eLpNorm_add_le (by norm_num)
    _ ≤ ENNReal.ofReal (E*‖w‖)+ENNReal.ofReal ((L:ℝ)*B*‖w‖)*K := add_le_add ha hd
    _ = ENNReal.ofReal (C*‖w‖) := by
      rw [← ENNReal.ofReal_toReal hK,← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg L.coe_nonneg hB0) (norm_nonneg _)),
        ← ENNReal.ofReal_add (mul_nonneg hE (norm_nonneg _)) (by positivity)]
      congr 1
      dsimp [C]
      ring

lemma cutoff_hasCompactSupport (χ : ℂ → ℂ) {R : ℝ}
    (hs : ∀ x, R < ‖x‖ → χ x=0) : HasCompactSupport χ := by
  apply (isCompact_closedBall (0:ℂ) R).of_isClosed_subset (isClosed_tsupport χ)
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hh
  have hz := hs x (by simpa [mem_closedBall,dist_zero_right,not_le] using hh)
  exact hx hz

theorem weakQS_cutoff_increment_bound (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hf : WeakQS f H) (χ : ℂ → ℂ) {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hχb : ∀ x, ‖χ x‖ ≤ 1) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ x, R < ‖x‖ → χ x=0) :
    MemLp (fun x => χ x*f x) 2 volume ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, ‖w‖ ≤ 1 →
      eLpNorm (fun x => χ (x+w)*f (x+w)-χ x*f x) 2 volume ≤
        ENNReal.ofReal (C*‖w‖) := by
  refine ⟨(hχ.continuous.mul f.continuous).memLp_of_hasCompactSupport
    ((cutoff_hasCompactSupport χ hs).mul_right),?_⟩
  exact cutoff_increment_bound f f.continuous χ hχ hχb hR hs
    (weakQS_increment_lp f hH hf 0 (R+1))
end CannonMetricQC

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
