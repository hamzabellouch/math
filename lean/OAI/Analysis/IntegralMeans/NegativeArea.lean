import OAI.Analysis.IntegralMeans.Spectrum

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma polar_symm_circle (p : ℝ × ℝ) : Complex.polarCoord.symm p = circlePoint p.1 p.2 := by
  simp [Complex.polarCoord_symm_apply,circlePoint,Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin]

lemma disk_lintegral_le_polar (F : ℂ → ℝ≥0∞) :
    (∫⁻ z in disk, F z) ≤ ∫⁻ r in Ioo (0:ℝ) 1,
      ENNReal.ofReal r * ∫⁻ θ in Ioo (-Real.pi) Real.pi, F (circlePoint r θ) := by
  have hm : MeasurableSet disk := Metric.isOpen_ball.measurableSet
  rw [← lintegral_indicator hm,← Complex.lintegral_comp_polarCoord_symm]
  change (∫⁻ p in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
    ENNReal.ofReal p.1 * disk.indicator F (Complex.polarCoord.symm p)) ≤ _
  rw [← lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo)]
  have he : (Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi).indicator
      (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * disk.indicator F (Complex.polarCoord.symm p)) =
      (Ioo (0:ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi).indicator
      (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * F (circlePoint p.1 p.2)) := by
    ext p
    simp_rw [polar_symm_circle]
    by_cases h0 : 0 < p.1
    · have hd : circlePoint p.1 p.2 ∈ disk ↔ p.1 < 1 := by
        simp [disk,circlePoint_norm,abs_of_pos h0]
      by_cases h1 : p.1 < 1 <;> by_cases hθ : p.2 ∈ Ioo (-Real.pi) Real.pi <;>
        simp [Set.indicator,h0,h1,hθ,hd]
    · simp [Set.indicator,h0]
  rw [he,lintegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
  change (∫⁻ p in Ioo (0:ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
    ENNReal.ofReal p.1 * F (circlePoint p.1 p.2) ∂(volume.prod volume)) ≤ _
  rw [← Measure.prod_restrict]
  refine (lintegral_prod_le _).trans_eq ?_
  apply lintegral_congr
  intro r
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

lemma integrableOn_disk_of_circle_bound {F : ℂ → ℝ} (hF : ContinuousOn F disk)
    (hFn : ∀ z ∈ disk, 0 ≤ F z) {B : ℝ → ℝ}
    (hB : IntegrableOn B (Ioo (0:ℝ) 1))
    (hBn : ∀ r ∈ Ioo (0:ℝ) 1, 0 ≤ B r)
    (hbound : ∀ r ∈ Ioo (0:ℝ) 1,
      (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (F (circlePoint r θ))) ≤ ENNReal.ofReal (B r)) :
    IntegrableOn F disk := by
  refine ⟨hF.aestronglyMeasurable Metric.isOpen_ball.measurableSet,?_⟩
  have hn : ∀ᵐ z ∂(volume.restrict disk), 0 ≤ F z := ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet hFn
  apply (hasFiniteIntegral_iff_ofReal hn).mpr
  refine lt_of_le_of_lt (disk_lintegral_le_polar (fun z => ENNReal.ofReal (F z))) ?_
  refine lt_of_le_of_lt ?_ hB.hasFiniteIntegral
  apply setLIntegral_mono' measurableSet_Ioo
  intro r hr
  calc
    ENNReal.ofReal r * (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (F (circlePoint r θ))) ≤
        ENNReal.ofReal r * ENNReal.ofReal (B r) := mul_le_mul le_rfl (hbound r hr) zero_le zero_le
    _ ≤ ENNReal.ofReal (B r) := by
      exact mul_le_of_le_one_left zero_le (by exact_mod_cast hr.2.le)
    _ = ‖B r‖ₑ := by rw [Real.enorm_eq_ofReal (hBn r hr)]

lemma circle_lintegral_eq {F : ℂ → ℝ} {r : ℝ}
    (hc : Continuous (fun θ : ℝ => F (circlePoint r θ)))
    (hn : ∀ θ, 0 ≤ F (circlePoint r θ)) :
    (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (F (circlePoint r θ))) =
      ENNReal.ofReal (∫ θ in -Real.pi..Real.pi, F (circlePoint r θ)) := by
  rw [restrict_Ioo_eq_restrict_Ioc]
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  exact (ofReal_integral_eq_lintegral_ofReal
    (hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (Eventually.of_forall hn)).symm

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma continuousOn_deriv_univalent {f : ℂ → ℂ} (hf : UnivalentOn f disk) :
    ContinuousOn (deriv f) disk :=
  (hf.1.deriv Metric.isOpen_ball).continuousOn

lemma continuousOn_deriv_norm_rpow {f : ℂ → ℂ} (hf : UnivalentOn f disk) (t : ℝ) :
    ContinuousOn (fun z => ‖deriv f z‖^t) disk := by
  apply (continuousOn_deriv_univalent hf).norm.rpow_const
  intro z hz
  exact Or.inl (norm_ne_zero_iff.mpr (univalent_deriv_ne_zero Metric.isOpen_ball hf hz))

lemma integrableOn_boundary_rpow {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun r : ℝ => (1-r)^a) (Ioo (0:ℝ) 1) := by
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := (1:ℝ)) ha).comp_sub_left 1
  have hi' : IntervalIntegrable (fun r : ℝ => (1-r)^a) volume 0 1 := by
    simpa using hi.symm
  exact hi'.1.mono_set Ioo_subset_Ioc_self

lemma integrableOn_disk_of_power_circle_bound {F : ℂ → ℝ} (hF : ContinuousOn F disk)
    (hFn : ∀ z ∈ disk, 0 ≤ F z) {C a : ℝ} (hC : 0 ≤ C) (ha : -1 < a)
    (hbound : ∀ r : ℝ, 0 < r → r < 1 →
      (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (F (circlePoint r θ))) ≤
        ENNReal.ofReal (C*(1-r)^a)) :
    IntegrableOn F disk :=
  integrableOn_disk_of_circle_bound hF hFn ((integrableOn_boundary_rpow ha).const_mul C)
    (fun r hr => mul_nonneg hC (Real.rpow_nonneg (by linarith [hr.2]) _))
    (fun r hr => hbound r hr.1 hr.2)

lemma integrableOn_disk_boundary_power {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun z : ℂ => (1-‖z‖)^a) disk := by
  have hc : ContinuousOn (fun z : ℂ => (1-‖z‖)^a) disk := by
    apply (continuous_const.sub continuous_norm).continuousOn.rpow_const
    intro z hz
    exact Or.inl (ne_of_gt (by simpa [disk] using sub_pos.mpr (show ‖z‖ < 1 by simpa [disk] using hz)))
  apply integrableOn_disk_of_power_circle_bound hc
    (fun z hz => Real.rpow_nonneg (sub_nonneg.mpr (le_of_lt (by simpa [disk] using hz))) _) (C := 2*Real.pi)
    (by positivity) ha
  intro r hr hr1
  have he : (fun θ : ℝ => (1-‖circlePoint r θ‖)^a) = fun _ => (1-r)^a := by
    ext θ
    rw [circlePoint_norm,abs_of_pos hr]
  rw [circle_lintegral_eq (F := fun z => (1-‖z‖)^a) (r := r) (by rw [he]; exact continuous_const) (fun θ => Real.rpow_nonneg (by rw [circlePoint_norm,abs_of_pos hr]; linarith) _)]
  rw [he,intervalIntegral.integral_const]
  norm_num [smul_eq_mul]
  rw [show Real.pi + Real.pi = 2*Real.pi by ring]

lemma integrableOn_geometric_product {A B F : ℂ → ℝ} {s : Set ℂ} (hs : MeasurableSet s)
    (hA : IntegrableOn A s) (hB : IntegrableOn B s) (hF : AEStronglyMeasurable F (volume.restrict s))
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hAn : ∀ z ∈ s, 0 ≤ A z) (hBn : ∀ z ∈ s, 0 ≤ B z)
    (hEq : ∀ z ∈ s, F z = A z^q * B z^(1-q)) : IntegrableOn F s := by
  apply ((hA.const_mul q).add (hB.const_mul (1-q))).mono' hF
  apply ae_restrict_of_forall_mem hs
  intro z hz
  rw [hEq z hz,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
    (Real.rpow_nonneg (hAn z hz) _) (Real.rpow_nonneg (hBn z hz) _))]
  exact Real.geom_mean_le_arith_mean2_weighted hq (by linarith) (hAn z hz) (hBn z hz) (by ring)

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma schlicht_inverse_bound_small {f : ℂ → ℂ} (hf : Schlicht f) {z : ℂ}
    (hz : ‖z‖ ≤ 1/2) : ‖deriv f z‖^(-2:ℝ) ≤ 256 := by
  have hm : z ∈ disk := by simp only [disk,Metric.mem_ball,dist_zero_right]; linarith
  have hb := (schlicht_deriv_bounds hf hm).1
  have hp : (1+‖z‖)^3 ≤ (2:ℝ)^3 := pow_le_pow_left₀ (by positivity) (by linarith) _
  have hl : (1/16:ℝ) ≤ (1-‖z‖)/(1+‖z‖)^3 := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have he := Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ) < 1/16) (hl.trans hb) (by norm_num : (-2:ℝ) ≤ 0)
  norm_num at he
  simpa only [Real.rpow_neg (norm_nonneg _), Real.rpow_ofNat] using he

lemma inverse_square_bound_all (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℂ, Schlicht f → ∀ r : ℝ, 0 ≤ r → r < 1 →
      integralMean f (-2) r ≤ C*(1-r)^(-1-ε) := by
  obtain ⟨C,hC,hbound⟩ := uniform_inverse_square_bound ε hε
  refine ⟨C+256,by linarith,fun f hf r hr hr1 => ?_⟩
  have hd : 0 < 1-r := by linarith
  have hp : 1 ≤ (1-r)^(-1-ε) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd (by linarith) (by linarith)
  by_cases hrh : 1/2 ≤ r
  · exact (hbound f hf r hrh hr1).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hd.le _))
  · have hn (θ : ℝ) : ‖deriv f (circlePoint r θ)‖^(-2:ℝ) ≤ 256 :=
      schlicht_inverse_bound_small hf (by rw [circlePoint_norm,abs_of_nonneg hr]; linarith)
    have hi := intervalIntegral.integral_mono_on (a := -Real.pi) (b := Real.pi) (f := fun θ => ‖deriv f (circlePoint r θ)‖^(-2:ℝ))
      (g := fun _ => (256:ℝ)) (by linarith [Real.pi_pos])
      ((continuous_circle_deriv_rpow hf.1 hr hr1 (-2)).intervalIntegrable _ _)
      (intervalIntegrable_const (μ := volume)) (fun θ _ => hn θ)
    have hm : integralMean f (-2) r ≤ 256 := by
      change (2*Real.pi)⁻¹*(∫ θ in -Real.pi..Real.pi,‖deriv f (circlePoint r θ)‖^(-2:ℝ)) ≤ _
      have hh := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (by positivity : (0:ℝ) ≤ 2*Real.pi))
      refine hh.trans_eq ?_
      simp only [intervalIntegral.integral_const,smul_eq_mul]
      field_simp
      ring
    nlinarith

lemma weighted_inverse_integrable {f : ℂ → ℂ} (hf : Schlicht f) {α : ℝ} (hα : 0 < α) :
    IntegrableOn (fun z => (1-‖z‖)^α*‖deriv f z‖^(-2:ℝ)) disk := by
  obtain ⟨C,hC,hbound⟩ := inverse_square_bound_all (α/2) (by linarith)
  have hδ (z : ℂ) (hz : z ∈ disk) : 0 < 1-‖z‖ := by
    have hn : ‖z‖ < 1 := by simpa [disk] using hz
    linarith
  have hc : ContinuousOn (fun z : ℂ => (1-‖z‖)^α*‖deriv f z‖^(-2:ℝ)) disk :=
    ((continuous_const.sub continuous_norm).continuousOn.rpow_const (fun z hz => Or.inl (hδ z hz).ne')).mul
      (continuousOn_deriv_norm_rpow hf.1 _)
  apply integrableOn_disk_of_power_circle_bound hc
    (fun z hz => mul_nonneg (Real.rpow_nonneg (hδ z hz).le _) (Real.rpow_nonneg (norm_nonneg _) _))
    (C := 2*Real.pi*C) (a := α/2-1) (by positivity) (by linarith)
  intro r hr hr1
  have hd : 0 < 1-r := by linarith
  have he : (fun θ => (1-‖circlePoint r θ‖)^α*‖deriv f (circlePoint r θ)‖^(-2:ℝ)) =
      fun θ => (1-r)^α*‖deriv f (circlePoint r θ)‖^(-2:ℝ) := by
    ext θ
    rw [circlePoint_norm,abs_of_pos hr]
  rw [circle_lintegral_eq (F := fun z => (1-‖z‖)^α*‖deriv f z‖^(-2:ℝ)) (r := r) (by rw [he]; exact continuous_const.mul (continuous_circle_deriv_rpow hf.1 hr.le hr1 _))
    (fun θ => by rw [circlePoint_norm,abs_of_pos hr]; positivity),he,intervalIntegral.integral_const_mul]
  apply ENNReal.ofReal_le_ofReal
  have hmean : (∫ θ in -Real.pi..Real.pi,‖deriv f (circlePoint r θ)‖^(-2:ℝ)) =
      2*Real.pi*integralMean f (-2) r := by
    unfold integralMean circlePoint
    field_simp
    simp only [mul_comm Complex.I]
  rw [hmean]
  calc
    _ ≤ (1-r)^α*(2*Real.pi*(C*(1-r)^(-1-α/2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hbound f hf r hr.le hr1) (by positivity)) (by positivity)
    _ = 2*Real.pi*C*(1-r)^(α/2-1) := by
      have hp : (1-r)^α*(1-r)^(-1-α/2) = (1-r)^(α/2-1) := by
        rw [← Real.rpow_add hd]
        congr 1
        ring
      calc
        _ = (2*Real.pi*C)*((1-r)^α*(1-r)^(-1-α/2)) := by ring
        _ = _ := by rw [hp]

lemma schlicht_negative_area {f : ℂ → ℂ} (hf : Schlicht f) {t : ℝ}
    (ht : -2 < t) (ht0 : t < 0) : IntegrableOn (fun z => ‖deriv f z‖^t) disk := by
  let q : ℝ := -t/2
  let α : ℝ := (1-q)/(2*q)
  have hq : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hα : 0 < α := div_pos (by linarith) (by positivity)
  let A : ℂ → ℝ := fun z => (1-‖z‖)^α*‖deriv f z‖^(-2:ℝ)
  let B : ℂ → ℝ := fun z => (1-‖z‖)^(-1/2:ℝ)
  apply integrableOn_geometric_product Metric.isOpen_ball.measurableSet
    (A := A) (B := B) (weighted_inverse_integrable hf hα)
    (integrableOn_disk_boundary_power (by norm_num))
    ((continuousOn_deriv_norm_rpow hf.1 t).aestronglyMeasurable Metric.isOpen_ball.measurableSet)
    hq.le hq1.le
  · intro z hz
    dsimp [A]
    apply mul_nonneg
    · apply Real.rpow_nonneg
      have hn : ‖z‖ < 1 := by simpa [disk] using hz
      linarith
    · exact Real.rpow_nonneg (norm_nonneg _) _
  · intro z hz
    apply Real.rpow_nonneg
    have hn : ‖z‖ < 1 := by simpa [disk] using hz
    linarith
  · intro z hz
    have hn : ‖z‖ < 1 := by simpa [disk] using hz
    have hd : 0 < 1-‖z‖ := by linarith
    dsimp [A,B]
    rw [Real.mul_rpow (Real.rpow_nonneg hd.le _) (Real.rpow_nonneg (norm_nonneg _) _),
      ← Real.rpow_mul hd.le,← Real.rpow_mul (norm_nonneg _),← Real.rpow_mul hd.le]
    have he : α*q+(-1/2)*(1-q) = 0 := by
      dsimp [α]
      field_simp
      ring
    have htq : (-2:ℝ)*q = t := by dsimp [q]; ring
    rw [htq]
    calc
      _ = ‖deriv f z‖^t*1 := by ring
      _ = ‖deriv f z‖^t*((1-‖z‖)^(α*q)*(1-‖z‖)^((-1/2)*(1-q))) := by rw [← Real.rpow_add hd,he,Real.rpow_zero]
      _ = _ := by ring

end Brennan

end

end OAI
