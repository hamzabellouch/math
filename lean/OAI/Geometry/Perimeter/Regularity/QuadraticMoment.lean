import OAI.Geometry.Perimeter.Regularity.PhaseMomentLimit
import OAI.Geometry.Perimeter.Regularity.NormalWindowTest

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n : ℕ}

theorem exactFiberHeight_measurable {E : Set (Euc n)} (hE : MeasurableSet E)
    (v : Euc n) {b : ℝ} (hb : 0≤b) : Measurable (exactFiberHeight E v b) := by
  have hm : Measurable (fun z : normalPlane v × ℝ ↦
      E.indicator (fun _ ↦ (1:ℝ)) ((z.1:Euc n)+z.2•v)) :=
    (measurable_const.indicator hE).comp
      (((normalPlane v).subtypeL.continuous.comp continuous_fst).add
        (continuous_snd.smul continuous_const)).measurable
  have hi := hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (-b) b)) |>.measurable
  unfold exactFiberHeight
  simp_rw [intervalIntegral.integral_of_le (by linarith : -b≤b)]
  exact (measurable_const : Measurable (fun _ : normalPlane v ↦ -b)).add hi

theorem exactFiberHeight_norm_le {E : Set (Euc n)} (hE : MeasurableSet E)
    (v : Euc n) {b : ℝ} (hb : 0≤b) (y : normalPlane v) : ‖exactFiberHeight E v b y‖≤b := by
  apply interval_height_abs_le
    ((measurable_const.indicator hE).comp (continuous_const.add (continuous_id.smul continuous_const)).measurable)
    hb
  intro s
  by_cases hs : (y:Euc n)+s•v∈E <;> simp [hs]

theorem exactFiberMoment_integrable {E : Set (Euc n)} (hE : MeasurableSet E)
    (v : Euc n) {φ : normalPlane v → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    {b : ℝ} (hb : 0≤b) (k : ℕ) : Integrable (fun y ↦ φ y*(exactFiberHeight E v b y)^k) volume := by
  apply Integrable.mono' ((hφ.integrable_of_hasCompactSupport hcφ).norm.mul_const (b^k))
    ((hφ.measurable.mul ((exactFiberHeight_measurable hE v hb).pow_const k)).aestronglyMeasurable)
  exact ae_of_all _ fun y ↦ by
    dsimp only [Pi.mul_apply]
    rw [norm_mul,norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (exactFiberHeight_norm_le hE v hb y) k) (norm_nonneg _)

theorem normalWindowTest_integrableOn {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (v : Euc n) {φ : normalPlane v → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    {b R : ℝ} (hb : 0≤b) (hR : 0<R) (k : ℕ) :
    IntegrableOn (normalWindowTest v φ b k) (Metric.ball 0 R) (perimeterMeasure E) := by
  have : IsFiniteMeasure ((perimeterMeasure E).restrict (Metric.ball 0 R)) := ⟨by
    rw [Measure.restrict_apply_univ,perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 0 R hR⟩
  obtain ⟨M,hM⟩ := hcφ.exists_bound_of_continuous hφ
  exact (integrable_const (M*b^k)).mono' (normalWindowTest_measurable hφ b k).aestronglyMeasurable
    (ae_of_all _ (normalWindowTest_bound hM hb k))

theorem setIntegral_tsupport_mul {direction : Euc n} (φ f : normalPlane direction → ℝ) :
    (∫ y in tsupport φ, φ y*f y) = ∫ y, φ y*f y := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  rw [Function.notMem_support.mp (fun h ↦ hy (subset_closure h)),zero_mul]

def normalWindowQuadratic (v : Euc n) (φ w : normalPlane v → ℝ) (a b : ℝ)
    (x : Euc n) : ℝ :=
  {z:Euc n | |inner ℝ v z|≤b}.indicator
    (fun z ↦ φ (normalProjection v z)*(inner ℝ v z/a-w (normalProjection v z))^2) x

theorem normalWindowQuadratic_expand (v : Euc n) (φ w : normalPlane v → ℝ) (a b : ℝ) :
    normalWindowQuadratic v φ w a b = fun x ↦ (a⁻¹)^2*normalWindowTest v φ b 2 x -
      (2/a)*normalWindowTest v (fun y ↦ φ y*w y) b 1 x +
      normalWindowTest v (fun y ↦ φ y*(w y)^2) b 0 x := by
  funext x
  by_cases hx : |inner ℝ v x|≤b
  · simp only [normalWindowQuadratic,normalWindowTest,Set.indicator_apply,Set.mem_ofPred_eq,
      ite_eq_left hx,pow_one,pow_zero,mul_one]
    ring
  · simp [normalWindowQuadratic,normalWindowTest,hx]

theorem normalWindowQuadratic_integral_expand {E : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) (v : Euc n) {φ w : normalPlane v → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hw : Continuous w)
    {a b R : ℝ} (hb : 0≤b) (hR : 0<R) :
    (∫ x in Metric.ball 0 R, normalWindowQuadratic v φ w a b x ∂perimeterMeasure E) =
      (a⁻¹)^2*(∫ x in Metric.ball 0 R, normalWindowTest v φ b 2 x ∂perimeterMeasure E) -
      (2/a)*(∫ x in Metric.ball 0 R, normalWindowTest v (fun y ↦ φ y*w y) b 1 x ∂perimeterMeasure E) +
      ∫ x in Metric.ball 0 R, normalWindowTest v (fun y ↦ φ y*(w y)^2) b 0 x ∂perimeterMeasure E := by
  have hi2 := normalWindowTest_integrableOn hmin v hφ hcφ hb hR 2
  have hi1 := normalWindowTest_integrableOn hmin v (hφ.mul hw) (hcφ.mul_right) hb hR 1
  have hi0 := normalWindowTest_integrableOn hmin v (hφ.mul (hw.pow 2)) (hcφ.mul_right) hb hR 0
  change IntegrableOn (normalWindowTest v (fun y ↦ φ y*w y) b 1) _ _ at hi1
  change IntegrableOn (normalWindowTest v (fun y ↦ φ y*(w y)^2) b 0) _ _ at hi0
  simp only [normalWindowQuadratic_expand]
  have h := integral_add ((hi2.const_mul ((a⁻¹)^2)).sub (hi1.const_mul (2/a))) hi0
  simp only [Pi.sub_apply] at h
  rw [integral_sub (hi2.const_mul ((a⁻¹)^2)) (hi1.const_mul (2/a)),
    integral_const_mul,integral_const_mul] at h
  exact h

theorem exactFiberQuadratic_integral_expand {E : Set (Euc n)} (hE : MeasurableSet E)
    (v : Euc n) {φ w : normalPlane v → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hw : Continuous w)
    {a b : ℝ} (hb : 0≤b) :
    (∫ y, φ y*(exactFiberHeight E v b y/a-w y)^2) =
      (a⁻¹)^2*(∫ y, φ y*(exactFiberHeight E v b y)^2) -
      (2/a)*(∫ y, (φ y*w y)*exactFiberHeight E v b y) + ∫ y, φ y*(w y)^2 := by
  have hi2 := exactFiberMoment_integrable hE v hφ hcφ hb 2
  have hi1 := exactFiberMoment_integrable hE v (hφ.mul hw) (hcφ.mul_right) hb 1
  simp only [pow_one] at hi1
  have hi0 := (hφ.mul (hw.pow 2)).integrable_of_hasCompactSupport (μ := volume) (hcφ.mul_right)
  have he : (fun y ↦ φ y*(exactFiberHeight E v b y/a-w y)^2) = fun y ↦
      (a⁻¹)^2*(φ y*(exactFiberHeight E v b y)^2) - (2/a)*((φ y*w y)*exactFiberHeight E v b y) +
        φ y*(w y)^2 := by funext y; ring
  rw [he]
  simp only [Pi.mul_apply] at hi1 hi0
  have h := integral_add ((hi2.const_mul ((a⁻¹)^2)).sub (hi1.const_mul (2/a))) hi0
  simp only [Pi.sub_apply] at h
  rw [integral_sub (hi2.const_mul ((a⁻¹)^2)) (hi1.const_mul (2/a)),
    integral_const_mul,integral_const_mul] at h
  exact h

end RPISingularHarnack

end

end OAI
