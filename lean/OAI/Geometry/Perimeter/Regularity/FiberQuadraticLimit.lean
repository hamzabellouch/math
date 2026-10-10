import OAI.Geometry.Perimeter.Regularity.FiberLocalization
import OAI.Geometry.Perimeter.Regularity.QuadraticError
import OAI.Geometry.Perimeter.Regularity.WeightedSquareLimit

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n m : ℕ}

theorem chartFiber_cutoff_exact_ae {E : Set (Euc n)} (hE : MeasurableSet E)
    {v : Euc n} (hv : ‖v‖=1) (e : Euc m ≃ₗᵢ[ℝ] normalPlane v)
    {η : Euc n → ℝ} {a b R A : ℝ} (ha : 0≤a) (hab : a<b)
    (hηs : Function.support η ⊆ Metric.ball 0 R) (K : Set (normalPlane v))
    (hηone : ∀ y ∈ K, ∀ s : ℝ, |s|≤b → η ((y:Euc n)+s•v)=1)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x∈E ↔ inner ℝ v x<0)) :
    ∀ᵐ y : Euc m ∂volume, e y∈K → chartFiber v e A (cutoffPhaseError E v η) y =
      exactFiberHeight E v b (e y)/A := by
  have h := e.measurePreserving.quasiMeasurePreserving.ae
    (planeFiber_cutoff_eq_exact_ae hE hv ha hab hηs K hηone hphase)
  filter_upwards [h] with y hy
  intro hyK
  change A⁻¹*planeFiber v (cutoffPhaseError E v η) (e y) = _
  rw [hy hyK]
  ring

theorem chartFiber_quadratic_eq_exact {E : Set (Euc n)} (hE : MeasurableSet E)
    {v : Euc n} (hv : ‖v‖=1) (e : Euc m ≃ₗᵢ[ℝ] normalPlane v)
    {η : Euc n → ℝ} {a b R A : ℝ} (ha : 0≤a) (hab : a<b)
    (hηs : Function.support η ⊆ Metric.ball 0 R) (φ w : normalPlane v → ℝ)
    (hηone : ∀ y ∈ tsupport φ, ∀ s : ℝ, |s|≤b → η ((y:Euc n)+s•v)=1)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x∈E ↔ inner ℝ v x<0)) :
    (∫ y, φ (e y)*(chartFiber v e A (cutoffPhaseError E v η) y-w (e y))^2) =
      ∫ y, φ y*(exactFiberHeight E v b y/A-w y)^2 := by
  rw [← e.measurePreserving.integral_comp e.toMeasurableEquiv.measurableEmbedding
    (fun y ↦ φ y*(exactFiberHeight E v b y/A-w y)^2)]
  apply integral_congr_ae
  filter_upwards [chartFiber_cutoff_exact_ae hE hv e ha hab hηs (tsupport φ) hηone hphase]
    with y hy
  by_cases hφ : φ (e y)=0
  · simp only [hφ,zero_mul]
  · rw [hy (subset_closure hφ)]

theorem chartFiber_normalized_local_bound {E : Set (Euc n)} (hE : MeasurableSet E)
    {v : Euc n} (hv : ‖v‖=1) (e : Euc m ≃ₗᵢ[ℝ] normalPlane v)
    {η : Euc n → ℝ} {a R : ℝ} (ha : 0<a)
    (hηs : Function.support η ⊆ Metric.ball 0 R) (K : Set (normalPlane v))
    (hηone : ∀ y ∈ K, ∀ s : ℝ, |s|≤2*a → η ((y:Euc n)+s•v)=1)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x∈E ↔ inner ℝ v x<0)) :
    ∀ᵐ y : Euc m ∂volume, e y∈K → ‖chartFiber v e a (cutoffPhaseError E v η) y‖≤2 := by
  filter_upwards [chartFiber_cutoff_exact_ae hE hv e ha.le (by linarith : a<2*a)
    hηs K hηone hphase] with y hy
  intro hyK
  rw [hy hyK,norm_div,Real.norm_of_nonneg ha.le]
  exact (div_le_iff₀ ha).mpr (by simpa only [mul_comm] using exactFiberHeight_norm_le hE v (by positivity : 0≤2*a) (e y))

theorem cutoffPhaseError_integrable {E : Set (Euc n)} (hE : MeasurableSet E)
    (v : Euc n) {η : Euc n → ℝ} (hη : Continuous η) (hcη : HasCompactSupport η) :
    Integrable (cutoffPhaseError E v η) volume := by
  apply Integrable.mono' (hη.integrable_of_hasCompactSupport hcη).norm
    (cutoffPhaseError_measurable hE v hη.measurable).aestronglyMeasurable
  apply ae_of_all
  intro x
  dsimp only [cutoffPhaseError]
  rw [norm_mul]
  have hb : ‖E.indicator (fun _ ↦ (1:ℝ)) x - {z | inner ℝ v z<0}.indicator (fun _ ↦ (1:ℝ)) x‖≤1 := by
    by_cases he : x∈E <;> by_cases hh : inner ℝ v x<0 <;> simp [he,hh]
  simpa using mul_le_mul_of_nonneg_left hb (norm_nonneg (η x))

theorem minimizing_quadratic_height_trace_tendsto_zero (hn : 1<n)
    (E : ℕ → Set (Euc n)) (hmin : ∀ i, IsLocallyPerimeterMinimizing (E i))
    {v : Euc n} (hv : ‖v‖=1) (e : Euc m ≃ₗᵢ[ℝ] normalPlane v)
    {η : Euc n → ℝ} (hη : Continuous η) (hcη : HasCompactSupport η)
    (hηs : Function.support η ⊆ Metric.ball 0 4)
    (hηone : ∀ x ∈ Metric.ball (0:Euc n) 3, η x=1)
    (a : ℕ → ℝ) (ha : ∀ i, 0<a i) (hat : Tendsto a atTop (𝓝 0))
    (hh : ∀ i x, x ∈ perimeterSupport (E i) ∩ Metric.ball 0 4 → |inner ℝ v x|≤a i)
    (hphase : ∀ i, ∀ᵐ x ∂volume, x ∈ Metric.ball 0 4 → a i < |inner ℝ v x| →
      (x∈E i ↔ inner ℝ v x<0))
    (htilt : Tendsto (fun i ↦ orientedTilt (E i) v (Metric.ball 0 4)) atTop (𝓝 0))
    {g : Euc m → ℝ} (hg : Integrable g volume)
    (hL : Tendsto (fun i ↦ ∫⁻ y, ‖chartFiber v e (a i) (cutoffPhaseError (E i) v η) y-g y‖ₑ)
      atTop (𝓝 0))
    {φ w : normalPlane v → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (hpφ : ∀ y, 0≤φ y) (hsφ : tsupport φ ⊆ Metric.ball 0 1)
    (hw : Continuous w) (hwg : ∀ᵐ y : Euc m ∂volume, φ (e y)≠0 → w (e y)=g y) :
    Tendsto (fun i ↦ ∫ x in Metric.ball 0 4,
      normalWindowQuadratic v φ w (a i) (2*a i) x ∂perimeterMeasure (E i)) atTop (𝓝 0) := by
  obtain ⟨M₂,hM₂⟩ := hcφ.exists_bound_of_continuous hφ
  obtain ⟨M₁,hM₁⟩ := hcφ.mul_right.exists_bound_of_continuous (hφ.mul hw)
  obtain ⟨M₀,hM₀⟩ := hcφ.mul_right.exists_bound_of_continuous (hφ.mul (hw.pow 2))
  obtain ⟨B,hB⟩ := hcφ.exists_bound_of_continuousOn hw.continuousOn
  let B' := max B 0
  have hB' : 0≤B' := le_max_right _ _
  have haev : ∀ᶠ i in atTop, a i<1/2 := hat.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
  have hone (i) (hai : a i<1/2) : ∀ y ∈ tsupport φ, ∀ s : ℝ, |s|≤2*a i →
      η ((y:Euc n)+s•v)=1 := by
    intro y hy s hs
    apply hηone
    have hyb : ‖y‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using hsφ hy
    rw [Metric.mem_ball,dist_zero_right]
    have h := norm_add_le (y:Euc n) (s•v)
    rw [norm_smul,hv,mul_one,Real.norm_eq_abs] at h
    change ‖(y:Euc n)+s•v‖≤‖y‖+|s| at h
    linarith
  have hbf : ∀ᶠ i in atTop, ∀ᵐ y : Euc m ∂volume, φ (e y)≠0 →
      ‖chartFiber v e (a i) (cutoffPhaseError (E i) v η) y‖≤2 := by
    filter_upwards [haev] with i hai
    filter_upwards [chartFiber_normalized_local_bound (hmin i).1 hv e (ha i) hηs
      (tsupport φ) (hone i hai) (hphase i)] with y hy
    exact fun hh ↦ hy (subset_closure hh)
  have hplane := weighted_square_L1_tendsto_zero
    (fun i ↦ chartFiber v e (a i) (cutoffPhaseError (E i) v η))
    (fun i ↦ chartFiber_integrable (cutoffPhaseError_integrable (hmin i).1 v hη hcη) hv e (a i))
    hg (hw.comp e.continuous).aestronglyMeasurable (hφ.comp e.continuous).aestronglyMeasurable
    ((norm_nonneg _).trans (hM₂ 0)) (by norm_num : (0:ℝ)≤2) hB'
    (ae_of_all _ fun y ↦ hM₂ (e y)) hwg
    (ae_of_all _ fun y hy ↦ (hB (e y) (subset_closure hy)).trans (le_max_left _ _)) hbf hL
  have hplane' : Tendsto (fun i ↦ ∫ y, φ y*(exactFiberHeight (E i) v (2*a i) y/a i-w y)^2)
      atTop (𝓝 0) := by
    apply hplane.congr'
    filter_upwards [haev] with i hai
    exact chartFiber_quadratic_eq_exact (hmin i).1 hv e (ha i).le (by linarith [ha i])
      hηs φ w (hone i hai) (hphase i)
  have hdef : Tendsto (fun i ↦ (∫ x in Metric.ball 0 4,
      normalWindowQuadratic v φ w (a i) (2*a i) x ∂perimeterMeasure (E i))-
      (∫ y, φ y*(exactFiberHeight (E i) v (2*a i) y/a i-w y)^2)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) _
      (by simpa only [mul_zero] using htilt.const_mul (18*M₂+2*M₁+M₀/2))
    filter_upwards [haev] with i hai
    rw [Real.norm_eq_abs]
    apply actual_fiber_quadratic_error hn (hmin i) hv hφ hcφ hpφ hw hM₂ hM₁ hM₀
      (ha i) (show 0<a i/2 from div_pos (ha i) (by norm_num)) (by linarith [ha i]) (by norm_num)
      _ (hh i) (hphase i)
    intro y hy
    have hyb : ‖y‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using hsφ hy
    linarith
  simpa only [sub_add_cancel,add_zero] using hdef.add hplane'

end RPISingularHarnack

end

end OAI
