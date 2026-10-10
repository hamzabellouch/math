import OAI.Geometry.Perimeter.Regularity.FiberHeight
import OAI.Geometry.Perimeter.Regularity.PlaneFiberCompactness
import OAI.Geometry.Perimeter.Regularity.PhaseMomentLimit
import OAI.Geometry.Perimeter.Regularity.NormalWindowTest

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace ContDiff
namespace RPISingularHarnack
open RPI.Boundary
variable {n m : ℕ}

theorem interval_negative_phase (b : ℝ) (hb : 0 ≤ b) :
    (∫ s in (-b)..b, {t : ℝ | t<0}.indicator (fun _ ↦ (1:ℝ)) s)=b := by
  have he : (fun s : ℝ ↦ {t : ℝ | t<0}.indicator (fun _ ↦ (1:ℝ)) s) =ᵐ[volume]
      (fun s : ℝ ↦ {t : ℝ | t≤0}.indicator (fun _ ↦ (1:ℝ)) s) := by
    filter_upwards [volume.ae_ne (0:ℝ)] with s hs
    have hh : s<0 ↔ s≤0 := lt_iff_le_and_ne.trans (and_iff_left hs)
    simp only [Set.indicator_apply,Set.mem_ofPred_eq,hh]
  rw [intervalIntegral.integral_congr_ae (he.mono (fun _ h _ ↦ h)),
    intervalIntegral.integral_indicator (show (0:ℝ) ∈ Icc (-b) b by constructor <;> linarith)]
  simp

theorem exactFiberHeight_eq_phase_integral {E : Set (Euc n)} (hE : MeasurableSet E)
    {v : Euc n} (hv : ‖v‖=1) {b : ℝ} (hb : 0 ≤ b) (y : normalPlane v) :
    exactFiberHeight E v b y = ∫ s in (-b)..b,
      (E.indicator (fun _ ↦ (1:ℝ)) ((y:Euc n)+s•v)-
        {z : Euc n | inner ℝ v z<0}.indicator (fun _ ↦ (1:ℝ)) ((y:Euc n)+s•v)) := by
  have hi : IntervalIntegrable (fun s : ℝ ↦ E.indicator (fun _ ↦ (1:ℝ))
      ((y:Euc n)+s•v)) volume (-b) b := by
    apply (intervalIntegrable_const (c := (1:ℝ))).mono_fun
      (((measurable_const.indicator hE).comp
        (continuous_const.add (continuous_id.smul continuous_const)).measurable).aestronglyMeasurable)
    exact ae_of_all _ fun s ↦ by by_cases h : (y:Euc n)+s•v ∈ E <;> simp [h]
  have hj : IntervalIntegrable (fun s : ℝ ↦ {t : ℝ | t<0}.indicator (fun _ ↦ (1:ℝ)) s)
      volume (-b) b := by
    apply (intervalIntegrable_const (c := (1:ℝ))).mono_fun
      ((measurable_const.indicator measurableSet_Iio).aestronglyMeasurable)
    exact ae_of_all _ fun s ↦ by by_cases h : s<0 <;> simp [h]
  have he (s : ℝ) : {z : Euc n | inner ℝ v z<0}.indicator (fun _ ↦ (1:ℝ))
      ((y:Euc n)+s•v) = {t : ℝ | t<0}.indicator (fun _ ↦ (1:ℝ)) s := by
    simp only [Set.indicator_apply,Set.mem_ofPred_eq,normal_fiber_inner hv]
  simp_rw [he]
  rw [intervalIntegral.integral_sub hi hj,interval_negative_phase b hb,exactFiberHeight]
  ring

theorem planeFiber_cutoff_eq_exact_ae {E : Set (Euc n)} (hE : MeasurableSet E)
    {v : Euc n} (hv : ‖v‖=1) {η : Euc n → ℝ} {a b R : ℝ}
    (ha : 0 ≤ a) (hab : a<b) (hηs : Function.support η ⊆ Metric.ball 0 R)
    (K : Set (normalPlane v))
    (hηone : ∀ y ∈ K, ∀ s : ℝ, |s|≤b → η ((y:Euc n)+s•v)=1)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x ∈ E ↔ inner ℝ v x<0)) :
    ∀ᵐ y : normalPlane v ∂volume, y ∈ K →
      planeFiber v (cutoffPhaseError E v η) y = exactFiberHeight E v b y := by
  have hp := (normalCoordinates_measurePreserving v hv).quasiMeasurePreserving.ae hphase
  change ∀ᵐ z : normalPlane v × ℝ ∂volume.prod volume, _ at hp
  have hpf := Measure.ae_ae_of_ae_prod hp
  filter_upwards [hpf] with y hy
  intro hyK
  rw [exactFiberHeight_eq_phase_integral hE hv (ha.trans hab.le) y,
    intervalIntegral.integral_of_le (by linarith : -b≤b),← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [hy] with s hs
  change ( (y:Euc n)+s•v ∈ Metric.ball 0 R → a < |inner ℝ v ((y:Euc n)+s•v)| →
      ((y:Euc n)+s•v ∈ E ↔ inner ℝ v ((y:Euc n)+s•v)<0)) at hs
  rw [normal_fiber_inner hv] at hs
  by_cases his : s ∈ Ioc (-b) b
  · have hsabs : |s|≤b := abs_le.mpr ⟨his.1.le,his.2⟩
    simp only [Set.indicator_of_mem his,cutoffPhaseError,hηone y hyK s hsabs,one_mul]
  · rw [Set.indicator_of_notMem his]
    by_cases hη : η ((y:Euc n)+s•v)=0
    · simp [cutoffPhaseError,hη]
    · have hxB := hηs hη
      have hsabs : a < |s| := by
        have hh : s≤-b ∨ b<s := by simpa only [Set.mem_Ioc,not_and_or,not_lt,not_le] using his
        rcases hh with hh | hh
        · exact hab.trans_le ((neg_le_abs s).trans' (by linarith))
        · exact hab.trans (hh.trans_le (le_abs_self s))
      have hq := hs hxB hsabs
      have hq' : ((y:Euc n)+s•v ∈ E ↔ (y:Euc n)+s•v ∈ {z | inner ℝ v z<0}) := by
        simpa only [Set.mem_ofPred_eq,normal_fiber_inner hv] using hq
      dsimp only [cutoffPhaseError]
      by_cases he : (y:Euc n)+s•v ∈ E
      · rw [Set.indicator_of_mem he,Set.indicator_of_mem (hq'.mp he),sub_self,mul_zero]
      · rw [Set.indicator_of_notMem he,Set.indicator_of_notMem (fun h ↦ he (hq'.mpr h)),
          sub_self,mul_zero]

theorem chartFiber_test_eq_exact {E : Set (Euc n)} (hE : MeasurableSet E)
    {v : Euc n} (hv : ‖v‖=1) (e : Euc m ≃ₗᵢ[ℝ] normalPlane v)
    {η : Euc n → ℝ} {a b R A : ℝ} (ha : 0 ≤ a) (hab : a<b)
    (hηs : Function.support η ⊆ Metric.ball 0 R) (φ : normalPlane v → ℝ)
    (hηone : ∀ y ∈ tsupport φ, ∀ s : ℝ, |s|≤b → η ((y:Euc n)+s•v)=1)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x ∈ E ↔ inner ℝ v x<0)) :
    (∫ y, chartFiber v e A (cutoffPhaseError E v η) y * φ (e y)) =
      A⁻¹ * ∫ y in tsupport φ, φ y*exactFiberHeight E v b y := by
  simp only [chartFiber,mul_assoc]
  rw [integral_const_mul]
  congr 1
  rw [e.measurePreserving.integral_comp e.toMeasurableEquiv.measurableEmbedding
    (fun y ↦ planeFiber v (cutoffPhaseError E v η) y * φ y)]
  rw [← integral_indicator (isClosed_tsupport φ).measurableSet]
  apply integral_congr_ae
  filter_upwards [planeFiber_cutoff_eq_exact_ae hE hv ha hab hηs (tsupport φ) hηone hphase]
    with y hy
  by_cases hs : y ∈ tsupport φ
  · rw [Set.indicator_of_mem hs,hy hs,mul_comm]
  · rw [Set.indicator_of_notMem hs,
      show φ y=0 from Function.notMem_support.mp (fun hh ↦ hs (subset_closure hh)),mul_zero]

end RPISingularHarnack

end

end OAI
