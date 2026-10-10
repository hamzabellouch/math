import OAI.Geometry.Perimeter.Regularity.EllipticOneScale
import OAI.Geometry.Perimeter.Regularity.EllipticC1Parts

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

theorem continuous_field_ball_memLp {W : Euc n → Euc n} (hW : Continuous W)
    (p : Euc n) (r : ℝ) : MemLp ((Metric.ball p r).indicator W) 2 volume := by
  rw [memLp_indicator_iff_restrict measurableSet_ball]
  apply (memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).mpr
  exact ((hW.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall p r)).mono_set
    Metric.ball_subset_closedBall

def cutFieldLp (W : Euc n → Euc n) (hW : Continuous W) (p : Euc n) (r : ℝ) : VectorL2 n :=
  (continuous_field_ball_memLp hW p r).toLp ((Metric.ball p r).indicator W)

theorem cutFieldLp_ae (W : Euc n → Euc n) (hW : Continuous W) (p : Euc n) (r : ℝ) :
    (cutFieldLp W hW p r : Euc n → Euc n)=ᵐ[volume] (Metric.ball p r).indicator W :=
  MemLp.coeFn_toLp _

theorem cutFieldLp_norm_sq (W : Euc n → Euc n) (hW : Continuous W) (p : Euc n) (r : ℝ) :
    ‖cutFieldLp W hW p r‖^2 = ∫ x in Metric.ball p r, ‖W x‖^2 := by
  rw [←vectorLp_integral_sq]
  calc
    (∫ x, ‖cutFieldLp W hW p r x‖^2) = ∫ x, (Metric.ball p r).indicator (fun x ↦ ‖W x‖^2) x := by
      apply integral_congr_ae
      filter_upwards [cutFieldLp_ae W hW p r] with x hx
      rw [hx]
      by_cases hb : x∈Metric.ball p r <;> simp [hb]
    _ = _ := integral_indicator measurableSet_ball

theorem cutFieldLp_pairing (W : Euc n → Euc n) (hW : Continuous W) (p : Euc n) (r : ℝ)
    {g : Euc n → Euc n} (hg : tsupport g ⊆ Metric.ball p r) :
    (∫ x, inner ℝ (cutFieldLp W hW p r x) (g x)) = ∫ x, inner ℝ (W x) (g x) := by
  apply integral_congr_ae
  filter_upwards [cutFieldLp_ae W hW p r] with x hx
  rw [hx]
  by_cases hb : x∈Metric.ball p r
  · simp [hb]
  · have hz : g x=0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hb (hg h))
    simp [hz]

theorem cutGradient_curlFree {f : Euc n → ℝ} (hf : ContDiff ℝ 1 f) (p : Euc n) (r : ℝ) :
    CurlFreeLpOn (cutFieldLp (gradient f) (gradient_continuous_C1 hf) p r) (Metric.ball p r) := by
  intro φ a b
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x, inner ℝ (cutFieldLp (gradient f) (gradient_continuous_C1 hf) p r x) (curlTestLp φ a b x)) =
        ∫ x, inner ℝ (cutFieldLp (gradient f) (gradient_continuous_C1 hf) p r x) (curlTest φ.val a b x) := by
      apply integral_congr_ae
      filter_upwards [curlTestLp_ae φ a b] with x hx
      rw [hx]
    _ = _ := cutFieldLp_pairing _ _ _ _ ((curlTest_tsupport _ _ _).trans φ.property.2.2)
    _ = 0 := C1_gradient_curl_pairing_zero hf φ a b

end RPISingularHarnack

end

end OAI
