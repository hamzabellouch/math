import OAI.Geometry.Perimeter.Regularity.NormalizedHeight
import OAI.Geometry.Perimeter.Regularity.PlaneFiberCompactness
import OAI.Geometry.Perimeter.Regularity.CompactLpExtension
import OAI.Geometry.Perimeter.Regularity.NormalWindowTest

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace ContDiff
namespace RPISingularHarnack
open RPI.Boundary
variable {n m : ℕ}

theorem chartFiber_support {f : Euc n → ℝ} {v : Euc n}
    (e : Euc m ≃ₗᵢ[ℝ] normalPlane v) (a : ℝ) {R : ℝ}
    (hs : Function.support f ⊆ Metric.ball 0 R) :
    Function.support (chartFiber v e a f) ⊆ Metric.closedBall 0 R := by
  intro y hy
  by_contra hnot
  have hR : R < ‖y‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hnot
  have hz (s : ℝ) : f ((e y:Euc n)+s•v)=0 := by
    apply Function.notMem_support.mp
    intro hh
    have hb := hs hh
    rw [Metric.mem_ball,dist_zero_right] at hb
    have hp := (normalPlane v).norm_orthogonalProjectionOnto_apply_le ((e y:Euc n)+s•v)
    change ‖normalProjection v ((e y:Euc n)+s•v)‖ ≤ _ at hp
    rw [normalProjection_fiber,e.norm_map] at hp
    linarith
  exact hy (by simp [chartFiber,planeFiber,hz])

theorem chartFiber_normalized_mass {f : Euc n → ℝ} (hm : Measurable f)
    {v : Euc n} (hv : ‖v‖=1) (e : Euc m ≃ₗᵢ[ℝ] normalPlane v)
    {a V : ℝ} (ha : 0 < a)
    (hV : (∫⁻ x, ‖f x‖ₑ) ≤ ENNReal.ofReal (a*V)) :
    (∫⁻ y, ‖chartFiber v e a f y‖ₑ) ≤ ENNReal.ofReal V := by
  apply (chartFiber_lintegral_le hm hv e a).trans
  calc
    _ ≤ ENNReal.ofReal |a⁻¹| *ENNReal.ofReal (a*V) := mul_le_mul_right hV _
    _ = _ := by
      rw [abs_of_pos (inv_pos.mpr ha),← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp

theorem chartFiber_normalized_translation {f : Euc n → ℝ} (hm : Measurable f)
    (hi : Integrable f volume) {v : Euc n} (hv : ‖v‖=1)
    (e : Euc m ≃ₗᵢ[ℝ] normalPlane v) {a H : ℝ} (ha : 0 < a)
    (hhor : ∀ z, inner ℝ v z=0 →
      (∫⁻ x, ‖f (x+z)-f x‖ₑ) ≤ ENNReal.ofReal (‖z‖*(a*H))) (w : Euc m) :
    (∫⁻ y, ‖chartFiber v e a f (y+w)-chartFiber v e a f y‖ₑ) ≤
      ‖w‖ₑ * ENNReal.ofReal H := by
  apply (chartFiber_translation_le hm hi hv e a w).trans
  calc
    _ ≤ ENNReal.ofReal |a⁻¹| * ENNReal.ofReal (‖(e w:Euc n)‖*(a*H)) := by
      apply mul_le_mul_right
      exact hhor _ (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (e w).property)
    _ = _ := by
      rw [abs_of_pos (inv_pos.mpr ha),← ENNReal.ofReal_mul (by positivity)]
      change ENNReal.ofReal (a⁻¹*(‖e w‖*(a*H))) = _
      rw [e.norm_map,← ofReal_norm,← ENNReal.ofReal_mul (norm_nonneg _)]
      congr 1
      field_simp

theorem normalized_plane_height_subsequence
    (f : ℕ → Euc n → ℝ) (hm : ∀ i, Measurable (f i))
    {v : Euc n} (hv : ‖v‖=1) (e : Euc m ≃ₗᵢ[ℝ] normalPlane v)
    (a : ℕ → ℝ) (ha : ∀ i, 0 < a i) {R V H : ℝ} (hV : 0 ≤ V)
    (hs : ∀ i, Function.support (f i) ⊆ Metric.ball 0 R)
    (hmass : ∀ i, (∫⁻ x, ‖f i x‖ₑ) ≤ ENNReal.ofReal (a i*V))
    (hhor : ∀ i z, inner ℝ v z=0 →
      (∫⁻ x, ‖f i (x+z)-f i x‖ₑ) ≤ ENNReal.ofReal (‖z‖*(a i*H))) :
    ∃ g : Euc m → ℝ, Integrable g volume ∧ Function.support g ⊆ Metric.closedBall 0 R ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun i ↦ ∫⁻ y, ‖chartFiber v e (a (σ i)) (f (σ i)) y-g y‖ₑ) atTop (𝓝 0) := by
  have hi (i) : Integrable (f i) volume :=
    ⟨(hm i).aestronglyMeasurable,(hmass i).trans_lt ENNReal.ofReal_lt_top⟩
  have hig (i) := chartFiber_integrable (hi i) hv e (a i)
  apply compact_support_L1_subsequence (Metric.closedBall 0 R) (isCompact_closedBall _ _)
    (fun i ↦ chartFiber v e (a i) (f i)) (fun i ↦ chartFiber_measurable (hm i) v e (a i))
    hig (fun i ↦ chartFiber_support e (a i) (hs i)) V hV _
    (ENNReal.ofReal H) ENNReal.ofReal_ne_top _
  · intro i
    have h := chartFiber_normalized_mass (hm i) hv e (ha i) (hmass i)
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hig i)] at h
    exact (ENNReal.ofReal_le_ofReal_iff hV).mp h
  · intro i w
    exact chartFiber_normalized_translation (hm i) (hi i) hv e (ha i) (hhor i) w

theorem minimizing_plane_height_subsequence (hn : 1 < n)
    (E : ℕ → Set (Euc n)) (hmin : ∀ i, IsLocallyPerimeterMinimizing (E i))
    {v : Euc n} (hv : ‖v‖=1) (e : Euc m ≃ₗᵢ[ℝ] normalPlane v)
    {η : Euc n → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hb : ∀ x, ‖η x‖ ≤ 1) {R L P : ℝ} (hR : 0 < R) (hL : 0 ≤ L)
    (hs : tsupport η ⊆ Metric.ball 0 R)
    (hgrad : ∀ x ∈ Metric.ball 0 R, ‖gradient η x‖ ≤ L)
    (a : ℕ → ℝ) (ha : ∀ i, 0 < a i)
    (hheight : ∀ i x, x ∈ perimeterSupport (E i) ∩ Metric.ball 0 R → |inner ℝ v x| ≤ a i)
    (hper : ∀ i, (perimeter (E i) (Metric.ball 0 R)).toReal ≤ P)
    (hphase : ∀ i, ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a i < |inner ℝ v x| →
      (x ∈ E i ↔ inner ℝ v x < 0)) :
    ∃ g : Euc m → ℝ, Integrable g volume ∧ Function.support g ⊆ Metric.closedBall 0 R ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun i ↦ ∫⁻ y, ‖chartFiber v e (a (σ i))
          (cutoffPhaseError (E (σ i)) v η) y-g y‖ₑ) atTop (𝓝 0) := by
  let V := volume.real (Metric.ball (0:Euc n) (2*R))/R
  have hV : 0 ≤ V := div_nonneg measureReal_nonneg hR.le
  apply normalized_plane_height_subsequence (fun i ↦ cutoffPhaseError (E i) v η)
    (fun i ↦ cutoffPhaseError_measurable (hmin i).1 v hη.continuous.measurable)
    hv e a ha (H := L*(V+2*P)) hV
  · intro i
    exact (cutoffPhaseError_support (E i) v η).trans (subset_closure.trans hs)
  · intro i
    exact cutoffPhaseError_lintegral_height_le (hmin i).1 hv hη.continuous.measurable hb
      hR (ha i).le (subset_closure.trans hs) (hphase i)
  · intro i z hz
    apply (cutoffPhaseError_horizontal_translation_le hn (hmin i) hv hz hη hc hR hs
      (ha i).le hL (hheight i) hgrad (hphase i)).trans
    apply ENNReal.ofReal_le_ofReal
    have hai := (ha i).le
    have hp := mul_le_mul_of_nonneg_left (hper i) (by positivity : 0 ≤ ‖z‖*a i*L*2)
    dsimp only [V]
    nlinarith

end RPISingularHarnack

end

end OAI
