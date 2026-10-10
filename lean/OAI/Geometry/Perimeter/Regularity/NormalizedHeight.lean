import OAI.Geometry.Perimeter.Regularity.FiberCompactness
import OAI.Geometry.Perimeter.Regularity.FiberAveraging
import OAI.Geometry.Perimeter.Regularity.WindowAverage
import OAI.Geometry.Perimeter.Regularity.HeightCompactness

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Convolution
namespace RPISingularHarnack
open RPI.Boundary

def normalizedWindowHeight {n : ℕ} (v : Euc n) (T a : ℝ)
    (f : Euc n → ℝ) (x : Euc n) : ℝ := a⁻¹ * normalWindowAverage v T f x

theorem normalizedWindowHeight_measurable {n : ℕ} {f : Euc n → ℝ}
    (hf : Measurable f) (v : Euc n) (T a : ℝ) :
    Measurable (normalizedWindowHeight v T a f) :=
  (normalWindowAverage_stronglyMeasurable hf v T).measurable.const_mul _

theorem normalizedWindowHeight_lintegral_le {n : ℕ} {f : Euc n → ℝ}
    (hf : Measurable f) (v : Euc n) {T a V : ℝ} (ha : 0 < a)
    (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hm : (∫⁻ x, ‖f x‖ₑ) ≤ ENNReal.ofReal (a*V)) :
    (∫⁻ x, ‖normalizedWindowHeight v T a f x‖ₑ) ≤ ENNReal.ofReal (2*T*V) := by
  have he : (∫⁻ x, ‖normalizedWindowHeight v T a f x‖ₑ) =
      ENNReal.ofReal a⁻¹ * ∫⁻ x, ‖normalWindowAverage v T f x‖ₑ := by
    simp only [normalizedWindowHeight]
    simp_rw [enorm_mul]
    rw [show ‖a⁻¹‖ₑ = ENNReal.ofReal a⁻¹ by
      rw [← ofReal_norm,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]]
    exact lintegral_const_mul _ (normalWindowAverage_stronglyMeasurable hf v T).measurable.enorm
  rw [he]
  calc
    _ ≤ ENNReal.ofReal a⁻¹ * (ENNReal.ofReal (2*T) * ENNReal.ofReal (a*V)) :=
      mul_le_mul_right ((normalWindowAverage_lintegral_le hf v T).trans
        (mul_le_mul_right hm _)) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul' (mul_nonneg (mul_nonneg (by norm_num) hT) (mul_nonneg ha.le hV))]
      congr 1
      field_simp

theorem normalizedWindowHeight_integrable {n : ℕ} {f : Euc n → ℝ}
    (hf : Measurable f) (v : Euc n) {T a V : ℝ} (ha : 0 < a)
    (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hm : (∫⁻ x, ‖f x‖ₑ) ≤ ENNReal.ofReal (a*V)) :
    Integrable (normalizedWindowHeight v T a f) volume := by
  refine ⟨(normalizedWindowHeight_measurable hf v T a).aestronglyMeasurable, ?_⟩
  exact (normalizedWindowHeight_lintegral_le hf v ha hT hV hm).trans_lt ENNReal.ofReal_lt_top

theorem normalizedWindowHeight_translation_le {n : ℕ} {f : Euc n → ℝ}
    (hf : Measurable f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C)
    {v : Euc n} (hv : ‖v‖ = 1) {T a H V : ℝ} (ha : 0 < a)
    (hT : 0 ≤ T) (hH : 0 ≤ H) (hV : 0 ≤ V)
    (hm : (∫⁻ x, ‖f x‖ₑ) ≤ ENNReal.ofReal (a*V))
    (hh : ∀ z, inner ℝ v z = 0 →
      (∫⁻ x, ‖f (x+z)-f x‖ₑ) ≤ ENNReal.ofReal (‖z‖*(a*H))) (w : Euc n) :
    (∫⁻ x, ‖normalizedWindowHeight v T a f (x+w)-normalizedWindowHeight v T a f x‖ₑ) ≤
      ‖w‖ₑ * ENNReal.ofReal (4*T*H+4*V) := by
  have he : (∫⁻ x, ‖normalizedWindowHeight v T a f (x+w)-normalizedWindowHeight v T a f x‖ₑ) =
      ENNReal.ofReal a⁻¹ * ∫⁻ x, ‖normalWindowAverage v T f (x+w)-normalWindowAverage v T f x‖ₑ := by
    simp only [normalizedWindowHeight,← mul_sub]
    simp_rw [enorm_mul]
    rw [show ‖a⁻¹‖ₑ = ENNReal.ofReal a⁻¹ by
      rw [← ofReal_norm,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]]
    apply lintegral_const_mul
    exact (((normalWindowAverage_stronglyMeasurable hf v T).measurable.comp
      (measurable_id.add measurable_const)).sub
      (normalWindowAverage_stronglyMeasurable hf v T).measurable).enorm
  rw [he]
  calc
    _ ≤ ENNReal.ofReal a⁻¹ * ENNReal.ofReal (‖w‖*(4*T*(a*H)+4*(a*V))) :=
      mul_le_mul_right (normalWindowAverage_all_translation_le hf hb hv hT
        (by positivity) (by positivity) hm hh w) _
    _ = _ := by
      rw [← ofReal_norm,← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (norm_nonneg _)]
      congr 1
      field_simp

theorem normalizedWindowHeight_subsequence {n : ℕ}
    (K : Set (Euc n)) (hK : IsCompact K) (f : ℕ → Euc n → ℝ)
    (hm : ∀ i, Measurable (f i)) (C : ℝ) (hb : ∀ i x, ‖f i x‖ ≤ C)
    {v : Euc n} (hv : ‖v‖ = 1) {T H V : ℝ}
    (hT : 0 ≤ T) (hH : 0 ≤ H) (hV : 0 ≤ V)
    (a : ℕ → ℝ) (ha : ∀ i, 0 < a i)
    (hmass : ∀ i, (∫⁻ x, ‖f i x‖ₑ) ≤ ENNReal.ofReal (a i*V))
    (hhor : ∀ i z, inner ℝ v z = 0 →
      (∫⁻ x, ‖f i (x+z)-f i x‖ₑ) ≤ ENNReal.ofReal (‖z‖*(a i*H))) :
    ∃ hi : ∀ i, Integrable (normalizedWindowHeight v T (a i) (f i)) volume,
      ∃ g : Lp ℝ 1 (volume.comap (Subtype.val : K → Euc n)),
        ∃ σ : ℕ → ℕ, StrictMono σ ∧
          Tendsto (fun i ↦ compactFunctionLp K hK
            (normalizedWindowHeight v T (a (σ i)) (f (σ i))) (hi (σ i))) atTop (𝓝 g) := by
  have hi := fun i ↦ normalizedWindowHeight_integrable (hm i) v (ha i) hT hV (hmass i)
  refine ⟨hi, ?_⟩
  refine compactFunctionLp_subsequence_of_translation K hK _
    (fun i ↦ normalizedWindowHeight_measurable (hm i) v T (a i)) hi
    (2*T*V) (by positivity) ?_ (ENNReal.ofReal (4*T*H+4*V)) ENNReal.ofReal_ne_top ?_
  · intro i
    have h := normalizedWindowHeight_lintegral_le (hm i) v (ha i) hT hV (hmass i)
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hi i)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  · intro i w
    exact normalizedWindowHeight_translation_le (hm i) (hb i) hv (ha i) hT hH hV
      (hmass i) (hhor i) w

theorem normalWindowAverage_eq_normalFiberAverage {n : ℕ}
    {f : Euc n → ℝ} {v : Euc n} (hv : ‖v‖ = 1) {R T : ℝ}
    (hs : Function.support f ⊆ Metric.ball 0 R) (x : Euc n)
    (hT : R+‖x‖ ≤ T) :
    normalWindowAverage v T f x = normalFiberAverage v f x := by
  unfold normalWindowAverage normalFiberAverage
  apply integral_congr_ae
  apply ae_of_all
  intro s
  by_cases ht : s ∈ Icc (-T) T
  · simp [lineWindow,ht]
  · have hz : f (x+s•v) = 0 := by
      by_contra hz
      have hi := fiber_support_subset_interval hv hs x hz
      exact ht ((Icc_subset_Icc (by linarith) hT) hi)
    simp [hz]

theorem cutoffPhaseError_norm_le_one {n : ℕ} (E : Set (Euc n)) (v : Euc n)
    {η : Euc n → ℝ} (hη : ∀ x, ‖η x‖ ≤ 1) (x : Euc n) :
    ‖cutoffPhaseError E v η x‖ ≤ 1 := by
  unfold cutoffPhaseError
  rw [norm_mul]
  have h : ‖E.indicator (fun _ ↦ (1:ℝ)) x -
      {z | inner ℝ v z < 0}.indicator (fun _ ↦ (1:ℝ)) x‖ ≤ 1 := by
    by_cases he : x ∈ E <;> by_cases hh : inner ℝ v x < 0 <;> simp [he,hh]
  exact (mul_le_mul (hη x) h (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem cutoffPhaseError_lintegral_height_le {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) {v : Euc n} (hv : ‖v‖ = 1)
    {η : Euc n → ℝ} (hη : Measurable η) (hb : ∀ x, ‖η x‖ ≤ 1)
    {R a : ℝ} (hR : 0 < R) (ha : 0 ≤ a)
    (hs : Function.support η ⊆ Metric.ball 0 R)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x ∈ E ↔ inner ℝ v x < 0)) :
    (∫⁻ x, ‖cutoffPhaseError E v η x‖ₑ) ≤
      ENNReal.ofReal (a*(volume.real (Metric.ball (0:Euc n) (2*R))/R)) := by
  have hmass := slab_lintegral_bound (cutoffPhaseError_measurable hE v hη) hv ha hR
    ((cutoffPhaseError_support E v η).trans hs)
    (cutoffPhaseError_slab_bound E v η hs hb hphase)
  have hfinite : volume (Metric.ball (0:Euc n) (2*R)) ≠ ⊤ := measure_ball_lt_top.ne
  have hnorm : ENNReal.ofReal (a*(volume.real (Metric.ball (0:Euc n) (2*R))/R)) =
      (ENNReal.ofReal (2*a)*volume (Metric.ball (0:Euc n) (2*R))) / ENNReal.ofReal (2*R) := by
    rw [← ENNReal.ofReal_toReal hfinite]
    simp only [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*a),
      ← ENNReal.ofReal_div_of_pos (by positivity : 0 < 2*R)]
    congr 1
    change a*((volume (Metric.ball (0:Euc n) (2*R))).toReal/R) =
      2*a*(volume (Metric.ball (0:Euc n) (2*R))).toReal/(2*R)
    field_simp
  rw [hnorm]
  exact (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr (by positivity)).ne')
    (Or.inl ENNReal.ofReal_ne_top)).mpr
    (by simpa only [mul_comm] using hmass)

theorem minimizing_normalized_height_subsequence {n : ℕ} (hn : 1 < n)
    (K : Set (Euc n)) (hK : IsCompact K) (E : ℕ → Set (Euc n))
    (hmin : ∀ i, IsLocallyPerimeterMinimizing (E i))
    {v : Euc n} (hv : ‖v‖ = 1)
    {η : Euc n → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hb : ∀ x, ‖η x‖ ≤ 1) {R T L P : ℝ} (hR : 0 < R) (hT : 0 ≤ T)
    (hL : 0 ≤ L) (hP : 0 ≤ P) (hs : tsupport η ⊆ Metric.ball 0 R)
    (hgrad : ∀ x ∈ Metric.ball 0 R, ‖gradient η x‖ ≤ L)
    (a : ℕ → ℝ) (ha : ∀ i, 0 < a i)
    (hheight : ∀ i x, x ∈ perimeterSupport (E i) ∩ Metric.ball 0 R → |inner ℝ v x| ≤ a i)
    (hper : ∀ i, (perimeter (E i) (Metric.ball 0 R)).toReal ≤ P)
    (hphase : ∀ i, ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a i < |inner ℝ v x| →
      (x ∈ E i ↔ inner ℝ v x < 0)) :
    ∃ hi : ∀ i, Integrable (normalizedWindowHeight v T (a i) (cutoffPhaseError (E i) v η)) volume,
      ∃ g : Lp ℝ 1 (volume.comap (Subtype.val : K → Euc n)),
        ∃ σ : ℕ → ℕ, StrictMono σ ∧
          Tendsto (fun i ↦ compactFunctionLp K hK
            (normalizedWindowHeight v T (a (σ i)) (cutoffPhaseError (E (σ i)) v η))
              (hi (σ i))) atTop (𝓝 g) := by
  let V := volume.real (Metric.ball (0:Euc n) (2*R))/R
  have hV : 0 ≤ V := div_nonneg measureReal_nonneg hR.le
  apply normalizedWindowHeight_subsequence K hK (fun i ↦ cutoffPhaseError (E i) v η)
    (fun i ↦ cutoffPhaseError_measurable (hmin i).1 v hη.continuous.measurable)
    1 (fun i x ↦ cutoffPhaseError_norm_le_one (E i) v hb x) hv hT
    (H := L*(V+2*P)) (by positivity) hV a ha
  · intro i
    exact cutoffPhaseError_lintegral_height_le (hmin i).1 hv hη.continuous.measurable hb
      hR (ha i).le ((show Function.support η ⊆ tsupport η from subset_closure).trans hs) (hphase i)
  · intro i z hz
    apply (cutoffPhaseError_horizontal_translation_le hn (hmin i) hv hz hη hc hR hs
      (ha i).le hL (hheight i) hgrad (hphase i)).trans
    apply ENNReal.ofReal_le_ofReal
    have hai := (ha i).le
    have hp := mul_le_mul_of_nonneg_left (hper i) (by positivity : 0 ≤ ‖z‖*a i*L*2)
    dsimp [V]
    nlinarith

end RPISingularHarnack

end

end OAI
