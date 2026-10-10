import OAI.Analysis.PlanarEndpoint.DualMass
import OAI.Analysis.PlanarEndpoint.Fourier
import OAI.Analysis.PlanarEndpoint.FrequencyWeak
import OAI.Analysis.PlanarEndpoint.GraphDual

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
namespace PlanarEndpoint

def affineScale (x₀ : Plane) (r : ℝ) (X : Plane) : Plane := x₀ + r • X

def scaledTime (x₀ : Plane) (t₀ r : ℝ) (T : Plane → ℝ) (X : Plane) : ℝ :=
  (T (affineScale x₀ r X) - t₀) / r^2

lemma measurable_affineScale (x₀ : Plane) (r : ℝ) : Measurable (affineScale x₀ r) := by
  unfold affineScale
  fun_prop

lemma measurable_scaledTime (x₀ : Plane) (t₀ r : ℝ) {T : Plane → ℝ}
    (hT : Measurable T) : Measurable (scaledTime x₀ t₀ r T) := by
  exact ((hT.comp (measurable_affineScale x₀ r)).sub measurable_const).div_const _

lemma integral_affineScale {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Plane → V) (x₀ : Plane) {r : ℝ} (hr : 0 < r) :
    (∫ x, f x) = r^2 • ∫ X, f (affineScale x₀ r X) := by
  change _ = r^2 • ∫ X, (fun x => f (x₀+x)) (r • X)
  rw [Measure.integral_comp_smul_of_nonneg (volume : Measure Plane) (fun x => f (x₀+x)) r (hR := hr.le)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, integral_add_left_eq_self,
    smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hr.ne'), one_smul]

lemma setIntegral_affineScale {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Plane → V) {E : Set Plane} (hE : MeasurableSet E)
    (x₀ : Plane) {r : ℝ} (hr : 0 < r) :
    (∫ x in E, f x) = r^2 • ∫ X in affineScale x₀ r ⁻¹' E, f (affineScale x₀ r X) := by
  rw [← integral_indicator hE, integral_affineScale _ x₀ hr]
  congr 1
  rw [← integral_indicator (hE.preimage (measurable_affineScale x₀ r))]
  apply integral_congr_ae
  filter_upwards [] with X
  by_cases hx : affineScale x₀ r X ∈ E <;> simp [hx]

lemma volumeReal_affineScale {E : Set Plane} (hE : MeasurableSet E)
    (x₀ : Plane) {r : ℝ} (hr : 0 < r) :
    volume.real E = r^2 * volume.real (affineScale x₀ r ⁻¹' E) := by
  simpa using setIntegral_affineScale (fun _ => (1 : ℝ)) hE x₀ hr

lemma phase_affineScale (x₀ X η : Plane) (t₀ s : ℝ) {r : ℝ} (hr : 0 < r) :
    phase (affineScale x₀ r X) (t₀+r^2*s) (r⁻¹ • η) =
      phase x₀ t₀ (r⁻¹ • η) * phase X s η := by
  have he : inner ℝ (x₀+r • X) (r⁻¹ • η) - (t₀+r^2*s)*‖r⁻¹ • η‖^2 =
      (inner ℝ x₀ (r⁻¹ • η) - t₀*‖r⁻¹ • η‖^2) +
        (inner ℝ X η - s*‖η‖^2) := by
    simp only [inner_add_left, inner_smul_left, inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_inv, abs_of_pos hr, starRingEnd_apply, star_trivial]
    field_simp
    ring
  unfold phase affineScale
  rw [he, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma graphDual_affineScale (χ : Plane → ℂ) {E : Set Plane} (hE : MeasurableSet E)
    (x₀ : Plane) (t₀ : ℝ) {r : ℝ} (hr : 0 < r)
    (T : Plane → ℝ) (w : Plane → ℂ) (η : Plane) :
    graphDual χ (volume.restrict E) T w (r⁻¹ • η) =
      (r^2 : ℝ) • (phase x₀ t₀ (r⁻¹ • η) *
        graphDual (fun ξ => χ (r⁻¹ • ξ)) (volume.restrict (affineScale x₀ r ⁻¹' E))
          (scaledTime x₀ t₀ r T) (w ∘ affineScale x₀ r) η) := by
  unfold graphDual graphFourier
  rw [setIntegral_affineScale _ hE x₀ hr]
  have he (X : Plane) : T (affineScale x₀ r X) =
      t₀ + r^2 * scaledTime x₀ t₀ r T X := by
    unfold scaledTime
    field_simp
    ring
  simp_rw [he, phase_affineScale x₀ _ η t₀ _ hr]
  have hprod : (fun X => w (affineScale x₀ r X) *
      (phase x₀ t₀ (r⁻¹ • η) * phase X (scaledTime x₀ t₀ r T X) η)) =
      (fun X => phase x₀ t₀ (r⁻¹ • η) *
        (w (affineScale x₀ r X) * phase X (scaledTime x₀ t₀ r T X) η)) := by
    funext X
    ring
  rw [hprod, integral_const_mul]
  simp only [Complex.real_smul, Function.comp_apply]
  ring

lemma graphLp_norm_sq_integral (χ : Plane → ℂ) (hχ : MemLp χ 2 volume)
    (μ : Measure Plane) [IsFiniteMeasure μ]
    (T : Plane → ℝ) (w : Plane → ℂ) (hT : Measurable T) (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) :
    ‖graphLp χ hχ μ T w hT hw hb‖^2 = ∫ ξ, ‖graphDual χ μ T w ξ‖^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [L2.inner_def, real_inner_self_eq_norm_sq]
  exact integral_congr_ae ((graphLp_ae χ hχ μ T w hT hw hb).fun_comp (fun z : ℂ => ‖z‖^2))

lemma norm_graphDual_affineScale (χ : Plane → ℂ) {E : Set Plane} (hE : MeasurableSet E)
    (x₀ : Plane) (t₀ : ℝ) {r : ℝ} (hr : 0 < r)
    (T : Plane → ℝ) (w : Plane → ℂ) (η : Plane) :
    ‖graphDual χ (volume.restrict E) T w (r⁻¹ • η)‖ = r^2 *
        ‖graphDual (fun ξ => χ (r⁻¹ • ξ)) (volume.restrict (affineScale x₀ r ⁻¹' E))
          (scaledTime x₀ t₀ r T) (w ∘ affineScale x₀ r) η‖ := by
  rw [graphDual_affineScale χ hE x₀ t₀ hr, norm_smul, norm_mul, norm_phase, one_mul]
  simp [Real.norm_eq_abs, abs_of_pos hr]

lemma graphLp_norm_sq_affineScale (χ : Plane → ℂ) (hχ : MemLp χ 2 volume)
    {E : Set Plane} (hE : MeasurableSet E) [IsFiniteMeasure (volume.restrict E)]
    (x₀ : Plane) (t₀ : ℝ) {r : ℝ} (hr : 0 < r)
    [IsFiniteMeasure (volume.restrict (affineScale x₀ r ⁻¹' E))]
    (T : Plane → ℝ) (w : Plane → ℂ) (hT : Measurable T) (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) :
    ‖graphLp χ hχ (volume.restrict E) T w hT hw hb‖^2 = r^2 *
      ‖graphLp (fun ξ => χ (r⁻¹ • ξ)) (memLp_comp_real_smul hχ (inv_ne_zero hr.ne'))
        (volume.restrict (affineScale x₀ r ⁻¹' E))
        (scaledTime x₀ t₀ r T) (w ∘ affineScale x₀ r)
        (measurable_scaledTime x₀ t₀ r hT) (hw.comp (measurable_affineScale x₀ r))
        (fun point => hb (affineScale x₀ r point))‖^2 := by
  rw [graphLp_norm_sq_integral, graphLp_norm_sq_integral]
  have he := Measure.integral_comp_inv_smul_of_nonneg volume
    (fun ξ => ‖graphDual χ (volume.restrict E) T w ξ‖^2) hr.le
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul,
    norm_graphDual_affineScale χ hE x₀ t₀ hr T w] at he
  simp_rw [mul_pow] at he
  rw [integral_const_mul] at he
  nlinarith [sq_pos_of_pos hr]

lemma affineScale_preimage_ball {E : Set Plane} {x₀ : Plane} {r : ℝ}
    (hr : 0 < r) (hE : E ⊆ Metric.ball x₀ r) :
    affineScale x₀ r ⁻¹' E ⊆ Metric.ball (0 : Plane) 1 := by
  intro X hX
  have hx := hE hX
  have he : affineScale x₀ r X - x₀ = r • X := by unfold affineScale; abel
  rw [Metric.mem_ball, dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos hr] at hx
  simpa using (mul_lt_mul_iff_right₀ hr).mp (show r*‖X‖ < r*1 by simpa using hx)

lemma annular_support_rescale {χ : Plane → ℂ} {c₀ C₀ N r : ℝ} (hr : 0 < r)
    (hs : ∀ᵐ ξ : Plane ∂volume,
      ξ ∉ {ξ | c₀*N ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ C₀*N} → χ ξ = 0) :
    ∀ᵐ η : Plane ∂volume,
      η ∉ {η | c₀*(N*r) ≤ ‖η‖ ∧ ‖η‖ ≤ C₀*(N*r)} → χ (r⁻¹ • η) = 0 := by
  have h := (Measure.quasiMeasurePreserving_smul volume (r := r⁻¹)
    (inv_ne_zero hr.ne')).ae hs
  filter_upwards [h] with η hη hn
  apply hη
  intro hh
  apply hn
  rcases hh with ⟨h1,h2⟩
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr] at h1 h2
  have h1' := mul_le_mul_of_nonneg_left h1 hr.le
  have h2' := mul_le_mul_of_nonneg_left h2 hr.le
  simp only [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at h1' h2'
  constructor <;> nlinarith

lemma rpow_mass_sq_le {p m M : ℝ} (hp : 2 < p) (hm : 0 ≤ m) (hM : m ≤ M) :
    (m^(1-1/p))^2 ≤ M^(1-2/p)*m := by
  have hp0 : 0 < p := by linarith
  have hql : 0 < 1-1/p := by have := (div_lt_iff₀ hp0).2 (show 1 < 1*p by linarith); linarith
  have hq : 0 ≤ 1-2/p := by have := (div_lt_iff₀ hp0).2 (show 2 < 1*p by linarith); linarith
  rcases hm.eq_or_lt with hm0 | hmpos
  · rw [← hm0]
    rw [Real.zero_rpow hql.ne']
    simp
  · rw [← Real.rpow_two, ← Real.rpow_mul hm,
      show (1-1/p)*2 = (1-2/p)+1 by ring, Real.rpow_add hmpos, Real.rpow_one]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hm hM hq) hm

lemma graph_ball_bound_of_shortTime {c₀ C₀ p : ℝ} (hp : 2 < p)
    (hshort : ShortTimeWeakEstimate c₀ C₀ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ l : ℕ, ∀ (N r : ℝ), 0 < r → N*r=(2:ℝ)^l →
      ∀ (χ : Plane → ℂ) (_ : Measurable χ) (hχ : MemLp χ 2 volume)
      (B : ℝ), 0 ≤ B → (∀ ξ, ‖χ ξ‖ ≤ B) →
      (∀ᵐ ξ : Plane ∂volume, ξ ∉ {ξ | c₀*N ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ C₀*N} → χ ξ = 0) →
      ∀ (x₀ : Plane) (t₀ s : ℝ), 0 ≤ s → s ≤ r^2/((2:ℝ)^l) →
      ∀ (E : Set Plane), MeasurableSet E → E ⊆ Metric.ball x₀ r →
      ∀ (T : Plane → ℝ) (w : Plane → ℂ) (hT : Measurable T) (hw : Measurable w)
      (hb : ∀ x, ‖w x‖ ≤ 1), (∀ x ∈ E, T x ∈ Icc t₀ (t₀+s)) →
      ∀ [IsFiniteMeasure (volume.restrict E)],
      ‖graphLp χ hχ (volume.restrict E) T w hT hw hb‖^2 ≤
        C*B^2*((2:ℝ)^l)^(2/3:ℝ)*volume.real E := by
  obtain ⟨K,hK,hbnd⟩ := graph_mass_bound_of_shortTime (show 1 < p by linarith) hshort
  refine ⟨K^2*Real.pi^(1-2/p), mul_pos (sq_pos_of_pos hK) (Real.rpow_pos_of_pos Real.pi_pos _), ?_⟩
  intro l N r hr hNr χ hχm hχ B hB hχB hχs x₀ t₀ s hs hs' E hE hEB T w hT hw hb hTs inst
  let F := affineScale x₀ r ⁻¹' E
  have hF : MeasurableSet F := hE.preimage (measurable_affineScale x₀ r)
  have hFB : F ⊆ Metric.ball (0 : Plane) 1 := affineScale_preimage_ball hr hEB
  let : IsFiniteMeasure (volume.restrict F) := isFiniteMeasure_restrict.2
    ((measure_mono hFB).trans_lt measure_ball_lt_top).ne
  have hFs : ∀ X ∈ F, scaledTime x₀ t₀ r T X ∈ Icc 0 (0+s/r^2) := by
    intro X hX
    rcases hTs _ hX with ⟨h1,h2⟩
    dsimp [scaledTime]
    constructor
    · exact div_nonneg (sub_nonneg.mpr h1) (sq_nonneg r)
    · simp only [zero_add]
      exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg r)
  have htime : s/r^2 ≤ ((2:ℝ)^l)⁻¹ := by
    rw [div_le_iff₀ (sq_pos_of_pos hr)]
    simpa [div_eq_mul_inv, mul_comm] using hs'
  have hscl := annular_support_rescale hr hχs
  rw [hNr] at hscl
  have hsc := memLp_comp_real_smul hχ (inv_ne_zero hr.ne')
  have hm : ‖graphLp (fun ξ => χ (r⁻¹ • ξ)) hsc (volume.restrict F)
      (scaledTime x₀ t₀ r T) (w ∘ affineScale x₀ r)
      (measurable_scaledTime x₀ t₀ r hT) (hw.comp (measurable_affineScale x₀ r))
      (fun X => hb _)‖ ≤ K*B*((2:ℝ)^l)^(1/3:ℝ)*(volume.real F)^(1-1/p) :=
    hbnd l _ (hχm.comp (measurable_const_smul _)) hsc B hB (fun ξ => hχB _) hscl
      0 0 (s/r^2) (div_nonneg hs (sq_nonneg r)) htime F hF hFB _ _
      (measurable_scaledTime x₀ t₀ r hT) (hw.comp (measurable_affineScale x₀ r))
      (fun X => hb _) hFs
  have hm0 : 0 ≤ volume.real F := ENNReal.toReal_nonneg
  have hmπ : volume.real F ≤ Real.pi := by
    apply le_trans (measureReal_mono hFB)
    simp [measureReal_def, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_ofReal Real.pi_nonneg]
  have hpow := rpow_mass_sq_le hp hm0 hmπ
  have hmsq := (sq_le_sq₀ (norm_nonneg _) (show 0 ≤ K*B*((2:ℝ)^l)^(1/3:ℝ)*
      (volume.real F)^(1-1/p) by positivity)).2 hm
  simp only [mul_pow] at hmsq
  have hfreq : (((2:ℝ)^l)^(1/3:ℝ))^2 = ((2:ℝ)^l)^(2/3:ℝ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [hfreq] at hmsq
  have hmsq' := hmsq.trans (mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ K^2*B^2*((2:ℝ)^l)^(2/3:ℝ) by positivity))
  rw [graphLp_norm_sq_affineScale χ hχ hE x₀ t₀ hr T w hT hw hb]
  have hmE := volumeReal_affineScale hE x₀ hr
  change volume.real E = r^2 * volume.real F at hmE
  calc
    _ ≤ r^2*(K^2*B^2*((2:ℝ)^l)^(2/3:ℝ)*(Real.pi^(1-2/p)*volume.real F)) :=
      mul_le_mul_of_nonneg_left hmsq' (sq_nonneg r)
    _ = _ := by rw [hmE]; ring

end PlanarEndpoint
end

end OAI
