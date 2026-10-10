import OAI.Probability.SLE.Gauge.UniformFrontPassage
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace OAI

/-! Positive affine rescaling of the physical one-step passage.  A mesh
`v` becomes `ell * v`; its normalized sausage mass is multiplied by
`ell ^ dimension κ`, exactly as in the width-rescaled ribbon statement. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal Pointwise

namespace SLEExactGauge.RibbonPassageScaling
open FirstFrontPassage PassageSuccess

/-- Translate and dilate the physical coordinates without changing the
curve parameter. -/
def affine (a : ℂ) (ell : ℝ) (z : ℂ) : ℂ := a + (ell : ℂ) * z

theorem affine_dist (a : ℂ) {ell : ℝ} (hell : 0 ≤ ell) (z w : ℂ) :
    dist (affine a ell z) (affine a ell w) = ell * dist z w := by
  simp only [affine, dist_eq_norm, add_sub_add_left_eq_sub, ← mul_sub, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hell]

theorem affine_bijective (a : ℂ) {ell : ℝ} (hell : 0 < ell) :
    Function.Bijective (affine a ell) := by
  have he : (ell : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hell.ne'
  constructor
  · intro z w h
    exact mul_left_cancel₀ he (add_left_cancel h)
  · intro z
    refine ⟨(z - a) / (ell : ℂ), ?_⟩
    dsimp [affine]
    field_simp
    ring

/-- Planar area scales by the square of the physical length scale, also
for sets for which no measurability has been assumed. -/
theorem affine_volume (a : ℂ) {ell : ℝ} (hell : 0 ≤ ell) (S : Set ℂ) :
    volume (affine a ell '' S) = ENNReal.ofReal (ell ^ 2) * volume S := by
  have he : affine a ell '' S = (fun z : ℂ => a + z) '' (ell • S) := by
    rw [← image_smul, image_image]
    rfl
  rw [he, image_add_left, measure_preimage_add, Measure.addHaar_smul_of_nonneg volume hell]
  rw [Complex.finrank_real_complex]

/-- The full sausage, including its intersection with a physical middle
strip, scales exactly under a positive affine map. -/
theorem sourceSausageSet_affine
    (a : ℂ) {ell : ℝ} (hell : 0 < ell) (γ : ℝ≥0 → ℂ) (s t : ℝ≥0) (v : ℝ) :
    sourceSausageSet (fun u => affine a ell (γ u)) s t (ell * v) =
      affine a ell '' sourceSausageSet γ s t v := by
  ext z
  obtain ⟨w, rfl⟩ := (affine_bijective a hell).2 z
  constructor
  · rintro ⟨u, hu, hd⟩
    rw [affine_dist a hell.le] at hd
    exact ⟨w, ⟨u, hu, (mul_lt_mul_iff_right₀ hell).mp hd⟩, rfl⟩
  · rintro ⟨w', ⟨u, hu, hd⟩, he⟩
    have hw' : w' = w := (affine_bijective a hell).1 he
    subst w'
    exact ⟨u, hu, by rw [affine_dist a hell.le]; exact mul_lt_mul_of_pos_left hd hell⟩

theorem segmentSausageCharge_affine
    (κ : ℝ) (a : ℂ) {ell : ℝ} (hell : 0 < ell)
    (γ : ℝ≥0 → ℂ) (s t : ℝ≥0) {v : ℝ} (hv : 0 < v) (R : Set ℂ) :
    segmentSausageCharge κ (fun u => affine a ell (γ u)) s t (ell * v)
        (affine a ell '' R) =
      ENNReal.ofReal (ell ^ dimension κ) * segmentSausageCharge κ γ s t v R := by
  have he : (ell * v) ^ (-codimension κ) * ell ^ 2 =
      ell ^ dimension κ * v ^ (-codimension κ) := by
    rw [Real.mul_rpow hell.le hv.le]
    calc
      ell ^ (-codimension κ) * v ^ (-codimension κ) * ell ^ 2 =
          (ell ^ (-codimension κ) * ell ^ (2 : ℝ)) * v ^ (-codimension κ) := by
            rw [Real.rpow_two]
            ring
      _ = ell ^ (-codimension κ + 2) * v ^ (-codimension κ) := by
        rw [Real.rpow_add hell]
      _ = _ := by congr 2; unfold codimension; ring
  simp only [segmentSausageCharge, sourceSausageSet_affine a hell]
  rw [← image_inter (affine_bijective a hell).1, affine_volume a hell.le]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg (mul_pos hell hv).le _), he,
    ENNReal.ofReal_mul (Real.rpow_nonneg hell.le _), mul_assoc]

/-- The prescribed mass threshold scales by `ell^d`. -/
theorem affine_mass_threshold_iff
    (κ : ℝ) (a : ℂ) {ell : ℝ} (hell : 0 < ell)
    (γ : ℝ≥0 → ℂ) (s t : ℝ≥0) {v : ℝ} (hv : 0 < v) (R : Set ℂ) (c : ℝ) :
    ENNReal.ofReal (c * ell ^ dimension κ) ≤
        segmentSausageCharge κ (fun u => affine a ell (γ u)) s t (ell * v)
          (affine a ell '' R) ↔
      ENNReal.ofReal c ≤ segmentSausageCharge κ γ s t v R := by
  rw [segmentSausageCharge_affine κ a hell γ s t hv R, mul_comm c,
    ENNReal.ofReal_mul (Real.rpow_pos_of_pos hell _).le]
  exact ENNReal.mul_le_mul_iff_right ((ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hell _)).ne')
    ENNReal.ofReal_ne_top

/-- Pulling back the longitudinal coordinate leaves the actual first-front
clock unchanged. Spatial rescaling does not change curve order. -/
theorem firstFrontTime_affine
    (a : ℂ) (ell : ℝ) (γ : ℝ≥0 → ℂ) (p p' : ℂ → ℝ)
    (hp : ∀ z, p' (affine a ell z) = p z) :
    firstFrontTime (fun t => p' (affine a ell (γ t))) 1 =
      firstFrontTime (fun t => p (γ t)) 1 := by
  congr 1
  funext t
  exact hp (γ t)

/-- Affine scaling preserves all actual front-success conditions, including
whole-prefix containment and the terminal offset. -/
theorem frontSuccess_affine_iff
    {Ω : Type*} (η : ℕ → Ω → ℝ≥0 → ℂ) (p p' : ℕ → ℂ → ℝ)
    (σ : Ω → ℝ≥0) (V : ℕ → Set ℂ) (b : ℕ → ℂ) (ε : ℝ)
    (a : ℂ) {ell : ℝ} (hell : 0 < ell) (n : ℕ)
    (hp : ∀ z, p' n (affine a ell z) = p n z) :
    FrontSuccess (fun j ω t => affine a ell (η j ω t)) p' σ
        (fun j => affine a ell '' V j) (fun j => affine a ell (b j)) (ell * ε) n =
      FrontSuccess η p σ V b ε n := by
  ext ω
  have hmaps (T : ℝ≥0) :
      MapsTo (fun t => affine a ell (η n ω t)) (Icc 0 T) (affine a ell '' V n) ↔
        MapsTo (η n ω) (Icc 0 T) (V n) := by
    constructor
    · intro h t ht
      obtain ⟨z, hz, he⟩ := h ht
      exact (affine_bijective a hell).1 he ▸ hz
    · intro h t ht
      exact mem_image_of_mem _ (h ht)
  have hterminal (T : ℝ≥0) :
      ‖affine a ell (η n ω T) - affine a ell (b n)‖ < ell * ε / 4 ↔
        ‖η n ω T - b n‖ < ε / 4 := by
    have hd := affine_dist a hell.le (η n ω T) (b n)
    rw [dist_eq_norm, dist_eq_norm] at hd
    rw [hd, mul_div_assoc, mul_lt_mul_iff_right₀ hell]
  simp only [FrontSuccess, mem_ofPred_eq, hp, hmaps, hterminal]

/-- The complete one-step event has the same probability after simultaneous
spatial, mesh and mass rescaling. This is a deterministic event identity;
the trace law need not itself have been scaled. -/
theorem frontSuccess_mass_probability_affine
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (η : ℕ → Ω → ℝ≥0 → ℂ) (p p' : ℕ → ℂ → ℝ)
    (σ : Ω → ℝ≥0) (V : ℕ → Set ℂ) (b : ℕ → ℂ) (ε : ℝ)
    (a : ℂ) {ell : ℝ} (hell : 0 < ell) (n : ℕ)
    (hp : ∀ z, p' n (affine a ell z) = p n z)
    (κ : ℝ) (R : Set ℂ) {v : ℝ} (hv : 0 < v) (c : ℝ) :
    P {ω | ω ∈ FrontSuccess (fun j ω t => affine a ell (η j ω t)) p' σ
          (fun j => affine a ell '' V j) (fun j => affine a ell (b j)) (ell * ε) n ∧
        ENNReal.ofReal (c * ell ^ dimension κ) ≤
          segmentSausageCharge κ (fun t => affine a ell (η n ω t)) (σ ω)
            (frontTime (fun t => p' n (affine a ell (η n ω t))) 1)
            (ell * v) (affine a ell '' R)} =
      P {ω | ω ∈ FrontSuccess η p σ V b ε n ∧ ENNReal.ofReal c ≤
        segmentSausageCharge κ (η n ω) (σ ω)
          (frontTime (fun t => p n (η n ω t)) 1) v R} := by
  congr 1
  ext ω
  have hevent := frontSuccess_affine_iff η p p' σ V b ε a hell n hp
  have ht : frontTime (fun t => p' n (affine a ell (η n ω t))) 1 =
      frontTime (fun t => p n (η n ω t)) 1 := by
    congr 1
    funext t
    exact hp (η n ω t)
  simp only [mem_ofPred_eq, hevent, ht,
    affine_mass_threshold_iff κ a hell (η n ω) (σ ω) _ hv R c]

end SLEExactGauge.RibbonPassageScaling

end

end OAI
