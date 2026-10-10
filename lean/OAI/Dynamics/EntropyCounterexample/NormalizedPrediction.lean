import OAI.Dynamics.EntropyCounterexample.AmbientRetraction
import OAI.Dynamics.EntropyCounterexample.PredictionDerivative

namespace OAI

noncomputable section

open scoped ContDiff

namespace Problem340.NormalizedPrediction

open AmbientRetraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {G : ℝ × E → ℝ × E}

theorem contDiffOn_iterate {n : ℕ∞ω} (hG : ContDiff ℝ n G)
    (hsphere : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖(G x).2‖ = 1) (m : ℕ) :
    ContDiffOn ℝ n ((G ∘ cylinder)^[m]) cylinderDomain := by
  induction m with
  | zero => exact contDiffOn_id
  | succ m hm =>
      rw [Function.iterate_succ']
      exact (contDiffOn_normalizedPredictor G hG).comp hm
        ((mapsTo_normalizedPredictor G hsphere).iterate m)

theorem norm_fderiv_iterate_le
    (hG : ContDiff ℝ 1 G)
    (hsphere : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖(G x).2‖ = 1)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖fderiv ℝ G x‖ ≤ B)
    (m : ℕ) (x : ℝ × E) (hx : x ∈ cylinderDomain) :
    ‖fderiv ℝ ((G ∘ cylinder)^[m]) x‖ ≤ (B * 4) ^ m := by
  apply (Prediction.differentiableAt_iterate_and_norm_le_on
    (fun y hy => ?_) (mapsTo_normalizedPredictor G hsphere)
    (mul_nonneg hB (by norm_num))
    (fun y hy => norm_fderiv_normalizedPredictor_le G hG hB hbound hy) m x hx).2
  exact ((contDiffOn_normalizedPredictor G hG).contDiffAt
    (isOpen_cylinderDomain.mem_nhds hy)).differentiableAt one_ne_zero

theorem norm_fderiv_iterate_le_scaled
    (hG : ContDiff ℝ 1 G)
    (hsphere : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖(G x).2‖ = 1)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖fderiv ℝ G x‖ ≤ B)
    (m : ℕ) (x : ℝ × E) (hx : x ∈ cylinderDomain) :
    ‖fderiv ℝ ((G ∘ cylinder)^[m]) x‖ ≤ 4 * B ^ m := by
  cases m with
  | zero =>
      have hid := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℝ × E)
      simpa only [Function.iterate_zero, fderiv_id, pow_zero, mul_one] using
        hid.trans (by norm_num : (1 : ℝ) ≤ 4)
  | succ m =>
      have hxpos : 0 < ‖x.2‖ := by
        change (1 / 2 : ℝ) < ‖x.2‖ at hx
        linarith
      have heq : ((G ∘ cylinder)^[m + 1]) =ᶠ[nhds x]
          (G^[m + 1] ∘ cylinder) := by
        filter_upwards [isOpen_cylinderDomain.mem_nhds hx] with y hy
        have hypos : 0 < ‖y.2‖ := by
          change (1 / 2 : ℝ) < ‖y.2‖ at hy
          linarith
        exact normalizedPredictor_iterate_succ_eq G hsphere (norm_pos_iff.mp hypos) m
      have hnorm : ‖(cylinder x).2‖ = 1 :=
        mem_sphere_zero_iff_norm.mp (normalize_mem_sphere (norm_pos_iff.mp hxpos))
      have hinv : Set.MapsTo G {y : ℝ × E | ‖y.2‖ = 1}
          {y : ℝ × E | ‖y.2‖ = 1} := hsphere
      obtain ⟨hd, hb⟩ := Prediction.differentiableAt_iterate_and_norm_le_on
        (fun y _ => hG.differentiable one_ne_zero y) hinv hB
        (fun y hy => hbound y hy) (m + 1) (cylinder x) hnorm
      rw [heq.fderiv_eq, fderiv_comp x hd
        ((contDiffAt_cylinder (n := 1) (norm_pos_iff.mp hxpos)).differentiableAt one_ne_zero)]
      calc
        ‖(fderiv ℝ (G^[m + 1]) (cylinder x)).comp (fderiv ℝ cylinder x)‖
            ≤ ‖fderiv ℝ (G^[m + 1]) (cylinder x)‖ * ‖fderiv ℝ cylinder x‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ B ^ (m + 1) * 4 := mul_le_mul hb (norm_fderiv_cylinder_le_four (le_of_lt hx))
          (norm_nonneg (fderiv ℝ (cylinder (E := E)) x)) (pow_nonneg hB _)
        _ = 4 * B ^ (m + 1) := mul_comm _ _

def clock (G : ℝ × E → ℝ × E) (m : ℕ) (x : ℝ × E) : ℝ :=
  ((G ∘ cylinder)^[m] x).1

theorem contDiffOn_clock {n : ℕ∞ω} (hG : ContDiff ℝ n G)
    (hsphere : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖(G x).2‖ = 1) (m : ℕ) :
    ContDiffOn ℝ n (clock G m) cylinderDomain :=
  (contDiffOn_iterate hG hsphere m).fst

theorem norm_fderiv_clock_le
    (hG : ContDiff ℝ 1 G)
    (hsphere : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖(G x).2‖ = 1)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖fderiv ℝ G x‖ ≤ B)
    (m : ℕ) (x : ℝ × E) (hx : x ∈ cylinderDomain) :
    ‖fderiv ℝ (clock G m) x‖ ≤ (B * 4) ^ m := by
  exact Prediction.norm_fderiv_projection_iterate_le_on
    (fun y hy => ((contDiffOn_normalizedPredictor G hG).contDiffAt
      (isOpen_cylinderDomain.mem_nhds hy)).differentiableAt one_ne_zero)
    (mapsTo_normalizedPredictor G hsphere) (mul_nonneg hB (by norm_num))
    (fun y hy => norm_fderiv_normalizedPredictor_le G hG hB hbound hy)
    (ContinuousLinearMap.fst ℝ ℝ E) (ContinuousLinearMap.norm_fst_le ..) m x hx

theorem norm_fderiv_clock_le_scaled
    (hG : ContDiff ℝ 1 G)
    (hsphere : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖(G x).2‖ = 1)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖fderiv ℝ G x‖ ≤ B)
    (m : ℕ) (x : ℝ × E) (hx : x ∈ cylinderDomain) :
    ‖fderiv ℝ (clock G m) x‖ ≤ 4 * B ^ m := by
  have hd := ((contDiffOn_iterate hG hsphere m).contDiffAt
    (isOpen_cylinderDomain.mem_nhds hx)).differentiableAt one_ne_zero
  change ‖fderiv ℝ ((ContinuousLinearMap.fst ℝ ℝ E) ∘ (G ∘ cylinder)^[m]) x‖ ≤ _
  rw [fderiv_comp x (ContinuousLinearMap.fst ℝ ℝ E).differentiableAt hd,
    (ContinuousLinearMap.fst ℝ ℝ E).fderiv]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    ‖ContinuousLinearMap.fst ℝ ℝ E‖ * ‖fderiv ℝ ((G ∘ cylinder)^[m]) x‖
        ≤ 1 * (4 * B ^ m) := mul_le_mul (ContinuousLinearMap.norm_fst_le ..)
          (norm_fderiv_iterate_le_scaled hG hsphere hB hbound m x hx)
          (norm_nonneg (fderiv ℝ ((G ∘ cylinder)^[m]) x)) (by norm_num)
    _ = 4 * B ^ m := one_mul _

theorem clock_eq_original_on_sphere
    (hsphere : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖(G x).2‖ = 1)
    {x : ℝ × E} (hx : ‖x.2‖ = 1) (m : ℕ) : clock G m x = (G^[m] x).1 := by
  unfold clock
  rw [normalizedPredictor_iterate_eq G hsphere hx m]

end Problem340.NormalizedPrediction

end

end OAI
