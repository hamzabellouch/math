import OAI.MathematicalPhysics.Boltzmann.Collision.SheetMixtures

namespace OAI

section

/-!
# Algebraic reduction of the quadratic hot gain

Symmetry allows the output polynomial weight to be assigned to either
incoming velocity. The resulting mixed gain has only one polynomial factor,
while its two Gaussian factors cancel by collision energy conservation.
-/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotWeight

def G (q : ℝ) (v : Velocity) : ℝ := Real.exp (-‖v‖ ^ 2) * W q v

def polynomial (v : Velocity) : ℝ := (1 + ‖v‖ ^ 2) ^ (50 : ℕ)

theorem G_pos (q : ℝ) (v : Velocity) : 0 < G q v :=
  mul_pos (Real.exp_pos _) (W_pos q v)

theorem polynomial_pos (v : Velocity) : 0 < polynomial v := by
  unfold polynomial
  positivity

theorem H_mul_polynomial (q : ℝ) (v : Velocity) : H q v * polynomial v = G q v := by
  unfold H polynomial G
  change Real.exp (-‖v‖ ^ 2) * (1 + ‖v‖ ^ 2) ^ (-50 : ℝ) * W q v *
    (1 + ‖v‖ ^ 2) ^ (50 : ℕ) = _
  rw [show (-50 : ℝ) = -(50 : ℕ) by norm_num,
    Real.rpow_neg (by positivity), Real.rpow_natCast]
  have hp : (1 + ‖v‖ ^ 2) ^ (50 : ℕ) ≠ 0 := by positivity
  field_simp

theorem H_eq_G_div (q : ℝ) (v : Velocity) : H q v = G q v / polynomial v :=
  (eq_div_iff (polynomial_pos v).ne').mpr (H_mul_polynomial q v)

theorem measurable_G (q : ℝ) : Measurable (G q) := by
  unfold G
  have he : Measurable (fun v : Velocity => Real.exp (-‖v‖ ^ 2)) := by fun_prop
  exact he.mul (ChartKernel.measurable_W q)

/-- The fixed manuscript exponent `m = 100` needs only this two-input estimate. -/
theorem polynomial_pair_bound (p ξ v : Velocity)
    (hv : ‖v‖ ^ 2 ≤ ‖p‖ ^ 2 + ‖ξ‖ ^ 2) :
    polynomial v ≤ (2 : ℝ) ^ (50 : ℕ) * (polynomial p + polynomial ξ) := by
  by_cases h : ‖ξ‖ ^ 2 ≤ ‖p‖ ^ 2
  · have hb : 1 + ‖v‖ ^ 2 ≤ 2 * (1 + ‖p‖ ^ 2) := by linarith
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖v‖ ^ 2) hb 50
    rw [mul_pow] at hp
    exact hp.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (polynomial_pos ξ).le) (by positivity))
  · have hb : 1 + ‖v‖ ^ 2 ≤ 2 * (1 + ‖ξ‖ ^ 2) := by linarith
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖v‖ ^ 2) hb 50
    rw [mul_pow] at hp
    exact hp.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (polynomial_pos p).le) (by positivity))

/-- The quadratic integrand is bounded by a symmetric mixed integrand. -/
theorem quadratic_ratio_bound (q : ℝ) (p ξ v : Velocity)
    (hv : ‖v‖ ^ 2 ≤ ‖p‖ ^ 2 + ‖ξ‖ ^ 2) :
    H q p * H q ξ / H q v ≤ (2 : ℝ) ^ (50 : ℕ) *
      ((H q p * G q ξ + G q p * H q ξ) / G q v) := by
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (H_pos q v) (G_pos q v)).mpr
  have h := mul_le_mul_of_nonneg_left (polynomial_pair_bound p ξ v hv)
    (mul_nonneg (mul_nonneg (H_nonneg q p) (H_nonneg q ξ)) (H_nonneg q v))
  rw [← H_mul_polynomial q p, ← H_mul_polynomial q ξ, ← H_mul_polynomial q v]
  convert h using 1 <;> ring

theorem quadratic_product_bound (q : ℝ) (p ξ v : Velocity)
    (hv : ‖v‖ ^ 2 ≤ ‖p‖ ^ 2 + ‖ξ‖ ^ 2) :
    H q p * H q ξ ≤ (2 : ℝ) ^ (50 : ℕ) * (H q v / G q v) *
      (H q p * G q ξ + G q p * H q ξ) := by
  calc
    _ ≤ ((2 : ℝ) ^ (50 : ℕ) *
        ((H q p * G q ξ + G q p * H q ξ) / G q v)) * H q v :=
      (div_le_iff₀ (H_pos q v)).mp (quadratic_ratio_bound q p ξ v hv)
    _ = _ := by ring

/-- Both Gaussian factors cancel against the output Gaussian on the collision plane. -/
theorem mixed_plane_weight (q : ℝ) (p ξ v : Velocity)
    (h : inner ℝ (v - p) (ξ - v) = 0) :
    H q p * (G q ξ / G q v) =
      Real.exp (-‖companionVelocity p ξ v‖ ^ 2) * (polynomial p)⁻¹ *
        (W q p * W q ξ / W q v) := by
  have hr : G q ξ / G q v =
      Real.exp (‖p‖ ^ 2 - ‖companionVelocity p ξ v‖ ^ 2) * (W q ξ / W q v) := by
    unfold G
    rw [mul_div_mul_comm, carleman_gaussian_ratio p ξ v h]
  rw [H_eq_G_div q p, hr]
  unfold G
  have he : Real.exp (-‖p‖ ^ 2) *
      Real.exp (‖p‖ ^ 2 - ‖companionVelocity p ξ v‖ ^ 2) =
      Real.exp (-‖companionVelocity p ξ v‖ ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-‖p‖ ^ 2) *
          Real.exp (‖p‖ ^ 2 - ‖companionVelocity p ξ v‖ ^ 2)) *
        (polynomial p)⁻¹ * (W q p * W q ξ / W q v) := by ring
    _ = _ := by rw [he]

end BoltzmannNonuniqueness.HotWeight

end

end

section

/-! # Polynomial decay on collision shells

Eight powers suffice after the five-dimensional geometric estimate;
the manuscript's fixed polynomial exponent fifty supplies these powers.
-/

noncomputable section

open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.HotWeight

namespace BoltzmannNonuniqueness.HotShellWeight

def constant : ℝ := 4 ^ (8 : ℕ) + 4 ^ (4 : ℕ) * Nat.factorial 4

theorem constant_pos : 0 < constant := by norm_num [constant]

theorem polynomial_eighth_bound (p : Velocity) {u : ℝ}
    (hu : 0 ≤ u) (hp : u ≤ ‖p‖) : u ^ 8 ≤ polynomial p := by
  have h₂ : u ^ 2 ≤ 1 + ‖p‖ ^ 2 := by nlinarith [norm_nonneg p]
  have h₄ := pow_le_pow_left₀ (sq_nonneg u) h₂ 4
  have h₅₀ : (1 + ‖p‖ ^ 2) ^ (4 : ℕ) ≤ (1 + ‖p‖ ^ 2) ^ (50 : ℕ) :=
    pow_le_pow_right₀ (by nlinarith [sq_nonneg ‖p‖]) (by norm_num)
  calc
    u ^ 8 = (u ^ 2) ^ 4 := by ring
    _ ≤ (1 + ‖p‖ ^ 2) ^ (4 : ℕ) := h₄
    _ ≤ polynomial p := h₅₀

theorem polynomial_inv_le_one (p : Velocity) : (polynomial p)⁻¹ ≤ 1 := by
  apply inv_le_one_of_one_le₀
  exact one_le_pow₀ (by nlinarith [sq_nonneg ‖p‖])

theorem gaussian_eighth_bound (R : ℝ) :
    R ^ 8 * Real.exp (-R ^ 2 / 4) ≤ 4 ^ (4 : ℕ) * Nat.factorial 4 := by
  have h := Real.pow_div_factorial_le_exp (R ^ 2 / 4) (by positivity) 4
  have he : Real.exp (R ^ 2 / 4) * Real.exp (-R ^ 2 / 4) = 1 := by
    rw [← Real.exp_add, show R ^ 2 / 4 + -R ^ 2 / 4 = 0 by ring, Real.exp_zero]
  have hh := mul_le_mul_of_nonneg_right h (Real.exp_pos (-R ^ 2 / 4)).le
  rw [he] at hh
  norm_num [Nat.factorial] at hh ⊢
  nlinarith

theorem decay {R : ℝ} (hR : 0 < R) (p w : Velocity)
    (h : R / 4 < ‖p‖ ∨ R / 2 < ‖w‖) :
    Real.exp (-‖w‖ ^ 2) * (polynomial p)⁻¹ ≤ constant / R ^ 8 := by
  have hpow : 0 < R ^ 8 := pow_pos hR _
  have hP := polynomial_pos p
  have he : Real.exp (-‖w‖ ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  rcases h with hp | hw
  · have hb := polynomial_eighth_bound p (by positivity : 0 ≤ R / 4) hp.le
    have hi : (polynomial p)⁻¹ ≤ 4 ^ (8 : ℕ) / R ^ 8 := by
      apply (le_div_iff₀ hpow).mpr
      apply (inv_mul_le_iff₀ hP).mpr
      norm_num [div_pow] at hb ⊢
      nlinarith
    calc
      _ ≤ (polynomial p)⁻¹ := mul_le_of_le_one_left (inv_nonneg.mpr hP.le) he
      _ ≤ 4 ^ (8 : ℕ) / R ^ 8 := hi
      _ ≤ constant / R ^ 8 := by
        apply div_le_div_of_nonneg_right _ hpow.le
        norm_num [constant]
  · have hg := gaussian_shell_decay hR.le hw.le
    have ht : Real.exp (-R ^ 2 / 4) ≤
        (4 ^ (4 : ℕ) * Nat.factorial 4 : ℝ) / R ^ 8 := by
      apply (le_div_iff₀ hpow).mpr
      simpa only [mul_comm] using gaussian_eighth_bound R
    calc
      _ ≤ Real.exp (-‖w‖ ^ 2) :=
        mul_le_of_le_one_right (Real.exp_pos _).le (polynomial_inv_le_one p)
      _ ≤ Real.exp (-R ^ 2 / 4) := hg
      _ ≤ (4 ^ (4 : ℕ) * Nat.factorial 4 : ℝ) / R ^ 8 := ht
      _ ≤ constant / R ^ 8 := by
        apply div_le_div_of_nonneg_right _ hpow.le
        norm_num [constant]

end BoltzmannNonuniqueness.HotShellWeight

end

end

section

/-!
# Reduction of the original quadratic gain to a mixed gain

The reduction is proved in the original collision variables and uses no
additional change-of-variables hypothesis. This retains the bilinear form
covered by the published Carleman identity.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.HotWeight

namespace BoltzmannNonuniqueness.HotGainReduction

def coefficient (q : ℝ) (v : Velocity) : ℝ :=
  (2 : ℝ) ^ (51 : ℕ) * (H q v / G q v)

theorem coefficient_nonneg (q : ℝ) (v : Velocity) : 0 ≤ coefficient q v := by
  unfold coefficient
  exact mul_nonneg (by positivity) (div_nonneg (H_nonneg q v) (G_pos q v).le)

theorem pair_bound (q : ℝ) (v w : Velocity) (ω : Sphere) :
    ENNReal.ofReal (H q (scatterLeft v w ω)) * ENNReal.ofReal (H q (scatterRight v w ω)) +
      ENNReal.ofReal (H q (scatterLeft v w ω)) * ENNReal.ofReal (H q (scatterRight v w ω)) ≤
    ENNReal.ofReal (coefficient q v) *
      (ENNReal.ofReal (H q (scatterLeft v w ω)) * ENNReal.ofReal (G q (scatterRight v w ω)) +
       ENNReal.ofReal (G q (scatterLeft v w ω)) * ENNReal.ofReal (H q (scatterRight v w ω))) := by
  have hω : ‖(ω : Velocity)‖ = 1 := by
    simpa only [Sphere, Metric.mem_sphere, dist_zero_right] using ω.property
  have he := scatter_energy v w ω hω
  have hv : ‖v‖ ^ 2 ≤ ‖scatterLeft v w ω‖ ^ 2 + ‖scatterRight v w ω‖ ^ 2 := by
    linarith [sq_nonneg ‖w‖]
  have hb := mul_le_mul_of_nonneg_left
    (quadratic_product_bound q (scatterLeft v w ω) (scatterRight v w ω) v hv)
    (by norm_num : (0 : ℝ) ≤ 2)
  have hr : H q (scatterLeft v w ω) * H q (scatterRight v w ω) +
      H q (scatterLeft v w ω) * H q (scatterRight v w ω) ≤
      coefficient q v *
        (H q (scatterLeft v w ω) * G q (scatterRight v w ω) +
          G q (scatterLeft v w ω) * H q (scatterRight v w ω)) := by
    unfold coefficient
    rw [show (51 : ℕ) = 50 + 1 by rfl, pow_succ]
    convert hb using 1 <;> ring
  have hn := ENNReal.ofReal_le_ofReal hr
  simpa only [ENNReal.ofReal_add (mul_nonneg (H_nonneg _ _) (H_nonneg _ _))
      (mul_nonneg (H_nonneg _ _) (H_nonneg _ _)),
    ENNReal.ofReal_mul (coefficient_nonneg q v),
    ENNReal.ofReal_add (mul_nonneg (H_nonneg _ _) (G_pos _ _).le)
      (mul_nonneg (G_pos _ _).le (H_nonneg _ _)),
    ENNReal.ofReal_mul (H_nonneg _ _), ENNReal.ofReal_mul (G_pos _ _).le] using hn

/-- The factor `H(v)/G(v)` is essential: division by `H(v)` leaves a uniform
mixed-gain problem normalized by `G(v)`. -/
theorem quadratic_gain_le_mixed (q : ℝ) (v : Velocity) :
    nonnegativeGain (fun ξ => ENNReal.ofReal (H q ξ))
      (fun ξ => ENNReal.ofReal (H q ξ)) v ≤
    ENNReal.ofReal (coefficient q v) *
      nonnegativeGain (fun ξ => ENNReal.ofReal (H q ξ))
        (fun ξ => ENNReal.ofReal (G q ξ)) v := by
  unfold nonnegativeGain
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro p
  have h := mul_le_mul' (le_rfl : ENNReal.ofReal (collisionKernel v p.1 p.2) / 2 ≤ _)
    (pair_bound q v p.1 p.2)
  convert h using 1
  ac_rfl

end BoltzmannNonuniqueness.HotGainReduction

end

end

end OAI
