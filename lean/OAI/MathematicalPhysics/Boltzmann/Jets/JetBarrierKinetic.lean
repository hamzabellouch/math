import OAI.MathematicalPhysics.Boltzmann.Branching.PlaneChart
import OAI.MathematicalPhysics.Boltzmann.Collision.AxialJointAnalytic

namespace OAI

section

/-! # The exact axial thermal-coordinate map for a free core -/

noncomputable section

open BoltzmannNonuniqueness.AxialFlow
open BoltzmannNonuniqueness.AxialDerivative

namespace BoltzmannNonuniqueness.JetCoreMap

def axialMap (σ α γ s d t z w : ℝ) : ℝ :=
  d * w + velocity σ α γ s t (z - t * d * w)

def axialInverse (σ α γ s d t z p : ℝ) : ℝ :=
  (p - profile σ α γ s (z - t * p)) / d

def sourceFoot (σ α γ s d t z w : ℝ) : ℝ :=
  foot σ α γ s t (z - t * d * w)

theorem sourceFoot_eq (σ α γ s d t z w : ℝ) :
    sourceFoot σ α γ s d t z w = z - t * axialMap σ α γ s d t z w := by
  unfold sourceFoot foot axialMap
  ring

theorem axialMap_spec {α : ℝ} (hα : 0 ≤ α) (σ γ s d t z w : ℝ) :
    axialMap σ α γ s d t z w = profile σ α γ s (z - t * axialMap σ α γ s d t z w) + d * w := by
  have hu := velocity_spec (σ := σ) (γ := γ) (s := s) (t := t) (z := z - t * d * w) hα
  rw [← sourceFoot_eq]
  change d * w + velocity σ α γ s t (z - t * d * w) =
    profile σ α γ s (z - t * d * w - t * velocity σ α γ s t (z - t * d * w)) + d * w
  rw [← hu]
  ring

theorem inverse_map {α d : ℝ} (hα : 0 ≤ α) (hd : d ≠ 0) (σ γ s t z w : ℝ) :
    axialInverse σ α γ s d t z (axialMap σ α γ s d t z w) = w := by
  unfold axialInverse
  apply (div_eq_iff hd).mpr
  have h := axialMap_spec hα σ γ s d t z w
  linarith

theorem map_inverse {α γ s t d : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (ht : 0 ≤ t) (hd : d ≠ 0) (σ z p : ℝ) :
    axialMap σ α γ s d t z (axialInverse σ α γ s d t z p) = p := by
  let w := axialInverse σ α γ s d t z p
  have hw : d * w = p - profile σ α γ s (z - t * p) := by
    dsimp only [w, axialInverse]
    field_simp
  have hu : p - d * w = velocity σ α γ s t (z - t * d * w) := by
    apply velocity_unique hα hγ hs ht
    rw [show z - t * d * w - t * (p - d * w) = z - t * p by ring]
    linarith
  change d * w + velocity σ α γ s t (z - t * d * w) = p
  rw [← hu]
  ring

theorem axialMap_derivative {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (σ d z w : ℝ) :
    HasDerivAt (axialMap σ α γ s d t z)
      (d / (1 + t * A α γ s (sourceFoot σ α γ s d t z w))) w := by
  have hu := velocity_derivative (σ := σ) hα hγ hs ht (z - t * d * w)
  have hl : HasDerivAt (fun y : ℝ => z - t * d * y) (-(t * d)) w := by
    convert (hasDerivAt_const w z).sub ((hasDerivAt_id w).const_mul (t * d)) using 1
    · funext y
      rfl
    · simp only [mul_one, zero_sub]
  have h := ((hasDerivAt_id w).const_mul d).add (hu.comp w hl)
  have ha := A_nonneg hα hγ hs.le (sourceFoot σ α γ s d t z w)
  have hden : 1 + t * A α γ s (sourceFoot σ α γ s d t z w) ≠ 0 := by positivity
  convert h using 1
  · funext y
    unfold axialMap
    dsimp only [Function.comp_apply, Pi.add_apply, id]
  · change d / (1 + t * A α γ s (sourceFoot σ α γ s d t z w)) =
      d * 1 + (A α γ s (sourceFoot σ α γ s d t z w) /
        (1 + t * A α γ s (sourceFoot σ α γ s d t z w))) * -(t * d)
    field_simp [hden]
    ring

def axialHomeomorph {α γ s t d : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (ht : 0 ≤ t) (hd : d ≠ 0) (σ z : ℝ) : ℝ ≃ₜ ℝ where
  toFun := axialMap σ α γ s d t z
  invFun := axialInverse σ α γ s d t z
  left_inv := inverse_map hα hd σ γ s t z
  right_inv := map_inverse hα hγ hs ht hd σ z
  continuous_toFun := continuous_iff_continuousAt.mpr fun w =>
    (axialMap_derivative hα hγ hs ht σ d z w).continuousAt
  continuous_invFun := by
    unfold axialInverse
    exact (continuous_id.sub ((continuous_profile σ α γ s).comp
      (continuous_const.sub (continuous_const.mul continuous_id)))).div_const d

end BoltzmannNonuniqueness.JetCoreMap

end

end

section

/-! # The exact one-dimensional core Jacobian and compression bound -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.AxialDerivative
open BoltzmannNonuniqueness.JetCoreMap

namespace BoltzmannNonuniqueness.JetCoreJacobian

def jacobian (σ α γ s d t z w : ℝ) : ℝ :=
  d / (1 + t * A α γ s (sourceFoot σ α γ s d t z w))

theorem jacobian_pos {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (hd : 0 < d) (ht : 0 ≤ t) (σ z w : ℝ) : 0 < jacobian σ α γ s d t z w := by
  unfold jacobian
  have := A_nonneg hα hγ hs.le (sourceFoot σ α γ s d t z w)
  positivity

theorem integral_substitution {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (hd : 0 < d) (ht : 0 ≤ t) (σ z : ℝ) (f : ℝ → ℝ) :
    (∫ p, f p) = ∫ w, jacobian σ α γ s d t z w * f (axialMap σ α γ s d t z w) := by
  have hi := integral_image_eq_integral_abs_deriv_smul .univ
    (fun w _ => (axialMap_derivative hα hγ hs ht σ d z w).hasDerivWithinAt)
    (axialHomeomorph hα hγ hs ht hd.ne' σ z).injective.injOn f
  have hr : axialMap σ α γ s d t z '' univ = univ :=
    Set.image_univ ▸ (axialHomeomorph hα hγ hs ht hd.ne' σ z).surjective.range_eq
  rw [hr, Measure.restrict_univ] at hi
  change (∫ p, f p) = ∫ w, |jacobian σ α γ s d t z w| • f (axialMap σ α γ s d t z w) at hi
  simpa only [abs_of_pos (jacobian_pos hα hγ hs hd ht σ z _), smul_eq_mul] using hi

theorem integrable_substitution {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (hd : 0 < d) (ht : 0 ≤ t) (σ z : ℝ) (f : ℝ → ℝ) :
    Integrable f ↔ Integrable (fun w => jacobian σ α γ s d t z w * f (axialMap σ α γ s d t z w)) := by
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul .univ
    (fun w _ => (axialMap_derivative hα hγ hs ht σ d z w).hasDerivWithinAt)
    (axialHomeomorph hα hγ hs ht hd.ne' σ z).injective.injOn f
  have hr : axialMap σ α γ s d t z '' univ = univ :=
    Set.image_univ ▸ (axialHomeomorph hα hγ hs ht hd.ne' σ z).surjective.range_eq
  rw [hr, integrableOn_univ, integrableOn_univ] at hi
  change Integrable f ↔ Integrable (fun w => |jacobian σ α γ s d t z w| • f (axialMap σ α γ s d t z w)) at hi
  simpa only [abs_of_pos (jacobian_pos hα hγ hs hd ht σ z _), smul_eq_mul] using hi

theorem compression_bound {K s t k S : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (ht : 0 ≤ t)
    (hk : 0 < k) (hS : 0 ≤ S) (hSmax : S ≤ 1) :
    K * S / (s + t * k * S) ≤ (K * max 1 k⁻¹) / (s + t) := by
  have hden : 0 < s + t * k * S := by positivity
  have hsk : 0 < s + t * k := by positivity
  have hst : 0 < s + t := by positivity
  have hfirst : K * S / (s + t * k * S) ≤ K / (s + t * k) := by
    apply (div_le_div_iff₀ hden hsk).mpr
    nlinarith [mul_le_mul_of_nonneg_left hSmax (mul_nonneg hK hs.le)]
  have hmax1 : 1 ≤ max (1 : ℝ) k⁻¹ := le_max_left _ _
  have hmaxk : 1 ≤ max (1 : ℝ) k⁻¹ * k := by
    calc
      1 = k⁻¹ * k := (inv_mul_cancel₀ hk.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hk.le
  have hcover : s + t ≤ max (1 : ℝ) k⁻¹ * (s + t * k) := by
    nlinarith [mul_le_mul_of_nonneg_right hmax1 hs.le, mul_le_mul_of_nonneg_right hmaxk ht]
  apply hfirst.trans
  apply (div_le_div_iff₀ hsk hst).mpr
  nlinarith [mul_le_mul_of_nonneg_left hcover hK]

end BoltzmannNonuniqueness.JetCoreJacobian

end

end

section

/-! # Kinetic exponent in the transported cold-jet barrier -/

noncomputable section

open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.AxialDerivative
open BoltzmannNonuniqueness.AxialTransport
open BoltzmannNonuniqueness.AxialFlightDerivative

namespace BoltzmannNonuniqueness.JetBarrierKinetic

def compression (σ α γ s z v t : ℝ) : ℝ :=
  A α γ s (flightFoot σ α γ s z v t) / (1 + t * A α γ s (flightFoot σ α γ s z v t))

def squaredError (σ α γ s z : ℝ) (v : Velocity) (t : ℝ) : ℝ :=
  ‖transverse v‖ ^ 2 + (axial v - flightVelocity σ α γ s z (axial v) t) ^ 2

theorem compression_nonneg {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (ht : 0 ≤ t) (σ z v : ℝ) : 0 ≤ compression σ α γ s z v t := by
  unfold compression
  exact div_nonneg (A_nonneg hα hγ hs.le _) (by
    have := A_nonneg hα hγ hs.le (flightFoot σ α γ s z v t)
    positivity)

theorem squaredError_derivative {σ α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (z : ℝ) (v : Velocity) :
    HasDerivAt (squaredError σ α γ s z v)
      (-2 * compression σ α γ s z (axial v) t *
        (axial v - flightVelocity σ α γ s z (axial v) t) ^ 2) t := by
  have hu := flightVelocity_derivative (σ := σ) hα hγ hs ht z (axial v)
  have h := (hasDerivAt_const t (‖transverse v‖ ^ 2)).add
    (((hasDerivAt_const t (axial v)).sub hu).pow 2)
  convert h using 1
  · funext r
    rfl
  · unfold compression
    dsimp only [Pi.sub_apply]
    ring

theorem kineticExponent_derivative {σ α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (z d : ℝ) (v : Velocity) :
    HasDerivAt (fun r => -(2 - r) * squaredError σ α γ s z v r / d ^ 2)
      ((squaredError σ α γ s z v t +
        2 * (2 - t) * compression σ α γ s z (axial v) t *
          (axial v - flightVelocity σ α γ s z (axial v) t) ^ 2) / d ^ 2) t := by
  have h := ((((hasDerivAt_const t 2).sub (hasDerivAt_id t)).neg).mul
    (squaredError_derivative (σ := σ) hα hγ hs ht z v)).div_const (d ^ 2)
  convert h using 1
  · funext r
    rfl
  · dsimp only [Pi.sub_apply, Pi.neg_apply, Pi.mul_apply, id]
    ring

theorem kineticExponent_derivative_lower {σ α γ s t d : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (htmax : t ≤ 2) (z : ℝ) (v : Velocity) :
    squaredError σ α γ s z v t / d ^ 2 ≤
      (squaredError σ α γ s z v t +
        2 * (2 - t) * compression σ α γ s z (axial v) t *
          (axial v - flightVelocity σ α γ s z (axial v) t) ^ 2) / d ^ 2 := by
  apply div_le_div_of_nonneg_right _ (sq_nonneg d)
  have hc := compression_nonneg hα hγ hs ht σ z (axial v)
  have hn : 0 ≤ 2 * (2 - t) * compression σ α γ s z (axial v) t *
      (axial v - flightVelocity σ α γ s z (axial v) t) ^ 2 := by positivity
  linarith

end BoltzmannNonuniqueness.JetBarrierKinetic

end

end

end OAI
