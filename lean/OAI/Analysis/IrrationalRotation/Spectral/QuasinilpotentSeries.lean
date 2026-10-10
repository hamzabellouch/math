import OAI.Analysis.IrrationalRotation.Model.Analytic
import OAI.Analysis.IrrationalRotation.Model.OperatorProperties
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Invariant233

variable {A : Type*} [NormedRing A]

theorem NormQuasinilpotent.eventually_norm_pow_le {T : A}
    (hT : NormQuasinilpotent T) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, ‖T ^ n‖ ≤ r ^ n := by
  have he := (tendsto_order.mp hT).2 r hr
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have hpow := pow_le_pow_left₀
    (Real.rpow_nonneg (norm_nonneg (T ^ n)) (1 / (n : ℝ))) hn.le n
  simpa only [one_div, Real.rpow_inv_natCast_pow (norm_nonneg (T ^ n))
    (Nat.ne_of_gt hnpos)] using hpow

variable [NormedAlgebra ℂ A]

theorem NormQuasinilpotent.summable_norm_smul_pow {T : A}
    (hT : NormQuasinilpotent T) (z : ℂ) :
    Summable (fun n : ℕ => ‖z ^ n • T ^ n‖) := by
  let r : ℝ := 1 / (2 * (‖z‖ + 1))
  have hr : 0 < r := by dsimp [r]; positivity
  have hzr : ‖z‖ * r ≤ (1 / 2 : ℝ) := by
    dsimp [r]
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith [norm_nonneg z]
  apply (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).of_norm_bounded_eventually_nat
  filter_upwards [hT.eventually_norm_pow_le hr] with n hn
  rw [norm_norm, norm_smul, norm_pow]
  calc
    ‖z‖ ^ n * ‖T ^ n‖ ≤ ‖z‖ ^ n * r ^ n :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (‖z‖ * r) ^ n := (mul_pow _ _ _).symm
    _ ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_left₀ (by positivity) hzr n

variable [CompleteSpace A]

theorem NormQuasinilpotent.summable_smul_pow {T : A}
    (hT : NormQuasinilpotent T) (z : ℂ) :
    Summable (fun n : ℕ => z ^ n • T ^ n) :=
  (hT.summable_norm_smul_pow z).of_norm

omit [CompleteSpace A] in

theorem NormQuasinilpotent.summable_norm_logSeries {T : A}
    (hT : NormQuasinilpotent T) (z : ℂ) :
    Summable (fun n : ℕ => ‖(-(z ^ (n + 1) / (n + 1 : ℂ))) • T ^ (n + 1)‖) := by
  have hs : Summable (fun n : ℕ => ‖z ^ (n + 1) • T ^ (n + 1)‖) :=
    (summable_nat_add_iff 1).2 (hT.summable_norm_smul_pow z)
  apply hs.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  simp only [norm_smul, norm_neg, norm_div, norm_pow]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply div_le_self (by positivity)
  rw [show (n + 1 : ℂ) = ((n + 1 : ℕ) : ℂ) by push_cast; rfl, Complex.norm_natCast]
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

theorem NormQuasinilpotent.geometric_inverse_identities {T : A}
    (hT : NormQuasinilpotent T) (z : ℂ) :
    (∑' n : ℕ, z ^ n • T ^ n) * (1 - z • T) = 1 ∧
      (1 - z • T) * (∑' n : ℕ, z ^ n • T ^ n) = 1 := by
  have hs : Summable (fun n : ℕ => (z • T) ^ n) := by
    simpa only [smul_pow] using hT.summable_smul_pow z
  constructor
  · simpa only [smul_pow] using hs.tsum_pow_mul_one_sub
  · simpa only [smul_pow] using hs.one_sub_mul_tsum_pow

theorem NormQuasinilpotent.inverse_one_sub_smul {T : A}
    (hT : NormQuasinilpotent T) (z : ℂ) :
    Ring.inverse (1 - z • T) = ∑' n : ℕ, z ^ n • T ^ n := by
  have hi := hT.geometric_inverse_identities z
  let u : Aˣ := ⟨1 - z • T, (∑' n : ℕ, z ^ n • T ^ n), hi.2, hi.1⟩
  exact Ring.inverse_unit u

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def vectorTraceContinuousLinearMap (ξ : H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (innerSL ℂ ξ).comp (ContinuousLinearMap.apply ℂ H ξ)

@[simp] theorem vectorTraceContinuousLinearMap_apply (ξ : H) (T : H →L[ℂ] H) :
    vectorTraceContinuousLinearMap ξ T = vectorTrace ξ T := rfl

theorem vectorTrace_tsum {ι : Type*} (ξ : H) (f : ι → H →L[ℂ] H)
    (hf : Summable f) :
    vectorTrace ξ (∑' i, f i) = ∑' i, vectorTrace ξ (f i) :=
  (vectorTraceContinuousLinearMap ξ).map_tsum hf

variable [CompleteSpace H]

theorem vectorTrace_geometric_series {T : H →L[ℂ] H} (ξ : H)
    (hT : NormQuasinilpotent T)
    (hmom : ∀ n : ℕ, 0 < n → vectorTrace ξ (T ^ n) = 0) (z : ℂ) :
    vectorTrace ξ (∑' n : ℕ, z ^ n • T ^ n) = vectorTrace ξ 1 := by
  rw [vectorTrace_tsum ξ _ (hT.summable_smul_pow z)]
  rw [tsum_eq_single 0]
  · simp [vectorTrace]
  · intro n hn
    simp only [vectorTrace, smul_apply, inner_smul_right]
    change z ^ n * vectorTrace ξ (T ^ n) = 0
    rw [hmom n (Nat.pos_of_ne_zero hn), mul_zero]

theorem vectorTrace_inverse_one_sub_smul {T : H →L[ℂ] H} (ξ : H)
    (hT : NormQuasinilpotent T)
    (hmom : ∀ n : ℕ, 0 < n → vectorTrace ξ (T ^ n) = 0) (z : ℂ) :
    vectorTrace ξ (Ring.inverse (1 - z • T)) = vectorTrace ξ 1 := by
  rw [hT.inverse_one_sub_smul z]
  exact vectorTrace_geometric_series ξ hT hmom z

theorem vectorTrace_resolvent_of_moments_zero {T : H →L[ℂ] H} (ξ : H)
    (hT : NormQuasinilpotent T)
    (hmom : ∀ n : ℕ, 0 < n → vectorTrace ξ (T ^ n) = 0)
    (z : ℂ) (hz : z ≠ 0) :
    vectorTrace ξ (resolvent T z) = z⁻¹ * vectorTrace ξ 1 := by
  lift z to ℂˣ using hz.isUnit
  have hres : (z : ℂ) • resolvent T (z : ℂ) =
      Ring.inverse (1 - (↑z⁻¹ : ℂ) • T) := by
    simpa only [Units.smul_def, resolvent, map_one] using
      (spectrum.units_smul_resolvent_self (r := z) (a := T))
  have ht := congrArg (vectorTrace ξ) hres
  rw [vectorTrace_inverse_one_sub_smul ξ hT hmom] at ht
  simp only [vectorTrace, smul_apply, inner_smul_right] at ht
  change (z : ℂ) * vectorTrace ξ (resolvent T (z : ℂ)) =
    vectorTrace ξ 1 at ht
  calc
    vectorTrace ξ (resolvent T (z : ℂ)) =
        (↑z⁻¹ : ℂ) * ((z : ℂ) * vectorTrace ξ (resolvent T (z : ℂ))) := by
      rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = (↑z⁻¹ : ℂ) * vectorTrace ξ 1 := by rw [ht]
    _ = (z : ℂ)⁻¹ * vectorTrace ξ 1 := by simp

theorem vectorTrace_logSeries_eq_zero {T : H →L[ℂ] H} (ξ : H)
    (hT : NormQuasinilpotent T)
    (hmom : ∀ n : ℕ, 0 < n → vectorTrace ξ (T ^ n) = 0) (z : ℂ) :
    vectorTrace ξ (∑' n : ℕ, (-(z ^ (n + 1) / (n + 1 : ℂ))) • T ^ (n + 1)) = 0 := by
  rw [vectorTrace_tsum ξ _ (hT.summable_norm_logSeries z).of_norm]
  have hz (n : ℕ) :
      vectorTrace ξ ((-(z ^ (n + 1) / (n + 1 : ℂ))) • T ^ (n + 1)) = 0 := by
    simp only [vectorTrace, smul_apply, inner_smul_right]
    change (-(z ^ (n + 1) / (n + 1 : ℂ))) * vectorTrace ξ (T ^ (n + 1)) = 0
    rw [hmom (n + 1) (Nat.succ_pos n), mul_zero]
  simp only [hz, tsum_zero]

end Invariant233

end

end OAI
