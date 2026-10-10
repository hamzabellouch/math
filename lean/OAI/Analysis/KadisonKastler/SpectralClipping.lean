import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing

namespace OAI

/-!
# Norm clipping with preserved support and quotient image

The cutoff multiplies an element on the right by a continuous function of
its absolute value. Both the clipped part and the discarded part have
star squares bounded by the original star square.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

def clippingFunction (β t : ℝ) : ℝ := β / max β t

theorem clippingFunction_continuous {β : ℝ} (hβ : 0 < β) :
    Continuous (clippingFunction β) :=
  continuous_const.div (continuous_const.max continuous_id)
    (fun t => ne_of_gt (hβ.trans_le (le_max_left β t)))

theorem clippingFunction_nonneg {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    0 ≤ clippingFunction β t :=
  div_nonneg hβ.le (hβ.le.trans (le_max_left β t))

theorem clippingFunction_le_one {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    clippingFunction β t ≤ 1 :=
  (div_le_one (hβ.trans_le (le_max_left β t))).mpr (le_max_left β t)

theorem mul_clippingFunction {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    t * clippingFunction β t = min t β := by
  by_cases ht : t ≤ β
  · simp [clippingFunction, max_eq_left ht, min_eq_left ht, ne_of_gt hβ]
  · have ht' : β ≤ t := (lt_of_not_ge ht).le
    have htpos : 0 < t := hβ.trans_le ht'
    rw [clippingFunction, max_eq_right ht', min_eq_right ht']
    field_simp

theorem clippingFunction_square_le {β t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t) :
    (t * clippingFunction β t) ^ 2 ≤ t ^ 2 := by
  have h0 := clippingFunction_nonneg hβ t
  have h1 := clippingFunction_le_one hβ t
  have ht0 : 0 ≤ t * clippingFunction β t := mul_nonneg ht h0
  have ht1 : t * clippingFunction β t ≤ t := by nlinarith
  nlinarith

theorem clippingFunction_square_le_bound {β t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t) :
    (t * clippingFunction β t) ^ 2 ≤ β ^ 2 := by
  rw [mul_clippingFunction hβ]
  have h0 : 0 ≤ min t β := le_min ht hβ.le
  have h1 := min_le_right t β
  nlinarith

theorem discardedFunction_square_le {β t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t) :
    (t * (1 - clippingFunction β t)) ^ 2 ≤ t ^ 2 := by
  have h0 := clippingFunction_nonneg hβ t
  have h1 := clippingFunction_le_one hβ t
  have ht0 : 0 ≤ t * (1 - clippingFunction β t) := mul_nonneg ht (by linarith)
  have ht1 : t * (1 - clippingFunction β t) ≤ t := by nlinarith
  nlinarith

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def spectralClip (β : ℝ) (x : A) : A :=
  x * cfc (clippingFunction β) (CFC.abs x)

/-- A scalar functional-calculus identity for any continuous right multiplier. -/
theorem star_mul_cfc_abs (x : A) (f : ℝ → ℝ) (hf : Continuous f) :
    star (x * cfc f (CFC.abs x)) * (x * cfc f (CFC.abs x)) =
      cfc (fun t => (t * f t) ^ 2) (CFC.abs x) := by
  have ha : IsSelfAdjoint (CFC.abs x) := (CFC.abs_nonneg x).isSelfAdjoint
  have hfstar : star (cfc f (CFC.abs x)) = cfc f (CFC.abs x) :=
    (cfc_predicate f (CFC.abs x)).star_eq
  calc
    _ = cfc f (CFC.abs x) * (star x * x) * cfc f (CFC.abs x) := by
      rw [star_mul, hfstar]
      simp only [mul_assoc]
    _ = cfc f (CFC.abs x) * cfc (fun t : ℝ => t ^ 2) (CFC.abs x) *
        cfc f (CFC.abs x) := by
      rw [cfc_pow_id (R := ℝ) _ 2 ha, pow_two, CFC.abs_mul_abs]
    _ = cfc (fun t => f t * t ^ 2 * f t) (CFC.abs x) := by
      rw [← cfc_mul f (fun t : ℝ => t ^ 2) _ hf.continuousOn (by fun_prop),
        ← cfc_mul (fun t => f t * t ^ 2) f _ (by fun_prop) hf.continuousOn]
    _ = _ := by congr 1; funext t; ring

theorem spectralClip_star_mul_self {β : ℝ} (hβ : 0 < β) (x : A) :
    star (spectralClip β x) * spectralClip β x =
      cfc (fun t => (t * clippingFunction β t) ^ 2) (CFC.abs x) :=
  star_mul_cfc_abs x _ (clippingFunction_continuous hβ)

/-- Clipping does not increase the star square. -/
theorem spectralClip_star_mul_self_le {β : ℝ} (hβ : 0 < β) (x : A) :
    star (spectralClip β x) * spectralClip β x ≤ star x * x := by
  rw [spectralClip_star_mul_self hβ,
    ← CFC.abs_mul_abs x, ← pow_two, ← cfc_pow_id (R := ℝ) (CFC.abs x) 2]
  apply (cfc_le_iff _ _ _ (by exact
    ((continuous_id.mul (clippingFunction_continuous hβ)).pow 2).continuousOn)).mpr
  intro t ht
  exact clippingFunction_square_le hβ (spectrum_nonneg_of_nonneg (CFC.abs_nonneg x) ht)

/-- The discarded part also has star square bounded by the original. -/
theorem spectralClip_discard_star_mul_self_le {β : ℝ} (hβ : 0 < β) (x : A) :
    star (x - spectralClip β x) * (x - spectralClip β x) ≤ star x * x := by
  have hcut : x - spectralClip β x =
      x * cfc (fun t => 1 - clippingFunction β t) (CFC.abs x) := by
    rw [cfc_sub (fun _ : ℝ => 1) (clippingFunction β) _ (by fun_prop)
      (clippingFunction_continuous hβ).continuousOn, cfc_const_one ℝ (CFC.abs x),
      mul_sub, mul_one]
    rfl
  rw [hcut, star_mul_cfc_abs x (fun t : ℝ => 1 - clippingFunction β t)
      (continuous_const.sub (clippingFunction_continuous hβ)),
    ← CFC.abs_mul_abs x, ← pow_two, ← cfc_pow_id (R := ℝ) (CFC.abs x) 2]
  apply (cfc_le_iff _ _ _ (by exact
    ((continuous_id.mul (continuous_const.sub (clippingFunction_continuous hβ))).pow 2).continuousOn)).mpr
  intro t ht
  exact discardedFunction_square_le hβ (spectrum_nonneg_of_nonneg (CFC.abs_nonneg x) ht)

theorem spectralClip_norm_le {β : ℝ} (hβ : 0 < β) (x : A) : ‖spectralClip β x‖ ≤ β := by
  have hsq : ‖spectralClip β x‖ ^ 2 ≤ β ^ 2 := by
    rw [pow_two, ← CStarRing.norm_star_mul_self, spectralClip_star_mul_self hβ]
    apply norm_cfc_le (sq_nonneg β)
    intro t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact clippingFunction_square_le_bound hβ
      (spectrum_nonneg_of_nonneg (CFC.abs_nonneg x) ht)
  nlinarith [norm_nonneg (spectralClip β x)]

/-- Star-square domination preserves every right support identity. -/
theorem mul_right_eq_of_star_mul_self_le (x y p : A)
    (hxy : star y * y ≤ star x * x) (hxp : x * p = x) : y * p = y := by
  have hx : x * (1 - p) = 0 := by rw [mul_sub, mul_one, hxp, sub_self]
  have h := star_left_conjugate_le_conjugate hxy (1 - p)
  have hid (z : A) : star (1 - p) * (star z * z) * (1 - p) =
      star (z * (1 - p)) * (z * (1 - p)) := by
    rw [star_mul]
    simp only [mul_assoc]
  rw [hid x, hid y, hx, star_zero, zero_mul] at h
  have hy : y * (1 - p) = 0 := (CStarRing.star_mul_self_eq_zero_iff _).mp
    (le_antisymm h (star_mul_self_nonneg _))
  rw [mul_sub, mul_one, sub_eq_zero] at hy
  exact hy.symm

theorem spectralClip_mul_right_eq {β : ℝ} (hβ : 0 < β) (x p : A)
    (hxp : x * p = x) : spectralClip β x * p = spectralClip β x :=
  mul_right_eq_of_star_mul_self_le x _ p (spectralClip_star_mul_self_le hβ x) hxp

theorem spectralClip_eq_self {β : ℝ} (hβ : 0 < β) (x : A) (hx : ‖x‖ ≤ β) :
    spectralClip β x = x := by
  nontriviality A
  have hfc : cfc (clippingFunction β) (CFC.abs x) = 1 := by
    rw [← cfc_const_one ℝ (CFC.abs x)]
    apply cfc_congr
    intro t ht
    have htβ : t ≤ β := (Real.le_norm_self t).trans
      ((spectrum.norm_le_norm_of_mem ht).trans (by simpa only [CFC.norm_abs] using hx))
    simp [clippingFunction, max_eq_left htβ, ne_of_gt hβ]
  rw [spectralClip, hfc, mul_one]

section Hom

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem starAlgHom_map_abs (π : A →⋆ₐ[ℂ] B) (x : A) :
    π (CFC.abs x) = CFC.abs (π x) := by
  simp only [CFC.abs]
  rw [CFC.sqrt_eq_real_sqrt _ (star_mul_self_nonneg x),
    CFC.sqrt_eq_real_sqrt _ (star_mul_self_nonneg (π x)), cfcₙ_eq_cfc, cfcₙ_eq_cfc]
  rw [π.map_cfc Real.sqrt (star x * x) (by fun_prop) (by fun_prop)
    (star_mul_self_nonneg x).isSelfAdjoint (by
      simp only [map_mul, map_star]
      exact (star_mul_self_nonneg (π x)).isSelfAdjoint)]
  simp only [map_mul, map_star]

/-- The cutoff is natural for star homomorphisms, including quotient maps. -/
theorem map_spectralClip (π : A →⋆ₐ[ℂ] B) {β : ℝ} (hβ : 0 < β) (x : A) :
    π (spectralClip β x) = spectralClip β (π x) := by
  rw [spectralClip, map_mul, π.map_cfc (clippingFunction β) (CFC.abs x)
    (clippingFunction_continuous hβ).continuousOn, starAlgHom_map_abs]
  rfl

/-- If the image is already in the target ball, clipping changes the
element only by an element of the homomorphism's kernel. -/
theorem map_spectralClip_eq {β : ℝ} (π : A →⋆ₐ[ℂ] B) (hβ : 0 < β) (x : A)
    (hx : ‖π x‖ ≤ β) : π (spectralClip β x) = π x := by
  rw [map_spectralClip π hβ, spectralClip_eq_self hβ _ hx]

theorem map_sub_spectralClip_eq_zero {β : ℝ} (π : A →⋆ₐ[ℂ] B)
    (hβ : 0 < β) (x : A) (hx : ‖π x‖ ≤ β) : π (x - spectralClip β x) = 0 := by
  rw [map_sub, map_spectralClip_eq π hβ x hx, sub_self]

end Hom

end

end KadisonKastler

end OAI
