import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.MeanValue
import OAI.NumberTheory.Ostmann.Construction.HistorySmoothFactor
import OAI.NumberTheory.Ostmann.Arithmetic.SmoothPolynomialWeight

namespace OAI

/-! # Bounds for the actual normalized level-zero Fourier profile -/

namespace Ostmann

open scoped SchwartzMap

theorem abs_inv_sub_inv_le_of_one_le (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |x⁻¹ - y⁻¹| ≤ |x - y| := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have he : x⁻¹ - y⁻¹ = (y - x) / (x * y) := by field_simp
  rw [he, abs_div, abs_of_pos (mul_pos hx0 hy0), abs_sub_comm]
  exact div_le_self (abs_nonneg _) (by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)])

theorem abs_sqrt_sub_sqrt_le_of_one_le (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ |x - y| := by
  have hsx : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  have hsy : 1 ≤ Real.sqrt y := Real.one_le_sqrt.mpr hy
  have he : (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) = x - y := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ x), Real.sq_sqrt (by linarith : 0 ≤ y)]
  have hab : |Real.sqrt x - Real.sqrt y| * (Real.sqrt x + Real.sqrt y) = |x - y| := by
    rw [← abs_of_nonneg (show 0 ≤ Real.sqrt x + Real.sqrt y by positivity), ← abs_mul, he]
  nlinarith [abs_nonneg (Real.sqrt x - Real.sqrt y)]

theorem abs_inv_sqrt_sub_inv_sqrt_le (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |(Real.sqrt x)⁻¹ - (Real.sqrt y)⁻¹| ≤ |x - y| :=
  (abs_inv_sub_inv_le_of_one_le _ _ (Real.one_le_sqrt.mpr hx) (Real.one_le_sqrt.mpr hy)).trans
    (abs_sqrt_sub_sqrt_le_of_one_le x y hx hy)

noncomputable def normalizedFourierProfile (ψ : ℝ → ℂ) (v z : ℝ) : ℂ :=
  Complex.ofReal ((Real.sqrt z)⁻¹) * ψ (-v * z⁻¹)

theorem normalizedFourierProfile_norm (ψ : ℝ → ℂ) (v B z : ℝ)
    (hψ : ∀ t, ‖ψ t‖ ≤ B) (hz : 1 ≤ z) :
    ‖normalizedFourierProfile ψ v z‖ ≤ B := by
  have hs : 0 ≤ (Real.sqrt z)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hs1 : (Real.sqrt z)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hz)
  rw [normalizedFourierProfile, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
  exact (mul_le_mul hs1 (hψ _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul B)

theorem normalizedFourierProfile_lipschitz (ψ : ℝ → ℂ) (v B D x y : ℝ)
    (hψ : ∀ t, ‖ψ t‖ ≤ B) (hD : 0 ≤ D)
    (hlip : ∀ s t, ‖ψ s - ψ t‖ ≤ D * |s - t|) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    ‖normalizedFourierProfile ψ v x - normalizedFourierProfile ψ v y‖ ≤
      (B + D * |v|) * |x - y| := by
  have hxroot : 0 ≤ (Real.sqrt x)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hxroot1 : (Real.sqrt x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hx)
  have harg : |-v * x⁻¹ - -v * y⁻¹| ≤ |v| * |x - y| := by
    rw [← mul_sub, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (abs_inv_sub_inv_le_of_one_le x y hx hy) (abs_nonneg _)
  have hψdiff : ‖ψ (-v * x⁻¹) - ψ (-v * y⁻¹)‖ ≤ D * |v| * |x - y| :=
    (hlip _ _).trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left harg hD)
  have he : normalizedFourierProfile ψ v x - normalizedFourierProfile ψ v y =
      Complex.ofReal ((Real.sqrt x)⁻¹) * (ψ (-v * x⁻¹) - ψ (-v * y⁻¹)) +
      (Complex.ofReal ((Real.sqrt x)⁻¹) - Complex.ofReal ((Real.sqrt y)⁻¹)) * ψ (-v * y⁻¹) := by
    unfold normalizedFourierProfile
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hxroot,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have h1 := mul_le_mul hxroot1 hψdiff (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have h2 := mul_le_mul (abs_inv_sqrt_sub_inv_sqrt_le x y hx hy) (hψ (-v * y⁻¹))
    (norm_nonneg _) (abs_nonneg _)
  nlinarith only [h1, h2]

/-- Normalizing by X exactly recovers the original Fourier factor, before
its separate bounded support cutoff is applied. -/
theorem normalizedFourierProfile_original (ψ : ℝ → ℂ) (X M v : ℝ)
    (hX : X ≠ 0) (hM : M ≠ 0) :
    normalizedFourierProfile ψ v (M / X) = archimedeanLeafFactor X M v 1 ψ := by
  have hi : (M / X)⁻¹ = X / M := by field_simp
  have ha : -v * (M / X)⁻¹ = -v * X / M := by rw [hi]; ring
  have hs : (Real.sqrt (M / X))⁻¹ = Real.sqrt (X / M) := by rw [← Real.sqrt_inv, hi]
  simp only [normalizedFourierProfile, archimedeanLeafFactor, mul_one, hs, ha]

/-- A Schwartz profile supplies its bounded derivative and Lipschitz constant
from existing library seminorms, with no analytic input left as an assumption. -/
theorem schwartz_profile_bounds (ψ : 𝓢(ℝ, ℂ)) :
    (∀ t, ‖ψ t‖ ≤ SchwartzMap.seminorm ℝ 0 0 ψ) ∧
    (∀ s t, ‖ψ s - ψ t‖ ≤ SchwartzMap.seminorm ℝ 0 1 ψ * |s - t|) := by
  refine ⟨fun t => ψ.norm_le_seminorm ℝ t, ?_⟩
  intro s t
  have hb (x : ℝ) : ‖deriv ψ x‖ ≤ SchwartzMap.seminorm ℝ 0 1 ψ := by
    simpa only [pow_zero, one_mul, iteratedDeriv_one] using ψ.le_seminorm' ℝ 0 1 x
  have hd : ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ ψ x :=
    fun x _ => (ψ.smooth 1).differentiable (by simp) x
  have ht := convex_univ.norm_image_sub_le_of_norm_deriv_le hd (fun x _ => hb x)
    (Set.mem_univ t) (Set.mem_univ s)
  simpa only [Real.norm_eq_abs] using ht

theorem schwartz_profile_lip_nonneg (ψ : 𝓢(ℝ, ℂ)) : 0 ≤ SchwartzMap.seminorm ℝ 0 1 ψ := by
  apply (norm_nonneg (deriv ψ 0)).trans
  simpa only [pow_zero, one_mul, iteratedDeriv_one] using ψ.le_seminorm' ℝ 0 1 0

/-- Concrete clipped factor for the Fourier weight on its declared M/X range. -/
noncomputable def fourierPolynomialFactor (P : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (v lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) : ClippedPolynomialFactor where
  polynomial := P
  profile := normalizedFourierProfile ψ v
  lo := lo
  hi := hi
  bound := SchwartzMap.seminorm ℝ 0 0 ψ
  lip := SchwartzMap.seminorm ℝ 0 0 ψ + SchwartzMap.seminorm ℝ 0 1 ψ * |v|
  lo_le_hi := hhi
  bound_nonneg := (norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0)
  lip_nonneg := add_nonneg ((norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0))
    (mul_nonneg (schwartz_profile_lip_nonneg ψ) (abs_nonneg v))
  norm_le := fun x hx => normalizedFourierProfile_norm ψ v _ x
    (schwartz_profile_bounds ψ).1 (hlo.trans hx.1)
  lipschitz := fun x hx y hy => normalizedFourierProfile_lipschitz ψ v _ _ x y
    (schwartz_profile_bounds ψ).1 (schwartz_profile_lip_nonneg ψ)
    (schwartz_profile_bounds ψ).2 (hlo.trans hx.1) (hlo.trans hy.1)

theorem fourierPolynomialFactor_original (P : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (v lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (x X M : ℝ)
    (hX : X ≠ 0) (hM : M ≠ 0) (hPM : P.eval x = M / X)
    (hmem : P.eval x ∈ Set.Icc lo hi) :
    (fourierPolynomialFactor P ψ v lo hi hlo hhi).value x =
      archimedeanLeafFactor X M v 1 ψ := by
  rw [ClippedPolynomialFactor.value_of_mem _ x hmem]
  change normalizedFourierProfile ψ v (P.eval x) = _
  rw [hPM]
  exact normalizedFourierProfile_original ψ X M v hX hM

end Ostmann

end OAI
