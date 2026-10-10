import Mathlib
import OAI.Analysis.Unitarizability.MeanBounds

namespace OAI

noncomputable section
namespace Dixmier
namespace DayDixmier
open scoped BoundedContinuousFunction ComplexConjugate
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

section Form
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (π : G →* (H →L[ℂ] H)) {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ g, ‖π g‖ ≤ M)

def coefficient (x y : H) : G →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun g => inner ℂ (π g⁻¹ x) (π g⁻¹ y)) (M^2 * ‖x‖ * ‖y‖) (fun g => by
      calc
        ‖inner ℂ (π g⁻¹ x) (π g⁻¹ y)‖ ≤ ‖π g⁻¹ x‖ * ‖π g⁻¹ y‖ := norm_inner_le_norm _ _
        _ ≤ (M * ‖x‖) * (M * ‖y‖) := mul_le_mul
          ((π g⁻¹).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hπ _) (norm_nonneg _)))
          ((π g⁻¹).le_opNorm y |>.trans (mul_le_mul_of_nonneg_right (hπ _) (norm_nonneg _)))
          (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))
        _ = M^2 * ‖x‖ * ‖y‖ := by ring)

@[simp] lemma coefficient_apply (x y : H) (g : G) :
    coefficient π hM hπ x y g = inner ℂ (π g⁻¹ x) (π g⁻¹ y) := rfl

lemma coefficient_norm_le (x y : H) :
    ‖coefficient π hM hπ x y‖ ≤ M^2 * ‖x‖ * ‖y‖ := by
  unfold coefficient BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity) _

lemma coefficient_add_left (x y z : H) :
    coefficient π hM hπ (x + y) z = coefficient π hM hπ x z + coefficient π hM hπ y z := by
  ext g
  simp

lemma coefficient_add_right (x y z : H) :
    coefficient π hM hπ x (y + z) = coefficient π hM hπ x y + coefficient π hM hπ x z := by
  ext g
  simp

lemma coefficient_smul_left (c : ℂ) (x y : H) :
    coefficient π hM hπ (c • x) y = (starRingEnd ℂ c) • coefficient π hM hπ x y := by
  ext g
  simp [mul_comm]

lemma coefficient_smul_right (c : ℂ) (x y : H) :
    coefficient π hM hπ x (c • y) = c • coefficient π hM hπ x y := by
  ext g
  simp

lemma coefficient_translate (h : G) (x y : H) :
    coefficient π hM hπ (π h x) (π h y) = leftTranslate h (coefficient π hM hπ x y) := by
  ext g
  simp [leftTranslate, coefficient, map_mul, mul_apply_eq_comp]

def averagedForm (m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ) : H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ where
  toFun x :=
    { toFun y := m (coefficient π hM hπ x y)
      map_add' y z := by rw [coefficient_add_right, map_add]
      map_smul' c y := by rw [coefficient_smul_right, map_smul]; rfl }
  map_add' x y := by
    ext z
    change m (coefficient π hM hπ (x + y) z) = _
    rw [coefficient_add_left, map_add]
    rfl
  map_smul' c x := by
    ext y
    change m (coefficient π hM hπ (c • x) y) = _
    rw [coefficient_smul_left, map_smul]
    rfl

lemma averagedForm_bound (m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ)
    (h1 : m (BoundedContinuousFunction.const G 1) = 1)
    (hp : ∀ f : G →ᵇ ℂ, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (m f).re ∧ (m f).im = 0) (x y : H) :
    ‖averagedForm π hM hπ m x y‖ ≤ (2 * M^2) * ‖x‖ * ‖y‖ := by
  change ‖m (coefficient π hM hπ x y)‖ ≤ _
  calc
    _ ≤ 2 * ‖coefficient π hM hπ x y‖ := mean_norm_le m h1 hp _
    _ ≤ 2 * (M^2 * ‖x‖ * ‖y‖) := mul_le_mul_of_nonneg_left
      (coefficient_norm_le π hM hπ x y) (by norm_num)
    _ = _ := by ring

lemma averagedForm_nonneg (m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ)
    (hp : ∀ f : G →ᵇ ℂ, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (m f).re ∧ (m f).im = 0) (x : H) :
    0 ≤ (m (coefficient π hM hπ x x)).re ∧ (m (coefficient π hM hπ x x)).im = 0 := by
  apply hp
  intro g
  simpa only [coefficient_apply, RCLike.re_to_complex, RCLike.im_to_complex] using
    And.intro (inner_self_nonneg (𝕜 := ℂ) (x := π g⁻¹ x)) (inner_self_im (𝕜 := ℂ) (π g⁻¹ x))

lemma averagedForm_lower (m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ)
    (h1 : m (BoundedContinuousFunction.const G 1) = 1)
    (hp : ∀ f : G →ᵇ ℂ, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (m f).re ∧ (m f).im = 0) (x : H) :
    ‖x‖^2 ≤ M^2 * (m (coefficient π hM hπ x x)).re := by
  have hnorm (g : G) : ‖x‖ ≤ M * ‖π g⁻¹ x‖ := by
    calc
      ‖x‖ = ‖π g (π g⁻¹ x)‖ := by simp [← mul_apply_eq_comp, ← map_mul]
      _ ≤ ‖π g‖ * ‖π g⁻¹ x‖ := (π g).le_opNorm _
      _ ≤ M * ‖π g⁻¹ x‖ := mul_le_mul_of_nonneg_right (hπ g) (norm_nonneg _)
  have hpos := hp (((M^2 : ℝ) : ℂ) • coefficient π hM hπ x x -
      BoundedContinuousFunction.const G ((‖x‖^2 : ℝ) : ℂ)) (by
    intro g
    have hre : (inner ℂ (π g⁻¹ x) (π g⁻¹ x)).re = ‖π g⁻¹ x‖^2 := by
      simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) (π g⁻¹ x)
    have him : (inner ℂ (π g⁻¹ x) (π g⁻¹ x)).im = 0 := by
      simpa only [RCLike.im_to_complex] using inner_self_im (𝕜 := ℂ) (π g⁻¹ x)
    simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.smul_apply,
      BoundedContinuousFunction.const_apply, coefficient_apply, smul_eq_mul, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.sub_im, Complex.mul_im, zero_add, hre, him, mul_zero]
    constructor
    · have hsqr := (sq_le_sq₀ (norm_nonneg x)
        (mul_nonneg hM (norm_nonneg (π g⁻¹ x)))).mpr (hnorm g)
      nlinarith [hsqr]
    · simp)
  rw [map_sub, map_smul, mean_const m h1] at hpos
  simpa only [smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, sub_nonneg] using hpos.1

end Form

end DayDixmier
end Dixmier
end

end OAI
