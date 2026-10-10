import OAI.GroupTheory.PolycyclicRecognition.Analysis.BasedImagePaths
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ProfileChainHeightBounds

namespace OAI

/-! # The bridge between the two actual probe images -/

noncomputable section
namespace PolycyclicRecognition

open Filter
open scoped Topology NNReal

variable {G W Z V : Type*} [Group G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [AddCommGroup V] [Module ℝ V]

/-- The product of the second path endpoint and the image bridge is the
first probe endpoint in the same anchor frame. -/
theorem basedImage_bridge_product (f : G → G) (a b c : G) :
    basedImage f a b * basedImage f b c = basedImage f a c := by
  simp [basedImage, mul_assoc]

/-- The normalization used for counting probe images cancels from every
raw height profile. -/
theorem rescaledMapProfile_basedImage
    (height : G →* Multiplicative W) (f : G → G) (a x k : G)
    (r : ℝ) (chart : Z → G) (z : Z) :
    rescaledMapProfile (fun g => (height (basedImage f a g)).toAdd) x k r chart z =
      rescaledMapProfile (fun g => (height (f g)).toAdd) x k r chart z := by
  dsimp only [rescaledMapProfile]
  rw [basedImage_height, basedImage_height]
  congr 1
  abel

/-- At the same Cartan coordinate the common affine profile gives a
sublinear endpoint height, independently of its affine offset. -/
theorem basedImage_height_le_of_common_profile
    (height : G →* Multiplicative W) (f : G → G)
    (x first second : G) (r : ℝ) (chart : Z → G)
    (q : Z → V) (A : V →ₗ[ℝ] W) (b : W) (z : Z)
    {ε₁ ε₂ : ℝ}
    (hfirst : ‖rescaledMapProfile (fun g => (height (f g)).toAdd) x first r chart z -
      (A (q z) + b)‖ ≤ ε₁)
    (hsecond : ‖rescaledMapProfile (fun g => (height (f g)).toAdd) x second r chart z -
      (A (q z) + b)‖ ≤ ε₂) :
    ‖(height (basedImage f (x * first * chart z) (x * second * chart z))).toAdd‖ ≤
      Real.exp r * (ε₁ + ε₂) := by
  have hh := relative_height_of_common_affine_profiles
    (fun g => (height (f g)).toAdd) x second first r chart q A b z z hsecond hfirst
  rw [basedImage_height]
  simpa only [sub_self, map_zero, smul_zero, sub_zero, add_comm] using hh

/-- Vanishing profile error makes the same-coordinate endpoint height
smaller than any fixed positive multiple of the geometric scale. -/
theorem eventually_basedImage_height_small
    (height : G →* Multiplicative W) (f : ℕ → G → G)
    (x first second : ℕ → G) (scale ε : ℕ → ℝ) (chart : ℕ → Z → G)
    (q : Z → V) (A : V →ₗ[ℝ] W) (b : W) (z : ℕ → Z)
    (hscale : ∀ n, 0 < scale n) (hε : Tendsto ε atTop (𝓝 0))
    (hfirst : ∀ n, ‖rescaledMapProfile (fun g => (height (f n g)).toAdd)
      (x n) (first n) (Real.log (scale n)) (chart n) (z n) -
        (A (q (z n)) + b)‖ ≤ ε n)
    (hsecond : ∀ n, ‖rescaledMapProfile (fun g => (height (f n g)).toAdd)
      (x n) (second n) (Real.log (scale n)) (chart n) (z n) -
        (A (q (z n)) + b)‖ ≤ ε n)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop,
      ‖(height (basedImage (f n) (x n * first n * chart n (z n))
        (x n * second n * chart n (z n)))).toAdd‖ ≤ δ * scale n := by
  have hsmall : ∀ᶠ n in atTop, ε n + ε n ≤ δ :=
    ((hε.add hε).eventually (eventually_le_nhds (by simpa using hδ)))
  filter_upwards [hsmall] with n hn
  have hh := basedImage_height_le_of_common_profile height (f n) (x n) (first n) (second n)
    (Real.log (scale n)) (chart n) q A b (z n) (hfirst n) (hsecond n)
  rw [Real.exp_log (hscale n)] at hh
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hn (hscale n).le])

section Metric

variable [MetricSpace G] [IsIsometricSMul G G]

theorem basedImage_lipschitz (f : G → G) {K : ℝ≥0} (hf : LipschitzWith K f) (a : G) :
    LipschitzWith K (basedImage f a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [basedImage_dist]
  exact hf.dist_le_mul x y

/-- Left invariance identifies the bridge length with endpoint distance. -/
theorem dist_one_inv_mul_eq (a b : G) : dist 1 (a⁻¹ * b) = dist a b := by
  simpa only [inv_mul_cancel] using dist_mul_left a⁻¹ a b

/-- The actual image bridge has the Lipschitz-scaled source length. -/
theorem basedImage_bridge_dist (f : G → G) {K : ℝ≥0} (hf : LipschitzWith K f)
    (a b : G) : dist 1 (basedImage f a b) ≤ (K : ℝ) * dist a b := by
  calc
    dist 1 (basedImage f a b) = dist (f a) (f b) := by
      rw [← basedImage_dist f a a b]
      simp only [basedImage, inv_mul_cancel]
    _ ≤ _ := hf.dist_le_mul a b

/-- A single small source parameter works for every probe when the
source bridge constants are uniform. No division by a possibly zero
Lipschitz constant or bridge constant is used. -/
theorem exists_uniform_bridge_parameter {K C D τ : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D) (hτ : 0 < τ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ε : ℝ, 0 ≤ δ → δ ≤ δ₀ →
      0 ≤ ε → ε ≤ δ₀ → K * (C * δ + D * ε) ≤ τ := by
  let a := K * (C + D)
  have ha : 0 ≤ a := mul_nonneg hK (add_nonneg hC hD)
  refine ⟨τ / (a + 1), div_pos hτ (by positivity), ?_⟩
  intro δ ε _ hδ _ hε
  calc
    K * (C * δ + D * ε) ≤ K * (C * (τ / (a + 1)) + D * (τ / (a + 1))) := by
      exact mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left hδ hC) (mul_le_mul_of_nonneg_left hε hD)) hK
    _ = a * (τ / (a + 1)) := by dsimp only [a]; ring
    _ ≤ (a + 1) * (τ / (a + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = τ := mul_div_cancel₀ τ (by positivity)

end Metric

/-- Profile agreement controls the endpoint heights uniformly over a
retained family of probes, with one scale threshold for the whole family. -/
theorem eventually_uniform_probe_height_small {J : ℕ → Type*}
    (height : G →* Multiplicative W) (f : ℕ → G → G)
    (x : ℕ → G) (first second : ∀ n, J n → G) (good : ∀ n, Set (J n))
    (scale ε : ℕ → ℝ) (chart : ℕ → Z → G)
    (q : Z → V) (A : V →ₗ[ℝ] W) (b : W) (z : ℕ → Z)
    (hscale : ∀ n, 0 < scale n) (hε : Tendsto ε atTop (𝓝 0))
    (hgood : ∀ᶠ n in atTop, ∀ j ∈ good n,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd)
        (x n) (first n j) (Real.log (scale n)) (chart n) (z n) -
          (A (q (z n)) + b)‖ ≤ ε n ∧
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd)
        (x n) (second n j) (Real.log (scale n)) (chart n) (z n) -
          (A (q (z n)) + b)‖ ≤ ε n)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ j ∈ good n,
      ‖(height (basedImage (f n) (x n * first n j * chart n (z n))
        (x n * second n j * chart n (z n)))).toAdd‖ ≤ δ * scale n := by
  have hsmall : ∀ᶠ n in atTop, ε n + ε n ≤ δ :=
    (hε.add hε).eventually (eventually_le_nhds (by simpa using hδ))
  filter_upwards [hgood, hsmall] with n hn hεn
  intro j hj
  have hh := basedImage_height_le_of_common_profile height (f n) (x n)
    (first n j) (second n j) (Real.log (scale n)) (chart n) q A b (z n)
    (hn j hj).1 (hn j hj).2
  rw [Real.exp_log (hscale n)] at hh
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hεn (hscale n).le])

end PolycyclicRecognition

end

end OAI
