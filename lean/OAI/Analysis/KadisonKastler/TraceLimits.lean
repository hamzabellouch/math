import OAI.Analysis.KadisonKastler.FreeHaarClosure

namespace OAI

/-! # Limits in the faithful tracial two-norm -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B : Type*} [CStarAlgebra B]

@[simp]
theorem traceTwoNorm_zero (τ : FaithfulTracialState B) : traceTwoNorm τ 0 = 0 := by
  simp [traceTwoNorm]

@[simp]
theorem traceTwoNorm_eq_zero_iff (τ : FaithfulTracialState B) (x : B) :
    traceTwoNorm τ x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply τ.faithful
    apply Complex.ext
    · have h := traceTwoNorm_sq τ x
      rw [hx, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
      simpa only [Complex.zero_re] using h.symm
    · simpa only [Complex.zero_im] using τ.positive_im x
  · rintro rfl
    exact traceTwoNorm_zero τ

/-- Limits in the faithful tracial two-norm are unique. -/
theorem traceTwoNorm_limit_unique (τ : FaithfulTracialState B)
    {J : Type*} {l : Filter J} [l.NeBot] (x : J → B) {a b : B}
    (ha : Tendsto (fun j => traceTwoNorm τ (x j - a)) l (𝓝 0))
    (hb : Tendsto (fun j => traceTwoNorm τ (x j - b)) l (𝓝 0)) : a = b := by
  have hbound (j : J) : traceTwoNorm τ (a - b) ≤
      traceTwoNorm τ (x j - a) + traceTwoNorm τ (x j - b) := by
    calc
      _ = traceTwoNorm τ (-(x j - a) + (x j - b)) := by congr 1; abel
      _ ≤ _ := by simpa only [traceTwoNorm_neg] using traceTwoNorm_add_le τ (-(x j - a)) (x j - b)
  have hz : traceTwoNorm τ (a - b) ≤ 0 :=
    ge_of_tendsto (by simpa only [zero_add] using ha.add hb) (Eventually.of_forall hbound)
  exact sub_eq_zero.mp ((traceTwoNorm_eq_zero_iff τ _).mp
    (le_antisymm hz (traceTwoNorm_nonneg τ _)))

/-- Multiplication preserves two-norm limits on a uniformly bounded left factor. -/
theorem traceTwoNorm_tendsto_mul (τ : FaithfulTracialState B)
    {J : Type*} {l : Filter J} (x y : J → B) (a b : B)
    {C : ℝ} (hx : ∀ j, ‖x j‖ ≤ C)
    (ha : Tendsto (fun j => traceTwoNorm τ (x j - a)) l (𝓝 0))
    (hb : Tendsto (fun j => traceTwoNorm τ (y j - b)) l (𝓝 0)) :
    Tendsto (fun j => traceTwoNorm τ (x j * y j - a * b)) l (𝓝 0) := by
  apply squeeze_zero (g := fun j => C * traceTwoNorm τ (y j - b) +
    traceTwoNorm τ (x j - a) * ‖b‖) (fun j => traceTwoNorm_nonneg τ _)
  · intro j
    have he : x j * y j - a * b = x j * (y j - b) + (x j - a) * b := by noncomm_ring
    rw [he]
    exact (traceTwoNorm_add_le τ _ _).trans (add_le_add
      ((traceTwoNorm_mul_le_left τ _ _).trans
        (mul_le_mul_of_nonneg_right (hx j) (traceTwoNorm_nonneg τ _)))
      (traceTwoNorm_mul_le_right τ _ _))
  · simpa only [mul_zero, zero_mul, zero_add] using (hb.const_mul C).add (ha.mul_const ‖b‖)

end

end KadisonKastler

end OAI
