import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PrimeCellFreezing
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem opNorm_le_card_mul (L : (ι → ℝ) →L[ℝ] ℂ) {D : ℝ} (hD : 0 ≤ D)
    (hL : ∀ i, ‖L (Pi.single i 1)‖ ≤ D) : ‖L‖ ≤ (Fintype.card ι:ℝ)*D := by
  apply L.opNorm_le_bound (by positivity)
  intro x
  have hx : x=∑ i, (x i) • Pi.single i (1:ℝ) := by
    funext j
    simp [Finset.sum_apply,Pi.single_apply]
  conv_lhs => arg 1; rw [hx]
  rw [map_sum]
  calc
    _ ≤ ∑ i, ‖L ((x i) • Pi.single i (1:ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖x‖*D := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul,norm_smul]
      exact mul_le_mul (norm_le_pi_norm x i) (hL i) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

def logRectangle (lo hi : ι → ℝ) : Set (ι → ℝ) :=
  Set.pi Set.univ (fun i => Set.Icc (lo i) (hi i))

omit [Fintype ι] [DecidableEq ι] in
theorem logRectangle_convex (lo hi : ι → ℝ) : Convex ℝ (logRectangle lo hi) :=
  convex_pi (fun _ _ => convex_Icc _ _)

theorem norm_sub_le_of_partials (f : (ι → ℝ) → ℂ) (lo hi : ι → ℝ)
    {D mesh : ℝ} (hD : 0 ≤ D) (hm : 0 ≤ mesh)
    (hf : ∀ z ∈ logRectangle lo hi, DifferentiableAt ℝ f z)
    (hderiv : ∀ z ∈ logRectangle lo hi, ∀ i, ‖fderiv ℝ f z (Pi.single i 1)‖ ≤ D)
    {x y : ι → ℝ} (hx : x ∈ logRectangle lo hi) (hy : y ∈ logRectangle lo hi)
    (hxy : ∀ i, |x i-y i| ≤ mesh) :
    ‖f x-f y‖ ≤ (Fintype.card ι:ℝ)*D*mesh := by
  have hh := (logRectangle_convex lo hi).norm_image_sub_le_of_norm_fderiv_le hf
    (fun z hz => opNorm_le_card_mul _ hD (hderiv z hz)) hy hx
  have hn : ‖x-y‖ ≤ mesh := (pi_norm_le_iff_of_nonneg hm).mpr (fun i => by
    simpa only [Pi.sub_apply,Real.norm_eq_abs] using hxy i)
  exact hh.trans (mul_le_mul_of_nonneg_left hn (by positivity))

theorem weighted_freezing_bound {A : Type*} (s : Finset A) (c : A → ℂ)
    (f : (ι → ℝ) → ℂ) (lo hi : ι → ℝ) (x y : A → ι → ℝ)
    {D mesh : ℝ} (hD : 0 ≤ D) (hm : 0 ≤ mesh)
    (hf : ∀ z ∈ logRectangle lo hi, DifferentiableAt ℝ f z)
    (hderiv : ∀ z ∈ logRectangle lo hi, ∀ i, ‖fderiv ℝ f z (Pi.single i 1)‖ ≤ D)
    (hx : ∀ a ∈ s, x a ∈ logRectangle lo hi) (hy : ∀ a ∈ s, y a ∈ logRectangle lo hi)
    (hxy : ∀ a ∈ s, ∀ i, |x a i-y a i| ≤ mesh) :
    ‖(∑ a ∈ s,c a*f (x a))-(∑ a ∈ s,c a*f (y a))‖ ≤
      (Fintype.card ι:ℝ)*D*mesh*∑ a ∈ s,‖c a‖ := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a ∈ s, ‖c a*f (x a)-c a*f (y a)‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ s, ‖c a‖*((Fintype.card ι:ℝ)*D*mesh) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [← mul_sub,norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_sub_le_of_partials f lo hi hD hm hf hderiv (hx a ha) (hy a ha) (hxy a ha))
        (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

end Ostmann.Arithmetic.PrimeCellFreezing

end

end OAI
