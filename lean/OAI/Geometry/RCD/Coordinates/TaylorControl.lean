import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

namespace OAI

/-!
# Taylor control on a coordinate-value segment

The final pair estimate only differentiates maps in Euclidean coordinate
value space. This lemma isolates that calculation, with an explicit second
derivative and no differentiability assumption on the underlying metric.
The bound has constant one; the final scale can absorb this harmless choice.
-/

open Set

namespace RegularPointCoordinates

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- First-order Taylor control along a unit parameter interval. -/
theorem norm_unit_interval_taylor_remainder_le
    {f g k : ℝ → F} {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (g t) t)
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g (k t) t)
    (hk : ∀ t ∈ Icc (0 : ℝ) 1, ‖k t‖ ≤ M) :
    ‖f 1 - f 0 - g 0‖ ≤ M := by
  have hgdiff (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖g t - g 0‖ ≤ M := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s hs => (hg s hs).hasDerivWithinAt)
      (fun s hs => hk s (Ico_subset_Icc_self hs)) t ht
    exact h.trans (by nlinarith [ht.2])
  have hder (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun s => f s - s • g 0) (g t - g 0) (Icc (0 : ℝ) 1) t := by
    simpa only [Pi.sub_apply, id_eq, one_smul] using
      ((hf t ht).fun_sub ((hasDerivAt_id t).smul_const (g 0))).hasDerivWithinAt
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hder
    (fun t ht => hgdiff t (Ico_subset_Icc_self ht))
  simpa only [one_smul, zero_smul, sub_zero, sub_right_comm] using h

/-- Only the second derivative in the direction of the segment is needed.
This form allows an arbitrary anisotropic frozen metric in the application. -/
theorem norm_taylor_remainder_le_directional
    {f : E → F} {df : E → E →L[ℝ] F}
    {ddf : E → E →L[ℝ] (E →L[ℝ] F)} {x z : E} {M : ℝ}
    (hM : 0 ≤ M)
    (hf : ∀ y ∈ segment ℝ x z, HasFDerivAt f (df y) y)
    (hdf : ∀ y ∈ segment ℝ x z, HasFDerivAt df (ddf y) y)
    (hbound : ∀ y ∈ segment ℝ x z, ‖ddf y (z - x) (z - x)‖ ≤ M) :
    ‖f z - f x - df x (z - x)‖ ≤ M := by
  let path : ℝ → E := fun t => x + t • (z - x)
  have hpathmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : path t ∈ segment ℝ x z := by
    have heq : path t = (1 - t) • x + t • z := by dsimp [path]; module
    rw [heq]
    simpa only [AffineMap.lineMap_apply_module] using lineMap_mem_segment ℝ x z ht
  have hpath (t : ℝ) : HasDerivAt path (z - x) t := by
    simpa [path] using ((hasDerivAt_id t).smul_const (z - x)).const_add x
  have hfpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s => f (path s)) (df (path t) (z - x)) t :=
    (hf (path t) (hpathmem t ht)).comp_hasDerivAt t (hpath t)
  have hgpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s => df (path s) (z - x)) (ddf (path t) (z - x) (z - x)) t := by
    have h := (hdf (path t) (hpathmem t ht)).comp_hasDerivAt t (hpath t)
    have hc : HasDerivAt (fun _ : ℝ => z - x) 0 t := hasDerivAt_const t (z - x)
    simpa only [map_zero, add_zero, Function.comp_apply] using h.clm_apply hc
  have h := norm_unit_interval_taylor_remainder_le hM hfpath hgpath
    (fun t ht => hbound (path t) (hpathmem t ht))
  simpa [path] using h

/-- A bound on the second derivative gives a quadratic Taylor error along
one segment. No convexity beyond that single segment is required. -/
theorem norm_taylor_remainder_le
    {f : E → F} {df : E → E →L[ℝ] F}
    {ddf : E → E →L[ℝ] (E →L[ℝ] F)} {x z : E} {M : ℝ}
    (hM : 0 ≤ M)
    (hf : ∀ y ∈ segment ℝ x z, HasFDerivAt f (df y) y)
    (hdf : ∀ y ∈ segment ℝ x z, HasFDerivAt df (ddf y) y)
    (hbound : ∀ y ∈ segment ℝ x z, ‖ddf y‖ ≤ M) :
    ‖f z - f x - df x (z - x)‖ ≤ M * ‖z - x‖ ^ 2 := by
  have hx : x ∈ segment ℝ x z := left_mem_segment ℝ x z
  have hz : z ∈ segment ℝ x z := right_mem_segment ℝ x z
  have hdiff (y : E) (hy : y ∈ segment ℝ x z) :
      ‖df y - df x‖ ≤ M * ‖z - x‖ := by
    have h₁ := (convex_segment x z).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun y hy => (hdf y hy).hasFDerivWithinAt) hbound hx hy
    exact h₁.trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hy) hM)
  let g : E → F := fun y => f y - df x y
  have hg (y : E) (hy : y ∈ segment ℝ x z) :
      HasFDerivWithinAt g (df y - df x) (segment ℝ x z) y :=
    ((hf y hy).sub (df x).hasFDerivAt).hasFDerivWithinAt
  have h := (convex_segment x z).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hg hdiff hx hz
  simpa [g, map_sub, sub_sub_sub_comm, pow_two, mul_assoc] using h

/-- Taylor control combined with bounds on the linearized image. -/
theorem dist_bounds_of_taylor
    {f : E → F} {df : E → E →L[ℝ] F}
    {ddf : E → E →L[ℝ] (E →L[ℝ] F)} {x z : E}
    {M a b t e : ℝ} (hM : 0 ≤ M)
    (hf : ∀ y ∈ segment ℝ x z, HasFDerivAt f (df y) y)
    (hdf : ∀ y ∈ segment ℝ x z, HasFDerivAt df (ddf y) y)
    (hbound : ∀ y ∈ segment ℝ x z, ‖ddf y‖ ≤ M)
    (hlower : a * t ≤ ‖df x (z - x)‖)
    (hupper : ‖df x (z - x)‖ ≤ b * t)
    (hsmall : M * ‖z - x‖ ^ 2 ≤ e * t) :
    (a - e) * t ≤ dist (f z) (f x) ∧ dist (f z) (f x) ≤ (b + e) * t := by
  have herr := (norm_taylor_remainder_le hM hf hdf hbound).trans hsmall
  have hnorm := norm_sub_norm_le (f z - f x) (df x (z - x))
  have hnorm' := norm_sub_norm_le (df x (z - x)) (f z - f x)
  rw [norm_sub_rev (df x (z - x)) (f z - f x)] at hnorm'
  rw [dist_eq_norm]
  constructor <;> nlinarith

/-- The metric comparison using only the diagonal second derivative. -/
theorem dist_bounds_of_directional_taylor
    {f : E → F} {df : E → E →L[ℝ] F}
    {ddf : E → E →L[ℝ] (E →L[ℝ] F)} {x z : E}
    {M a b t e : ℝ} (hM : 0 ≤ M)
    (hf : ∀ y ∈ segment ℝ x z, HasFDerivAt f (df y) y)
    (hdf : ∀ y ∈ segment ℝ x z, HasFDerivAt df (ddf y) y)
    (hbound : ∀ y ∈ segment ℝ x z, ‖ddf y (z - x) (z - x)‖ ≤ M)
    (hlower : a * t ≤ ‖df x (z - x)‖)
    (hupper : ‖df x (z - x)‖ ≤ b * t)
    (hsmall : M ≤ e * t) :
    (a - e) * t ≤ dist (f z) (f x) ∧ dist (f z) (f x) ≤ (b + e) * t := by
  have herr := (norm_taylor_remainder_le_directional hM hf hdf hbound).trans hsmall
  have hnorm := norm_sub_norm_le (f z - f x) (df x (z - x))
  have hnorm' := norm_sub_norm_le (df x (z - x)) (f z - f x)
  rw [norm_sub_rev (df x (z - x)) (f z - f x)] at hnorm'
  rw [dist_eq_norm]
  constructor <;> nlinarith

end RegularPointCoordinates

end OAI
