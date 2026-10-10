import OAI.Geometry.ProjectionVolume.Arithmetic
import OAI.Geometry.ProjectionVolume.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

namespace OAI

universe uE

open Set
open scoped RealInnerProductSpace

namespace Paper092

theorem centered_segment_neg {E : Type uE} [AddCommGroup E] [Module ℝ E] (v : E) :
    segment ℝ (-(1 / 2 : ℝ) • (-v)) ((1 / 2 : ℝ) • (-v)) =
      segment ℝ (-(1 / 2 : ℝ) • v) ((1 / 2 : ℝ) • v) := by
  simpa only [smul_neg, neg_smul, neg_neg] using
    (segment_symm ℝ ((1 / 2 : ℝ) • v) (-((1 / 2 : ℝ) • v)))

theorem nearest_point_separates {n : ℕ} (K : Set (Euclidean n))
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    {x : Euclidean n} (hx : x ∉ K) :
    ∃ y ∈ K, (∀ z ∈ K, ⟪x - y, z - y⟫ ≤ 0) ∧
      (∀ z ∈ K, ⟪x - y, z⟫ ≤ ⟪x - y, y⟫) ∧
      ⟪x - y, y⟫ < ⟪x - y, x⟫ := by
  obtain ⟨y, hy, hmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hne hK.isComplete hconv x
  have hi := (norm_eq_iInf_iff_real_inner_le_zero hconv hy).mp hmin
  refine ⟨y, hy, hi, ?_, ?_⟩
  · intro z hz
    have h := hi z hz
    rwa [inner_sub_right, sub_nonpos] at h
  · have hxy : x - y ≠ 0 := sub_ne_zero.mpr (fun h => hx (h ▸ hy))
    have hpos : 0 < ⟪x - y, x - y⟫ := by
      rw [real_inner_self_eq_norm_sq]
      exact sq_pos_of_pos (norm_pos_iff.mpr hxy)
    rwa [inner_sub_right, sub_pos] at hpos

theorem binomial_twenty_ten : Nat.choose 20 10 = 184756 := by
  rw [Nat.choose_eq_factorial_div_factorial (by norm_num : 10 ≤ 20)]
  norm_num [Nat.factorial]

theorem exact_integer_certificate :
    (121 : ℤ) * 184756 - 21 * 1048576 = 335380 ∧ (0 : ℤ) < 335380 := by norm_num

end Paper092

end OAI
