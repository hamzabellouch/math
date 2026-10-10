import Mathlib
import OAI.Geometry.DoublingHilbert.FinitePlacement
import OAI.Geometry.DoublingHilbert.CoverTransfer
import OAI.Geometry.DoublingHilbert.Main

namespace OAI

open Set Metric
open scoped BigOperators
noncomputable section
namespace CompactBanach
open DoublingHilbert

theorem cluster_placement {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (hB : ¬ FiniteDimensional ℝ B)
    (hS : AmbientDoubling constructedSet 76800)
    (s : Finset constructedSet) (v : B) {r : ℝ} (hr : 0 < r) :
    ∃ f : s → B, (∀ x, dist (f x) (r • v) ≤ r / 100) ∧
      DoublingAtMost (Set.range f) (76800 ^ 8) ∧
      ∃ a : ℝ, 0 < a ∧ ∀ x y : s,
        a * dist x y ≤ dist (f x) (f y) ∧
          dist (f x) (f y) ≤ 36 * a * dist x y := by
  classical
  let X : Finset RealL2 := s.image Subtype.val
  have hX : ∀ z ∈ X, z ∈ constructedSet := by
    intro z hz
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    exact x.property
  obtain ⟨T, hT⟩ := finite_placement hB X hX
  let M : ℝ := 1 + ∑ x : s, ‖T x.val.val‖
  have hM : 0 < M := by dsimp [M]; positivity
  have hxM (x : s) : ‖T x.val.val‖ ≤ M := by
    have ht := Finset.single_le_sum (fun (y : s) _ => norm_nonneg (T y.val.val))
      (Finset.mem_univ x)
    exact ht.trans (le_add_of_nonneg_left zero_le_one)
  let ρ : ℝ := r / (100 * M)
  have hρ : 0 < ρ := div_pos hr (mul_pos (by norm_num) hM)
  have hρM : ρ * M = r / 100 := by dsimp [ρ]; field_simp [ne_of_gt hM]
  let f : s → B := fun x => r • v + ρ • T x.val.val
  have hf (x y : s) : dist (f x) (f y) = ρ * dist (T x.val.val) (T y.val.val) := by
    dsimp [f]
    rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hρ]
  have hTs (x y : s) : dist x y / 6 ≤ dist (T x.val.val) (T y.val.val) ∧
      dist (T x.val.val) (T y.val.val) ≤ 6 * dist x y := by
    apply hT
    · exact Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩
    · exact Finset.mem_image.mpr ⟨y.val, y.property, rfl⟩
  have hd (x y : s) : (ρ / 6) * dist x y ≤ dist (f x) (f y) ∧
      dist (f x) (f y) ≤ 36 * (ρ / 6) * dist x y := by
    rw [hf]
    constructor
    · have hh := mul_le_mul_of_nonneg_left (hTs x y).1 hρ.le
      nlinarith
    · have hh := mul_le_mul_of_nonneg_left (hTs x y).2 hρ.le
      nlinarith
  refine ⟨f, ?_, ?_, ρ / 6, by positivity, hd⟩
  · intro x
    dsimp [f]
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    exact (mul_le_mul_of_nonneg_left (hxM x) hρ.le).trans_eq hρM
  · exact range_doubling_of_distortion36 hS (fun x : s => x.val.val)
      (fun x => x.val.property) f (by positivity : 0 < ρ / 6) hd

end CompactBanach
end

end OAI
