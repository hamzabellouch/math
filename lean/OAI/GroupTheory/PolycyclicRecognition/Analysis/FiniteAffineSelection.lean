import OAI.GroupTheory.PolycyclicRecognition.Analysis.AffineMeanApproximation
import Mathlib.Data.Fintype.Order

namespace OAI

/-! # Canonical finite labels and separation from translated competitors -/

noncomputable section
namespace PolycyclicRecognition

open Filter Set
open scoped Topology

/-- Fix one minimizing label at every parameter value. -/
def minimizingFiniteLabel {L : Type*} [Fintype L] [Nonempty L] (cost : L → ℝ) : L :=
  (Finset.exists_min_image Finset.univ cost Finset.univ_nonempty).choose

theorem minimizingFiniteLabel_le {L : Type*} [Fintype L] [Nonempty L]
    (cost : L → ℝ) (a : L) : cost (minimizingFiniteLabel cost) ≤ cost a :=
  (Finset.exists_min_image Finset.univ cost Finset.univ_nonempty).choose_spec.2 a
    (Finset.mem_univ a)

/-- The canonical choices inherit any vanishing competitor bound. -/
theorem minimizingFiniteLabel_tendsto_zero
    {L : Type*} [Fintype L] [Nonempty L] (cost : ℕ → L → ℝ)
    (hnonneg : ∀ n a, 0 ≤ cost n a)
    (a : ℕ → L) (ha : Tendsto (fun n => cost n (a n)) atTop (𝓝 0)) :
    Tendsto (fun n => cost n (minimizingFiniteLabel (cost n))) atTop (𝓝 0) :=
  squeeze_zero (fun n => hnonneg n _) (fun n => minimizingFiniteLabel_le (cost n) (a n)) ha

/-- Subtracting the value at the identity costs at most a factor of two
in the uniform norm. This removes arbitrary offsets from a comparison. -/
theorem linear_profile_distance_le_twice_affine
    {Z W : Type*} [TopologicalSpace Z] [CompactSpace Z] [NormedAddCommGroup W]
    (A B : C(Z, W)) (z₀ : Z) (hA : A z₀ = 0) (hB : B z₀ = 0) (b c : W) :
    dist A B ≤ 2 * dist (A + ContinuousMap.const Z b) (B + ContinuousMap.const Z c) := by
  let D := dist (A + ContinuousMap.const Z b) (B + ContinuousMap.const Z c)
  have hoff : dist b c ≤ D := by
    simpa only [ContinuousMap.add_apply, ContinuousMap.const_apply, hA, hB, zero_add] using
      (A + ContinuousMap.const Z b).dist_apply_le_dist
        (g := B + ContinuousMap.const Z c) z₀
  apply (ContinuousMap.dist_le (mul_nonneg (by norm_num) dist_nonneg)).mpr
  intro z
  have hpoint : dist (A z + b) (B z + c) ≤ D :=
    (A + ContinuousMap.const Z b).dist_apply_le_dist
      (g := B + ContinuousMap.const Z c) z
  calc
    dist (A z) (B z) = dist (A z + b) (B z + b) := (dist_add_right _ _ _).symm
    _ ≤ dist (A z + b) (B z + c) + dist (B z + c) (B z + b) := dist_triangle _ _ _
    _ = dist (A z + b) (B z + c) + dist b c := by rw [dist_add_left, dist_comm c b]
    _ ≤ D + D := add_le_add hpoint hoff
    _ = 2 * D := by ring

/-- Finitely many distinct centered profiles have a uniform positive
separation, even after arbitrary offsets are added. -/
theorem exists_finite_affine_label_separation
    {Z W L : Type*} [TopologicalSpace Z] [CompactSpace Z] [NormedAddCommGroup W]
    [Fintype L] [Nonempty L] (A : L → C(Z, W)) (hA : Function.Injective A)
    (z₀ : Z) (hzero : ∀ a, A a z₀ = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a a' b b',
      dist (A a + ContinuousMap.const Z b) (A a' + ContinuousMap.const Z b') < ε → a = a' := by
  classical
  let cost : L × L → ℝ := fun p => if p.1 = p.2 then 1 else dist (A p.1) (A p.2) / 3
  have hpos p : 0 < cost p := by
    dsimp only [cost]
    split_ifs with h
    · exact zero_lt_one
    · exact div_pos (dist_pos.mpr (fun he => h (hA he))) (by norm_num)
  let p := minimizingFiniteLabel cost
  refine ⟨cost p, hpos p, ?_⟩
  intro a a' b b' hd
  by_contra hne
  have hmin := minimizingFiniteLabel_le cost (a, a')
  have hdist := linear_profile_distance_le_twice_affine (A a) (A a') z₀
    (hzero a) (hzero a') b b'
  have he : cost (a, a') = dist (A a) (A a') / 3 := by simp [cost, hne]
  have hposdist : 0 < dist (A a) (A a') := dist_pos.mpr (fun h => hne (hA h))
  change cost p ≤ cost (a, a') at hmin
  rw [he] at hmin
  linarith

end PolycyclicRecognition

end

end OAI
