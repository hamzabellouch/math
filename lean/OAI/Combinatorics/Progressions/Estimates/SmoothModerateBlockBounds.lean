import OAI.Combinatorics.Progressions.Probability.SmoothModerateBlockLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem smoothModerateBlockSum_support {b g q M K : ℕ} {B T : ℝ≥0}
    (c : Fin b → SmoothCoefficientSlice M B T) (s : Fin b → Fin g → SmoothCubeSlice q M B T)
    (offset : Fin b → ℤ) (stride : Fin b → ℕ) {O F : ℝ} (hO : 0 ≤ O)
    (hroot : ∀ a j, |((s a j).root : ℝ)| ≤ O * (s a j).length)
    (hupper : ∀ a, (|(offset a : ℝ)| + (stride a : ℝ) * (c a).length) *
      (∏ j, ((s a j).length : ℝ)) ≤ F * K)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ g)
    (center : J → ℤ) (x : SmoothModerateBlockDomain c s) (Z : J) :
    |(smoothModerateBlockSum c s offset stride J center x Z : ℝ) - center Z| ≤
      (affineTorusRadius q g b (O + 1) F : ℝ) * K := by
  let fs := fun a j => (s a j).finiteSlice
  let coeff := fun (z : ∀ a, (c a).Domain) a => offset a + (stride a : ℤ) * (z a).val
  let z := fun a => (x a).1
  let y := fun a j => (x a).2 j
  let H := fun a => |(offset a : ℝ)| + (stride a : ℝ) * (c a).length
  have hradius (a : Fin b) (j : Fin g) :
      ((fs a j).radius : ℝ) ≤ (((q + 1 : ℕ) : ℝ) * (O + 1)) * (fs a j).length := by
    apply ((s a j).finiteSlice.radius_relative (hroot a j)).trans
    have hq : (1 : ℝ) ≤ (q + 1 : ℕ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le q))
    have h := mul_le_mul_of_nonneg_right hq
      (show 0 ≤ (O + 1) * (fs a j).length by positivity)
    simpa only [one_mul, mul_assoc] using h
  have hbound := cubeSliceBlockSum_bound fs coeff J center (z, y) Z
  have hscale := cubeSliceBlockBound_le_scale fs coeff z H
    (show 0 ≤ ((q + 1 : ℕ) : ℝ) * (O + 1) by positivity)
    (fun a => (c a).affine_abs_le (offset a) (stride a) (z a)) hradius
    (fun a => by simpa only [H, fs, SmoothCubeSlice.finiteSlice] using hupper a)
    Z (hJ Z Z.property)
  have hraw : |(smoothModerateBlockSum c s offset stride J center x Z : ℝ) - center Z| ≤
      (cubeSliceBlockBound fs coeff z Z : ℝ) := by
    exact_mod_cast (show |smoothModerateBlockSum c s offset stride J center x Z - center Z| ≤
      cubeSliceBlockBound fs coeff z Z from by
        simpa only [cubeSliceBlockSum, coeff, smoothModerateBlockSum, fs, z, y] using hbound)
  exact (hraw.trans hscale).trans
    (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg K))

end Erdos3

end

end OAI
