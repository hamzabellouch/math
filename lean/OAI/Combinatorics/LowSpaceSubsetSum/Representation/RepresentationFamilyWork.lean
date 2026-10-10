import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationFamilyPreparation

namespace OAI

/-! # The complete family draw fits the half-exponential work scale -/

namespace LowSpaceSubsetSum.RepresentationFamilyWork

variable {n : ℕ}

theorem bound (I : Instance n) (hn : 10000 ≤ n) :
    60 * RepresentationFamilyPreparation.width n + 51 +
      44 * 2 ^ RepresentationFamilyPreparation.width n *
        (RepresentationFamilyPreparation.width n * n ^ 3 +
          32 * (RepresentationFamilyPreparation.width n + 1) ^ 3 + 4) + 22 ≤
      inputScale I ^ 6 * 2 ^ ((n + 1) / 2) := by
  let g := RepresentationFamilyPreparation.width n
  let u := inputScale I
  let H := 2 ^ ((n + 1) / 2)
  have hu : n + 1 ≤ u := by dsimp [u, inputScale]; omega
  have hu0 : 10000 ≤ u := by omega
  have hg : g ≤ n := by
    dsimp [g, RepresentationFamilyPreparation.width, StoredTopCoordinates.width,
      RepresentationSetup.blockHalf]
    omega
  have hgh : g ≤ (n + 1) / 2 := by
    dsimp [g, RepresentationFamilyPreparation.width, StoredTopCoordinates.width,
      RepresentationSetup.blockHalf]
    omega
  have hH : 1 ≤ H := Nat.one_le_two_pow
  have hpow : 2 ^ g ≤ H := Nat.pow_le_pow_right (by decide) hgh
  have hu1 : 1 ≤ u ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hu3 : u ^ 3 ≤ u ^ 4 := pow_le_pow_right' (by omega) (by decide)
  have hgu : g ≤ u ^ 4 := by
    exact (show g ≤ u by omega).trans (by
      simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ u) (by decide : 1 ≤ 4))
  have hgn : g * n ^ 3 ≤ u ^ 4 := by
    have h := Nat.mul_le_mul (show g ≤ u by omega) (Nat.pow_le_pow_left (show n ≤ u by omega) 3)
    simpa only [← pow_succ'] using h
  have hg3 : (g + 1) ^ 3 ≤ u ^ 4 :=
    (Nat.pow_le_pow_left (show g + 1 ≤ u by omega) 3).trans hu3
  have hinner : g * n ^ 3 + 32 * (g + 1) ^ 3 + 4 ≤ 37 * u ^ 4 := by
    nlinarith only [hgn, hg3, hu1]
  have hmain := Nat.mul_le_mul (Nat.mul_le_mul_left 44 hpow) hinner
  have hlinear : 60 * g + 73 ≤ 133 * u ^ 4 := by nlinarith only [hgu, hu1]
  have hlinearH := hlinear.trans (Nat.le_mul_of_pos_right _ hH)
  have htotal : 60 * g + 51 + 44 * 2 ^ g * (g * n ^ 3 + 32 * (g + 1) ^ 3 + 4) + 22 ≤
      1761 * u ^ 4 * H := by nlinarith only [hmain, hlinearH]
  have hu2 : 1761 ≤ u ^ 2 := by nlinarith only [hu0]
  have hf : 1761 * u ^ 4 ≤ u ^ 6 := by
    calc
      _ ≤ u ^ 2 * u ^ 4 := Nat.mul_le_mul_right _ hu2
      _ = _ := by ring
  exact htotal.trans (Nat.mul_le_mul_right H hf)

end LowSpaceSubsetSum.RepresentationFamilyWork

end OAI
