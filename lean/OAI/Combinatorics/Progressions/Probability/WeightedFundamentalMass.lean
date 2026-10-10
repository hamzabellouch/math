import OAI.Combinatorics.Progressions.Fourier.WeightedBlockTorus
import OAI.Combinatorics.Progressions.Lattices.AffineBlockScale

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem weightedCube_mass_on_fundamental_box {B I : Type*}
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {n K Q : ℕ} (s : B → Fin (n + 1) → NormalizedScalarCubeSource I) {V : ℝ}
    (hV : 0 ≤ V) (hK : 0 < K) (hvol : ∀ b, (∏ j, ((s b j).length : ℝ)) ≤ V * K)
    (hQ : blockJetScaleBound (Fintype.card I) (n + 1) (Fintype.card B) V ≤ Q)
    (J : Finset (Finset I)) (hJ : ∀ T ∈ J, T.card ≤ n + 1) (center z : J → ℤ)
    (hz : centeredFundamentalBox Q K center z) :
    integerGridMass (weightedCubeIntegerSource s) (weightedCubeIntegerJetSum s J center)
      ((2 * Q + 1) * K) z = finiteImageMass (weightedCubeIntegerSource s)
        (weightedCubeIntegerJetSum s J center) z := by
  apply integerGridMass_eq_imageMass_on_centered_box _ _ center z hK hQ _ hz
  intro x _ T
  exact weightedCubeIntegerJetSum_scale_bound s hV (Nat.cast_nonneg K) hvol J hJ center x T

theorem weightedModerate_mass_on_fundamental_box {B I : Type*}
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {n K Q : ℕ} (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin n → NormalizedScalarCubeSource I) (offset : B → ℤ) {V : ℝ}
    (hV : 0 ≤ V) (hK : 0 < K)
    (hvol : ∀ b, (|(offset b : ℝ)| + (c b).length) * (∏ j, ((s b j).length : ℝ)) ≤ V * K)
    (hQ : blockJetScaleBound (Fintype.card I) n (Fintype.card B) V ≤ Q)
    (J : Finset (Finset I)) (hJ : ∀ T ∈ J, T.card ≤ n) (center z : J → ℤ)
    (hz : centeredFundamentalBox Q K center z) :
    integerGridMass (weightedModerateIntegerProductSource c s)
      (weightedModerateIntegerJetSum c s J offset center) ((2 * Q + 1) * K) z =
        finiteImageMass (weightedModerateIntegerProductSource c s)
          (weightedModerateIntegerJetSum c s J offset center) z := by
  apply integerGridMass_eq_imageMass_on_centered_box _ _ center z hK hQ _ hz
  intro x _ T
  exact weightedModerateIntegerJetSum_scale_bound c s offset hV (Nat.cast_nonneg K) hvol J hJ center x T

end Erdos3

end

end OAI
