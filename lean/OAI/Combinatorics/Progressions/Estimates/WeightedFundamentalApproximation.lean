import OAI.Combinatorics.Progressions.Probability.WeightedFundamentalMass
import OAI.Combinatorics.Progressions.Sampling.JointGridAccuracy
import OAI.Combinatorics.Progressions.Sampling.WeightedUniformGridDensity

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem weightedCube_uniform_fundamental_approximation {B I : Type*}
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {n K Q : ℕ} [NeZero K] (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L T ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hT : 0 ≤ T) (hε : 0 < ε)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U) (hlen : ∀ b j, L ≤ (s b j).length)
    (hvol : ∀ b, (∏ j, ((s b j).length : ℝ)) ≤ T * K)
    (hQ : blockJetScaleBound (Fintype.card I) (n + 1) (Fintype.card B) T ≤ Q)
    (t : ℕ) (J : Finset (Finset I)) (hJ : ∀ F ∈ J, F.card ≤ n + 1)
    (hB : uniformSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (((2 * Q + 1) * K : ℕ) : ℝ) ^ J.card ≤ W * L ^ t)
    (hscale : ∀ b, (((2 * Q + 1) * K : ℕ) : ℝ) / ∏ j, ((s b j).length : ℝ) ≤ V) :
    let ζ := uniformBlockRetainedBias n J.card t U V W ε
    let S := uniformBlockSpectrumCover J ((2 * Q + 1) * K) n U V L ζ
    ∀ center z : J → ℤ, centeredFundamentalBox Q K center z →
      ‖(((K : ℝ) ^ J.card * finiteImageMass (weightedCubeIntegerSource s)
        (weightedCubeIntegerJetSum s J center) z : ℝ) : ℂ) -
        weightedCubeGridApproximation s K ((2 * Q + 1) * K) J center z S‖ ≤ ε := by
  dsimp only
  have hK : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hd := (weightedCube_uniform_grid_density s A hA hU hV hW hL hε h hlen K
    ((2 * Q + 1) * K) t J hJ hB hsize hscale).2
  intro center z hz
  have he : integerGridDensity (weightedCubeIntegerSource s) (weightedCubeIntegerJetSum s J center)
      K ((2 * Q + 1) * K) z = (K : ℝ) ^ J.card * finiteImageMass (weightedCubeIntegerSource s)
        (weightedCubeIntegerJetSum s J center) z := by
    unfold integerGridDensity
    rw [weightedCube_mass_on_fundamental_box s hT hK hvol hQ J hJ center z hz, Fintype.card_coe]
  have ht := hd center z
  rw [he] at ht
  apply ht.trans
  have hf := mul_le_mul_of_nonneg_right (grid_scale_factor_le_one (2 * Q + 1) K J.card (by omega) hK) hε.le
  simpa only [Nat.cast_mul, one_mul] using hf

theorem weightedModerate_uniform_fundamental_approximation {B I : Type*}
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {n K Q : ℕ} [NeZero K] (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin n → NormalizedScalarCubeSource I) (offset : B → ℤ)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L T ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hT : 0 ≤ T) (hε : 0 < ε)
    (hc : ∀ b, ScalarCubePrimitiveBudget (c b) A U) (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (hclen : ∀ b, L ≤ (c b).length) (hlen : ∀ b j, L ≤ (s b j).length)
    (hvol : ∀ b, (|(offset b : ℝ)| + (c b).length) * (∏ j, ((s b j).length : ℝ)) ≤ T * K)
    (hQ : blockJetScaleBound (Fintype.card I) n (Fintype.card B) T ≤ Q)
    (t : ℕ) (J : Finset (Finset I)) (hJ : ∀ F ∈ J, F.card ≤ n)
    (hB : uniformSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (((2 * Q + 1) * K : ℕ) : ℝ) ^ J.card ≤ W * L ^ t)
    (hscale : ∀ b, (((2 * Q + 1) * K : ℕ) : ℝ) /
      ((((c b).modulus none : ℝ) * (c b).length) * ∏ j, ((s b j).length : ℝ)) ≤ V) :
    let ζ := uniformBlockRetainedBias n J.card t U V W ε
    let S := uniformBlockSpectrumCover J ((2 * Q + 1) * K) n U V L ζ
    ∀ center z : J → ℤ, centeredFundamentalBox Q K center z →
      ‖(((K : ℝ) ^ J.card * finiteImageMass (weightedModerateIntegerProductSource c s)
        (weightedModerateIntegerJetSum c s J offset center) z : ℝ) : ℂ) -
        weightedModerateGridApproximation c s K ((2 * Q + 1) * K) J offset center z S‖ ≤ ε := by
  dsimp only
  have hK : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hd := (weightedModerate_uniform_grid_density c s offset A hA hU hV hW hL hε hc h hclen hlen K
    ((2 * Q + 1) * K) t J hJ hB hsize hscale).2
  intro center z hz
  have he : integerGridDensity (weightedModerateIntegerProductSource c s)
      (weightedModerateIntegerJetSum c s J offset center) K ((2 * Q + 1) * K) z =
      (K : ℝ) ^ J.card * finiteImageMass (weightedModerateIntegerProductSource c s)
        (weightedModerateIntegerJetSum c s J offset center) z := by
    unfold integerGridDensity
    rw [weightedModerate_mass_on_fundamental_box c s offset hT hK hvol hQ J hJ center z hz, Fintype.card_coe]
  have ht := hd center z
  rw [he] at ht
  apply ht.trans
  have hf := mul_le_mul_of_nonneg_right (grid_scale_factor_le_one (2 * Q + 1) K J.card (by omega) hK) hε.le
  simpa only [Nat.cast_mul, one_mul] using hf

end Erdos3

end

end OAI
