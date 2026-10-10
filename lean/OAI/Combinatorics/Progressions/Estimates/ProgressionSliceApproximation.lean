import OAI.Combinatorics.Progressions.Geometry.ProgressionGeometricApproximation

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem progressionSlice_approximation {b n K : ℕ} [NeZero b] [NeZero K] (q : ℕ)
    (L m H : Fin b → Fin (n + 1) → ℕ) (c : Fin b → Fin (n + 1) → ℤ)
    (hL : ∀ a j, 0 < L a j) (hm : ∀ a j, 0 < m a j)
    (hH : ∀ a j, 2 ≤ H a j) (hq : ∀ a j, q + 1 ≤ H a j) {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ a j, integerProgressionSupport (c a j) (m a j : ℤ) (H a j) ⊆
      Finset.Ico (0 : ℤ) (L a j : ℤ))
    (hdense : ∀ a j, δ * L a j ≤ ((integerProgressionSupport (c a j) (m a j : ℤ) (H a j)).card : ℝ))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {F D E ε : ℝ}
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hupper : ∀ a, (∏ j, (L a j : ℝ)) ≤ F * K)
    (hlower : ∀ a, (K : ℝ) ≤ D * ∏ j, (L a j : ℝ))
    (p : ℕ) (hpower : ∀ a j, (K : ℝ) ≤ E * (L a j : ℝ) ^ p)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : uniformSpectrumBlockCount n J.card (p * J.card) ≤ b) :
    let hlen : ∀ a j, 0 < m a j * H a j := fun a j => Nat.mul_pos (hm a j) (by have := hH a j; omega)
    let F' := (2 : ℝ) ^ (n + 1) * F
    let D' := D * (δ⁻¹) ^ (n + 1)
    let E' := E * (δ⁻¹) ^ p
    let U := affinePrimitiveEnvelope (Fin q) A 1 0 ⌈2 / δ⌉₊ 1
    let Q := affineTorusRadius (Fintype.card (Fin q)) (n + 1) (Fintype.card (Fin b)) (δ⁻¹ + 1) F'
    let R := affineTorusFactor (Fintype.card (Fin q)) (n + 1) (Fintype.card (Fin b)) (δ⁻¹ + 1) F'
    let ζ := uniformBlockRetainedBias n J.card (p * J.card) U ((R : ℝ) * D') (((R : ℝ) * E') ^ J.card) ε
    ∃ S : Finset (J → Fin (R * K)),
      (S.card : ℝ) ≤ uniformSpectrumSizeConstant n J.card (p * J.card)
        U ((R : ℝ) * D') (((R : ℝ) * E') ^ J.card) /
          ε ^ max (majorArcSpectrumExponent n J.card) (majorArcLengthExponent n * (p * J.card)) ∧
      (∀ center : J → ℤ, (∑ k, ‖integerGridCoefficient (progressionCubeBlockWeights q m H c hlen hm)
          (progressionCubeIntegerSum q m H c J center) (R * K) k‖) ≤
        uniformSpectrumAbsoluteCap n J.card (p * J.card) U ((R : ℝ) * D') (((R : ℝ) * E') ^ J.card)) ∧
      (∀ k ∈ S, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ uniformCharacterDenominatorBound n J.card (p * J.card)
        U ((R : ℝ) * D') (((R : ℝ) * E') ^ J.card) ζ ∧
        ∃ (a : J → ℤ) (ξ : J → ℝ),
          (∀ Z, |ξ Z| ≤ 2 * majorArcCoverConstant n J.card U ((R : ℝ) * D') / ζ ^ majorArcCoverExponent n J.card) ∧
          ∀ Z, ((k Z).val : ℝ) / (R * K) = (a Z : ℝ) / d + ξ Z / K) ∧
      ∀ center z : J → ℤ, centeredFundamentalBox Q K center z →
        ‖(((K : ℝ) ^ J.card * finiteImageMass (progressionCubeBlockWeights q m H c hlen hm)
            (progressionCubeIntegerSum q m H c J center) z : ℝ) : ℂ) -
          integerGridApproximation (progressionCubeBlockWeights q m H c hlen hm)
            (progressionCubeIntegerSum q m H c J center) K (R * K) S z‖ ≤ ε := by
  let hlen : ∀ a j, 0 < m a j * H a j := fun a j => Nat.mul_pos (hm a j) (by have := hH a j; omega)
  have hsize (a) (j) : (q + 1) * m a j ≤ m a j * H a j := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (m a j) (hq a j)
  have hg a := progressionFamily_geometric_bounds (L a) (m a) (H a) (c a) (hL a) (hm a) (hH a) hδ
    (hsubset a) (hdense a) hD hE (hupper a) (hlower a) p (hpower a)
  exact progressionCube_geometric_approximation q m H c hlen hm hsize A hA ⌈2 / δ⌉₊
    (fun a j => (hg a).1 j) (inv_nonneg.mpr hδ.le) (by positivity) (by positivity) hε hε1
    (fun a j => (hg a).2.1 j) (fun a => (hg a).2.2.1) (fun a => (hg a).2.2.2.1) p
    (fun a j => (hg a).2.2.2.2 j) J hJ hB

end Erdos3

end

end OAI
