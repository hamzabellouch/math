import OAI.Combinatorics.Progressions.Lattices.AffineModerateGeometricApproximation

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem progressionCube_geometric_approximation {b n K : ℕ} [NeZero b] [NeZero K] (q : ℕ)
    (m H : Fin b → Fin (n + 1) → ℕ) (c : Fin b → Fin (n + 1) → ℤ)
    (hL : ∀ a j, 0 < m a j * H a j) (hm : ∀ a j, 0 < m a j)
    (hsize : ∀ a j, (q + 1) * m a j ≤ m a j * H a j)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (M : ℕ) (hM : ∀ a j, m a j ≤ M)
    {O F D E ε : ℝ} (hO : 0 ≤ O) (hD : 0 ≤ D) (hE : 0 ≤ E) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hc : ∀ a j, |(c a j : ℝ)| ≤ O * (m a j * H a j : ℕ))
    (hupper : ∀ a, (∏ j, ((m a j * H a j : ℕ) : ℝ)) ≤ F * K)
    (hlower : ∀ a, (K : ℝ) ≤ D * ∏ j, ((m a j * H a j : ℕ) : ℝ))
    (p : ℕ) (hpower : ∀ a j, (K : ℝ) ≤ E * ((m a j * H a j : ℕ) : ℝ) ^ p)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : uniformSpectrumBlockCount n J.card (p * J.card) ≤ b) :
    let U := affinePrimitiveEnvelope (Fin q) A 1 0 M 1
    let Q := affineTorusRadius (Fintype.card (Fin q)) (n + 1) (Fintype.card (Fin b)) (O + 1) F
    let R := affineTorusFactor (Fintype.card (Fin q)) (n + 1) (Fintype.card (Fin b)) (O + 1) F
    let ζ := uniformBlockRetainedBias n J.card (p * J.card) U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) ε
    ∃ S : Finset (J → Fin (R * K)),
      (S.card : ℝ) ≤ uniformSpectrumSizeConstant n J.card (p * J.card)
        U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) /
          ε ^ max (majorArcSpectrumExponent n J.card) (majorArcLengthExponent n * (p * J.card)) ∧
      (∀ center : J → ℤ, (∑ k, ‖integerGridCoefficient (progressionCubeBlockWeights q m H c hL hm)
          (progressionCubeIntegerSum q m H c J center) (R * K) k‖) ≤
        uniformSpectrumAbsoluteCap n J.card (p * J.card) U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card)) ∧
      (∀ k ∈ S, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ uniformCharacterDenominatorBound n J.card (p * J.card)
        U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) ζ ∧
        ∃ (a : J → ℤ) (ξ : J → ℝ),
          (∀ Z, |ξ Z| ≤ 2 * majorArcCoverConstant n J.card U ((R : ℝ) * D) / ζ ^ majorArcCoverExponent n J.card) ∧
          ∀ Z, ((k Z).val : ℝ) / (R * K) = (a Z : ℝ) / d + ξ Z / K) ∧
      ∀ center z : J → ℤ, centeredFundamentalBox Q K center z →
        ‖(((K : ℝ) ^ J.card * finiteImageMass (progressionCubeBlockWeights q m H c hL hm)
            (progressionCubeIntegerSum q m H c J center) z : ℝ) : ℂ) -
          integerGridApproximation (progressionCubeBlockWeights q m H c hL hm)
            (progressionCubeIntegerSum q m H c J center) K (R * K) S z‖ ≤ ε := by
  let s := progressionCubeSources q m H c hL hm hsize
  let u (a : Fin b) (j : Fin (n + 1)) := cubeRootOffset (c a j) (I := Fin q)
  let R := affineTorusFactor (Fintype.card (Fin q)) (n + 1) (Fintype.card (Fin b)) (O + 1) F
  have hcoord (a : Fin b) (j : Fin (n + 1)) (i : Option (Fin q)) :
      |(u a j i : ℝ)| + ((1 : ℕ) : ℝ) * (s a j).length ≤ (O + 1) * (s a j).length := by
    have hlength : (s a j).length = m a j * H a j := rfl
    rw [hlength]
    cases i with
    | none =>
        change |(c a j : ℝ)| + ((1 : ℕ) : ℝ) * (m a j * H a j : ℕ) ≤ _
        push_cast
        have he := hc a j
        push_cast at he
        nlinarith
    | some i =>
        have he : 0 ≤ O * ((m a j * H a j : ℕ) : ℝ) := mul_nonneg hO (Nat.cast_nonneg _)
        simp only [u, cubeRootOffset, Int.cast_zero, abs_zero, Nat.cast_one, zero_add, one_mul]
        nlinarith
  have he := affineCube_geometric_approximation s u (fun _ _ _ => 1) A 1 0 hA M 1 hM
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ _ => by omega) (fun _ _ _ => le_rfl)
    (by linarith : 0 ≤ O + 1) hD hE hε hε1 hcoord hupper hlower p hpower J hJ
    (by simpa only [Fintype.card_fin] using hB)
  dsimp only at he
  obtain ⟨S, hS, hcap, hchar, happ⟩ := he
  refine ⟨S, hS, ?_, hchar, ?_⟩
  · intro center
    apply le_trans ?_ hcap
    apply Finset.sum_le_sum
    intro k _
    have heq := progressionCubeIntegerSum_coefficient q m H c hL hm hsize J center (R * K) k
    rw [affineWeightedCubeIntegerSum_coefficient] at heq
    have hn := congrArg norm heq
    simpa only [norm_mul, rectangularGridCharacter_norm, one_mul] using hn.symm.le
  · intro center z hz
    simpa only [s, u, progressionCubeIntegerSum_mass, progressionCubeIntegerSum_approximation] using happ center z hz

end Erdos3

end

end OAI
