import OAI.Combinatorics.Progressions.Estimates.BoundedWeightedSliceAxis

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def moderateSliceFourierAxis {b n q K : ℕ} [NeZero b] [NeZero K]
    (c : Fin b → NormalizedScalarCubeSource Empty)
    (s : Fin b → Fin n → NormalizedScalarCubeSource (Fin q))
    (offset : Fin b → ℤ) (stride : Fin b → ℕ) (root : Fin b → Fin n → ℤ)
    (A W T : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (M V : ℕ) (hV : 1 ≤ V)
    (hcM : ∀ a, (c a).modulusBound ≤ M) (hcW : ∀ a, (c a).weightBound ≤ W)
    (hcT : ∀ a, (c a).weightLipschitz ≤ T)
    (hM : ∀ a j, (s a j).modulusBound ≤ M) (hW : ∀ a j, (s a j).weightBound ≤ W)
    (hT : ∀ a j, (s a j).weightLipschitz ≤ T) (ht : ∀ a, 0 < stride a) (htV : ∀ a, stride a ≤ V)
    {O F D E : ℝ} (hO : 0 ≤ O) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hroot : ∀ a j, |(root a j : ℝ)| ≤ O * (s a j).length)
    (hupper : ∀ a, (|(offset a : ℝ)| + (stride a : ℝ) * (c a).length) *
      (∏ j, ((s a j).length : ℝ)) ≤ F * K)
    (hlower : ∀ a, (K : ℝ) ≤ D * ((c a).length * ∏ j, ((s a j).length : ℝ)))
    (p : ℕ) (hpower : ∀ a j, (K : ℝ) ≤ E * ((s a j).length : ℝ) ^ p)
    (hcpower : ∀ a, (K : ℝ) ≤ E * ((c a).length : ℝ) ^ p)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ n)
    (hB : uniformSpectrumBlockCount n J.card (p * J.card) ≤ b) : IntegerFourierAxis := by
  let U := affinePrimitiveEnvelope (Fin q) A W T M V
  let Q := affineTorusRadius (Fintype.card (Fin q)) n (Fintype.card (Fin b)) (O + 1) F
  let R := affineTorusFactor (Fintype.card (Fin q)) n (Fintype.card (Fin b)) (O + 1) F
  let ζ := fun ε => uniformBlockRetainedBias n J.card (p * J.card) U ((R : ℝ) * D)
    (((R : ℝ) * E) ^ J.card) ε
  refine IntegerFourierAxis.ofEstimate (moderateSliceIntegerSource c s root)
    (moderateSliceIntegerSum c s offset stride root J) K Q (R * K)
    (Nat.le_mul_of_pos_left K (affineTorusFactor_pos _ _ _ _ _))
    (uniformSpectrumSizeConstant n J.card (p * J.card) U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card))
    (max (majorArcSpectrumExponent n J.card) (majorArcLengthExponent n * (p * J.card)))
    (uniformSpectrumAbsoluteCap n J.card (p * J.card) U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card))
    (fun ε => uniformCharacterDenominatorBound n J.card (p * J.card) U
      ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) (ζ ε))
    (fun ε => 2 * majorArcCoverConstant n J.card U ((R : ℝ) * D) /
      (ζ ε) ^ majorArcCoverExponent n J.card) ?_
  intro ε hε hε1
  have he := moderateSlice_geometric_approximation c s offset stride root
    A W T hA M V hV hcM hcW hcT hM hW hT ht htV hO hD hE hε hε1
    hroot hupper hlower p hpower hcpower J hJ hB
  dsimp only at he
  obtain ⟨S, hS, hcap, hchar, happ⟩ := he
  refine ⟨S, hS, ?_, ?_, ?_⟩
  · intro center
    apply le_trans ?_ (hcap center)
    apply le_of_eq
    apply Finset.sum_congr
    · ext k
      simp only [Finset.mem_univ]
    · intro k _
      rfl
  · intro k hk
    obtain ⟨d, hd, hdb, a, ξ, hξ, heq⟩ := hchar k hk
    refine ⟨d, hd, hdb, a, ξ, hξ, ?_⟩
    intro j
    simpa only [Nat.cast_mul]
      using heq j
  · intro center z hz
    simpa only [R, integerGridApproximation, Fintype.card_coe] using happ center z hz

end Erdos3

end

section

namespace Erdos3.IntegerFourierAxis

open scoped BigOperators Classical

attribute [local instance] sourceFinite coordinateFinite scaleNeZero periodNeZero

theorem family_approximation {D : Type*} [Fintype D] [DecidableEq D]
    (a : D → IntegerFourierAxis) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let C := finiteFamilyCap (fun d => (a d).coefficientCap)
    let δ := jointGridAxisTolerance (Fintype.card D) (C + 1) ε
    ∃ S : ∀ d, Finset ((a d).Coordinate → Fin (a d).period),
      (Fintype.card (∀ d, S d) : ℝ) ≤ ∏ d, (a d).countConstant / δ ^ (a d).countExponent ∧
      (∀ center : ∀ d, (a d).Coordinate → ℤ,
        (∑ k : ∀ d, S d, ‖∏ d, integerRetainedCoefficient (a d).law ((a d).image (center d))
          (a d).scale (a d).period (k d)‖) ≤ C ^ Fintype.card D) ∧
      (∀ k : ∀ d, S d, ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ ∏ d, (a d).denominatorBound δ ∧
        ∃ (v : ∀ d, (a d).Coordinate → ℤ) (ξ : ∀ d, (a d).Coordinate → ℝ),
          (∀ d j, |ξ d j| ≤ (a d).residualBound δ) ∧
          ∀ d j, (((k d).val j).val : ℝ) / (a d).period = (v d j : ℝ) / m + ξ d j / (a d).scale) ∧
      ∀ center z : ∀ d, (a d).Coordinate → ℤ,
        (∀ d, centeredFundamentalBox (a d).radius (a d).scale (center d) (z d)) →
        ‖(((∏ d, ((a d).scale : ℝ) ^ Fintype.card (a d).Coordinate) *
          finiteImageMass (FiniteProbabilityWeights.pi (fun d => (a d).law))
            (fun x d => (a d).image (center d) (x d)) z : ℝ) : ℂ) -
          jointRetainedExpansion S
            (fun d => integerRetainedCoefficient (a d).law ((a d).image (center d)) (a d).scale (a d).period)
            (fun d k w => star (rectangularGridCharacter (a d).period k w)) z‖ ≤ ε := by
  dsimp only
  let C := finiteFamilyCap (fun d => (a d).coefficientCap)
  let δ := jointGridAxisTolerance (Fintype.card D) (C + 1) ε
  have hC : 0 ≤ C := finiteFamilyCap_nonneg _
  have hδ := jointGridAxisTolerance_spec (Fintype.card D) (by linarith : 0 ≤ C + 1) hε
  have hi (d : D) := (a d).approximation δ hδ.1 (hδ.2.1.trans hε1)
  choose S hcard hcap hchar happ using hi
  have hcapC (center : ∀ d, (a d).Coordinate → ℤ) (d : D) :
      (∑ k, ‖integerGridCoefficient (a d).law ((a d).image (center d)) (a d).period k‖) ≤ C :=
    (hcap d (center d)).trans (le_finiteFamilyCap (fun e => (a e).coefficientCap) d)
  refine ⟨S, jointRetainedExpansion_card_le_product S _ hcard, ?_, ?_, ?_⟩
  · intro center
    exact independentPeriodTensor_coefficient_mass (fun d => (a d).law)
      (fun d => (a d).image (center d)) (fun d => (a d).scale) (fun d => (a d).period) S
      (fun d => (a d).scale_le_period) (hcapC center)
  · intro k
    exact independent_rational_frequencies
      (fun d j => (((k d).val j).val : ℝ) / (a d).period) (fun d => (a d).scale)
      (fun d => (a d).denominatorBound δ) (fun d => (a d).residualBound δ)
      (fun d => hchar d (k d).val (k d).property)
  · intro center z hz
    exact independentPeriodTensor_approximation (fun d => (a d).law)
      (fun d => (a d).image (center d)) (fun d => (a d).scale) (fun d => (a d).period)
      S z hC hε hε1 (fun d => (a d).scale_le_period) (hcapC center)
      (fun d => happ d (center d) (z d) (hz d))

end Erdos3.IntegerFourierAxis

end

end OAI
