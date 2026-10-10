import OAI.Combinatorics.Progressions.Estimates.RelativePatchPositivePowerInduction

namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators TensorProduct Classical

theorem exists_lowest_weight_source_ready_preparation (s scalarPower precisionPower : ℕ) :
    ∃ requiredPower preparationPower costPower : ℕ,
      2 ≤ requiredPower ∧ 2 ≤ preparationPower ∧ 2 ≤ costPower ∧
      ∀ (X : Type) [Fintype X] [DecidableEq X] (p : ℝ), 2 ≤ p →
      ∀ (d : ℕ) (A : PolynomialPatch X s d), 0 < d →
        relativePatchComplexity A ≤ p → (Fintype.card X : ℝ) ≤ p →
      ∀ (N : X → ℕ) (f : (X → ℤ) → ℝ) (target : ℝ),
        (∀ i, Real.exp ((p + 2) ^ (max costPower requiredPower + 1)) ≤ (N i : ℝ)) →
      let R := preparedRoundedRank p requiredPower
      ∃ (D j : ℕ) (hD : D ≤ d), 0 < D ∧ j + 1 ≤ s ∧
      ∃ (q : ℕ) (S : ResidueBoxSlice N q),
      let A' := (A.castRank (Nat.add_sub_of_le hD).symm).reparam
        S.polynomial S.polynomial_weighted_support
      ∃ (F : A'.LowestLayerModel (D := D) (E := d - D) (j + 1))
        (L : RankPreparationFamily X (Fin D) (j + 1))
        (ip : Fin D → MvPolynomial X ℤ) (c : Fin D → ℝ)
        (err : VectorPolynomial X ℝ (Fin D → ℝ)),
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + 2) ^ costPower) ∧
        (∀ i, 0 < S.length i ∧ (N i : ℝ) ≤ Real.exp ((p + 2) ^ costPower) * S.length i) ∧
        (∀ i : Fin D, A'.weight (i.castAdd (d - D)) = j + 1) ∧
        (∀ i : Fin (d - D), j + 1 < A'.weight (i.natAdd D)) ∧
        A'.kernel.lip = A.kernel.lip ∧
        relativePatchComplexity A' = relativePatchComplexity A ∧
        relativePatchDistinctWeights A' = relativePatchDistinctWeights A ∧
        (∑ u, (L u).rank) ≤ (j + 1) * D ∧ (∑ u, (L u).rank) ≤ s * D ∧
        L.Sized D ((j + 1) * D) ∧ L.PreparedHeights ((p + 2) ^ preparationPower) R ∧
        (∀ u, Fintype.card (L u).Coord ≤ preparationCoordinateCap (j + 1) D ((j + 1) * D)) ∧
        (∀ u, HasLayerSamplingRank (u.val + 1) (fun i => (S.length i : ℝ))
          R (L u).space (L u).poly) ∧
        (∀ i, (ip i).totalDegree ≤ j + 1) ∧ DegreeLE (fun _ => 1) (j + 1) err ∧
        VectorPolynomial.ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
          L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + err ∧
        (∀ x ∈ integerBox S.length, ∀ i,
          |eval (fun k => (x k : ℝ)) err i| ≤ Real.exp (-((p + 2) ^ (max (requiredPower + 1) precisionPower)))) ∧
        (∀ x ∈ integerBox S.length, ∀ i,
          |eval (fun k => (x k : ℝ)) err i| ≤ Real.exp (-((p + 2) ^ precisionPower))) ∧
        relativePatchBoxScore N f target A ≤ relativePatchSliceScore S f target A' ∧
        relativePatchBoxScore N f target A ≤
          relativePatchBoxScore S.length (S.integerPullback f) target A' ∧
        (∀ i, Real.exp ((p + 2) ^ requiredPower) ≤ (S.length i : ℝ)) ∧
        (∀ i, Real.exp (-((p + 2) ^ costPower)) * (N i : ℝ) ≤ (S.length i : ℝ)) ∧
        ∀ v : PreparedSourceScalarData, v.Bounded ((p + 2) ^ scalarPower) →
          Real.exp (v.shortRequired (j + 1)) ≤ (R : ℝ) ∧
          ∀ i, Real.exp (v.shortRequired (j + 1)) ≤ (S.length i : ℝ) := by
  obtain ⟨requiredPower, hrequiredPower, hsource⟩ :=
    exists_preparedUniformShortSourceRank_power_budget s scalarPower
  obtain ⟨preparationPower, costPower, hpreparationPower, hcostPower, hprepare⟩ :=
    exists_lowest_weight_prepared_patch s (max (requiredPower + 1) precisionPower)
  refine ⟨requiredPower, preparationPower, costPower,
    hrequiredPower, hpreparationPower, hcostPower, ?_⟩
  intro X _ _ p hp d A hd hA hX N f target hN
  let R := preparedRoundedRank p requiredPower
  have hNprep : ∀ i, Real.exp ((p + 2) ^ costPower) ≤ (N i : ℝ) := by
    intro i
    apply (Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2)
      ((Nat.le_max_left costPower requiredPower).trans (Nat.le_succ _)))).trans (hN i)
  obtain ⟨D, j, hD, hDpos, hjs, q, S, F, L, ip, c, err,
      hq, hqb, hlen, hfirst, hrest, hLip, hComplexity, hCount, hrank, hsRank,
      hsize, hheight, hcoord, hgood, hip, herrdeg, hid, herr, hscore, hboxScore⟩ :=
    hprepare X p hp d R A hd hA hX (preparedRoundedRank_one_le p requiredPower)
      ((preparedRoundedRank_le_exp hp requiredPower).trans (Real.exp_le_exp.mpr
        (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (Nat.le_max_left _ _))))
      N f target hNprep
  have hprecision : ∀ x ∈ integerBox S.length, ∀ i,
      |eval (fun k => (x k : ℝ)) err i| ≤ Real.exp (-((p + 2) ^ precisionPower)) := by
    intro x hx i
    exact (herr x hx i).trans (Real.exp_le_exp.mpr (neg_le_neg
      (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (Nat.le_max_right _ _))))
  have hchildren := prepared_source_side_budgets hp (le_refl ((p + 2) ^ requiredPower))
    N S.length hN (fun i => (hlen i).2)
  refine ⟨D, j, hD, hDpos, hjs, q, S, F, L, ip, c, err,
    hq, hqb, hlen, hfirst, hrest, hLip, hComplexity, hCount, hrank, hsRank,
    hsize, hheight, hcoord, hgood, hip, herrdeg, hid, herr, hprecision, hscore, hboxScore,
    hchildren.1, hchildren.2, ?_⟩
  intro v hv
  have hrequired := hsource hp (j + 1) hjs v hv
  exact ⟨hrequired.2.2.1, fun i =>
    (Real.exp_le_exp.mpr hrequired.1).trans (hchildren.1 i)⟩

end Erdos3

end

end OAI
