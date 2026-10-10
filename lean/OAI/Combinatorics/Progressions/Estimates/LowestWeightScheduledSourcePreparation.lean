import OAI.Combinatorics.Progressions.Linear.PreparedFiniteNestedSourceProjectionBudget

namespace OAI

section

namespace Erdos3

open VectorPolynomial Module
open scoped BigOperators TensorProduct Classical

theorem exists_lowest_weight_scheduled_source_preparation
    (s depth cutoff stageCount inputPower precisionPower : ℕ) :
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
        (∀ {Stage : Type} [Fintype Stage] (degree : Stage → ℕ),
          (∀ k, degree k ≤ cutoff) → Fintype.card Stage ≤ stageCount →
          ∀ (Pmaster : Stage → ℝ) (Plate Eforecast extraRequired : ℝ),
            (∀ k, 0 ≤ Pmaster k) → (∀ k, Pmaster k ≤ Plate) →
            Plate ≤ (p + 2) ^ inputPower →
            Eforecast ≤ (p + 2) ^ inputPower → extraRequired ≤ (p + 2) ^ inputPower →
            let required := preparedFiniteScheduleLocalDegreeRequired
              (max (j + 1) depth) degree Pmaster Plate Eforecast extraRequired
            Real.exp required ≤ (R : ℝ) ∧
              ∀ i, Real.exp required ≤ (S.length i : ℝ)) ∧
        ∃ (b : ∀ u, Module.Basis (Fin (preparedSamplerTransverse L u)) ℝ
            (euclideanSubspace (L u).space)ᗮ)
          (_o : ∀ u, OrthonormalBasis (PreparedSamplerContinuous L u) ℝ
            (euclideanSubspace (L u).space))
          (bW : ∀ u, Module.Basis (PreparedSamplerContinuous L u) ℤ
            (latticeSection (standardEuclideanLattice (L u).Coord)
              (euclideanSubspace (L u).space))),
          (∀ u, Submodule.span ℤ (Set.range (b u)) =
            projectedIntegerLattice (euclideanSubspace (L u).space)) ∧
          (∀ u z, ‖normalizedOrthogonalChart (euclideanSubspace (L u).space) (b u) z‖ ≤
            Real.exp (allocatedUniformChartLog
              (preparationCoordinateCap (j + 1) D ((j + 1) * D) : ℝ)) * ‖z‖) ∧
          (∀ u z, ‖(normalizedOrthogonalChart (euclideanSubspace (L u).space) (b u)).symm z‖ ≤
            Real.exp (allocatedUniformChartLog
              (preparationCoordinateCap (j + 1) D ((j + 1) * D) : ℝ)) * ‖z‖) ∧
          (∀ u, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (L u).space) (b u) ∧
            mixedDensityCovolumeRatio (euclideanSubspace (L u).space) (b u) ≤
              Real.exp (allocatedUniformChartLog
                (preparationCoordinateCap (j + 1) D ((j + 1) * D) : ℝ))) ∧
          (∀ u a, ‖(bW u a).val‖ ≤ Real.exp
            (((p + 2) ^ preparationPower +
              (preparationCoordinateCap (j + 1) D ((j + 1) * D) : ℝ) +
              (p + 2) ^ (requiredPower + 1) + 2) ^
                preparedIntegralBasisExponent (j + 1))) ∧
          (∀ u i, (basisAxisScale (b u) i : ℝ) ≤ Real.exp
            (((p + 2) ^ preparationPower +
              (preparationCoordinateCap (j + 1) D ((j + 1) * D) : ℝ) +
              (p + 2) ^ (requiredPower + 1) + 2) ^
                preparedIntegralBasisExponent (j + 1))) := by
  obtain ⟨requiredPower, hrequiredPower, hsource⟩ :=
    exists_preparedFiniteScheduleUniformRequiredRank_power_budget
      (max s depth) cutoff stageCount inputPower
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
    hchildren.1, hchildren.2, ?_, ?_⟩
  · intro Stage _ degree hdegree hstages Pmaster Plate Eforecast extraRequired
      hmaster hmasterLate hLate hE hExtra
    have hr := hsource (max (j + 1) depth) (max_le_max hjs le_rfl)
      degree hdegree hstages hp Pmaster Plate Eforecast extraRequired
      hmaster hmasterLate hLate hE hExtra
    exact ⟨hr.2.2.1, fun i => (Real.exp_le_exp.mpr hr.1).trans (hchildren.1 i)⟩
  · let M := preparationCoordinateCap (j + 1) D ((j + 1) * D)
    let pLate := (p + 2) ^ preparationPower + (M : ℝ) + (p + 2) ^ (requiredPower + 1)
    have hprep0 : 0 ≤ (p + 2) ^ preparationPower := by positivity
    have hrank0 : 0 ≤ (p + 2) ^ (requiredPower + 1) := by positivity
    have hcap0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
    apply hheight.exists_early_late_sampler_geometry L (pLate := pLate)
      hprep0 (preparedRoundedRank_one_le p requiredPower)
    · dsimp only [pLate]; linarith
    · apply (preparedRoundedRank_le_exp hp requiredPower).trans
      apply Real.exp_le_exp.mpr
      dsimp only [pLate]; linarith
    · exact hsize
    · exact le_rfl
    · dsimp only [pLate]; change (M : ℝ) ≤ _; linarith

end Erdos3

end

end OAI
