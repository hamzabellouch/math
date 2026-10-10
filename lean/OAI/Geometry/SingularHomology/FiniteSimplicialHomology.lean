import OAI.Dynamics.EntropyCounterexample.FiniteSpectrumBound

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Problem340

theorem finiteDimensional_shortComplex_homology
    (S : ShortComplex (ModuleCat ℝ)) [FiniteDimensional ℝ S.X₂] :
    FiniteDimensional ℝ S.homology := by
  have : FiniteDimensional ℝ S.moduleCatLeftHomologyData.H := by
    change FiniteDimensional ℝ (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
    infer_instance
  exact Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv.symm

theorem finiteDimensional_normalized_real_chains
    (X : SSet) [X.Finite] (n : ℕ) :
    FiniteDimensional ℝ ((X.normalizedChainComplex (ModuleCat.of ℝ ℝ)).X n) := by
  let R : ModuleCat ℝ := ModuleCat.of ℝ ℝ
  let e : (X.normalizedChainComplex R).X n ≅ (∐ fun _ : X.nonDegenerate n => R) :=
    (X.isColimitCofanNormalizedChainComplex R n).coconePointUniqueUpToIso
      (coproductIsCoproduct _)
  have : FiniteDimensional ℝ (∐ fun _ : X.nonDegenerate n => R : ModuleCat ℝ) := by
    infer_instance
  exact Module.Finite.equiv e.toLinearEquiv.symm

theorem finiteDimensional_real_simplicial_homology
    (X : SSet) [X.Finite] (n : ℕ) :
    FiniteDimensional ℝ (X.homology (ModuleCat.of ℝ ℝ) n : ModuleCat ℝ) := by
  let R : ModuleCat ℝ := ModuleCat.of ℝ ℝ
  have : FiniteDimensional ℝ ((X.normalizedChainComplex R).sc n).X₂ :=
    finiteDimensional_normalized_real_chains X n
  have : FiniteDimensional ℝ ((X.normalizedChainComplex R).homology n) :=
    finiteDimensional_shortComplex_homology ((X.normalizedChainComplex R).sc n)
  let e := asIso (HomologicalComplex.homologyMap (X.toNormalizedChainComplex R) n)
  exact Module.Finite.equiv e.toLinearEquiv.symm

theorem real_simplicial_homology_finite_support (X : SSet) [X.Finite] :
    ∃ N : ℕ, ∀ n, N ≤ n → Subsingleton (X.homology (ModuleCat.of ℝ ℝ) n : ModuleCat ℝ) := by
  obtain ⟨N, hN⟩ := X.hasDimensionLT_of_finite
  let := hN
  refine ⟨N, fun n hn => ?_⟩
  exact ModuleCat.isZero_iff_subsingleton.mp
    (X.isZero_homology_of_hasDimensionLT (ModuleCat.of ℝ ℝ) n N hn)

theorem bddAbove_real_simplicial_eigenpair_moduli
    (X : SSet) [X.Finite]
    (A : ∀ n : ℕ, (X.homology (ModuleCat.of ℝ ℝ) n : ModuleCat ℝ) →ₗ[ℝ]
      (X.homology (ModuleCat.of ℝ ℝ) n : ModuleCat ℝ)) :
    BddAbove {r : ℝ | ∃ n : ℕ, ∃ a b : ℝ,
      ∃ u v : (X.homology (ModuleCat.of ℝ ℝ) n : ModuleCat ℝ),
        (u ≠ 0 ∨ v ≠ 0) ∧
        A n u = a • u - b • v ∧ A n v = b • u + a • v ∧
        r = Real.sqrt (a ^ 2 + b ^ 2)} := by
  let (n : ℕ) := finiteDimensional_real_simplicial_homology X n
  obtain ⟨N, hN⟩ := real_simplicial_homology_finite_support X
  exact bddAbove_total_pairedEigenvalue_moduli A N (fun n hn => hN n hn.le)

theorem finrank_shortComplex_homology_le
    (S : ShortComplex (ModuleCat ℝ)) [FiniteDimensional ℝ S.X₂] :
    Module.finrank ℝ S.homology ≤ Module.finrank ℝ S.X₂ := by
  rw [S.moduleCatHomologyIso.toLinearEquiv.finrank_eq]
  change Module.finrank ℝ (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) ≤ _
  exact (Submodule.finrank_quotient_le (LinearMap.range S.moduleCatToCycles)).trans
    (Submodule.finrank_le (LinearMap.ker S.g.hom))

theorem finrank_normalized_real_chains
    (X : SSet) [X.Finite] (n : ℕ) :
    Module.finrank ℝ ((X.normalizedChainComplex (ModuleCat.of ℝ ℝ)).X n) =
      Nat.card (X.nonDegenerate n) := by
  classical
  let : Fintype (X.nonDegenerate n) := Fintype.ofFinite _
  let R : ModuleCat ℝ := ModuleCat.of ℝ ℝ
  let e : (X.normalizedChainComplex R).X n ≅ (∐ fun _ : X.nonDegenerate n => R) :=
    (X.isColimitCofanNormalizedChainComplex R n).coconePointUniqueUpToIso
      (coproductIsCoproduct _)
  rw [e.toLinearEquiv.finrank_eq,
    (ModuleCat.coprodIsoDirectSum (fun _ : X.nonDegenerate n => R)).toLinearEquiv.finrank_eq]
  change Module.finrank ℝ (DirectSum (X.nonDegenerate n) fun _ => ℝ) = _
  rw [Module.finrank_directSum]
  simp [Nat.card_eq_fintype_card]

theorem finrank_real_simplicial_homology_le
    (X : SSet) [X.Finite] (n : ℕ) :
    Module.finrank ℝ (X.homology (ModuleCat.of ℝ ℝ) n : ModuleCat ℝ) ≤
      Nat.card (X.nonDegenerate n) := by
  let R : ModuleCat ℝ := ModuleCat.of ℝ ℝ
  have : FiniteDimensional ℝ ((X.normalizedChainComplex R).sc n).X₂ :=
    finiteDimensional_normalized_real_chains X n
  let e := asIso (HomologicalComplex.homologyMap (X.toNormalizedChainComplex R) n)
  rw [e.toLinearEquiv.finrank_eq]
  exact (finrank_shortComplex_homology_le ((X.normalizedChainComplex R).sc n)).trans_eq
    (finrank_normalized_real_chains X n)

end Problem340

end

end OAI
