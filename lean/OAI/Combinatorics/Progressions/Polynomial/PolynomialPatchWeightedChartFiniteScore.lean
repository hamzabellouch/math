import OAI.Combinatorics.Progressions.Nilpotent.PolynomialPatchWeightedChartNiltest

namespace OAI

section

namespace Erdos3.PolynomialPatch

open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct NNReal

attribute [local irreducible] realChartSubstitute polynomialOrbitRealChart

variable {σ τ ξ Ω J X : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)

local notation "F" => polynomialShearFiltration A.weight s A.weight_le

theorem ofWeightedChartShearOrbit_complexMean
    [Fintype J] (w : ξ → ℕ) (β : ξ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (g : (F).realification.PolynomialOrbit w)
    (law : FiniteProbabilityWeights J) (site : J → τ → ℝ) (weight : J → ℂ) :
    law.complexMean (fun j => weight j *
      ((A.ofWeightedChartShearOrbit w β hβ g).value (site j) : ℂ)) =
    law.complexMean (fun j => weight j * (A.shearObservable (QuotientGroup.mk
      ((F).realification.polynomialOrbitRealEval w
        (fun i => MvPolynomial.eval (site j) (β i)) g)) : ℂ)) := by
  simp only [ofWeightedChartShearOrbit_value]

theorem ofWeightedChartShearOrbit_formal_mark
    {M : Type*} [LieRing M] [LieAlgebra ℚ M] {t : ℕ}
    (G : NilpotentLieFiltration M t)
    (φ : PolynomialShearLieAlgebra A.weight ℚ →ₗ⁅ℚ⁆ M)
    (w : ξ → ℕ) (β : ξ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (g : (F).realification.PolynomialOrbit w)
    (marked : G.realification.PolynomialOrbit w)
    (hmark : map (realLieHomToRat (realificationLieHom φ)).toLinearMap g.log = marked.log) :
    map (realLieHomToRat (realificationLieHom φ)).toLinearMap
      ((F).polynomialOrbitRealChart w (fun _ : τ => 1) β hβ g).log =
        (G.polynomialOrbitRealChart w (fun _ : τ => 1) β hβ marked).log ∧
    ∀ x : τ → ℝ, NilpotentLieBCHGroup.realificationMap
      (hnil := (F).lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) φ
        ((A.ofWeightedChartShearOrbit w β hβ g).form.shearGroupLift s A.weight_le x) =
      G.realification.polynomialOrbitRealEval w
        (fun i => MvPolynomial.eval x (β i)) marked := by
  constructor
  · rw [polynomialOrbitRealChart_log, polynomialOrbitRealChart_log]
    exact (realChartSubstitute_map β (realificationLieHom φ).toLinearMap g.log).symm.trans
      (congrArg (realChartSubstitute β) hmark)
  · intro x
    rw [ofWeightedChartShearOrbit_shearGroupLift]
    apply NilpotentLieBCHGroup.ext
    change realificationLieHom φ (eval₂ _ g.log) = eval₂ _ marked.log
    rw [← hmark]
    exact (eval₂_map (realificationLieHom φ).toLinearMap _ g.log).symm

variable [Fintype (PolynomialShearIndex A.weight)]
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]

theorem weightedChartShearOrbit_preserves_mark_and_finite_score
    [Fintype J]
    (mass : ℝ≥0) (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ mass)
    {cost : ℝ} (hcomplex : (A.shearNiltest mass hA).ComplexityLE cost)
    {M : Type*} [LieRing M] [LieAlgebra ℚ M] {t : ℕ}
    (G : NilpotentLieFiltration M t)
    (φ : PolynomialShearLieAlgebra A.weight ℚ →ₗ⁅ℚ⁆ M)
    (w : ξ → ℕ) (β : ξ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (g : (F).realification.PolynomialOrbit w)
    (marked : G.realification.PolynomialOrbit w)
    (hmark : map (realLieHomToRat (realificationLieHom φ)).toLinearMap g.log = marked.log)
    (H : Finset Ω) (localLaw : Ω → FiniteProbabilityWeights J)
    (physical : Ω → J → X) (site : X → τ → ℤ) (point : Ω → J → ξ → ℤ)
    (hsite : ∀ a ∈ H, ∀ j i,
      MvPolynomial.eval (fun k => (site (physical a j) k : ℝ)) (β i) = (point a j i : ℝ))
    (weight : X → ℂ) {δ : ℝ}
    (hscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean (fun j => weight (physical a j) *
      (A.shearObservable (QuotientGroup.mk
        ((F).realification.polynomialOrbitEval w (point a j) g)) : ℂ))).re) :
    let B := A.ofWeightedChartShearOrbit w β hβ g
    B.weight = A.weight ∧ B.kernel = A.kernel ∧
    map (realLieHomToRat (realificationLieHom φ)).toLinearMap
      ((F).polynomialOrbitRealChart w (fun _ : τ => 1) β hβ g).log =
        (G.polynomialOrbitRealChart w (fun _ : τ => 1) β hβ marked).log ∧
    (∀ x : τ → ℝ, NilpotentLieBCHGroup.realificationMap
      (hnil := (F).lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) φ
        (B.form.shearGroupLift s A.weight_le x) =
      G.realification.polynomialOrbitRealEval w
        (fun i => MvPolynomial.eval x (β i)) marked) ∧
    (∀ a ∈ H, δ ≤ ((localLaw a).complexMean (fun j => weight (physical a j) *
      (B.value (fun k => (site (physical a j) k : ℝ)) : ℂ))).re) ∧
    ∃ T : (polynomialShearNilmanifold A.weight s A.weight_le).Niltest (fun _ : τ => 1),
      T.observable = (A.shearNiltest mass hA).observable ∧
      T.normBound = (A.shearNiltest mass hA).normBound ∧
      T.lipBound = (A.shearNiltest mass hA).lipBound ∧
      T.UnitIntervalValued ∧ T.ComplexityLE cost ∧
      (∀ x : τ → ℤ, T.eval x = (B.value (fun i => (x i : ℝ)) : ℂ)) ∧
      ∀ a ∈ H, δ ≤ ((localLaw a).complexMean (fun j => weight (physical a j) *
        T.eval (site (physical a j)))).re := by
  dsimp only
  obtain ⟨hformal, hgroup⟩ := A.ofWeightedChartShearOrbit_formal_mark G φ w β hβ g marked hmark
  have hvalue (a : Ω) (ha : a ∈ H) (j : J) :
      (A.ofWeightedChartShearOrbit w β hβ g).value
        (fun k => (site (physical a j) k : ℝ)) =
      A.shearObservable (QuotientGroup.mk
        ((F).realification.polynomialOrbitEval w (point a j) g)) := by
    rw [ofWeightedChartShearOrbit_value]
    simp only [hsite a ha j, polynomialOrbitRealEval_integer]
  have hpatchscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean (fun j => weight (physical a j) *
      ((A.ofWeightedChartShearOrbit w β hβ g).value
        (fun k => (site (physical a j) k : ℝ)) : ℂ))).re := by
    intro a ha
    simpa only [hvalue a ha] using hscore a ha
  obtain ⟨T, hobs, hnorm, hlip, hunit, hcost, heval⟩ :=
    A.exists_ordinary_niltest_of_weighted_chart mass hA hcomplex w β hβ g
  refine ⟨rfl, rfl, hformal, hgroup, hpatchscore,
    T, hobs, hnorm, hlip, hunit, hcost, heval, ?_⟩
  intro a ha
  simpa only [heval] using hpatchscore a ha

end Erdos3.PolynomialPatch

end

end OAI
