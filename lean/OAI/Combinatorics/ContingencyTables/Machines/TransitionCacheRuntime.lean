import OAI.Combinatorics.ContingencyTables.Machines.PreparedTransitionCache

namespace OAI

/-! # Work bounds for cached completion multiplicities -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

attribute [local irreducible] completionMultiplicityRealizer prepareTransitionCacheRealizer
  residualParametersRealizer canonicalBitCountRealizer completionWeightsRealizer
  residualParameters canonicalBitCount completionWeights

/-- The cache is charged by the finite completion box and the requested
reserved word length; no random-tape enumeration appears in this measure. -/
def transitionCacheMeasure (z : TransitionCacheParameters) : ℕ :=
  z.2+completionWeightMeasure (residualParameters z.1)+weight z

private lemma weight_le_cacheMeasure (z : TransitionCacheParameters) :
    weight z≤transitionCacheMeasure z := by unfold transitionCacheMeasure; omega

lemma work_completionMultiplicity :
    WorkBound completionMultiplicityRealizer transitionCacheMeasure := by
  have hu : PolynomialTime
      (composition (composition (first (B := ℕ)) residualParametersRealizer) canonicalBitCountRealizer) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_residualParameters)
      polynomial_canonicalBitCount
  have hr := polynomial_composition (polynomial_pair polynomial_second hu) polynomial_subtract
  have hp : WorkBound (pair (constant 2) (composition (pair second
      (composition (composition first residualParametersRealizer) canonicalBitCountRealizer)) subtract))
      transitionCacheMeasure :=
    work_of_polynomial (polynomial_pair (polynomial_constant 2) hr) Polynomial.X
      (fun z => by simpa using weight_le_cacheMeasure z)
  obtain ⟨p,hp'⟩ := hp
  unfold completionMultiplicityRealizer
  apply work_composition ⟨p,hp'⟩ BinaryPowerPrograms.work_power (Polynomial.X+p)
  intro z
  have hw := hp' z
  simp only [Polynomial.eval_add,Polynomial.eval_X]
  change (z.2-canonicalBitCount (residualParameters z.1))+weight (2:ℕ)≤_
  change _+weight (2,z.2-canonicalBitCount (residualParameters z.1))≤
    p.eval (transitionCacheMeasure z) at hw
  have ht : weight (2:ℕ)≤weight (2,z.2-canonicalBitCount (residualParameters z.1)) :=
    weight_fst (2,z.2-canonicalBitCount (residualParameters z.1))
  have hn : z.2-canonicalBitCount (residualParameters z.1)≤transitionCacheMeasure z := by
    unfold transitionCacheMeasure
    omega
  omega

lemma work_prepareTransitionCache :
    WorkBound prepareTransitionCacheRealizer transitionCacheMeasure := by
  have hr : WorkBound (composition (first (B := ℕ)) residualParametersRealizer)
      transitionCacheMeasure :=
    work_of_polynomial (polynomial_composition polynomial_first polynomial_residualParameters)
      Polynomial.X (fun z => by simpa using weight_le_cacheMeasure z)
  have hc : WorkBound (composition (composition first residualParametersRealizer)
      completionWeightsRealizer) transitionCacheMeasure := by
    apply work_composition hr work_completionWeights Polynomial.X
    intro z
    simp only [Polynomial.eval_X,transitionCacheMeasure,Function.comp_apply]
    omega
  have hi : WorkBound (first (A := ResidualParameters) (B := ℕ)) transitionCacheMeasure :=
    work_of_polynomial polynomial_first Polynomial.X
      (fun z => by simpa using weight_le_cacheMeasure z)
  unfold prepareTransitionCacheRealizer
  exact work_pair hi (work_pair work_completionMultiplicity hc Polynomial.X
    (fun z => by simpa using weight_le_cacheMeasure z)) Polynomial.X
      (fun z => by simpa using weight_le_cacheMeasure z)

end ContingencyTables.ProfilePrograms

end OAI
