import OAI.Combinatorics.Progressions.Estimates.UniformFrozenDescent
import OAI.Combinatorics.Progressions.Linear.KernelProjectionNoPivotGlobalization

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold
open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

namespace Niltest

theorem topInvariant_of_no_pivots
    {L σ J : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (s + 1) d} {w : σ → ℕ}
    (T : D.Niltest w) (eta : J → L →ₗ[ℚ] ℚ) (code : Fin r → Option J)
    (hnone : ∀ i, code i = none)
    (hinv : ∀ z : D.RealGroup,
      z.coord ∈ (frequencyCodeKernel (D.filtration.layer (s + 1)) eta code).baseChange ℝ →
      ∀ x, T.observable (z • x) = T.observable x) :
    ∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
      T.observable (z • x) = T.observable x := by
  intro z hz
  apply hinv z
  rw [frequencyCodeKernel_eq_of_no_pivots _ _ _ hnone]
  exact hz

end Niltest

theorem exists_constructed_noPivot_top_descent (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ τ Ω J : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d r : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      {v : σ → ℕ} {w : τ → ℕ} (T : D.Niltest v)
      (localTests : Ω → D.Niltest w),
      (∀ a, (localTests a).observable = T.observable) → T.UnitIntervalValued →
      ∀ p : ℝ, 0 ≤ p → T.ComplexityLE p →
      ∀ (eta : J → L →ₗ[ℚ] ℚ) (code : Fin r → Option J),
      (∀ i, code i = none) →
      (∀ z : D.RealGroup,
        z.coord ∈ (frequencyCodeKernel (D.filtration.layer (s + 1)) eta code).baseChange ℝ →
        ∀ x, T.observable (z • x) = T.observable x) →
      ∃ n : ℕ, n ≤ d ∧
        ∃ Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n,
        ∃ hQF : Q.filtration = D.filtration.quotientTop,
          Q.lattice = D.lattice.map
            (D.filtration.quotientStepHom (D.filtration.layerIdeal (s + 1)) le_rfl) ∧
          letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))
          letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
            IsModuleTopology.isTopologicalAddGroup ℝ _
          letI : T2Space (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
            realification_moduleTopology_t2 Q.basis
          ∃ (S : Q.Niltest v) (quotientTests : Ω → Q.Niltest w),
            S.orbit = D.topQuotientOrbit Q hQF T.orbit ∧
            S.normBound = T.normBound ∧
            S.lipBound = rationalReconstructionLipschitzBound s d n
              ⌈Real.exp ((p + 3) ^ 11)⌉₊ T.lipBound T.normBound ∧
            S.UnitIntervalValued ∧ S.ComplexityLE ((p + C) ^ C) ∧
            (∀ g : D.RealGroup, S.observable (QuotientGroup.mk
              (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                (hM := Q.filtration.lowerCentralSeries_eq_bot)
                (lieQuotientMap (D.filtration.layerIdeal (s + 1))) g)) =
              T.observable (QuotientGroup.mk g)) ∧
            (∀ x, S.eval x = T.eval x) ∧
            ∀ a, (quotientTests a).observable = S.observable ∧
              (quotientTests a).orbit = D.topQuotientOrbit Q hQF (localTests a).orbit ∧
              (quotientTests a).normBound = S.normBound ∧
              (quotientTests a).lipBound = S.lipBound ∧
              (quotientTests a).UnitIntervalValued ∧
              (quotientTests a).ComplexityLE ((p + C) ^ C) ∧
              ∀ x, (quotientTests a).eval x = (localTests a).eval x := by
  obtain ⟨C, hC, hdescent⟩ := exists_constructed_fixedObservable_topInvariant_descent s
  refine ⟨C, hC, ?_⟩
  intro L σ τ Ω J _ _ _ _ _ _ d r D v w T localTests hcommon hunit p hp hT
    eta code hnone hinv
  exact hdescent D T localTests hcommon hunit p hp hT
    (T.topInvariant_of_no_pivots eta code hnone hinv)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
