import OAI.NumberTheory.DukePrimeDegree.Geometry.NeutralAction
import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootOrbitConcentration
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPairCoordinates
import OAI.NumberTheory.PrimePackets.ErgodicDecomposition

namespace OAI

/-!
# Excluding positive-measure sets of strong neutral returns

Ergodic decomposition, the compact-return orbit-concentration argument,
and the arithmetic centralizer-orbit obstruction together exclude a
measurable positive-measure set with uniform strong neutral returns.
This is the consequence of EKL (2006), Proposition 4.3 and Theorem 5.1,
needed for the low-entropy alternative on the arithmetic quotient.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology Classical BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem strong_neutral_return_set_null
    (d : ℕ) (hd : 2 < d + 1) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (K : Set (X (d + 1))) (hK : MeasurableSet K)
    (r : ℝ) (hr : 0 < r)
    (hstrong : ∀ x ∈ K,
      ∀ (ell : Fin (d + 1) → ℝ) (hell : ∑ a, ell a = 0), ell i = ell j →
      rightAction x (diagonalOneParameter ell hell 1) ∈ K →
      ∀ g ∈ matrixBall (d + 1) r,
        rightAction x g = rightAction x (diagonalOneParameter ell hell 1) →
          g ∈ rootPairCentralizer hij) : μ K = 0 := by
  let N := Multiplicative (neutralWeightSubgroup i j)
  let := neutralDiagonalAction hij
  let := neutralDiagonalAction_continuous hij
  let : SecondCountableTopology (neutralWeightSubgroup i j) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : SecondCountableTopology N :=
    (inferInstance : SecondCountableTopology (neutralWeightSubgroup i j))
  obtain ⟨s, hs, hdense⟩ := TopologicalSpace.exists_countable_dense N
  let : Countable s := hs.to_subtype
  let H := FreeGroup s
  let φ : H →* N := FreeGroup.lift (fun a : s => (a : N))
  have hdφ : DenseRange φ := hdense.mono (by
    intro g hg
    exact ⟨FreeGroup.of ⟨g, hg⟩, FreeGroup.lift_apply_of⟩)
  let := MulAction.compHom (X (d + 1)) φ
  let : MeasurableConstSMul H (X (d + 1)) :=
    ⟨fun h => (continuous_const_smul (φ h)).measurable⟩
  have hp (h : H) : MeasurePreserving (fun y : X (d + 1) => h • y) μ μ :=
    neutralDiagonal_preserving d hij μ hA (φ h)
  have hdec := action_ergodic_decomposition μ hp
  let κ := condExpKernel μ (actionInvariantSigma H (X (d + 1)))
  let τ := μ.trim (actionInvariantSigma_le H (X (d + 1)))
  have hzero : ∀ᵐ x ∂τ, κ x K = 0 := by
    filter_upwards [hdec.2] with x hx
    let ν := κ x
    let : ErgodicSMul H (X (d + 1)) ν := hx
    by_contra hpos
    have hν (u : N) : MeasurePreserving (fun y : X (d + 1) => u • y) ν ν :=
      preserving_of_dense_action φ hdφ ν (fun h => measurePreserving_smul h ν) u
    let ψ : H →* MulOpposite (rootPairCentralizer hij) :=
      (neutralDiagonalOppositeHom hij).comp φ
    have hErg : let := rightSubgroupAction (rootPairCentralizer hij)
        let := MulAction.compHom (X (d + 1)) ψ
        ErgodicSMul H (X (d + 1)) ν := hx
    have hret : ∀ y ∈ K, ∀ h : H, rightAction y ((ψ h).unop : G (d + 1)) ∈ K →
        ∀ g ∈ matrixBall (d + 1) r,
          rightAction y g = rightAction y ((ψ h).unop : G (d + 1)) →
            g ∈ rootPairCentralizer hij := by
      intro y hy h hh g hg heq
      exact hstrong y hy (φ h).toAdd.val (φ h).toAdd.property.1
        (φ h).toAdd.property.2 hh g hg heq
    obtain ⟨z, hz⟩ := rootPair_orbit_of_strong_returns d hij H ψ ν hErg K hK hpos r hr hret
    apply no_neutral_invariant_rootPair_orbit hd hij ν z hz
    intro ell hell hneutral
    exact (hν (Multiplicative.ofAdd (⟨ell, hell, hneutral⟩ : neutralWeightSubgroup i j))).map_eq
  have hcomp : κ ∘ₘ τ = μ := hdec.1
  rw [← hcomp, Measure.bind_apply hK κ.aemeasurable]
  rw [lintegral_congr_ae hzero]
  simp

/-- An almost-everywhere version, so that recurrence null sets may be
removed without changing the mass of the return set. -/
theorem strong_neutral_return_set_null_of_ae
    (d : ℕ) (hd : 2 < d + 1) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (K : Set (X (d + 1))) (hK : MeasurableSet K)
    (r : ℝ) (hr : 0 < r)
    (hstrong : ∀ᵐ x ∂μ, x ∈ K →
      ∀ (ell : Fin (d + 1) → ℝ) (hell : ∑ a, ell a = 0), ell i = ell j →
      rightAction x (diagonalOneParameter ell hell 1) ∈ K →
      ∀ g ∈ matrixBall (d + 1) r,
        rightAction x g = rightAction x (diagonalOneParameter ell hell 1) →
          g ∈ rootPairCentralizer hij) : μ K = 0 := by
  obtain ⟨N, hbad, hN, hzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hstrong)
  have hKN : μ (K \ N) = 0 := by
    apply strong_neutral_return_set_null d hd hij μ hA (K \ N) (hK.diff hN) r hr
    intro x hx ell hell hn hy g hg heq
    have hxgood : x ∉ {x | ¬ (x ∈ K →
        ∀ (ell : Fin (d + 1) → ℝ) (hell : ∑ a, ell a = 0), ell i = ell j →
        rightAction x (diagonalOneParameter ell hell 1) ∈ K →
        ∀ g ∈ matrixBall (d + 1) r,
          rightAction x g = rightAction x (diagonalOneParameter ell hell 1) →
            g ∈ rootPairCentralizer hij)} := fun h => hx.2 (hbad h)
    exact not_not.mp hxgood hx.1 ell hell hn hy.1 g hg heq
  apply measure_mono_null (show K ⊆ (K \ N) ∪ N by
    intro x hx
    by_cases hxN : x ∈ N
    · exact Or.inr hxN
    · exact Or.inl ⟨hx, hxN⟩)
  exact measure_union_null hKN hzero

end DukePrimeDegree

end

end OAI
