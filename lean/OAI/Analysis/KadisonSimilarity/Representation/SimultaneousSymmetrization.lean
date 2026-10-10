import OAI.Analysis.KadisonSimilarity.FreeProduct.HaarSymmetrization

namespace OAI

/-! Simultaneous symmetry for an increasing family of compact groups, using
actual Haar averages and a weak-operator cluster point. -/

noncomputable section
namespace KadisonSimilarity

open Filter ContinuousLinearMapWOT MeasureTheory
open scoped Topology

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
/-- A fixed rectangular compression is weak-operator continuous, so an exact
compression identity survives a weak-operator cluster point. -/
theorem compression_eq_of_weakOperator_cluster (T : ℕ → H →L[ℂ] H)
    (S : H →L[ℂ] H) (A : K →L[ℂ] H) (B : H →L[ℂ] K) (C : K →L[ℂ] K)
    (hcluster : MapClusterPt (ofCLM S) atTop (fun n => ofCLM (T n)))
    (heq : ∀ᶠ n in atTop, B.comp ((T n).comp A) = C) : B.comp (S.comp A) = C := by
  have hcont : Continuous (fun R : H →WOT[ℂ] H =>
      (ofCLM B).comp (R.comp (ofCLM A))) :=
    (continuous_postcomp (ofCLM B)).comp (continuous_precomp (ofCLM A))
  have hclosed : IsClosed {R : H →WOT[ℂ] H |
      (ofCLM B).comp (R.comp (ofCLM A)) = ofCLM C} :=
    isClosed_eq hcont continuous_const
  have heq' : ∀ᶠ n in atTop, ofCLM (T n) ∈
      {R : H →WOT[ℂ] H | (ofCLM B).comp (R.comp (ofCLM A)) = ofCLM C} := by
    filter_upwards [heq] with n hn
    exact congrArg ofCLM hn
  have he := hclosed.mem_of_mapClusterPt hcluster heq'
  exact congrArg toCLM he

variable {Γ : ℕ → Type*} [∀ n, Group (Γ n)] [∀ n, MeasurableSpace (Γ n)]
  [∀ n, MeasurableMul (Γ n)]
  (μ : ∀ n, Measure (Γ n)) [∀ n, IsProbabilityMeasure (μ n)]
  [∀ n, (μ n).IsMulLeftInvariant]

/-- A single cluster point has every finite-stage symmetry, all common
commutator bounds, and the original compression to the fixed subspace.
The stage maps are ordinary group-element inclusions; no limiting invariant
operator is assumed among the data. -/
theorem exists_simultaneously_symmetrized
    (U : ∀ n, Γ n →* (H →L[ℂ] H)) (hU : ∀ n g, ‖U n g‖ ≤ 1)
    (hstar : ∀ n g, (U n g).adjoint = U n g⁻¹)
    (embedding : ∀ n m, n ≤ m → Γ n → Γ m)
    (hcompat : ∀ n m h g, U m (embedding n m h g) = U n g)
    (T : H →L[ℂ] H)
    (hI : ∀ n, WeaklyIntegrable (μ n) (unitaryConjugate (U n) T))
    (J : K →L[ℂ] H) (hfix : ∀ n g, (U n g).comp J = J)
    {ι : Type*} (test : ι → H →L[ℂ] H) (bound : ι → ℝ) (hbound : ∀ i, 0 ≤ bound i)
    (htest : ∀ n g i, ‖commutator (unitaryConjugate (U n) T g) (test i)‖ ≤ bound i) :
    ∃ S : H →L[ℂ] H,
      ‖S‖ ≤ ‖T‖ ∧
      (∀ n g, commutator S (U n g) = 0) ∧
      (∀ i, ‖commutator S (test i)‖ ≤ bound i) ∧
      J.adjoint.comp (S.comp J) = J.adjoint.comp (T.comp J) := by
  let averages : ℕ → H →L[ℂ] H := fun n => haarTwirl (μ n) (U n) (hU n) T (hI n)
  obtain ⟨S, hS, hcluster⟩ := exists_weakOperator_cluster averages (norm_nonneg T)
    (fun n => norm_haarTwirl_le (μ n) (U n) (hU n) T (hI n))
  refine ⟨S, hS, ?_, ?_, ?_⟩
  · intro n g
    apply norm_eq_zero.mp
    apply le_antisymm ?_ (norm_nonneg _)
    apply norm_commutator_le_of_weakOperator_cluster averages S (U n g) hcluster (le_refl 0)
    filter_upwards [eventually_ge_atTop n] with m hm
    have he := haarTwirl_commute (μ m) (U m) (hU m) T (hI m) (embedding n m hm g)
    rw [hcompat] at he
    simp only [averages, he, norm_zero, le_refl]
  · intro i
    apply norm_commutator_le_of_weakOperator_cluster averages S (test i) hcluster (hbound i)
    exact Eventually.of_forall fun n =>
      norm_commutator_haarTwirl_le (μ n) (U n) (hU n) T (hI n) (test i)
        (hbound i) (fun g => htest n g i)
  · apply compression_eq_of_weakOperator_cluster averages S J J.adjoint
      (J.adjoint.comp (T.comp J)) hcluster
    exact Eventually.of_forall fun n =>
      haarTwirl_compression (μ n) (U n) (hU n) (hstar n) T (hI n) J (hfix n)

end KadisonSimilarity

end

end OAI
