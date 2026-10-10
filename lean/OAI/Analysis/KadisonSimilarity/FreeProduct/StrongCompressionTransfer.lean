import OAI.Analysis.KadisonSimilarity.Derivation.FiniteDerivationColumns
import OAI.Analysis.KadisonSimilarity.Representation.WeakOperatorLimits
import OAI.Analysis.KadisonSimilarity.Representation.OrthogonalColumns

namespace OAI

/-! Uniform finite-compression estimates pass to the full representation.
Only strong convergence of the selfadjoint compressions is needed: the
two projection factors are moved to the two test vectors in the weak
operator matrix coefficients. -/

noncomputable section
namespace KadisonSimilarity
open Filter ContinuousLinearMapWOT
open scoped Topology

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {l : Filter I}

theorem weakOperator_tendsto_selfadjoint_compressions
    (Q : I → H →L[ℂ] H) (hQ : ∀ i, (Q i).adjoint = Q i)
    (hlim : ∀ x, Tendsto (fun i => Q i x) l (𝓝 x)) (T : H →L[ℂ] H) :
    Tendsto (fun i => ofCLM ((Q i).comp (T.comp (Q i)))) l (𝓝 (ofCLM T)) := by
  apply tendsto_iff_forall_inner_apply_tendsto.mpr
  intro x y
  have h := (hlim y).inner (𝕜 := ℂ) ((T.continuous.tendsto x).comp (hlim x))
  convert h using 1
  funext i
  change inner ℂ y (Q i (T (Q i x))) = inner ℂ (Q i y) (T (Q i x))
  rw [← ContinuousLinearMap.adjoint_inner_left, hQ]

/-- A fixed matrix commutator estimate for all finite compressions survives
the limit, with exactly the same constant. -/
theorem matrix_commutator_bound_of_selfadjoint_compressions
    (Q : I → H →L[ℂ] H) (hQ : ∀ i, (Q i).adjoint = Q i)
    (hlim : ∀ x, Tendsto (fun i => Q i x) l (𝓝 x))
    [l.NeBot] (T : H →L[ℂ] H) (n : ℕ)
    (X : HilbertCopies H n →L[ℂ] HilbertCopies H n) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ᶠ i in l,
      ‖commutator (amplify ((Q i).comp (T.comp (Q i))) n) X‖ ≤ c) :
    ‖commutator (amplify T n) X‖ ≤ c := by
  have hconv := weakOperator_tendsto_selfadjoint_compressions
    (fun i => amplify (Q i) n)
    (fun i => by rw [adjoint_amplify, hQ])
    (amplify_tendsto_apply Q hlim n) (amplify T n)
  have heq (i : I) :
      (amplify (Q i) n).comp ((amplify T n).comp (amplify (Q i) n)) =
        amplify ((Q i).comp (T.comp (Q i))) n := by
    ext x j
    rfl
  simp only [heq] at hconv
  exact norm_commutator_le_of_weakOperator_tendsto _ (amplify T n) X hconv hc hbound

end KadisonSimilarity

end

end OAI
