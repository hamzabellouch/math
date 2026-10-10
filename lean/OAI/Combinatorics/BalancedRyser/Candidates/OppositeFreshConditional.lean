import OAI.Combinatorics.BalancedRyser.Candidates.CandidateConditionalMean
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateValidityWitness
import OAI.Combinatorics.BalancedRyser.Probability.FreshWitnessConditional
import OAI.Combinatorics.BalancedRyser.Probability.FreshWitnessProbability

namespace OAI

namespace Balanced.OppositeFreshConditional

noncomputable section
open scoped Classical BigOperators
attribute [local instance] Classical.propDecidable
open CandidateExposure CandidateValidityWitness FreshTupleWitness ConditionalRestriction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem uniform_probability_irrel {Ω : Type*} [Nonempty Ω]
    (f h : Fintype Ω) (E : Set Ω) :
    ((@PMF.uniformOfFintype Ω f inferInstance).toOuterMeasure E).toReal =
      ((@PMF.uniformOfFintype Ω h inferInstance).toOuterMeasure E).toReal := by
  cases Subsingleton.elim f h
  rfl

theorem exposed_probability_eq_fiber (D : Finset (Direction F)) (a : MergedPairs F)
    (E : Set (MergedPairs F)) :
    ((CandidateExposure.exposedLaw D a).toOuterMeasure E).toReal =
      ((PMF.uniformOfFintype (FixedArray (fun d => d ∈ D) a)).toOuterMeasure
        {M | M.1 ∈ E}).toReal := by
  simp only [CandidateExposure.exposedLaw, PartialAlignment.offsetLaw_eq_uniform]
  rw [uniform_fixed_filter, PMF.toOuterMeasure_map_apply]
  exact uniform_probability_irrel _ _ _

theorem oriented_probability (D : Finset (Direction F)) (a : MergedPairs F)
    (g : Direction F) (T : FourTuple F) (d : Direction F)
    (hd : d ∉ D) (hT : d ∉ generatorSet T) (i j : Fin 4) (σ : Bool) :
    ((CandidateExposure.exposedLaw D a).toOuterMeasure {M |
      M ∈ successfulInDirection T g ∧
      OnLine (tuplePoint M T i) (constituent M d σ) ∧
      OnLine (tuplePoint M T j) (constituent M d (!σ))}).toReal =
    ((CandidateExposure.exposedLaw D a).toOuterMeasure
      (successfulInDirection T g)).toReal / (Fintype.card F : ℝ)^2 := by
  rw [exposed_probability_eq_fiber, exposed_probability_eq_fiber]
  have hgen : ∀ k, T.generator k ≠ d := by
    intro k hk
    exact hT (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩)
  have h := oriented_pair_probability_on_event T d hgen i j σ
    (fun M => ∀ t, t ∈ D → M t = a t)
    (fixed_coordinates_update_invariant (fun t => t ∈ D) a d hd)
    (fun p => (∃ c, ∀ k, OnLine (p k) (g,c)) ∧ Function.Injective p)
  refine (uniform_probability_irrel _ _ _).trans (h.trans ?_)
  apply congrArg (fun r : ℝ => r / (Fintype.card F : ℝ)^2)
  exact uniform_probability_irrel _ _ _

theorem pair_probability_le (D : Finset (Direction F)) (a : MergedPairs F)
    (g : Direction F) (T : FourTuple F) (d : Direction F)
    (hd : d ∉ D) (hT : d ∉ generatorSet T) (i j : Fin 4) :
    ((CandidateExposure.exposedLaw D a).toOuterMeasure {M |
      M ∈ successfulInDirection T g ∧
      PairWitness M d (tuplePoint M T i) (tuplePoint M T j)}).toReal ≤
      2 * ((CandidateExposure.exposedLaw D a).toOuterMeasure
        (successfulInDirection T g)).toReal / (Fintype.card F : ℝ)^2 := by
  let E : Bool → Set (MergedPairs F) := fun σ => {M |
    M ∈ successfulInDirection T g ∧
    OnLine (tuplePoint M T i) (constituent M d σ) ∧
    OnLine (tuplePoint M T j) (constituent M d (!σ))}
  have heq : {M : MergedPairs F | M ∈ successfulInDirection T g ∧
      PairWitness M d (tuplePoint M T i) (tuplePoint M T j)} =
      {M | ∃ σ, M ∈ E σ} := by
    ext M
    simp only [Set.mem_ofPred_eq, E, PairWitness]
    constructor
    · rintro ⟨h, σ, hs⟩
      exact ⟨σ, h, hs⟩
    · rintro ⟨σ, h, hs⟩
      exact ⟨h, σ, hs⟩
  rw [heq]
  apply (FreshWitnessProbability.probability_exists_le_sum _ E).trans
  have hE (σ : Bool) :
      ((CandidateExposure.exposedLaw D a).toOuterMeasure (E σ)).toReal =
      ((CandidateExposure.exposedLaw D a).toOuterMeasure
        (successfulInDirection T g)).toReal / (Fintype.card F : ℝ)^2 :=
    oriented_probability D a g T d hd hT i j σ
  simp only [hE, Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
  ring_nf
  exact le_rfl

end
end Balanced.OppositeFreshConditional

end OAI
