import OAI.Combinatorics.BalancedRyser.Candidates.CandidateRootCount
import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence
import OAI.Combinatorics.BalancedRyser.Probability.FiniteUniformFibers
import OAI.Combinatorics.BalancedRyser.Probability.FreshDoublePrescription
import OAI.Combinatorics.BalancedRyser.Probability.FreshWitnessConditional

namespace OAI

namespace Balanced.FreshExternalWitness

noncomputable section
open scoped Classical BigOperators
open FreshTupleWitness TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem two_prescriptions_on_subtype
    (d e : Direction F) (hde : d ≠ e)
    (G E : MergedPairs F → Prop) [Nonempty {M : MergedPairs F // G M}]
    (b c : MergedPairs F → Bool → F)
    (hGd : ∀ M v, G (Function.update M d v) ↔ G M)
    (hGe : ∀ M v, G (Function.update M e v) ↔ G M)
    (hEd : ∀ M v, E (Function.update M d v) ↔ E M)
    (hEe : ∀ M v, E (Function.update M e v) ↔ E M)
    (hbd : ∀ M v, b (Function.update M d v) = b M)
    (hbe : ∀ M v, b (Function.update M e v) = b M)
    (hce : ∀ M v, c (Function.update M e v) = c M) :
    ((PMF.uniformOfFintype {M : MergedPairs F // G M}).toOuterMeasure
      {M | (E M.1 ∧ M.1 d = b M.1) ∧ M.1 e = c M.1}).toReal =
    ((PMF.uniformOfFintype {M : MergedPairs F // G M}).toOuterMeasure
      {M | E M.1}).toReal / (Fintype.card F : ℝ)^4 := by
  have h := FreshCoordinate.probability_two_prescriptions_on_subtype e d hde.symm
    G E c b hGe hGd hEe hEd hce hbe hbd
  have hcard : (Fintype.card (Bool → F) : ℝ)^2 = (Fintype.card F : ℝ)^4 := by
    simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow]
    ring
  rw [hcard] at h
  simpa only [and_assoc, and_left_comm, and_comm] using h

def targetPoint (g : Direction F) (T : FourTuple F) (z : F)
    (M : MergedPairs F) : Point F :=
  ((linePointsEquiv (g, lineEval g (tuplePoint M T 0))).symm z).1

omit [Fintype F] in
theorem targetPoint_update_fresh (g : Direction F) (T : FourTuple F)
    (z : F) (d : Direction F) (hd : ∀ i, T.generator i ≠ d)
    (M : MergedPairs F) (v : Bool → F) :
    targetPoint g T z (Function.update M d v) = targetPoint g T z M := by
  unfold targetPoint
  rw [tuplePoint_update_fresh T d hd]

omit [Fintype F] [DecidableEq F] in
theorem targetPoint_onLine (g : Direction F) (T : FourTuple F)
    (z : F) (M : MergedPairs F) :
    OnLine (targetPoint g T z M) (g, lineEval g (tuplePoint M T 0)) :=
  ((linePointsEquiv (g, lineEval g (tuplePoint M T 0))).symm z).2

omit [Fintype F] [DecidableEq F] in
theorem exists_targetPoint (g : Direction F) (T : FourTuple F)
    (M : MergedPairs F) (x : Point F)
    (hx : OnLine x (g, lineEval g (tuplePoint M T 0))) :
    ∃ z, targetPoint g T z M = x := by
  refine ⟨linePointsEquiv (g, lineEval g (tuplePoint M T 0)) ⟨x, hx⟩, ?_⟩
  exact congrArg Subtype.val ((linePointsEquiv
    (g, lineEval g (tuplePoint M T 0))).symm_apply_apply ⟨x, hx⟩)

def orientedEvent (g : Direction F) (T : FourTuple F) (d e : Direction F)
    (i j : Fin 4) (σ τ : Bool) (z : F) (M : MergedPairs F) : Prop :=
  ((((∃ c, ∀ k, OnLine (tuplePoint M T k) (g,c)) ∧
      Function.Injective (tuplePoint M T)) ∧
    (OnLine (targetPoint g T z M) (constituent M d σ) ∧
      OnLine (tuplePoint M T i) (constituent M d (!σ)))) ∧
    (OnLine (targetPoint g T z M) (constituent M e τ) ∧
      OnLine (tuplePoint M T j) (constituent M e (!τ))))

theorem orientedEvent_probability_eq
    (G : MergedPairs F → Prop) [Nonempty {M : MergedPairs F // G M}]
    (g : Direction F) (T : FourTuple F) (d e : Direction F)
    (hde : d ≠ e) (hd : ∀ k, T.generator k ≠ d)
    (he : ∀ k, T.generator k ≠ e)
    (hGd : ∀ M v, G (Function.update M d v) ↔ G M)
    (hGe : ∀ M v, G (Function.update M e v) ↔ G M)
    (i j : Fin 4) (σ τ : Bool) (z : F) :
    ((PMF.uniformOfFintype {M : MergedPairs F // G M}).toOuterMeasure
      {M | orientedEvent g T d e i j σ τ z M.1}).toReal =
      fiberSuccessProbability G g T / (Fintype.card F : ℝ)^4 := by
  have h := two_prescriptions_on_subtype d e hde G
    (fun M => (∃ c, ∀ k, OnLine (tuplePoint M T k) (g,c)) ∧
      Function.Injective (tuplePoint M T))
    (fun M => pairPrescription d (targetPoint g T z M) (tuplePoint M T i) σ)
    (fun M => pairPrescription e (targetPoint g T z M) (tuplePoint M T j) τ)
    hGd hGe
    (by intro M v; rw [tuplePoint_update_fresh T d hd])
    (by intro M v; rw [tuplePoint_update_fresh T e he])
    (by intro M v; rw [targetPoint_update_fresh g T z d hd,
      tuplePoint_update_fresh T d hd])
    (by intro M v; rw [targetPoint_update_fresh g T z e he,
      tuplePoint_update_fresh T e he])
    (by intro M v; rw [targetPoint_update_fresh g T z e he,
      tuplePoint_update_fresh T e he])
  simp_rw [pairPrescription_iff] at h
  exact h

theorem sum_orientedEvent_probability_eq
    (G : MergedPairs F → Prop) [Nonempty {M : MergedPairs F // G M}]
    (g : Direction F) (T : FourTuple F) (U : Finset (Direction F × Direction F))
    (hU : ∀ de ∈ U, de.1 ≠ de.2 ∧
      (∀ k, T.generator k ≠ de.1) ∧ (∀ k, T.generator k ≠ de.2))
    (hG : ∀ de ∈ U, (∀ M v, G (Function.update M de.1 v) ↔ G M) ∧
      (∀ M v, G (Function.update M de.2 v) ↔ G M))
    (i j : Fin 4) :
    (∑ de ∈ U, ∑ σ : Bool, ∑ τ : Bool, ∑ z : F,
      ((PMF.uniformOfFintype {M : MergedPairs F // G M}).toOuterMeasure
        {M | orientedEvent g T de.1 de.2 i j σ τ z M.1}).toReal) =
      4 * (U.card : ℝ) * Fintype.card F * fiberSuccessProbability G g T /
        (Fintype.card F : ℝ)^4 := by
  calc
    _ = ∑ _de ∈ U, ∑ _σ : Bool, ∑ _τ : Bool, ∑ _z : F,
        fiberSuccessProbability G g T / (Fintype.card F : ℝ)^4 := by
      apply Finset.sum_congr rfl
      intro de hde
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro τ _
      apply Finset.sum_congr rfl
      intro z _
      exact orientedEvent_probability_eq G g T de.1 de.2
        (hU de hde).1 (hU de hde).2.1 (hU de hde).2.2
        (hG de hde).1 (hG de hde).2 i j σ τ z
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool,
        nsmul_eq_mul]
      ring

theorem sum_orientedEvent_probability_le
    (G : MergedPairs F → Prop) [Nonempty {M : MergedPairs F // G M}]
    (g : Direction F) (T : FourTuple F) (U : Finset (Direction F × Direction F))
    (hU : ∀ de ∈ U, de.1 ≠ de.2 ∧
      (∀ k, T.generator k ≠ de.1) ∧ (∀ k, T.generator k ≠ de.2))
    (hG : ∀ de ∈ U, (∀ M v, G (Function.update M de.1 v) ↔ G M) ∧
      (∀ M v, G (Function.update M de.2 v) ↔ G M))
    (i j : Fin 4) :
    (∑ de ∈ U, ∑ σ : Bool, ∑ τ : Bool, ∑ z : F,
      ((PMF.uniformOfFintype {M : MergedPairs F // G M}).toOuterMeasure
        {M | orientedEvent g T de.1 de.2 i j σ τ z M.1}).toReal) ≤
      (16 / Fintype.card F : ℝ) * fiberSuccessProbability G g T := by
  rw [sum_orientedEvent_probability_eq G g T U hU hG i j]
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos (α := F)
  have hUcard : (U.card : ℝ) ≤ ((Fintype.card F : ℝ) + 1)^2 := by
    have h := Finset.card_le_univ U
    simp only [Fintype.card_prod, Direction, Fintype.card_option] at h
    rw [pow_two]
    exact_mod_cast h
  have hUm : (U.card : ℝ) ≤ 4 * (Fintype.card F : ℝ)^2 := by
    nlinarith [sq_nonneg ((Fintype.card F : ℝ) - 1)]
  have hp : 0 ≤ fiberSuccessProbability G g T := ENNReal.toReal_nonneg
  calc
    _ ≤ 4 * (4 * (Fintype.card F : ℝ)^2) * Fintype.card F *
        fiberSuccessProbability G g T / (Fintype.card F : ℝ)^4 := by gcongr
    _ = _ := by field_simp; ring

abbrev fixedValues (D : Finset (Direction F)) (a : MergedPairs F)
    (M : MergedPairs F) : Prop := ∀ d, d ∈ D → M d = a d

theorem fixedFiber_probability_eq (D : Finset (Direction F)) (a : MergedPairs F)
    (E : Set (MergedPairs F)) :
    ((PMF.uniformOfFintype {M : MergedPairs F // fixedValues D a M}).toOuterMeasure
      {M | M.1 ∈ E}).toReal = CandidateExposure.conditionalProbability D a E := by
  unfold CandidateExposure.conditionalProbability CandidateExposure.exposedLaw
  simp only [PartialAlignment.offsetLaw_eq_uniform]
  rw [ConditionalRestriction.uniform_fixed_filter, PMF.toOuterMeasure_map_apply]
  exact FiniteUniformFibers.probability_fintype_congr _ _ rfl

theorem sum_fiberSuccessProbability_eq (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (∑ r : RootPrescription g, fiberSuccessProbability (fixedValues D a) g r.tuple) =
      CandidateExposure.successProbabilitySum g D a := by
  have hp (T : FourTuple F) : fiberSuccessProbability (fixedValues D a) g T =
      CandidateExposure.conditionalProbability D a
        (CandidateExposure.successfulInDirection T g) := by
    unfold fiberSuccessProbability
    calc
      _ = ((PMF.uniformOfFintype {M : MergedPairs F // fixedValues D a M}).toOuterMeasure
          {M | M.1 ∈ CandidateExposure.successfulInDirection T g}).toReal :=
        FiniteUniformFibers.probability_fintype_congr _ _ rfl
      _ = _ := fixedFiber_probability_eq D a (CandidateExposure.successfulInDirection T g)
  simp_rw [hp]
  let f : FourTuple F → ℝ := fun T => CandidateExposure.conditionalProbability D a
    (CandidateExposure.successfulInDirection T g)
  have he := Equiv.sum_comp (CandidateExposure.eligibleTupleEquivRootPrescription g)
    (fun r => f r.tuple)
  simp only [CandidateExposure.equivRootPrescription_tuple] at he
  have hs := Finset.sum_subtype (CandidateExposure.eligibleTuples g)
    (p := fun T => T ∈ CandidateExposure.eligibleTuples g)
    (F := inferInstance) (fun _ => Iff.rfl) f
  exact (hs.trans he).symm

end
end Balanced.FreshExternalWitness

end OAI
