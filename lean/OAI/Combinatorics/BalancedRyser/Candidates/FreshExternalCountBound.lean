import OAI.Combinatorics.BalancedRyser.Candidates.ExternalWitnessModel
import OAI.Combinatorics.BalancedRyser.Candidates.FreshExternalCounting
import OAI.Combinatorics.BalancedRyser.Probability.FreshWitnessProbability

namespace OAI

namespace Balanced.FreshExternalWitness

noncomputable section
open scoped Classical BigOperators
open TupleAlignment CandidateExposure CandidateValidityWitness MeasureTheory

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def sourceEvent (g : Direction F) (T : FourTuple F) (i j : Fin 4)
    (de : Direction F × Direction F) (M : MergedPairs F) : Prop :=
  ∃ (c : F) (x : Point F), SuccessfulOn M T (g,c) ∧
    OnLine x (g,c) ∧ x ∉ designated M ⟨(g,c), T⟩ ∧ i ≠ j ∧
    de.1 ≠ g ∧ de.2 ≠ g ∧
    PairWitness M de.1 x (tuplePoint M T i) ∧
    PairWitness M de.2 x (tuplePoint M T j)

omit [Fintype F] in
theorem sourceEvent_iff_witnessEvent (g : Direction F) (T : FourTuple F)
    (i j : Fin 4) (de : Direction F × Direction F) (M : MergedPairs F) :
    sourceEvent g T i j de M ↔
      M ∈ ExternalAssembly.witnessEvent g ((T, (i,j)), de) := by
  constructor
  · rintro ⟨c, x, hs, hx, hex, hij, hd, he, hdi, hej⟩
    have hline : ExternalAssembly.targetLine g M T = (g,c) :=
      ExternalAssembly.targetLine_eq_of_success hs
    have hde := external_witness_directions_distinct hs hx hex hij hd hdi hej
    have hdT := external_witness_not_generator hs hx hex hdi
    have heT := external_witness_not_generator hs hx hex hej
    simp only [ExternalAssembly.witnessEvent, Set.mem_ofPred_eq, hline]
    exact ⟨hs, hij, hde, hd, he, hdT, heT, x, hx, hex, hdi, hej⟩
  · rintro ⟨hs, hij, _, hd, he, _, _, x, hx, hex, hdi, hej⟩
    exact ⟨lineEval g (tuplePoint M T 0), x, hs, hx, hex, hij, hd, he, hdi, hej⟩

theorem sourceEvent_eligible (g : Direction F) (T : FourTuple F)
    (i j : Fin 4) (de : Direction F × Direction F) (M : MergedPairs F)
    (h : sourceEvent g T i j de M) : T ∈ eligibleTuples g := by
  obtain ⟨c, x, hs, _⟩ := h
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.1, hs.2.1⟩

theorem sourceEvent_freshPairs_iff (g : Direction F) (D : Finset (Direction F))
    (T : FourTuple F) (i j : Fin 4) (de : Direction F × Direction F)
    (M : MergedPairs F) (h : sourceEvent g T i j de M) :
    de ∈ freshPairs D T ↔ de.1 ∉ D ∧ de.2 ∉ D := by
  have hw := (sourceEvent_iff_witnessEvent g T i j de M).mp h
  obtain ⟨_, _, hde, _, _, hdT, heT, _⟩ := hw
  have hdf : ∀ k, T.generator k ≠ de.1 := by
    intro k hk
    exact hdT (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩)
  have hef : ∀ k, T.generator k ≠ de.2 := by
    intro k hk
    exact heT (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩)
  rw [mem_freshPairs]
  constructor
  · intro hmem
    exact ⟨hmem.2.1, hmem.2.2.1⟩
  · rintro ⟨hdD, heD⟩
    exact ⟨hde, hdD, heD, hdf, hef⟩

omit [Fintype F] in
theorem sourceEvent_has_orientedEvent (g : Direction F) (T : FourTuple F)
    (i j : Fin 4) (de : Direction F × Direction F) (M : MergedPairs F)
    (h : sourceEvent g T i j de M) :
    ∃ σ τ z, orientedEvent g T de.1 de.2 i j σ τ z M := by
  obtain ⟨c, x, hs, hx, _, _, _, _, hdi, hej⟩ := h
  have hc : lineEval g (tuplePoint M T 0) = c := hs.2.2.2 0
  have hx' : OnLine x (g, lineEval g (tuplePoint M T 0)) := by
    simpa only [hc] using hx
  obtain ⟨z, hz⟩ := exists_targetPoint g T M x hx'
  obtain ⟨σ, hσ⟩ := hdi
  obtain ⟨τ, hτ⟩ := hej
  refine ⟨σ, τ, z, ?_⟩
  unfold orientedEvent
  rw [hz]
  exact ⟨⟨⟨⟨c, hs.2.2.2⟩, hs.2.2.1⟩, hσ⟩, hτ⟩

private theorem outerProbability_mono {Ω : Type*} (p : PMF Ω)
    {E H : Set Ω} (h : E ⊆ H) :
    (p.toOuterMeasure E).toReal ≤ (p.toOuterMeasure H).toReal := by
  apply ENNReal.toReal_mono
  · rw [PMF.toOuterMeasure_apply]
    exact p.tsum_coe_indicator_ne_top H
  · exact p.toOuterMeasure_mono (fun _ hx => h hx.1)

theorem sourceEvent_probability_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (T : FourTuple F) (i j : Fin 4)
    (de : Direction F × Direction F) :
    conditionalProbability D a {M | sourceEvent g T i j de M} ≤
      ∑ σ : Bool, ∑ τ : Bool, ∑ z : F,
        conditionalProbability D a {M | orientedEvent g T de.1 de.2 i j σ τ z M} := by
  let E : (Bool × Bool × F) → Set (MergedPairs F) :=
    fun s => {M | orientedEvent g T de.1 de.2 i j s.1 s.2.1 s.2.2 M}
  have hsub : {M | sourceEvent g T i j de M} ⊆ {M | ∃ s, M ∈ E s} := by
    intro M hM
    obtain ⟨σ, τ, z, hz⟩ := sourceEvent_has_orientedEvent g T i j de M hM
    exact ⟨(σ, τ, z), hz⟩
  calc
    _ ≤ ((exposedLaw D a).toOuterMeasure {M | ∃ s, M ∈ E s}).toReal :=
      outerProbability_mono _ hsub
    _ ≤ ∑ s, ((exposedLaw D a).toOuterMeasure (E s)).toReal :=
      FreshWitnessProbability.probability_exists_le_sum _ E
    _ = _ := by simp only [Fintype.sum_prod_type, E, conditionalProbability]

def sourceProbabilitySum (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, ∑ r : RootPrescription g,
    ∑ de ∈ freshPairs D r.tuple,
      conditionalProbability D a {M | sourceEvent g r.tuple i j de M}

theorem sourceProbabilitySum_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    sourceProbabilitySum g D a ≤ (5242880 * (m + 1)^4 : ℝ) := by
  apply le_trans _ (all_positions_probabilitySum_le g D a m hD)
  unfold sourceProbabilitySum probabilitySum
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro r _
  apply Finset.sum_le_sum
  intro de _
  exact sourceEvent_probability_le g D a r.tuple i j de

def sourceWitnessCount (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) : ℕ :=
  ∑ i : Fin 4, ∑ j : Fin 4, ∑ r : RootPrescription g,
    ((freshPairs D r.tuple).filter (fun de => sourceEvent g r.tuple i j de M)).card

omit [Field F] in
private theorem sum_roots_eq_all (g : Direction F) (f : FourTuple F → ℕ)
    (hf : ∀ T, T ∉ eligibleTuples g → f T = 0) :
    (∑ r : RootPrescription g, f r.tuple) = ∑ T : FourTuple F, f T := by
  have he := Equiv.sum_comp (eligibleTupleEquivRootPrescription g)
    (fun r => f r.tuple)
  simp only [equivRootPrescription_tuple] at he
  have hs := Finset.sum_subtype (eligibleTuples g)
    (p := fun T => T ∈ eligibleTuples g)
    (F := inferInstance) (fun _ => Iff.rfl) f
  calc
    _ = ∑ T ∈ eligibleTuples g, f T := (hs.trans he).symm
    _ = ∑ T : FourTuple F, f T := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro T _ hT
      exact hf T hT

private theorem sourceLabelCount_eq (g : Direction F) (D : Finset (Direction F))
    (T : FourTuple F) (i j : Fin 4) (M : MergedPairs F) :
    ((freshPairs D T).filter (fun de => sourceEvent g T i j de M)).card =
      ∑ de : Direction F × Direction F,
        if sourceEvent g T i j de M ∧ de.1 ∉ D ∧ de.2 ∉ D then 1 else 0 := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, freshPairs]
  apply Finset.sum_congr rfl
  intro de _
  by_cases hs : sourceEvent g T i j de M
  · have hmem := sourceEvent_freshPairs_iff g D T i j de M hs
    rw [mem_freshPairs] at hmem
    simp only [hs, ite_true, true_and, hmem]
  · simp only [hs, ite_false, false_and]
    split <;> rfl

theorem canonical_fresh_count_eq (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) :
    ((ExternalAssembly.witnesses g M).filter
      (fun w => w.2.1 ∉ D ∧ w.2.2 ∉ D)).card = sourceWitnessCount g D M := by
  unfold sourceWitnessCount
  have hs (i j : Fin 4) :
      (∑ r : RootPrescription g,
        ((freshPairs D r.tuple).filter
          (fun de => sourceEvent g r.tuple i j de M)).card) =
      ∑ T : FourTuple F,
        ((freshPairs D T).filter (fun de => sourceEvent g T i j de M)).card := by
    apply sum_roots_eq_all g (fun T =>
      ((freshPairs D T).filter (fun de => sourceEvent g T i j de M)).card)
    intro T hT
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro de _ hs
    exact hT (sourceEvent_eligible g T i j de M hs)
  simp_rw [hs, sourceLabelCount_eq]
  simp only [ExternalAssembly.witnesses, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fintype.sum_prod_type]
  simp_rw [← sourceEvent_iff_witnessEvent, ite_and]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

section Measurable
variable [MeasurableSpace F] [MeasurableSingletonClass F]

theorem integral_sourceWitnessCount (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) :
    (∫ M, (sourceWitnessCount g D M : ℝ) ∂(exposedLaw D a).toMeasure) =
      sourceProbabilitySum g D a := by
  simp only [sourceWitnessCount, Nat.cast_sum]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  unfold sourceProbabilitySum
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro r _
  exact integral_eventCount_eq_sum (exposedLaw D a) (freshPairs D r.tuple)
    (fun de => {M | sourceEvent g r.tuple i j de M})

theorem sourceWitnessCount_mean_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∫ M, (sourceWitnessCount g D M : ℝ) ∂(exposedLaw D a).toMeasure) ≤
      (5242880 * (m + 1)^4 : ℝ) := by
  rw [integral_sourceWitnessCount]
  exact sourceProbabilitySum_le g D a m hD

theorem canonical_fresh_count_integral_le (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ)
    (hD : D.card ≤ m) :
    (∫ M, (((ExternalAssembly.witnesses g M).filter
      (fun w => w.2.1 ∉ D ∧ w.2.2 ∉ D)).card : ℝ)
      ∂(exposedLaw D a).toMeasure) ≤ (5242880 * (m + 1)^4 : ℝ) := by
  simp_rw [canonical_fresh_count_eq]
  exact sourceWitnessCount_mean_le g D a m hD

end Measurable
end
end Balanced.FreshExternalWitness

end OAI
