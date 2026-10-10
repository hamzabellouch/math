import OAI.Combinatorics.BalancedRyser.Incidence.CandidateIncidenceModel
import OAI.Combinatorics.BalancedRyser.Incidence.CandidateIncidenceRootSums
import OAI.Combinatorics.BalancedRyser.Probability.PatternAllowedGate

namespace OAI

namespace Balanced.CandidateIncidenceSums

noncomputable section
open scoped Classical BigOperators
open PartialAlignment TupleAlignment CandidateExposure CandidateIncidence MeasureTheory

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance twoLineMeasurableSpace : MeasurableSpace F := ⊤

def tupleIncidenceSum (D : Finset (Direction F)) (a : MergedPairs F) (j : ℕ)
    (P : Direction F → (Fin 4 → Point F) → Prop) : ℝ :=
  ∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D j, conditionalProbability D a
    {M | M ∈ successfulInDirection T g ∧ P g (tuplePoint M T)}

theorem rootIncidenceSum_eq_tupleIncidenceSum (D : Finset (Direction F))
    (a : MergedPairs F) (j : ℕ) (P : Direction F → (Fin 4 → Point F) → Prop) :
    rootIncidenceSum D a j P = tupleIncidenceSum D a j P := by
  rw [rootIncidenceSum_eq_iterated]
  unfold tupleIncidenceSum
  apply Finset.sum_congr rfl
  intro g _
  let f : FourTuple F → ℝ := fun T =>
    if (exposedTupleIndices T D).card = j then conditionalProbability D a
      {M | M ∈ successfulInDirection T g ∧ P g (tuplePoint M T)} else 0
  have he := Equiv.sum_comp (eligibleTupleEquivRootPrescription g)
    (fun r : RootPrescription g => f r.tuple)
  simp only [equivRootPrescription_tuple] at he
  have hs := Finset.sum_subtype (eligibleTuples g)
    (p := fun T => T ∈ eligibleTuples g) (F := inferInstance) (fun _ => Iff.rfl) f
  have h := (hs.trans he).symm
  simpa only [f, tuplesWithExposure, Finset.sum_filter, probability,
    conditionalProbability, exposedLaw, successfulInDirection, alignedInDirection,
    SuccessfulPositions, Set.mem_ofPred_eq] using h

theorem tupleIncidenceSum_le_success (D : Finset (Direction F))
    (a : MergedPairs F) (j : ℕ) (P : Direction F → (Fin 4 → Point F) → Prop) :
    tupleIncidenceSum D a j P ≤ ∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D j,
      conditionalProbability D a (successfulInDirection T g) := by
  apply Finset.sum_le_sum
  intro g _
  apply Finset.sum_le_sum
  intro T _
  exact conditionalProbability_mono D a (fun _ h => h.1)

theorem allModel_fixed_count_eq_sum_strata
    (D : Finset (Direction F)) (a : MergedPairs F)
    (P : Direction F → (Fin 4 → Point F) → Prop) :
    (allModel (fun _ g p => P g p)).fixedExpectation D a
      (allModel (fun _ g p => P g p)).count =
      ∑ j ∈ Finset.range 5, tupleIncidenceSum D a j P := by
  rw [allModel_fixed_count]
  unfold tupleIncidenceSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (s := eligibleTuples g) (t := Finset.range 5)
    (g := fun T => (exposedTupleIndices T D).card)
    (fun T _ => Finset.mem_range.mpr (by
      have h := Finset.card_le_univ (exposedTupleIndices T D)
      simp only [Fintype.card_fin] at h
      omega))
    (fun T => conditionalProbability D a
      {M | M ∈ successfulInDirection T g ∧ P g (tuplePoint M T)})

def twoLineTest (L K : Line F) : Test F := fun _ g p => hitsTwoLines L K g p

theorem twoLine_stratum_le (D : Finset (Direction F)) (a : MergedPairs F)
    (L K : Line F) (hLK : L ≠ K)
    (havoid : ∀ d ∈ D, ∀ b, constituent a d b ≠ L)
    (m j : ℕ) (hD : D.card ≤ m) (hj : j < 5) :
    tupleIncidenceSum D a j (hitsTwoLines L K) ≤ (8192 * (m+1)^4 : ℝ) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hDreal : (D.card : ℝ) ≤ m := by exact_mod_cast hD
  have hbase : (1 : ℝ) ≤ (m : ℝ)+1 := by linarith
  have hpow : (1 : ℝ) ≤ ((m : ℝ)+1)^4 := one_le_pow₀ hbase
  have hmpow : (m : ℝ) ≤ ((m : ℝ)+1)^4 := by
    have h := pow_le_pow_right₀ hbase (show 1 ≤ 4 by omega)
    simp only [pow_one] at h
    linarith
  interval_cases j
  · rw [← rootIncidenceSum_eq_tupleIncidenceSum]
    exact (root_two_lines_sum_zero_le D a L K hLK).trans (by linarith)
  · rw [← rootIncidenceSum_eq_tupleIncidenceSum]
    exact (root_two_lines_sum_one_le D a L K havoid).trans (by nlinarith)
  · exact (tupleIncidenceSum_le_success D a 2 _).trans
      (sum_targets_success_two_three_le D a m 2 hD (Or.inl rfl))
  · exact (tupleIncidenceSum_le_success D a 3 _).trans
      (sum_targets_success_two_three_le D a m 3 hD (Or.inr rfl))
  · apply (tupleIncidenceSum_le_success D a 4 _).trans
    apply (sum_targets_success_four_le D a).trans
    have hp : (D.card : ℝ)^4 ≤ ((m : ℝ)+1)^4 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 4
    nlinarith

theorem twoLine_model_fixed_count_le (D : Finset (Direction F))
    (a : MergedPairs F) (L K : Line F) (hLK : L ≠ K)
    (havoid : ∀ d ∈ D, ∀ b, constituent a d b ≠ L)
    (m : ℕ) (hD : D.card ≤ m) :
    (allModel (twoLineTest L K)).fixedExpectation D a
      (allModel (twoLineTest L K)).count ≤ (40960 * (m+1)^4 : ℝ) := by
  rw [show twoLineTest L K = (fun _ g p => hitsTwoLines L K g p) from rfl,
    allModel_fixed_count_eq_sum_strata]
  calc
    _ ≤ ∑ _j ∈ Finset.range 5, (8192 * (m+1)^4 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact twoLine_stratum_le D a L K hLK havoid m j hD (Finset.mem_range.mp hj)
    _ = _ := by simp; ring

def twoLineInitial (L K : Line F) : Finset (Direction F) := {L.1,K.1}

def twoLineAllowed (L K : Line F) : Set (MergedPairs F) :=
  {M | L ≠ K ∧ (∀ b, M L.1 b ≠ L.2) ∧ (∀ b, M K.1 b ≠ K.2)}

omit [Field F] [Fintype F] in
theorem twoLineInitial_card_le (L K : Line F) : (twoLineInitial L K).card ≤ 2 := by
  calc
    _ ≤ ({K.1} : Finset (Direction F)).card + 1 := Finset.card_insert_le _ _
    _ = 2 := by simp

omit [Field F] [Fintype F] in
theorem twoLineAllowed_depends (L K : Line F) (x y : MergedPairs F)
    (h : ∀ d ∈ twoLineInitial L K, x d = y d) :
    x ∈ twoLineAllowed L K ↔ y ∈ twoLineAllowed L K := by
  have hL := h L.1 (by simp [twoLineInitial])
  have hK := h K.1 (by simp [twoLineInitial])
  simp only [twoLineAllowed, Set.mem_ofPred_eq, hL, hK]

abbrev twoLineModel (L K : Line F) : PatternModel.{u} :=
  (allModel (twoLineTest L K)).gateInitialEvent (twoLineInitial L K)
    (twoLineAllowed L K) (Set.toFinite _).measurableSet (twoLineAllowed_depends L K)

theorem twoLineModel_measure (L K : Line F) :
    (twoLineModel L K).measure = (offsetLaw F).toMeasure := allModel_measure (twoLineTest L K)

theorem twoLineModel_count (L K : Line F) (M : MergedPairs F) :
    (twoLineModel L K).count M =
      if M ∈ twoLineAllowed L K then (allModel (twoLineTest L K)).count M else 0 :=
  (allModel (twoLineTest L K)).gateInitialEvent_count (twoLineInitial L K)
    (twoLineAllowed L K) (Set.toFinite _).measurableSet (twoLineAllowed_depends L K) M

theorem twoLineModel_support_card (L K : Line F) (r : (twoLineModel L K).Label) :
    ((twoLineModel L K).support r).card ≤ 6 := by
  have h := (allModel (twoLineTest L K)).gateInitialEvent_support_card_le
    (twoLineInitial L K) (twoLineAllowed L K) (Set.toFinite _).measurableSet
    (twoLineAllowed_depends L K) 4 (fun a => (allModel_support_card _ a).le) r
  exact h.trans (by have := twoLineInitial_card_le L K; omega)

theorem twoLineModel_fixed_initial_count_le (L K : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (twoLineModel L K).fixedExpectation (twoLineInitial L K ∪ D) a
      (twoLineModel L K).count ≤ (40960 * (m+3)^4 : ℝ) := by
  change ((allModel (twoLineTest L K)).gateInitialEvent _ _ _ _).fixedExpectation
    _ _ _ ≤ _
  rw [PatternModel.gateInitialEvent_fixed_count]
  split_ifs with ha
  · have havoid : ∀ d ∈ twoLineInitial L K ∪ D, ∀ b, constituent a d b ≠ L := by
      intro d _ b heq
      have hd : d = L.1 := congrArg Prod.fst heq
      have hb : a d b = L.2 := congrArg Prod.snd heq
      rw [hd] at hb
      exact ha.2.1 b hb
    have hc : (twoLineInitial L K ∪ D).card ≤ m+2 :=
      (Finset.card_union_le _ _).trans (by have := twoLineInitial_card_le L K; omega)
    have h := twoLine_model_fixed_count_le (twoLineInitial L K ∪ D) a L K ha.1
      havoid (m+2) hc
    convert h using 1
    push_cast
    ring
  · positivity

theorem twoLineModel_fixed_count_le (L K : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (twoLineModel L K).fixedExpectation D a (twoLineModel L K).count ≤
      (40960 * (m+3)^4 : ℝ) := by
  let P := twoLineModel L K
  have hbound (y : P.Sample) : P.fixedExpectation (D ∪ twoLineInitial L K) y
      P.count ≤ (40960 * (m+3)^4 : ℝ) := by
    exact (congrArg (fun E : Finset (Direction F) =>
      (twoLineModel L K).fixedExpectation E y (twoLineModel L K).count ≤
        (40960 * (m+3)^4 : ℝ)) (Finset.union_comm (twoLineInitial L K) D)).mp
          (twoLineModel_fixed_initial_count_le L K D y m hD)
  have h := P.fixedExpectation_mul_le_of_fixedBounds D (twoLineInitial L K) a
    (fun _ => 1) P.count (40960 * (m+3)^4 : ℝ) 1 (Fintype.card P.Label)
    (by positivity) measurable_const P.measurable_count
    (fun _ => zero_le_one) (fun M => (PatternTails.count_mem_Icc P M).1)
    (fun _ => le_rfl) (fun M => (PatternTails.count_mem_Icc P M).2)
    (by intros; rfl) hbound
  have hconst : P.fixedExpectation D a (fun _ => (1 : ℝ)) = 1 := by
    simp [PatternModel.fixedExpectation, PatternModel.measure]
  rw [hconst, mul_one] at h
  simpa only [one_mul] using h

theorem twoLineModel_fixed_moment_le (L K : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m s : ℕ) (hD : D.card ≤ m) :
    (twoLineModel L K).fixedExpectation D a (fun M => (twoLineModel L K).count M ^ s) ≤
      (40960 * (((m + (s-1)*6 : ℕ) : ℝ)+3)^4)^s := by
  apply (twoLineModel L K).fixed_moment_le_pow D a 6 s _ (by positivity)
    (twoLineModel_support_card L K)
  intro E hE y
  exact twoLineModel_fixed_count_le L K (D ∪ E) y (m+(s-1)*6)
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hD hE))

theorem twoLineModel_moment_le (L K : Line F) (s : ℕ) :
    (∫ M, (twoLineModel L K).count M ^ s ∂(offsetLaw F).toMeasure) ≤
      (40960 * ((((s-1)*6 : ℕ) : ℝ)+3)^4)^s := by
  have h := twoLineModel_fixed_moment_le L K ∅ (fun _ _ => 0) 0 s (by simp)
  simp only [PatternModel.fixedExpectation, zero_add] at h
  rw [twoLineModel_measure] at h
  exact h

end
end Balanced.CandidateIncidenceSums

end OAI
