import OAI.Combinatorics.BalancedRyser.Candidates.CandidateExposure
import OAI.Combinatorics.BalancedRyser.Probability.ExactMultiplicity
import OAI.Combinatorics.BalancedRyser.Probability.FreshWitnessProbability

namespace OAI

namespace Balanced.CandidateExposure

noncomputable section
open scoped Classical BigOperators
open ConditionalRestriction TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem exposedLaw_fresh_direction_array (D : Finset (Direction F)) (a : MergedPairs F) :
    (exposedLaw D a).map (fun M (d : {d : Direction F // d ∉ D}) => M d.1) =
      PMF.uniformOfFintype ({d : Direction F // d ∉ D} → Bool → F) := by
  simpa only [exposedLaw, FreshWitnessProbability.exposedLaw,
    Function.Embedding.coeFn_mk] using
    FreshWitnessProbability.exposedLaw_map_fresh D a
      (⟨Subtype.val, Subtype.val_injective⟩ : {d : Direction F // d ∉ D} ↪ Direction F)
      (fun d => d.2)

def freshMultiplicity (D : Finset (Direction F)) (M : MergedPairs F) (p : Point F) : ℕ :=
  (Finset.univ.filter (fun ds : {d : Direction F // d ∉ D} × Bool =>
    OnLine p (constituent M ds.1.1 ds.2))).card

def exposedMultiplicity (D : Finset (Direction F)) (a : MergedPairs F) (p : Point F) : ℕ :=
  (Finset.univ.filter (fun ds : {d : Direction F // d ∈ D} × Bool =>
    OnLine p (constituent a ds.1.1 ds.2))).card

theorem sampledMultiplicity_eq_exposed_add_fresh (D : Finset (Direction F))
    (M : MergedPairs F) (p : Point F) :
    sampledMultiplicity M p = exposedMultiplicity D M p + freshMultiplicity D M p := by
  simp only [sampledMultiplicity, exposedMultiplicity, freshMultiplicity,
    Finset.card_filter, Fintype.sum_prod_type]
  convert (Fintype.sum_subtype_add_sum_subtype (fun d => d ∈ D)
    (fun d => ∑ b : Bool, if OnLine p (constituent M d b) then 1 else 0)).symm using 1
  congr 1
  apply Finset.sum_congr
  · ext d
    simp
  · intro d hd
    rfl

omit [Fintype F] in

theorem exposedMultiplicity_le (D : Finset (Direction F)) (a : MergedPairs F)
    (p : Point F) : exposedMultiplicity D a p ≤ 2 * D.card := by
  have h := Finset.card_filter_le (s :=
    (Finset.univ : Finset ({d : Direction F // d ∈ D} × Bool)))
    (p := fun ds => OnLine p (constituent a ds.1.1 ds.2))
  simpa [exposedMultiplicity, Fintype.card_prod, Nat.mul_comm] using h

theorem sampledMultiplicity_eq_fixed_add_fresh (D : Finset (Direction F))
    (a M : MergedPairs F) (p : Point F) (hM : M ∈ (exposedLaw D a).support) :
    sampledMultiplicity M p = exposedMultiplicity D a p + freshMultiplicity D M p := by
  have hfixed : ∀ d, d ∈ D → M d = a d :=
    (PMF.mem_support_filter_iff (PartialAlignment.canonical_exposure_supported D a)).mp hM |>.1
  rw [sampledMultiplicity_eq_exposed_add_fresh D M p]
  congr 1
  unfold exposedMultiplicity
  have hpred :
      (fun directionSide : {d : Direction F // d ∈ D} × Bool =>
        OnLine p (constituent M directionSide.1.1 directionSide.2)) =
      (fun directionSide : {d : Direction F // d ∈ D} × Bool =>
        OnLine p (constituent a directionSide.1.1 directionSide.2)) := by
    funext directionSide
    simp only [constituent, hfixed directionSide.1.1 directionSide.1.2]
  simp only [hpred]

theorem freshMultiplicity_atom (D : Finset (Direction F)) (a : MergedPairs F)
    (p : Point F) (m : ℕ) :
    conditionalProbability D a {M | freshMultiplicity D M p = m} =
      ((2 * (Fintype.card F + 1 - D.card)).choose m : ℝ) *
        (1 / (Fintype.card F : ℝ)) ^ m *
        (1 - 1 / (Fintype.card F : ℝ)) ^
          (2 * (Fintype.card F + 1 - D.card) - m) := by
  let fresh := {d : Direction F // d ∉ D}
  let E : Set (fresh → Bool → F) :=
    {o | (Finset.univ.filter (fun ds : fresh × Bool =>
      lineEval ds.1.1 p = o ds.1 ds.2)).card = m}
  have hlaw := congrArg (fun law => (law.toOuterMeasure E).toReal)
    (exposedLaw_fresh_direction_array D a)
  rw [PMF.toOuterMeasure_map_apply] at hlaw
  change conditionalProbability D a {M | freshMultiplicity D M p = m} =
    ((PMF.uniformOfFintype (fresh → Bool → F)).toOuterMeasure E).toReal at hlaw
  rw [hlaw]
  let e := Equiv.curry fresh Bool F
  rw [← uniform_toOuterMeasure_equiv e E]
  have h := uniform_exact_coordinate_matches_binomial
    (fun ds : fresh × Bool => lineEval ds.1.1 p) m
  have hcard : Fintype.card fresh = Fintype.card F + 1 - D.card := by
    dsimp [fresh]
    rw [Fintype.card_subtype_compl]
    simp [Direction, Fintype.card_option, Fintype.card_coe]
  simpa [e, E, Equiv.curry, Function.curry, eq_comm, Fintype.card_prod,
    hcard, Nat.mul_comm] using h

theorem freshMultiplicity_law (D : Finset (Direction F)) (a : MergedPairs F)
    (p : Point F) :
    ((exposedLaw D a).map (fun M => freshMultiplicity D M p)).toMeasure =
      ProbabilityTheory.binomial (2 * (Fintype.card F + 1 - D.card))
        (multiplicityParameter F) := by
  apply MeasureTheory.Measure.ext_of_measureReal_singleton
  intro m
  rw [ProbabilityTheory.binomial_real_singleton]
  change (((exposedLaw D a).map (fun M => freshMultiplicity D M p)).toMeasure {m}).toReal = _
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (measurableSet_singleton _),
    PMF.toOuterMeasure_map_apply]
  exact freshMultiplicity_atom D a p m

theorem sampledMultiplicity_conditional_atom (D : Finset (Direction F)) (a : MergedPairs F)
    (p : Point F) (m : ℕ) :
    conditionalProbability D a
        {M | sampledMultiplicity M p = exposedMultiplicity D a p + m} =
      ((2 * (Fintype.card F + 1 - D.card)).choose m : ℝ) *
        (1 / (Fintype.card F : ℝ)) ^ m *
        (1 - 1 / (Fintype.card F : ℝ)) ^
          (2 * (Fintype.card F + 1 - D.card) - m) := by
  rw [← freshMultiplicity_atom D a p m]
  have hsets : {M | sampledMultiplicity M p = exposedMultiplicity D a p + m} ∩
      (exposedLaw D a).support =
      {M | freshMultiplicity D M p = m} ∩ (exposedLaw D a).support := by
    ext M
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨he, hM⟩
      rw [sampledMultiplicity_eq_fixed_add_fresh D a M p hM] at he
      exact ⟨Nat.add_left_cancel he, hM⟩
    · rintro ⟨he, hM⟩
      exact ⟨by rw [sampledMultiplicity_eq_fixed_add_fresh D a M p hM, he], hM⟩
  unfold conditionalProbability
  rw [← PMF.toOuterMeasure_apply_inter_support (exposedLaw D a)
    {M | sampledMultiplicity M p = exposedMultiplicity D a p + m},
    hsets, PMF.toOuterMeasure_apply_inter_support]

theorem sampledMultiplicity_conditional_law (D : Finset (Direction F))
    (a : MergedPairs F) (p : Point F) :
    ((exposedLaw D a).map (fun M => sampledMultiplicity M p)).toMeasure =
      (ProbabilityTheory.binomial (2 * (Fintype.card F + 1 - D.card))
        (multiplicityParameter F)).map (fun m => exposedMultiplicity D a p + m) := by
  have hmap : (exposedLaw D a).map (fun M => sampledMultiplicity M p) =
      (exposedLaw D a).map (fun M => exposedMultiplicity D a p + freshMultiplicity D M p) := by
    ext n
    simp only [PMF.map_apply]
    apply tsum_congr
    intro M
    by_cases hM : M ∈ (exposedLaw D a).support
    · rw [sampledMultiplicity_eq_fixed_add_fresh D a M p hM]
    · have hz : exposedLaw D a M = 0 := (PMF.apply_eq_zero_iff _ _).mpr hM
      simp [hz]
  rw [hmap, ← freshMultiplicity_law D a p]
  rw [PMF.toMeasure_map (fun m => exposedMultiplicity D a p + m)
    ((exposedLaw D a).map (fun M => freshMultiplicity D M p)) (by fun_prop), PMF.map_comp]
  rfl

end
end Balanced.CandidateExposure

end OAI
