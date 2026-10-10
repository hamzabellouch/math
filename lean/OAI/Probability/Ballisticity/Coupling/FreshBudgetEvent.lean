import Mathlib
import OAI.Probability.Ballisticity.Coupling.SeedRadius
import OAI.Probability.Ballisticity.Coupling.StageSeedProfile

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma fresh_random_budget_mass_lt {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (a G r s : ℝ) (H : ℕ)
    (π : Environment d → BudgetProfile (k:=k) e f a G)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (A : Set (Environment d)) (hA : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] A)
    (c : ℝ≥0∞)
    (hbound : ∀ η ∈ A, environmentLaw ν {ω | relativeBudgetMass e f H r (π η).val ω<s}≤c) :
    environmentLaw ν (A∩{ω | relativeBudgetMass e f H r (π ω).val ω<s})≤c*environmentLaw ν A := by
  let S := BelowHeight (realPosition (step e)) a
  let T : Set (Lattice d) := {y | a≤dot (realPosition y) (realPosition (step e))}
  let B : Set (Environment d×Environment d) := {p | relativeBudgetMass e f H r (π p.1).val p.2<s}
  have hQ := budgetProfileMass_joint_rows (k:=k) e f a G H r T (fun x hx j y hy => by
    change a≤dot (realPosition y) (realPosition (step e))
    simpa only [hx j] using hy.1)
  have hB : @MeasurableSet (Environment d×Environment d) (MeasurableSpace.prod (rowSigma S) (rowSigma T)) B :=
    measurableSet_lt (hQ.comp ((hπ.comp measurable_fst).prodMk measurable_snd)) measurable_const
  have hV : @Measurable (Environment d) (Environment d) inferInstance (rowSigma T) id :=
    measurable_id.mono le_rfl (rowSigma_le T)
  have hb (η : Environment d) (hη : η∈A) :
      (@Measure.map (Environment d) (Environment d) inferInstance (rowSigma T) id (environmentLaw ν))
        {ω | (η,ω)∈B}≤c := by
    rw [show {ω | (η,ω)∈B}=Prod.mk η ⁻¹' B from rfl,
      Measure.map_apply hV (hB.preimage measurable_prodMk_left)]
    exact hbound η hη
  apply @fresh_rows_random_test_bound d (Environment d) (Environment d) (rowSigma S) (rowSigma T)
    ν _ S T _ id id measurable_id measurable_id A hA B hB c hb
  exact Set.disjoint_left.mpr fun x hx hy =>
    (not_lt.mpr (show a≤dot (realPosition x) (realPosition (step e)) from hy))
      (show dot (realPosition x) (realPosition (step e))<a from hx)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma fresh_layer_diagonal_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e : Direction d) (a : ℝ) (A : Set (Environment d))
    (hA : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] A)
    (B : Set (Environment d×Environment d))
    (hB : @MeasurableSet (Environment d×Environment d)
      (MeasurableSpace.prod (rowSigma (BelowHeight (realPosition (step e)) a))
        (rowSigma {y | a≤dot (realPosition y) (realPosition (step e))})) B)
    (c : ℝ≥0∞) (hbound : ∀ η∈A, environmentLaw ν {ω | (η,ω)∈B}≤c) :
    environmentLaw ν (A∩{ω | (ω,ω)∈B})≤c*environmentLaw ν A := by
  let S := BelowHeight (realPosition (step e)) a
  let T : Set (Lattice d) := {y | a≤dot (realPosition y) (realPosition (step e))}
  have hV : @Measurable (Environment d) (Environment d) inferInstance (rowSigma T) id :=
    measurable_id.mono le_rfl (rowSigma_le T)
  have hb (η : Environment d) (hη : η∈A) :
      (@Measure.map (Environment d) (Environment d) inferInstance (rowSigma T) id (environmentLaw ν))
        {ω | (η,ω)∈B}≤c := by
    rw [show {ω | (η,ω)∈B}=Prod.mk η ⁻¹' B from rfl,
      Measure.map_apply hV (hB.preimage measurable_prodMk_left)]
    exact hbound η hη
  apply @fresh_rows_random_test_bound d (Environment d) (Environment d) (rowSigma S) (rowSigma T)
    ν _ S T _ id id measurable_id measurable_id A hA B hB c hb
  exact Set.disjoint_left.mpr fun x hx hy =>
    (not_lt.mpr (show a≤dot (realPosition x) (realPosition (step e)) from hy))
      (show dot (realPosition x) (realPosition (step e))<a from hx)

lemma fresh_layer_profile_event_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e : Direction d) (a : ℝ) {D : Type*} [MeasurableSpace D]
    (b : D → Environment d → ℝ≥0∞)
    (hb : @Measurable (D×Environment d) ℝ≥0∞
      (MeasurableSpace.prod inferInstance
        (rowSigma {y | a≤dot (realPosition y) (realPosition (step e))})) _
      (fun p => b p.1 p.2))
    (π : Environment d → D)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (A : Set (Environment d)) (hA : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] A)
    (g c : ℝ≥0∞) (hbound : ∀ η∈A, environmentLaw ν {ω | b (π η) ω<g}≤c) :
    environmentLaw ν (A∩{ω | b (π ω) ω<g})≤c*environmentLaw ν A := by
  apply fresh_layer_diagonal_bound ν e a A hA {p | b (π p.1) p.2<g} _ c hbound
  exact measurableSet_lt (hb.comp ((hπ.comp measurable_fst).prodMk measurable_snd)) measurable_const

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma seedSeparatedMass_joint_upper {d k : ℕ} (e f : Direction d) (a G : ℝ) (H : ℕ) :
    @Measurable (LayerTupleProfile (k:=k) e a×Environment d) ℝ≥0∞
      (@Prod.instMeasurableSpace _ _ inferInstance
        (rowSigma {y | a≤dot (realPosition y) (realPosition (step e))})) _
      (fun p => seedSeparatedRaw e f H G p.1.val p.2 Set.univ) := by
  apply (Measure.measurable_coe MeasurableSet.univ).comp
  apply seedSeparatedRaw_joint_rows
  intro x hx j y hy
  change a≤dot (realPosition y) (realPosition (step e))
  simpa only [hx j] using hy.1

lemma fresh_random_seed_failure {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (a G : ℝ) (H : ℕ) (g : ℝ≥0∞)
    (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (A : Set (Environment d)) (hA : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] A)
    (c : ℝ≥0∞)
    (hbound : ∀ η∈A, environmentLaw ν {ω | seedSeparatedRaw e f H G (π η).val ω Set.univ<g}≤c) :
    environmentLaw ν (A∩{ω | seedSeparatedRaw e f H G (π ω).val ω Set.univ<g})≤c*environmentLaw ν A := by
  exact fresh_layer_profile_event_bound ν e a (D:=LayerTupleProfile (k:=k) e a)
    (fun (p : LayerTupleProfile (k:=k) e a) ω => seedSeparatedRaw e f H G p.val ω Set.univ)
    (seedSeparatedMass_joint_upper (k:=k) e f a G H) π hπ A hA g c hbound

lemma seedSeparatedRaw_measurable {d k : ℕ} (e f : Direction d) (H : ℕ) (G a : ℝ)
    (π : LayerTupleProfile (k:=k) e a) : Measurable (fun ω => seedSeparatedRaw e f H G π.val ω) := by
  have hh := seedSeparatedRaw_joint_rows (k:=k) e f H G a Set.univ (fun _ _ _ => Set.subset_univ _)
  exact (hh.comp (measurable_const.prodMk measurable_id)).mono (rowSigma_le _) le_rfl

theorem adapted_separated_seeds {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1≠f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (k : ℕ) (hk : 2≤k) (p : ℝ) (hp : 0<p) :
    ∃ C c₀ g₀ : ℝ, 0<C ∧ 0<c₀ ∧ 0<g₀ ∧ ∃ H₀ : ℕ, ∀ H≥H₀,
      ∀ (a : ℝ) (π : Environment d → LayerTupleProfile (k:=k) e a),
        @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π →
      ∀ A : Set (Environment d), MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] A →
        environmentLaw ν (A∩{ω | seedSeparatedRaw e f H
          (c₀*fluctuationRadius (independentConditionedPairLaw ν (realPosition (step e)))
            (commonIncrementProcess (realPosition (step e)) f 0) ((H:ℝ)/C))
          (π ω).val ω Set.univ<ENNReal.ofReal g₀})≤ENNReal.ofReal p*environmentLaw ν A := by
  obtain ⟨C,c₀,g₀,hC,hc,hg,H₀,hh⟩ := separated_seeds ν hue e f hef htrans k hk p hp
  refine ⟨C,c₀,g₀,hC,hc,hg,H₀,fun H hH a π hπ A hA => ?_⟩
  apply fresh_random_seed_failure ν e f a _ H _ π hπ A hA (ENNReal.ofReal p)
  intro η _
  have hs := hh H hH ⟨(π η).val,(π η).property.1⟩
  let G := c₀*fluctuationRadius (independentConditionedPairLaw ν (realPosition (step e)))
    (commonIncrementProcess (realPosition (step e)) f 0) ((H:ℝ)/C)
  have hm : MeasurableSet {ω | seedSeparatedRaw e f H G (π η).val ω Set.univ<ENNReal.ofReal g₀} :=
    measurableSet_lt ((Measure.measurable_coe MeasurableSet.univ).comp
      (seedSeparatedRaw_measurable e f H G a (π η))) measurable_const
  have he : {ω | ENNReal.ofReal g₀≤rawTupleMixture (realPosition (step e)) H (π η).val ω {v | TupleSeparated f G v}} =
      {ω | seedSeparatedRaw e f H G (π η).val ω Set.univ<ENNReal.ofReal g₀}ᶜ := by
    ext ω; simp only [Set.mem_ofPred_eq,Set.mem_compl_iff,not_lt,seedSeparatedRaw_univ]
  change 1-p < (environmentLaw ν).real {ω | ENNReal.ofReal g₀≤rawTupleMixture (realPosition (step e)) H (π η).val ω {v | TupleSeparated f G v}} at hs
  rw [he,measureReal_compl hm,probReal_univ] at hs
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  apply ENNReal.ofReal_le_ofReal
  linarith

end DirectionalTransience

end

end OAI
