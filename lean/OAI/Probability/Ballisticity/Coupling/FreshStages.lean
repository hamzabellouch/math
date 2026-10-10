import Mathlib
import OAI.Probability.Ballisticity.Estimates.CellBadEvent

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma stageBadEvent_joint_rows {d k : ℕ} (e f : Direction d) (a G Gminus Gplus : ℝ)
    (H : ℕ) (p : ℝ≥0∞) :
    @MeasurableSet (BudgetProfile (k:=k) e f a G × Environment d)
      (MeasurableSpace.prod inferInstance
        (rowSigma {y | a ≤ dot (realPosition y) (realPosition (step e))}))
      {z | z.2 ∈ stageBadEvent e f H Gminus Gplus z.1.val p} := by
  let : MeasurableSpace (Environment d) := rowSigma {y | a ≤ dot (realPosition y) (realPosition (step e))}
  have hm (h : ℕ) : Measurable (fun z : BudgetProfile (k:=k) e f a G × Environment d =>
      rawTupleMixture (realPosition (step e)) h z.1.val z.2) := by
    apply (rawTupleMixture_joint_rows (realPosition (step e)) h
      (TupleAtHeight (k:=k) (realPosition (step e)) a) _ (fun x hx j y hy => ?_)).comp
      (((BudgetProfile.measurable_toSupported e f a G).comp measurable_fst).prodMk measurable_snd)
    simpa only [hx j,Set.mem_ofPred_eq] using hy.1
  have he (h : ℕ) (g : ℝ) : Measurable (fun z : BudgetProfile (k:=k) e f a G × Environment d =>
      rawTupleMixture (realPosition (step e)) h z.1.val z.2 {y | TupleSeparated f g y}) :=
    (Measure.measurable_coe (Set.to_countable _).measurableSet).comp (hm h)
  have hE : MeasurableSet {z : BudgetProfile (k:=k) e f a G × Environment d |
      ∃ h : ℕ, 1 ≤ h ∧ h ≤ H ∧ rawTupleMixture (realPosition (step e)) h z.1.val z.2 {y | TupleSeparated f Gminus y} < p} := by
    rw [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro h
    exact (MeasurableSet.const (1 ≤ h)).inter ((MeasurableSet.const (h ≤ H)).inter (measurableSet_lt (he h Gminus) measurable_const))
  have hF : MeasurableSet {z : BudgetProfile (k:=k) e f a G × Environment d |
      rawTupleMixture (realPosition (step e)) H z.1.val z.2 {y | TupleSeparated f Gplus y} < p} :=
    measurableSet_lt (he H Gplus) measurable_const
  exact hE.union hF

lemma fresh_layer_test_bound {d : ℕ} {D : Type*} [MeasurableSpace D]
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (e : Direction d) (a : ℝ)
    (bad : D → Set (Environment d))
    (hbad : @MeasurableSet (D × Environment d)
      (MeasurableSpace.prod inferInstance
        (rowSigma {y | a ≤ dot (realPosition y) (realPosition (step e))})) {z | z.2 ∈ bad z.1})
    (π : Environment d → D)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (A : Set (Environment d)) (hA : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] A)
    (δ : ℝ≥0∞) (hb : ∀ η∈A, environmentLaw ν (bad (π η)) ≤ δ) :
    environmentLaw ν (A ∩ {ω | ω ∈ bad (π ω)}) ≤ δ*environmentLaw ν A := by
  let S := rowSigma (BelowHeight (realPosition (step e)) a)
  let T := rowSigma {y | a ≤ dot (realPosition y) (realPosition (step e))}
  have hp : @Measurable (Environment d×Environment d) D
      (MeasurableSpace.prod S T) _ (fun z => π z.1) := hπ.comp measurable_fst
  have hq : @Measurable (Environment d×Environment d) (Environment d)
      (MeasurableSpace.prod S T) T Prod.snd := measurable_snd
  have hpair : @Measurable (Environment d×Environment d) (D×Environment d)
      (MeasurableSpace.prod S T) (MeasurableSpace.prod inferInstance T)
      (fun z => (π z.1,z.2)) := hp.prodMk hq
  have hm : @MeasurableSet (Environment d×Environment d) (MeasurableSpace.prod S T)
      {z | z.2 ∈ bad (π z.1)} := hbad.preimage hpair
  exact fresh_layer_diagonal_bound ν e a A hA {z | z.2 ∈ bad (π z.1)} hm δ hb

lemma fresh_stage_bound {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (a G Gminus Gplus : ℝ) (H : ℕ) (p δ : ℝ≥0∞)
    (π : Environment d → BudgetProfile (k:=k) e f a G)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (hbound : ∀ η, environmentLaw ν (stageBadEvent e f H Gminus Gplus (π η).val p) ≤ δ)
    (A : Set (Environment d)) (hA : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] A) :
    environmentLaw ν (A ∩ {ω | ω ∈ stageBadEvent e f H Gminus Gplus (π ω).val p}) ≤
      δ*environmentLaw ν A :=
  fresh_layer_test_bound ν e a (fun ρ : BudgetProfile (k:=k) e f a G => stageBadEvent e f H Gminus Gplus ρ.val p)
    (stageBadEvent_joint_rows e f a G Gminus Gplus H p) π hπ A hA δ (fun η _ => hbound η)

lemma stopped_stage_failure_subset {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H R : ℕ) (hH : 1 ≤ H) (hR : 1 ≤ R) :
    {ω | stageTestMass e f a Gminus Gplus π H (stageStop e f a Gminus Gplus B π H R ω) ω <
      ENNReal.ofReal (Real.exp (-B))} ⊆
    {ω | ω ∈ stageBadEvent e f H Gminus Gplus (π ω).val (ENNReal.ofReal (Real.exp (-B)))} := by
  intro ω hω
  have hle : stageStop e f a Gminus Gplus B π H R ω ≤ min H R := hittingBtwn_le ω
  have hpos : 1 ≤ stageStop e f a Gminus Gplus B π H R ω :=
    le_hittingBtwn (le_min hH hR) _
  change stageTestMass e f a Gminus Gplus π H (stageStop e f a Gminus Gplus B π H R ω) ω < ENNReal.ofReal (Real.exp (-B)) at hω
  simp only [stageTestMass,ite_eq_right (by omega : stageStop e f a Gminus Gplus B π H R ω ≠ 0)] at hω
  by_cases he : stageStop e f a Gminus Gplus B π H R ω=H
  · simp only [ite_eq_left he,min_lt_iff] at hω
    exact hω.elim (fun hh => Or.inl ⟨_,hpos,hle.trans (min_le_left _ _),hh⟩)
      (fun hh => Or.inr (by simpa only [he,stageEndpointMass] using hh))
  · simp only [ite_eq_right he] at hω
    exact Or.inl ⟨_,hpos,hle.trans (min_le_left _ _),hω⟩

end DirectionalTransience

end

end OAI
