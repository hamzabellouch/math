import OAI.Analysis.CircleDomains.Modulus.ConfigurationNorm
import Mathlib.Topology.Maps.Proper.Basic

namespace OAI

/-! Finite visit witnesses have Borel incidence. The resulting extended count
records visits at distinct parameter times, including both endpoints. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

def separatedTimeSet (n : ℕ) (r : ℝ) : Set (Fin n → PathTime) :=
  {t | ∀ i j, i ≠ j → r ≤ dist (t i) (t j)}

abbrev SeparatedTimes (n : ℕ) (r : ℝ) := separatedTimeSet n r

theorem isClosed_separatedTimeSet (n : ℕ) (r : ℝ) : IsClosed (separatedTimeSet n r) := by
  simp only [separatedTimeSet, ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_iInter fun _ => isClosed_le continuous_const (by fun_prop)

instance (n : ℕ) (r : ℝ) : CompactSpace (SeparatedTimes n r) :=
  isCompact_iff_compactSpace.mp (isClosed_separatedTimeSet n r).isCompact

def separatedVisitSet {X : Type*} [MetricSpace X] (n : ℕ) (r : ℝ) :
    Set (C(PathTime, X) × X) :=
  {q | ∃ t : SeparatedTimes n r, ∀ i, q.1 (t.val i) = q.2}

theorem isClosed_separatedVisitSet {X : Type*} [MetricSpace X] (n : ℕ) (r : ℝ) :
    IsClosed (separatedVisitSet (X := X) n r) := by
  let H : Set ((C(PathTime, X) × X) × SeparatedTimes n r) :=
    {q | ∀ i, q.1.1 (q.2.val i) = q.1.2}
  have hH : IsClosed H := by
    simp only [H, ofPred_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_eq
    · exact continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))
    · exact continuous_snd.comp continuous_fst
  have heq : Prod.fst '' H = separatedVisitSet (X := X) n r := by
    ext q
    constructor
    · rintro ⟨⟨p, t⟩, ht, rfl⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨(q, t), ht, rfl⟩
  rw [← heq]
  exact isClosedMap_fst_of_compactSpace H hH

def visitAtLeastSet {X : Type*} [MetricSpace X] (n : ℕ) :
    Set (C(PathTime, X) × X) :=
  {q | ∃ t : Fin n → PathTime, Injective t ∧ ∀ i, q.1 (t i) = q.2}

theorem visitAtLeastSet_eq_iUnion {X : Type*} [MetricSpace X] (n : ℕ) :
    visitAtLeastSet (X := X) n =
      ⋃ m : ℕ, separatedVisitSet n (1 / ((m : ℝ) + 1)) := by
  ext q
  constructor
  · rintro ⟨t, ht, heq⟩
    obtain ⟨m, hm⟩ := exists_reciprocal_separation t ht
    exact mem_iUnion.mpr ⟨m, ⟨⟨t, hm⟩, heq⟩⟩
  · intro h
    obtain ⟨m, t, ht⟩ := mem_iUnion.mp h
    refine ⟨t.val, ?_, ht⟩
    intro i j hij
    by_contra hne
    have hd := t.property i j hne
    rw [hij, dist_self] at hd
    have hp : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurableSet_visitAtLeastSet (n : ℕ) :
    MeasurableSet (visitAtLeastSet (X := X) n) := by
  rw [visitAtLeastSet_eq_iUnion]
  exact MeasurableSet.iUnion fun m => (isClosed_separatedVisitSet n (1 / ((m : ℝ) + 1))).measurableSet

/-- Extended number of distinct visit times, defined by finite witnesses. -/
def visitCount (γ : C(PathTime, X)) (x : X) : ℝ≥0∞ := by
  classical
  exact ⨆ n : ℕ, if (γ, x) ∈ visitAtLeastSet n then (n : ℝ≥0∞) else 0

theorem measurable_visitCount : Measurable (fun q : C(PathTime, X) × X => visitCount q.1 q.2) := by
  classical
  unfold visitCount
  apply Measurable.iSup
  intro n
  exact measurable_const.piecewise (measurableSet_visitAtLeastSet (X := X) n) measurable_const

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem visitCount_ge_nat {γ : C(PathTime, X)} {x : X} {n : ℕ}
    (h : (γ, x) ∈ visitAtLeastSet n) : (n : ℝ≥0∞) ≤ visitCount γ x := by
  classical
  calc
    (n : ℝ≥0∞) = (if (γ, x) ∈ visitAtLeastSet n then (n : ℝ≥0∞) else 0) :=
      (ite_eq_left h).symm
    _ ≤ visitCount γ x := le_iSup (fun k : ℕ =>
      if (γ, x) ∈ visitAtLeastSet k then (k : ℝ≥0∞) else 0) n

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem visitCount_eq_zero_of_not_hit {γ : C(PathTime, X)} {x : X}
    (h : ¬∃ t, γ t = x) : visitCount γ x = 0 := by
  classical
  apply le_antisymm ?_ bot_le
  apply iSup_le
  intro n
  split
  · rename_i hn
    rcases n with _ | n
    · simp
    · obtain ⟨t, _, ht⟩ := hn
      exact (h ⟨t 0, ht 0⟩).elim
  · exact le_rfl


omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem one_le_visitCount_of_hit {γ : C(PathTime, X)} {x : X}
    (h : ∃ t, γ t = x) : 1 ≤ visitCount γ x := by
  obtain ⟨t, ht⟩ := h
  have h1 := visitCount_ge_nat (γ := γ) (x := x) (n := 1)
    ⟨fun _ => t, fun _ _ _ => Subsingleton.elim _ _, fun _ => ht⟩
  simpa only [Nat.cast_one] using h1

def meanVisitCount (μ : ProbabilityMeasure C(PathTime, X)) (x : X) : ℝ≥0∞ :=
  ∫⁻ γ, visitCount γ x ∂(μ : Measure C(PathTime, X))

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem pathHitProbability_le_meanVisitCount (μ : ProbabilityMeasure C(PathTime, X)) (x : X) :
    pathHitProbability μ x ≤ meanVisitCount μ x := by
  let H : Set C(PathTime, X) := {γ | ∃ t, γ t = x}
  calc
    pathHitProbability μ x = ∫⁻ γ, H.indicator (fun _ => (1 : ℝ≥0∞)) γ
        ∂(μ : Measure C(PathTime, X)) := by
      rw [lintegral_indicator (isClosed_paths_hitting x).measurableSet]
      simp only [lintegral_one, Measure.restrict_apply_univ]
      rfl
    _ ≤ meanVisitCount μ x := by
      apply lintegral_mono
      intro γ
      by_cases h : γ ∈ H
      · simpa only [Set.indicator_of_mem h] using one_le_visitCount_of_hit h
      · simp only [Set.indicator_of_notMem h]
        exact bot_le

end CircleDomainRigidity

end

end OAI
