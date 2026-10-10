import OAI.Analysis.CircleDomains.Probability.MarkedHitLaws
import OAI.Analysis.CircleDomains.Probability.FusionSmallSets
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

namespace OAI

/-! The sigma-ideal of path-law candidates failing a prescribed countable/atomless
test. A finite atomless measure dominating any countable list of such tests is
constructed from the existing finite-measure representative of an s-finite measure. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity.MarkedHit

variable {X Y Z : Type*} [MetricSpace X]
  [MetricSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  (ι : C(X, Y))

def PassesHitTests (C : ℝ) (μ : ProbabilityMeasure C(PathTime, Y))
    (D : Set X) (ν : Measure X) : Prop :=
  (∀ F : Finset X, (↑F : Set X) ⊆ D → ∑ x ∈ F, pathHitReal ι μ x ^ 2 ≤ C ^ 2) ∧
    ∫⁻ x, pathHitProbability ι μ x ∂ν = 0

theorem PassesHitTests.mono {C : ℝ} {μ : ProbabilityMeasure C(PathTime, Y)}
    {D E : Set X} {ν ρ : Measure X} (h : PassesHitTests ι C μ D ν)
    (hED : E ⊆ D) (hρν : ρ ≪ ν) : PassesHitTests ι C μ E ρ := by
  refine ⟨fun F hF => h.1 F (hF.trans hED), ?_⟩
  apply (lintegral_eq_zero_iff (measurable_pathHitProbability_point ι μ)).mpr
  exact hρν.ae_le ((lintegral_eq_zero_iff (measurable_pathHitProbability_point ι μ)).mp h.2)

/-- A candidate family is small when one countable set and one finite atomless
test measure rule out every member. This is the manuscript's small-set ideal. -/
def HitTestSmall (law : Z → ProbabilityMeasure C(PathTime, Y)) (C : ℝ) (A : Set Z) : Prop :=
  ∃ D : Set X, D.Countable ∧ ∃ ν : Measure X, IsFiniteMeasure ν ∧
    NullSingletonClass ν ∧ ∀ z ∈ A, ¬PassesHitTests ι C (law z) D ν

omit [BorelSpace X] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] [BorelSpace C(PathTime, Y)] in
theorem HitTestSmall.mono {law : Z → ProbabilityMeasure C(PathTime, Y)} {C : ℝ}
    {A B : Set Z} (hB : HitTestSmall ι law C B) (hAB : A ⊆ B) : HitTestSmall ι law C A := by
  obtain ⟨D, hD, ν, hν, hnull, hfail⟩ := hB
  exact ⟨D, hD, ν, hν, hnull, fun z hz => hfail z (hAB hz)⟩

omit [BorelSpace X] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] [BorelSpace C(PathTime, Y)] in
theorem hitTestSmall_empty (law : Z → ProbabilityMeasure C(PathTime, Y)) (C : ℝ) :
    HitTestSmall ι law C ∅ :=
  ⟨∅, countable_empty, 0, inferInstance, ⟨by simp⟩, by simp⟩

theorem hitTestSmall_iUnion {law : Z → ProbabilityMeasure C(PathTime, Y)} {C : ℝ}
    {A : ℕ → Set Z} (hA : ∀ n, HitTestSmall ι law C (A n)) :
    HitTestSmall ι law C (⋃ n, A n) := by
  classical
  choose D hD ν hν hnull hfail using hA
  let (n : ℕ) : IsFiniteMeasure (ν n) := hν n
  let (n : ℕ) : NullSingletonClass (ν n) := hnull n
  obtain ⟨ρ, hρ, hnullρ, hdom⟩ := exists_finite_atomless_dominating ν
  refine ⟨⋃ n, D n, countable_iUnion hD, ρ, hρ, hnullρ, ?_⟩
  intro z hz hpass
  obtain ⟨n, hn⟩ := mem_iUnion.mp hz
  exact hfail n z hn (PassesHitTests.mono ι hpass (subset_iUnion D n) (hdom n))

theorem HitTestSmall.union {law : Z → ProbabilityMeasure C(PathTime, Y)} {C : ℝ}
    {A B : Set Z} (hA : HitTestSmall ι law C A) (hB : HitTestSmall ι law C B) :
    HitTestSmall ι law C (A ∪ B) := by
  classical
  have h := hitTestSmall_iUnion ι (A := fun n : ℕ => if n = 0 then A else B)
    (fun n => by split <;> assumption)
  apply HitTestSmall.mono ι h
  intro z hz
  rcases hz with hz | hz
  · exact mem_iUnion.mpr ⟨0, by simpa using hz⟩
  · exact mem_iUnion.mpr ⟨1, by simpa using hz⟩

omit [BorelSpace X] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] [BorelSpace C(PathTime, Y)] in
/-- The extraction hypothesis makes the whole candidate space nonsmall. -/
theorem not_hitTestSmall_univ {law : Z → ProbabilityMeasure C(PathTime, Y)} {C : ℝ}
    (htest : ∀ D : Set X, D.Countable → ∀ ν : Measure X,
      IsFiniteMeasure ν → NullSingletonClass ν → ∃ z, PassesHitTests ι C (law z) D ν) :
    ¬HitTestSmall ι law C univ := by
  rintro ⟨D, hD, ν, hν, hnull, hfail⟩
  obtain ⟨z, hz⟩ := htest D hD ν hν hnull
  exact hfail z (mem_univ z) hz

end CircleDomainRigidity.MarkedHit

end

end OAI
