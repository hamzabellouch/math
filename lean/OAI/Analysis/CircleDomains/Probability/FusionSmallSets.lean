import OAI.Analysis.CircleDomains.Probability.PathLawMixtures
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

namespace OAI

/-! The sigma-ideal of path-law candidates failing a prescribed countable/atomless
test. A finite atomless measure dominating any countable list of such tests is
constructed from the existing finite-measure representative of an s-finite measure. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_finite_atomless_dominating {X : Type*} [MeasurableSpace X]
    (μ : ℕ → Measure X) [∀ n, IsFiniteMeasure (μ n)]
    [∀ n, NullSingletonClass (μ n)] :
    ∃ ν : Measure X, IsFiniteMeasure ν ∧ NullSingletonClass ν ∧ ∀ n, μ n ≪ ν := by
  obtain ⟨ν, hν, hsumν, hνsum⟩ :=
    exists_isFiniteMeasure_absolutelyContinuous (Measure.sum μ)
  refine ⟨ν, hν, ⟨fun x => hνsum ?_⟩, fun n =>
    (Measure.absolutelyContinuous_sum_right n (Measure.AbsolutelyContinuous.refl _)).trans hsumν⟩
  simp [Measure.sum_apply_of_countable]

variable {X Z : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

def PassesHitTests (C : ℝ) (μ : ProbabilityMeasure C(PathTime, X))
    (D : Set X) (ν : Measure X) : Prop :=
  (∀ F : Finset X, (↑F : Set X) ⊆ D → ∑ x ∈ F, pathHitReal μ x ^ 2 ≤ C ^ 2) ∧
    ∫⁻ x, pathHitProbability μ x ∂ν = 0

theorem PassesHitTests.mono {C : ℝ} {μ : ProbabilityMeasure C(PathTime, X)}
    {D E : Set X} {ν ρ : Measure X} (h : PassesHitTests C μ D ν)
    (hED : E ⊆ D) (hρν : ρ ≪ ν) : PassesHitTests C μ E ρ := by
  refine ⟨fun F hF => h.1 F (hF.trans hED), ?_⟩
  apply (lintegral_eq_zero_iff (measurable_pathHitProbability_point μ)).mpr
  exact hρν.ae_le ((lintegral_eq_zero_iff (measurable_pathHitProbability_point μ)).mp h.2)

/-- A candidate family is small when one countable set and one finite atomless
test measure rule out every member. This is the manuscript's small-set ideal. -/
def HitTestSmall (law : Z → ProbabilityMeasure C(PathTime, X)) (C : ℝ) (A : Set Z) : Prop :=
  ∃ D : Set X, D.Countable ∧ ∃ ν : Measure X, IsFiniteMeasure ν ∧
    NullSingletonClass ν ∧ ∀ z ∈ A, ¬PassesHitTests C (law z) D ν

omit [SecondCountableTopology X] [BorelSpace X] [BorelSpace C(PathTime, X)] in
theorem HitTestSmall.mono {law : Z → ProbabilityMeasure C(PathTime, X)} {C : ℝ}
    {A B : Set Z} (hB : HitTestSmall law C B) (hAB : A ⊆ B) : HitTestSmall law C A := by
  obtain ⟨D, hD, ν, hν, hnull, hfail⟩ := hB
  exact ⟨D, hD, ν, hν, hnull, fun z hz => hfail z (hAB hz)⟩

omit [SecondCountableTopology X] [BorelSpace X] [BorelSpace C(PathTime, X)] in
theorem hitTestSmall_empty (law : Z → ProbabilityMeasure C(PathTime, X)) (C : ℝ) :
    HitTestSmall law C ∅ :=
  ⟨∅, countable_empty, 0, inferInstance, ⟨by simp⟩, by simp⟩

theorem hitTestSmall_iUnion {law : Z → ProbabilityMeasure C(PathTime, X)} {C : ℝ}
    {A : ℕ → Set Z} (hA : ∀ n, HitTestSmall law C (A n)) :
    HitTestSmall law C (⋃ n, A n) := by
  classical
  choose D hD ν hν hnull hfail using hA
  let (n : ℕ) : IsFiniteMeasure (ν n) := hν n
  let (n : ℕ) : NullSingletonClass (ν n) := hnull n
  obtain ⟨ρ, hρ, hnullρ, hdom⟩ := exists_finite_atomless_dominating ν
  refine ⟨⋃ n, D n, countable_iUnion hD, ρ, hρ, hnullρ, ?_⟩
  intro z hz hpass
  obtain ⟨n, hn⟩ := mem_iUnion.mp hz
  exact hfail n z hn (hpass.mono (subset_iUnion D n) (hdom n))

theorem HitTestSmall.union {law : Z → ProbabilityMeasure C(PathTime, X)} {C : ℝ}
    {A B : Set Z} (hA : HitTestSmall law C A) (hB : HitTestSmall law C B) :
    HitTestSmall law C (A ∪ B) := by
  classical
  have h := hitTestSmall_iUnion (A := fun n : ℕ => if n = 0 then A else B)
    (fun n => by split <;> assumption)
  apply h.mono
  intro z hz
  rcases hz with hz | hz
  · exact mem_iUnion.mpr ⟨0, by simpa using hz⟩
  · exact mem_iUnion.mpr ⟨1, by simpa using hz⟩

omit [SecondCountableTopology X] [BorelSpace X] [BorelSpace C(PathTime, X)] in
/-- The extraction hypothesis makes the whole candidate space nonsmall. -/
theorem not_hitTestSmall_univ {law : Z → ProbabilityMeasure C(PathTime, X)} {C : ℝ}
    (htest : ∀ D : Set X, D.Countable → ∀ ν : Measure X,
      IsFiniteMeasure ν → NullSingletonClass ν → ∃ z, PassesHitTests C (law z) D ν) :
    ¬HitTestSmall law C univ := by
  rintro ⟨D, hD, ν, hν, hnull, hfail⟩
  obtain ⟨z, hz⟩ := htest D hD ν hν hnull
  exact hfail z (mem_univ z) hz

end CircleDomainRigidity

end

end OAI
