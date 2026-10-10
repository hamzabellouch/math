import OAI.Analysis.CircleDomains.Selection.ZeroRealCoordinate
import OAI.Analysis.CircleDomains.Selection.DelayedSelection

namespace OAI

/-! Countable selection of the constructed ungated tests, at every reciprocal
accuracy. Compatibility retains every earlier test and its exceptional set. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

structure GradedRealTest (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (EStar : Set Sphere) extends UngatedRealTest d π EStar where
  grade : ℕ
  small : toUngatedRealTest.size < ENNReal.ofReal (1 / ((grade : ℝ) + 1))

namespace GradedRealTest
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}

def Allowed (A : Set (GradedRealTest d π EStar)) (c : GradedRealTest d π EStar) : Prop :=
  c.toUngatedRealTest.CompatibleWith
    (insert (UngatedRealTest.zeroTest d π EStar) (toUngatedRealTest '' A))

theorem Allowed.mono {A B : Set (GradedRealTest d π EStar)} {c : GradedRealTest d π EStar}
    (h : Allowed B c) (hAB : A ⊆ B) : Allowed A c :=
  UngatedRealTest.CompatibleWith.mono h (insert_subset_insert (image_mono hAB))

theorem exists_countable_selection :
    ∃ A : ℕ → Set (GradedRealTest d π EStar),
      A 0 = ∅ ∧ (∀ n, (A n).Finite) ∧ Monotone A ∧
      (∀ n, (A (n + 1) \ A n).Subsingleton) ∧
      (∀ n c, c ∈ A (n + 1) \ A n → Allowed (A n) c) ∧
      (⋃ n, A n).Countable ∧
      ∀ c, Allowed (⋃ n, A n) c → ∀ x ∈ c.toUngatedRealTest.openEnds,
        ∃ e ∈ ⋃ n, A n, e.grade = c.grade ∧ x ∈ e.toUngatedRealTest.openEnds := by
  apply exists_countable_graded_open_selection
    (fun c : GradedRealTest d π EStar => c.toUngatedRealTest.openEnds)
    (fun c => c.toUngatedRealTest.open_openEnds) grade Allowed
  intro A B hAB c hc
  exact ⟨c, hc.mono hAB, rfl, Subset.rfl⟩

theorem exists_delayed_countable_selection :
    ∃ A : ℕ → Set (GradedRealTest d π EStar),
      A 0 = ∅ ∧ A 1 = ∅ ∧ Monotone A ∧
      (∀ n, (A (n + 1) \ A n).Subsingleton) ∧
      (∀ n c, c ∈ A (n + 1) \ A n → Allowed (A n) c) ∧
      (⋃ n, A n).Countable ∧
      ∀ c, Allowed (⋃ n, A n) c → ∀ x ∈ c.toUngatedRealTest.openEnds,
        ∃ e ∈ ⋃ n, A n, e.grade = c.grade ∧ x ∈ e.toUngatedRealTest.openEnds := by
  obtain ⟨A, hzero, _, hmono, hsingle, hnew, hcount, hcover⟩ :=
    exists_countable_selection (d := d) (π := π) (EStar := EStar)
  refine ⟨delayedSelection A, rfl, hzero, delayedSelection_mono A hmono,
    delayedSelection_single A hzero hsingle, ?_, ?_, ?_⟩
  · intro n c hc
    cases n with
    | zero => simp [delayedSelection, hzero] at hc
    | succ n => exact hnew n c hc
  · simpa only [iUnion_delayedSelection] using hcount
  · simpa only [iUnion_delayedSelection] using hcover

end GradedRealTest
end CircleDomainRigidity

end

end OAI
