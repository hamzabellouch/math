import OAI.Analysis.CircleDomains.Selection.GradedRealSelection

namespace OAI

/-! Graded selection retaining a prescribed family of real tests. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace GradedRealTest
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}

def AllowedWith (S : Set (UngatedRealTest d π EStar))
    (A : Set (GradedRealTest d π EStar)) (c : GradedRealTest d π EStar) : Prop :=
  c.toUngatedRealTest.CompatibleWith (S ∪ toUngatedRealTest '' A)

theorem AllowedWith.mono {S : Set (UngatedRealTest d π EStar)}
    {A B : Set (GradedRealTest d π EStar)} {c : GradedRealTest d π EStar}
    (h : AllowedWith S B c) (hAB : A ⊆ B) : AllowedWith S A c :=
  UngatedRealTest.CompatibleWith.mono h (union_subset_union_right _ (image_mono hAB))

theorem exists_countable_selection_with (S : Set (UngatedRealTest d π EStar)) :
    ∃ A : ℕ → Set (GradedRealTest d π EStar),
      A 0 = ∅ ∧ (∀ n, (A n).Finite) ∧ Monotone A ∧
      (∀ n, (A (n + 1) \ A n).Subsingleton) ∧
      (∀ n c, c ∈ A (n + 1) \ A n → AllowedWith S (A n) c) ∧
      (⋃ n, A n).Countable ∧
      ∀ c, AllowedWith S (⋃ n, A n) c → ∀ x ∈ c.toUngatedRealTest.openEnds,
        ∃ e ∈ ⋃ n, A n, e.grade = c.grade ∧ x ∈ e.toUngatedRealTest.openEnds := by
  apply exists_countable_graded_open_selection
    (fun c : GradedRealTest d π EStar => c.toUngatedRealTest.openEnds)
    (fun c => c.toUngatedRealTest.open_openEnds) grade (AllowedWith S)
  intro A B hAB c hc
  exact ⟨c, hc.mono hAB, rfl, Subset.rfl⟩

end GradedRealTest
end CircleDomainRigidity

end

end OAI
