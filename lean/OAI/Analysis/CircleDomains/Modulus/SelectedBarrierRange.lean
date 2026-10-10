import OAI.Analysis.CircleDomains.Modulus.SelectedBarrierTest

namespace OAI

/-! A small barrier is compatible with any subfamily of its retained levels. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

namespace GradedRealTest

theorem exists_compatible_of_small_barrier
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}
    (c : ℕ → UngatedRealTest d π EStar) (M : Set Sphere)
    (hM : ∀ i, (c i).exclusions ∩ d.dust ⊆ M)
    (S : Set (UngatedRealTest d π EStar))
    (hselected : ∀ a ∈ S, ∃ i, c i = a)
    {regions : ℕ → Set Sphere}
    (hopen : ∀ n, IsOpen (regions n))
    (R : CompatibleRealBarrier (realTestLevelData d c) π
      (realTestLevelData.previous c) M EStar regions
      (fun _ => ((0 : ℂ) : Sphere)) univ)
    (k : ℕ) (hsmall : R.controlledSize < ENNReal.ofReal (1 / ((k : ℝ) + 1))) :
    ∃ b : GradedRealTest d π EStar,
      b.toUngatedRealTest.CompatibleWith S ∧ b.grade = k ∧ b.region = regions R.level := by
  classical
  let labels (a : UngatedRealTest d π EStar) : ℕ :=
    if h : ∃ i, c i = a then Classical.choose h else 0
  have hlabels (a) (ha : a ∈ S) : c (labels a) = a := by
    have h := hselected a ha
    dsimp only [labels]
    rw [dite_eq_left h]
    exact Classical.choose_spec h
  let R' : CompatibleRealBarrier d π (fun i => (c i).coordinate) M EStar regions
      (fun _ => ((0 : ℂ) : Sphere)) univ :=
    R.rebase rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)
  let b : GradedRealTest d π EStar :=
    { toUngatedRealTest := UngatedRealTest.of_barrier R' (hopen R'.level)
      grade := k
      small := by
        rw [UngatedRealTest.size_of_barrier]
        exact hsmall }
  refine ⟨b, ?_, rfl, rfl⟩
  apply UngatedRealTest.of_barrier_compatible R' (hopen R'.level) _ labels
  · intro a ha
    rw [← hlabels a ha]
    exact hM (labels a)
  · intro a ha
    rw [hlabels a ha]

end GradedRealTest
end CircleDomainRigidity

end

end OAI
