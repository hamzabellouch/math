import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalPrefixWindows
import OAI.NumberTheory.DukePrimeDegree.Geometry.PrefixBoundedRegions

namespace OAI

/-! # Countable compact-covering atlases of physical product windows -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set TopologicalSpace
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*}
    [TopologicalSpace T] [SecondCountableTopology T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain q.processed D)
    (hf : c.finalEntries = allPositiveRoots (d+1))

theorem exists_countable_physical_windows (K : Set c.Time) (hK : IsCompact K) :
    ∃ F : Set (PhysicalPrefixWindow q C g), F.Countable ∧
      (∀ B ∈ F, K ⊆ (B.toBox c hf).time) ∧
      ∀ s : UpperRootTransverse (d+1) × T,
        (∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
          rightAction (Quotient.mk _ ((g*s.1.val)*C.base s.2)) v =
            Quotient.mk _ ((g*s.1.val)*C.base s.2) → v = 1) →
        ∃ B ∈ F, s ∈ B.rectangle.first := by
  let Good := {B : PhysicalPrefixWindow q C g | K ⊆ (B.toBox c hf).time}
  obtain ⟨F,hFG,hFc,hF⟩ := isOpen_biUnion_countable Good
    (fun B : PhysicalPrefixWindow q C g => B.rectangle.first)
    (fun B _ => B.rectangle.first_open)
  refine ⟨F,hFc,fun B hB => hFG hB,?_⟩
  intro s hs
  obtain ⟨B,hsB,hKB⟩ := C.exists_physicalPrefixWindow_covering q g c hf s hs K hK
  have H : s ∈ ⋃ B ∈ Good, B.rectangle.first :=
    mem_iUnion.mpr ⟨B,mem_iUnion.mpr ⟨hKB,hsB⟩⟩
  rw [←hF] at H
  simpa only [mem_iUnion,exists_prop] using H

def physicalWindowFamily (R : ℝ) (m : ℕ) : Set (PhysicalPrefixWindow q C g) :=
  (C.exists_countable_physical_windows q g c hf (c.closedCube (R+m))
    (c.closedCube_compact (R+m))).choose

lemma physicalWindowFamily_countable (R : ℝ) (m : ℕ) :
    (C.physicalWindowFamily q g c hf R m).Countable :=
  (C.exists_countable_physical_windows q g c hf (c.closedCube (R+m))
    (c.closedCube_compact (R+m))).choose_spec.1

lemma physicalWindowFamily_time (R : ℝ) (m : ℕ) (B : PhysicalPrefixWindow q C g)
    (hB : B ∈ C.physicalWindowFamily q g c hf R m) :
    c.remainingWindow R m ⊆ (B.toBox c hf).time :=
  (c.cube_subset_closedCube (R+m)).trans
    ((C.exists_countable_physical_windows q g c hf (c.closedCube (R+m))
      (c.closedCube_compact (R+m))).choose_spec.2.1 B hB)

lemma physicalWindowFamily_covers (R : ℝ) (m : ℕ) (s : UpperRootTransverse (d+1) × T)
    (hs : ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction (Quotient.mk _ ((g*s.1.val)*C.base s.2)) v =
        Quotient.mk _ ((g*s.1.val)*C.base s.2) → v = 1) :
    ∃ B ∈ C.physicalWindowFamily q g c hf R m, s ∈ B.rectangle.first :=
  (C.exists_countable_physical_windows q g c hf (c.closedCube (R+m))
    (c.closedCube_compact (R+m))).choose_spec.2.2 s hs

end RootPrefixCoordinates
namespace PhysicalPrefixWindow
variable {d : ℕ} {q : InitialRootStep (d+1)} {T : Type*} [TopologicalSpace T]
    {C : RootPrefixCoordinates (d+1) q.processed T} {g : G (d+1)}

theorem exists_next_time_bound (B : PhysicalPrefixWindow q C g)
    {D : Finset (Fin (d+1))} (c : EliminationChain (insert q.root q.processed) D)
    (hf : c.finalEntries = allPositiveRoots (d+1)) :
    ∃ m : ℕ, ∀ z ∈ C.exchangedRectangleRegion q g B.pivot c hf B.rectangle B.interval,
      z.2 ∈ c.remainingWindow 1 m :=
  C.exchangedRectangleRegion_time_bounded q c hf g B.pivot B.rectangle B.interval
    B.second_bound B.second_bound_compact B.second_subset
    B.interval_bound B.interval_bound_compact B.interval_subset

end PhysicalPrefixWindow
end DukePrimeDegree

end

end OAI
