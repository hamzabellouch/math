import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixLongBoxes
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixCompatibility

namespace OAI

/-! # Countable long-box exhaustions for each remaining subgroup -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
def remainingWindow (c : EliminationChain P D) (R : ℝ) (m : ℕ) : Set c.Time := c.cube (R+m)
lemma remainingWindow_open (c : EliminationChain P D) (R : ℝ) (m : ℕ) :
    IsOpen (c.remainingWindow R m) := c.cube_open _
lemma remainingWindow_mono (c : EliminationChain P D) (R : ℝ) : Monotone (c.remainingWindow R) := by
  intro a b hab
  apply c.cube_mono
  simpa only [add_comm] using add_le_add_left (Nat.cast_le.mpr hab) R
lemma remainingWindow_cover (c : EliminationChain P D) (R : ℝ) :
    ⋃ m, c.remainingWindow R m = univ := c.cubes_cover R
end EliminationChain

namespace RootPrefixCoordinates
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n) (g : G n)

theorem exists_countable_boxes_exact_time (R : ℝ) :
    ∃ F : Set (RootPrefixBox C c hP hfinal g), F.Countable ∧
      (∀ B ∈ F, B.time = c.cube R) ∧
      ∀ s : UpperRootTransverse n × T,
        Function.Injective (fun t => C.timeParam c hP hfinal g (s,t)) →
        ∃ B ∈ F, s ∈ B.transverse := by
  let Good := {B : RootPrefixBox C c hP hfinal g | B.time = c.cube R}
  obtain ⟨F,hFG,hFc,hF⟩ := isOpen_biUnion_countable Good
    (fun B : RootPrefixBox C c hP hfinal g => B.transverse) (fun B _ => B.transverse_open)
  refine ⟨F,hFc,fun B hB => hFG hB,?_⟩
  intro s hs
  obtain ⟨B,hsB,hKB⟩ := C.box_contains_compact_time c hP hfinal g s hs
    (c.closedCube R) (c.closedCube_compact R)
  let E := B.shrink B.transverse (c.cube R) B.transverse_open (c.cube_open R)
    subset_rfl ((c.cube_subset_closedCube R).trans hKB)
  have hE : E ∈ Good := rfl
  have H : s ∈ ⋃ B ∈ Good, B.transverse := mem_iUnion.mpr ⟨E,mem_iUnion.mpr ⟨hE,hsB⟩⟩
  rw [←hF] at H
  simpa only [mem_iUnion,exists_prop] using H

def longBoxFamily (R : ℝ) (m : ℕ) : Set (RootPrefixBox C c hP hfinal g) :=
  (C.exists_countable_boxes_exact_time c hP hfinal g (R+m)).choose

lemma longBoxFamily_countable (R : ℝ) (m : ℕ) :
    (C.longBoxFamily c hP hfinal g R m).Countable :=
  (C.exists_countable_boxes_exact_time c hP hfinal g (R+m)).choose_spec.1

lemma longBoxFamily_time (R : ℝ) (m : ℕ)
    (B : RootPrefixBox C c hP hfinal g) (hB : B ∈ C.longBoxFamily c hP hfinal g R m) :
    B.time = c.cube (R+m) :=
  (C.exists_countable_boxes_exact_time c hP hfinal g (R+m)).choose_spec.2.1 B hB

lemma longBoxFamily_covers (R : ℝ) (m : ℕ) (s : UpperRootTransverse n × T)
    (hs : Function.Injective (fun t => C.timeParam c hP hfinal g (s,t))) :
    ∃ B ∈ C.longBoxFamily c hP hfinal g R m, s ∈ B.transverse :=
  (C.exists_countable_boxes_exact_time c hP hfinal g (R+m)).choose_spec.2.2 s hs

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
