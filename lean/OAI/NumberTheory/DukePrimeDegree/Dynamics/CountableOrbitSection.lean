import Mathlib.MeasureTheory.MeasurableSpace.Basic

namespace OAI

/-! # A measurable section from a countable separated cover

The finite-neighbor relation in the application consists of the first
few forward and backward iterates. Removing earlier neighbors leaves a
separated section meeting every orbit in the cover. This construction
requires no ergodicity of the selected diagonal map.
-/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree

/-- The elementary marker construction, with orbit equivalence separated
from the finite-neighbor relation. -/
theorem exists_measurable_orbit_section
    {Y : Type*} [MeasurableSpace Y] (E : Setoid Y)
    (R : Y → Y → Prop) (hRsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hRE : ∀ x y, R x y → E.r x y)
    (C : ℕ → Set Y) (hC : ∀ n, MeasurableSet (C n))
    (hRC : ∀ n, MeasurableSet {x | ∃ y ∈ C n, R x y})
    (hsep : ∀ n, ∀ x ∈ C n, ∀ y ∈ C n, R x y → x=y) :
    ∃ S : Set Y, MeasurableSet S ∧ S ⊆ ⋃ n, C n ∧
      (∀ x ∈ S, ∀ y ∈ S, R x y → x=y) ∧
      ∀ x ∈ ⋃ n, C n, ∃ y ∈ S, E.r x y := by
  classical
  let B (n : ℕ) : Set Y := C n \ ⋃ i : Fin n, {x | ∃ y ∈ C i.val, R x y}
  let S := ⋃ n, B n
  have hB (n : ℕ) : MeasurableSet (B n) :=
    (hC n).diff (MeasurableSet.iUnion fun i => hRC i.val)
  have hSC : S ⊆ ⋃ n, C n := by
    intro x hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n,hn.1⟩
  refine ⟨S,MeasurableSet.iUnion hB,hSC,?_,?_⟩
  · intro x hx y hy hxy
    obtain ⟨n,hxn,hxearly⟩ := mem_iUnion.mp hx
    obtain ⟨m,hym,hyearly⟩ := mem_iUnion.mp hy
    rcases lt_trichotomy n m with hnm | rfl | hmn
    · exact (hyearly (mem_iUnion.mpr ⟨⟨n,hnm⟩,x,hxn,hRsymm hxy⟩)).elim
    · exact hsep n x hxn y hym hxy
    · exact (hxearly (mem_iUnion.mpr ⟨⟨m,hmn⟩,y,hym,hxy⟩)).elim
  · have hmeet : ∀ n, ∀ x ∈ C n, ∃ y ∈ S, E.r x y := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro x hx
        by_cases hxb : x ∈ B n
        · exact ⟨x,mem_iUnion.mpr ⟨n,hxb⟩,E.refl x⟩
        · have hnear : x ∈ ⋃ i : Fin n, {x | ∃ y ∈ C i.val, R x y} := by
            by_contra hn
            exact hxb ⟨hx,hn⟩
          obtain ⟨i,y,hy,hxy⟩ := mem_iUnion.mp hnear
          obtain ⟨z,hz,hyz⟩ := ih i.val i.isLt y hy
          exact ⟨z,hz,E.trans (hRE x y hxy) hyz⟩
    intro x hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    exact hmeet n x hn

end DukePrimeDegree

end

end OAI
