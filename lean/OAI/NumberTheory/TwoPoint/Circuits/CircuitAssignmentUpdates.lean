import OAI.NumberTheory.TwoPoint.Circuits.CircuitPartialAssignment

namespace OAI

/-! Updates along the disjoint blocks of a canonical DNF path. These lemmas
also justify recovering the original restriction after decoding a block. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace PartialAssignment

lemma free_assign {n : ℕ} (ρ : PartialAssignment n) (S : Finset (Fin n))
    (x : BooleanCube n) : (ρ.assign S x).free = ρ.free \ S := by
  ext i
  simp only [free, mem_filter, mem_univ, true_and, mem_sdiff]
  by_cases hi : i ∈ S <;> simp [assign, hi]

lemma assign_comm {n : ℕ} (ρ : PartialAssignment n) (S T : Finset (Fin n))
    (hST : Disjoint S T) (x y : BooleanCube n) :
    (ρ.assign S x).assign T y = (ρ.assign T y).assign S x := by
  funext i
  by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T
  · exact False.elim (Finset.disjoint_left.mp hST hiS hiT)
  all_goals simp [assign, hiS, hiT]

lemma assign_injective_of_free {n : ℕ} (ρ τ : PartialAssignment n)
    (S : Finset (Fin n)) (hρ : S ⊆ ρ.free) (hτ : S ⊆ τ.free)
    (x y : BooleanCube n) (h : ρ.assign S x = τ.assign S y) : ρ = τ := by
  funext i
  by_cases hi : i ∈ S
  · exact (mem_filter.mp (hρ hi)).2.trans (mem_filter.mp (hτ hi)).2.symm
  · have he := congrFun h i
    simpa [assign, hi] using he

lemma assign_congr_on {n : ℕ} (ρ : PartialAssignment n) (S : Finset (Fin n))
    (x y : BooleanCube n) (h : ∀ i ∈ S, x i = y i) : ρ.assign S x = ρ.assign S y := by
  funext i
  by_cases hi : i ∈ S <;> simp [assign, hi, h i]

end PartialAssignment

namespace CubeTerm

lemma live_update_disjoint {n : ℕ} (C : CubeTerm n) (ρ : PartialAssignment n)
    (x : BooleanCube n) : Disjoint C.support (ρ.assign (C.live ρ) x).free := by
  apply Finset.disjoint_left.mpr
  intro i hi hf
  rw [PartialAssignment.free_assign] at hf
  have hn := (mem_filter.mp (mem_sdiff.mp hf).1).2
  exact (mem_sdiff.mp hf).2 (mem_filter.mpr ⟨hi, hn⟩)

lemma compatible_assign_disjoint {n : ℕ} (C : CubeTerm n)
    (ρ : PartialAssignment n) (S : Finset (Fin n)) (hS : Disjoint C.support S)
    (x : BooleanCube n) (hC : C.Compatible ρ) : C.Compatible (ρ.assign S x) := by
  intro i hi
  have hn : i ∉ S := fun hs => Finset.disjoint_left.mp hS hi hs
  simpa [PartialAssignment.assign, hn] using hC i hi

lemma satisfied_mono {n : ℕ} (C : CubeTerm n) {ρ τ : PartialAssignment n}
    (hC : C.Satisfied ρ) (h : ρ.Extends τ) : C.Satisfied τ :=
  fun i hi => h i (C.value i) (hC i hi)

end CubeTerm

end TwoPointCorrelations

end OAI
