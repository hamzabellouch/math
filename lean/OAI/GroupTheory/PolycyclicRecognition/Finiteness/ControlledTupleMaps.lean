import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ControlledCochains
import Mathlib.Data.Fintype.Pi

namespace OAI

/-! # Properness estimates for controlled tuple maps

A bounded-difference tuple is determined up to finitely many choices once its
first vertex belongs to a finite set. This is the support estimate used for
the prism homotopy between close coarse maps.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Pointwise
variable {G H : Type*} [Group G] [Group H] {n m : ℕ}

/-- Fixing a finite set of possible first vertices makes a controlled
set of tuples finite. -/
theorem finite_controlled_tuples_first (S A : Set G) (hS : S.Finite) (hA : A.Finite) :
    {x : Fin (n + 1) → G | IsControlledTuple S x ∧ x 0 ∈ A}.Finite := by
  let B : Set G := A * S
  have hB : B.Finite := hA.mul hS
  apply (Set.Finite.pi' (fun _ : Fin (n + 1) => hB)).subset
  intro x hx i
  exact ⟨x 0, hx.2, (x 0)⁻¹ * x i, hx.1 0 i, by simp⟩

omit [Group H] in
/-- A tuple map whose first output is the image of its first input has
finite fibers on controlled tuples whenever the underlying map is proper. -/
theorem finite_controlled_tuple_map_fiber
    (f : G → H) (hf : ∀ y, (f ⁻¹' {y}).Finite)
    (F : (Fin (n + 1) → G) → (Fin (m + 1) → H))
    (hF : ∀ x, F x 0 = f (x 0))
    (S : Set G) (hS : S.Finite) (y : Fin (m + 1) → H) :
    {x | IsControlledTuple S x ∧ F x = y}.Finite := by
  apply (finite_controlled_tuples_first S (f ⁻¹' {y 0}) hS (hf _)).subset
  intro x hx
  refine ⟨hx.1, ?_⟩
  change f (x 0) = y 0
  rw [← hF, hx.2]

/-- Mixed tuples of two close maps have uniformly controlled differences.
This is precisely the estimate required by the usual prism construction. -/
theorem controlled_mixed_tuple
    (f g : G → H) (hf : GroupBornologous f) (hg : GroupBornologous g)
    (hclose : (Set.range fun x => (f x)⁻¹ * g x).Finite)
    (S : Set G) (hS : S.Finite) :
    ∃ T : Set H, T.Finite ∧
      ∀ (x : Fin (n + 1) → G), IsControlledTuple S x →
      ∀ (a : Fin (m + 1) → Fin (n + 1)) (choose : Fin (m + 1) → Bool),
        IsControlledTuple T (fun i => if choose i then g (x (a i)) else f (x (a i))) := by
  obtain ⟨A, hA, hfA⟩ := hf S hS
  obtain ⟨B, hB, hgB⟩ := hg S hS
  let C := Set.range fun x => (f x)⁻¹ * g x
  let T := (A ∪ B) ∪ (A * C ∪ C⁻¹ * A)
  refine ⟨T, (hA.union hB).union ((hA.mul hclose).union (hclose.inv.mul hA)), ?_⟩
  intro x hx a choose i j
  have hfij := hfA (x (a i)) (x (a j)) (hx _ _)
  have hgij := hgB (x (a i)) (x (a j)) (hx _ _)
  have hci : (f (x (a i)))⁻¹ * g (x (a i)) ∈ C := ⟨_, rfl⟩
  have hcj : (f (x (a j)))⁻¹ * g (x (a j)) ∈ C := ⟨_, rfl⟩
  cases hi : choose i <;> cases hj : choose j <;> simp only [hi, hj, Bool.false_eq_true,
    ite_false, ite_true]
  · exact Or.inl (Or.inl hfij)
  · exact Or.inr (Or.inl ⟨_, hfij, _, hcj, by simp [mul_assoc]⟩)
  · apply Or.inr ∘ Or.inr
    refine ⟨((f (x (a i)))⁻¹ * g (x (a i)))⁻¹, Set.inv_mem_inv.mpr hci,
      (f (x (a i)))⁻¹ * f (x (a j)), hfij, ?_⟩
    simp [mul_assoc]
  · exact Or.inl (Or.inr hgij)

end PolycyclicRecognition

end

end OAI
