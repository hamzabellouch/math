import Mathlib
import OAI.LinearAlgebra.MatrixFields.Tensors.ComplexDotPairing

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.JointExtraction

open MatrixMultiplication.Foundation

variable {F X Y Z I : Type*} [CommSemiring F]

structure Assignment (X Y Z I : Type*) where
  x : X → Option I
  y : Y → Option I
  z : Z → Option I

noncomputable def uniqueAssignment {A : Type*} (eligible : Finset I)
    (compatible : I → A → Prop) (v : A) : Option I := by
  classical
  exact if h : ∃ i, i ∈ eligible ∧ compatible i v ∧
      ∀ j, j ∈ eligible → compatible j v → j = i
    then some (Classical.choose h) else none

theorem uniqueAssignment_spec {A : Type*} (eligible : Finset I)
    (compatible : I → A → Prop) (v : A) (i : I)
    (h : uniqueAssignment eligible compatible v = some i) :
    i ∈ eligible ∧ compatible i v ∧
      ∀ j, j ∈ eligible → compatible j v → j = i := by
  classical
  unfold uniqueAssignment at h
  split_ifs at h with hex
  · have hi : Classical.choose hex = i := Option.some.inj h
    simpa only [hi] using Classical.choose_spec hex

theorem uniqueAssignment_unique {A : Type*} (eligible : Finset I)
    (compatible : I → A → Prop) (v : A) (i j : I)
    (hi : uniqueAssignment eligible compatible v = some i)
    (hj : j ∈ eligible) (hc : compatible j v) : i = j :=
  ((uniqueAssignment_spec eligible compatible v i hi).2.2 j hj hc).symm

noncomputable def retainAssignment {A : Type*} (f : A → Option I)
    (keep : A → Prop) (v : A) : Option I := by
  classical
  exact if keep v then f v else none

theorem retainAssignment_some {A : Type*} (f : A → Option I)
    (keep : A → Prop) (v : A) (i : I)
    (h : retainAssignment f keep v = some i) : f v = some i := by
  classical
  unfold retainAssignment at h
  split_ifs at h
  · exact h

def Coherent (T : Tensor F X Y Z) (a : Assignment X Y Z I) : Prop :=
  ∀ x y z i j k, T x y z ≠ 0 →
    a.x x = some i → a.y y = some j → a.z z = some k → i = j ∧ i = k

theorem coherent_of_sequential
    (T : Tensor F X Y Z) (a : Assignment X Y Z I)
    (compatibleY : I → Y → Prop) (compatibleZ : I → Z → Prop)
    (transferY : ∀ x y z i, T x y z ≠ 0 → a.x x = some i → compatibleY i y)
    (transferZ : ∀ x y z i, T x y z ≠ 0 →
      a.x x = some i → a.y y = some i → compatibleZ i z)
    (uniqueY : ∀ y j i, a.y y = some j → compatibleY i y → j = i)
    (uniqueZ : ∀ z k i, a.z z = some k → compatibleZ i z → k = i) :
    Coherent T a := by
  intro x y z i j k hT hx hy hz
  have hji : j = i := uniqueY y j i hy (transferY x y z i hT hx)
  have hki : k = i := uniqueZ z k i hz
    (transferZ x y z i hT hx (hji ▸ hy))
  exact ⟨hji.symm, hki.symm⟩

noncomputable def branch (T : Tensor F X Y Z) (a : Assignment X Y Z I)
    (i : I) : Tensor F X Y Z := by
  classical
  exact fun x y z => if a.x x = some i ∧ a.y y = some i ∧ a.z z = some i
    then T x y z else 0

noncomputable def assignmentMatrix {A : Type*} (f : A → Option I) :
    (I × A) → A → F := by
  classical
  exact fun p a => if a = p.2 ∧ f a = some p.1 then 1 else 0

theorem restrict_assignments_apply [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq I]
    (T : Tensor F X Y Z) (a : Assignment X Y Z I)
    (x : I × X) (y : I × Y) (z : I × Z) :
    Tensor.restrict (assignmentMatrix a.x) (assignmentMatrix a.y)
      (assignmentMatrix a.z) T x y z =
    if a.x x.2 = some x.1 ∧ a.y y.2 = some y.1 ∧ a.z z.2 = some z.1
      then T x.2 y.2 z.2 else 0 := by
  classical
  simp [Tensor.restrict, assignmentMatrix, ite_and, ite_mul, mul_ite]
  split_ifs <;> simp_all

theorem restrict_assignments_eq_directSum
    [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq I]
    (T : Tensor F X Y Z) (a : Assignment X Y Z I) (h : Coherent T a) :
    Tensor.restrict (assignmentMatrix a.x) (assignmentMatrix a.y)
      (assignmentMatrix a.z) T = Tensor.directSum (branch T a) := by
  classical
  funext x y z
  rw [restrict_assignments_apply]
  by_cases hx : x.1 = y.1
  · by_cases hz : x.1 = z.1
    · simp [Tensor.directSum, branch, ← hx, ← hz]
    · by_cases ht : T x.2 y.2 z.2 = 0
      · simp [Tensor.directSum, hz, ht]
      · have hn : ¬ (a.x x.2 = some x.1 ∧ a.y y.2 = some y.1 ∧
            a.z z.2 = some z.1) := by
          intro ha
          exact hz (h _ _ _ _ _ _ ht ha.1 ha.2.1 ha.2.2).2
        simp [Tensor.directSum, hz, hn]
  · by_cases ht : T x.2 y.2 z.2 = 0
    · simp [Tensor.directSum, hx, ht]
    · have hn : ¬ (a.x x.2 = some x.1 ∧ a.y y.2 = some y.1 ∧
          a.z z.2 = some z.1) := by
        intro ha
        exact hx (h _ _ _ _ _ _ ht ha.1 ha.2.1 ha.2.2).1
      simp [Tensor.directSum, hx, hn]

theorem rankAtMost_directSum_branches
    [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq I]
    (T : Tensor F X Y Z) (a : Assignment X Y Z I) (h : Coherent T a)
    {r : ℕ} (hT : Tensor.RankAtMost T r) :
    Tensor.RankAtMost (Tensor.directSum (branch T a)) r := by
  rw [← restrict_assignments_eq_directSum T a h]
  exact hT.restrict _ _ _

theorem coherent_of_support_subset (T S : Tensor F X Y Z)
    (a : Assignment X Y Z I) (h : Coherent T a)
    (hs : ∀ x y z, S x y z ≠ 0 → T x y z ≠ 0) : Coherent S a := by
  intro x y z i j k hS hx hy hz
  exact h x y z i j k (hs x y z hS) hx hy hz

end MatrixMultiplication.JointExtraction

end MatrixAllFields

end OAI
