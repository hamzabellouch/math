import OAI.Algebra.AuslanderReiten.Algebras.TrivialExtension

namespace OAI

noncomputable section

namespace ArExplicit

abbrev TIndex := Bool × Letter

namespace TIndex

def number : TIndex → ℕ
  | (upper, i) => (if upper then 10 else 0) + match i with
    | .e => 0 | .x => 1 | .y => 2 | .z => 3 | .u => 4
    | .v => 5 | .t => 6 | .j => 7 | .f => 8 | .n => 9

def star (i : TIndex) : TIndex := (!i.1, i.2)

end TIndex

namespace T

open BaseAlgebra TrivialExtension

variable {k : Type*} [Field k] (q : k)

def vector : TIndex → T k q
  | (false, i) => lower q i
  | (true, i) => upper q i

def coefficient (i : TIndex) : T k q →ₗ[k] k where
  toFun a := if i.1 then a.dual (basisVector q i.2) else a.base.coeff i.2
  map_add' a b := by cases i with | mk b i => cases b <;> rfl
  map_smul' r a := by cases i with | mk b i => cases b <;> rfl

@[simp] theorem coefficient_lower (i bidx : Letter) :
    coefficient q (false, i) (lower q bidx) = if i = bidx then 1 else 0 := by
  simp [coefficient, lower, inl]

@[simp] theorem coefficient_upper (i bidx : Letter) :
    coefficient q (true, i) (upper q bidx) = if i = bidx then 1 else 0 := by
  change (basisVector q i).coeff bidx = if i = bidx then 1 else 0
  simp [eq_comm]

@[simp] theorem coefficient_lower_upper (i bidx : Letter) :
    coefficient q (false, i) (upper q bidx) = 0 := rfl

@[simp] theorem coefficient_upper_lower (i bidx : Letter) :
    coefficient q (true, i) (lower q bidx) = 0 := rfl

@[simp] theorem coefficient_vector (i bidx : TIndex) :
    coefficient q i (vector q bidx) = if i = bidx then 1 else 0 := by
  obtain ⟨b, i⟩ := i
  obtain ⟨c, bidx⟩ := bidx
  cases b <;> cases c <;> simp [vector]

theorem base_expand (a : BaseAlgebra k q) :
    a = ∑ i : Letter, a.coeff i • basisVector q i := by
  apply BaseAlgebra.ext
  funext aidx
  change a.coeff aidx = BaseAlgebra.coordinateLinearEquiv q (∑ i : Letter, a.coeff i • basisVector q i) aidx
  rw [map_sum]
  have hb : ∀ i : Letter, BaseAlgebra.coordinateLinearEquiv q (basisVector q i) = Pi.single i 1 := by
    intro i
    rfl
  simp [hb, Pi.single_apply]

theorem coordinate_ext {a b : T k q} (h : ∀ i, coefficient q i a = coefficient q i b) : a = b := by
  apply TrivialExtension.ext
  · apply BaseAlgebra.ext
    funext i
    exact h (false, i)
  · apply LinearMap.ext
    intro c
    rw [base_expand q c]
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun x => c.coeff i • x) (h (true, i))

theorem expand (a : T k q) : a = ∑ i : TIndex, coefficient q i a • vector q i := by
  apply coordinate_ext q
  intro bidx
  simp

def coordinateEquiv : T k q ≃ₗ[k] (TIndex → k) where
  toFun a i := coefficient q i a
  invFun c := ∑ i, c i • vector q i
  left_inv a := (expand q a).symm
  right_inv c := by funext i; simp
  map_add' a b := by funext i; simp
  map_smul' r a := by funext i; simp

end T
end ArExplicit

end

end OAI
