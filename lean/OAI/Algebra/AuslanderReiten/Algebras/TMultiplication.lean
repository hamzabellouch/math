import OAI.Algebra.AuslanderReiten.Cocycles.CocycleData

namespace OAI

noncomputable section

namespace ArExplicit

namespace Letter

theorem sum_univ {M : Type*} [AddCommMonoid M] (f : Letter → M) :
    ∑ i, f i = f .e + f .x + f .y + f .z + f .u +
      f .v + f .t + f .j + f .f + f .n := by
  change (∑ i ∈ ({.e, .x, .y, .z, .u, .v, .t, .j, .f, .n} : Finset Letter), f i) = _
  simp [add_assoc]

end Letter

namespace CocycleData

open BaseAlgebra TrivialExtension

variable {k : Type*} [Field k] (q : k)

def multiplicationCoefficient (a b : T k q) (i : TIndex) : k :=
  (multiplication.map fun m => if m.output = i then
    q ^ m.degree * T.coefficient q m.first a * T.coefficient q m.second b else 0).sum

theorem dual_apply (φ : Module.Dual k (BaseAlgebra k q)) (a : BaseAlgebra k q) :
    φ a = ∑ i, a.coeff i * φ (basisVector q i) := by
  conv_lhs => rw [T.base_expand q a]
  simp

theorem upper_product_coefficient (a b : T k q) (i : Letter) :
    T.coefficient q (true, i) (a * b) =
      (∑ jidx, (basisVector q i * a.base).coeff jidx * b.dual (basisVector q jidx)) +
      (∑ jidx, (b.base * basisVector q i).coeff jidx * a.dual (basisVector q jidx)) := by
  change b.dual (basisVector q i * a.base) + a.dual (b.base * basisVector q i) = _
  rw [dual_apply, dual_apply]

private theorem multiplication_false_e (a b : T k q) :
    T.coefficient q (false, .e) (a * b) = multiplicationCoefficient q a b (false, .e) := by
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product]

private theorem multiplication_false_x (a b : T k q) :
    T.coefficient q (false, .x) (a * b) = multiplicationCoefficient q a b (false, .x) := by
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product]
  ring

private theorem multiplication_false_y (a b : T k q) :
    T.coefficient q (false, .y) (a * b) = multiplicationCoefficient q a b (false, .y) := by
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product]
  ring

private theorem multiplication_false_z (a b : T k q) :
    T.coefficient q (false, .z) (a * b) = multiplicationCoefficient q a b (false, .z) := by
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product]
  ring

private theorem multiplication_false_u (a b : T k q) :
    T.coefficient q (false, .u) (a * b) = multiplicationCoefficient q a b (false, .u) := by
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product]

private theorem multiplication_false_v (a b : T k q) :
    T.coefficient q (false, .v) (a * b) = multiplicationCoefficient q a b (false, .v) := by
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product]
  ring

private theorem multiplication_false_t (a b : T k q) :
    T.coefficient q (false, .t) (a * b) = multiplicationCoefficient q a b (false, .t) := by
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product]

private theorem multiplication_false_j (a b : T k q) :
    T.coefficient q (false, .j) (a * b) = multiplicationCoefficient q a b (false, .j) := by
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product]
  ring

private theorem multiplication_false_f (a b : T k q) :
    T.coefficient q (false, .f) (a * b) = multiplicationCoefficient q a b (false, .f) := by
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product]

private theorem multiplication_false_n (a b : T k q) :
    T.coefficient q (false, .n) (a * b) = multiplicationCoefficient q a b (false, .n) := by
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product]
  ring

private theorem multiplication_true_e (a b : T k q) :
    T.coefficient q (true, .e) (a * b) = multiplicationCoefficient q a b (true, .e) := by
  rw [upper_product_coefficient]
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product, Letter.sum_univ]
  ring

private theorem multiplication_true_x (a b : T k q) :
    T.coefficient q (true, .x) (a * b) = multiplicationCoefficient q a b (true, .x) := by
  rw [upper_product_coefficient]
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product, Letter.sum_univ]
  ring

private theorem multiplication_true_y (a b : T k q) :
    T.coefficient q (true, .y) (a * b) = multiplicationCoefficient q a b (true, .y) := by
  rw [upper_product_coefficient]
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product, Letter.sum_univ]
  ring

private theorem multiplication_true_z (a b : T k q) :
    T.coefficient q (true, .z) (a * b) = multiplicationCoefficient q a b (true, .z) := by
  rw [upper_product_coefficient]
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product, Letter.sum_univ]
  ring

private theorem multiplication_true_u (a b : T k q) :
    T.coefficient q (true, .u) (a * b) = multiplicationCoefficient q a b (true, .u) := by
  rw [upper_product_coefficient]
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product, Letter.sum_univ]
  ring

private theorem multiplication_true_v (a b : T k q) :
    T.coefficient q (true, .v) (a * b) = multiplicationCoefficient q a b (true, .v) := by
  rw [upper_product_coefficient]
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product, Letter.sum_univ]
  ring

private theorem multiplication_true_t (a b : T k q) :
    T.coefficient q (true, .t) (a * b) = multiplicationCoefficient q a b (true, .t) := by
  rw [upper_product_coefficient]
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product, Letter.sum_univ]
  ring

private theorem multiplication_true_j (a b : T k q) :
    T.coefficient q (true, .j) (a * b) = multiplicationCoefficient q a b (true, .j) := by
  rw [upper_product_coefficient]
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product, Letter.sum_univ]
  ring

private theorem multiplication_true_f (a b : T k q) :
    T.coefficient q (true, .f) (a * b) = multiplicationCoefficient q a b (true, .f) := by
  rw [upper_product_coefficient]
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product, Letter.sum_univ]
  ring

private theorem multiplication_true_n (a b : T k q) :
    T.coefficient q (true, .n) (a * b) = multiplicationCoefficient q a b (true, .n) := by
  rw [upper_product_coefficient]
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product, Letter.sum_univ]
  ring

theorem multiplication_coefficient (a b : T k q) (i : TIndex) :
    T.coefficient q i (a * b) = multiplicationCoefficient q a b i := by
  obtain ⟨upper, i⟩ := i
  cases upper <;> cases i
  · exact multiplication_false_e q a b
  · exact multiplication_false_x q a b
  · exact multiplication_false_y q a b
  · exact multiplication_false_z q a b
  · exact multiplication_false_u q a b
  · exact multiplication_false_v q a b
  · exact multiplication_false_t q a b
  · exact multiplication_false_j q a b
  · exact multiplication_false_f q a b
  · exact multiplication_false_n q a b
  · exact multiplication_true_e q a b
  · exact multiplication_true_x q a b
  · exact multiplication_true_y q a b
  · exact multiplication_true_z q a b
  · exact multiplication_true_u q a b
  · exact multiplication_true_v q a b
  · exact multiplication_true_t q a b
  · exact multiplication_true_j q a b
  · exact multiplication_true_f q a b
  · exact multiplication_true_n q a b

end CocycleData
end ArExplicit

end

end OAI
