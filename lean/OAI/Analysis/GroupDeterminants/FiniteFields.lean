import OAI.Analysis.GroupDeterminants.ClosedAlgebra

namespace OAI

universe uK uF uG ud

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section FiniteFieldPassage

variable {K : Type uK} {F : Type uF} {G : Type uG} {d : Type ud} [Semiring K] [Semiring F] [Monoid G]
variable [Fintype d] [DecidableEq d]

def coeffMatrix (φ : K →+* Matrix d d F) (a : MonoidAlgebra K G) :
    Matrix d d (MonoidAlgebra F G) := fun i j =>
  MonoidAlgebra.ofCoeff (a.coeff.mapRange (fun k => φ k i j) (by simp))

omit [Monoid G] in
@[simp] theorem coeffMatrix_coeff (φ : K →+* Matrix d d F) (a : MonoidAlgebra K G)
    (i j : d) (g : G) : (coeffMatrix φ a i j).coeff g = φ (a.coeff g) i j := rfl

omit [Monoid G] in
@[simp] theorem coeffMatrix_single (φ : K →+* Matrix d d F) (g : G) (k : K) :
    coeffMatrix φ (MonoidAlgebra.single g k) = Matrix.of (fun i j => MonoidAlgebra.single g (φ k i j)) := by
  ext i j h
  classical
  by_cases h = g <;> simp_all [coeffMatrix_coeff, MonoidAlgebra.coeff_single]

@[simp] theorem coeffMatrix_zero (φ : K →+* Matrix d d F) : coeffMatrix (G := G) φ 0 = 0 := by
  ext i j h
  simp

@[simp] theorem coeffMatrix_add (φ : K →+* Matrix d d F) (a b : MonoidAlgebra K G) :
    coeffMatrix φ (a + b) = coeffMatrix φ a + coeffMatrix φ b := by
  ext i j h
  simp

theorem coeffMatrix_mul_single (φ : K →+* Matrix d d F) (g h : G) (k l : K) :
    coeffMatrix φ (MonoidAlgebra.single g k * MonoidAlgebra.single h l) =
      coeffMatrix φ (MonoidAlgebra.single g k) * coeffMatrix φ (MonoidAlgebra.single h l) := by
  classical
  apply Matrix.ext
  intro i j
  simp only [MonoidAlgebra.single_mul_single, coeffMatrix_single, map_mul, Matrix.mul_apply, Matrix.of_apply]
  ext t
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single]
  by_cases ht : g * h = t <;> simp [ht]

theorem coeffMatrix_mul (φ : K →+* Matrix d d F) (a b : MonoidAlgebra K G) :
    coeffMatrix φ (a * b) = coeffMatrix φ a * coeffMatrix φ b := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | single g k =>
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | single h l => exact coeffMatrix_mul_single φ g h k l
    | add x y hx hy => simp_all [mul_add]
  | add x y hx hy => simp_all [add_mul]

@[simp] theorem coeffMatrix_one (φ : K →+* Matrix d d F) : coeffMatrix (G := G) φ 1 = 1 := by
  classical
  apply Matrix.ext
  intro i j
  by_cases hij : i = j <;> simp [MonoidAlgebra.one_def, Matrix.one_apply, hij]

def coeffMatrixHom (φ : K →+* Matrix d d F) :
    MonoidAlgebra K G →+* Matrix d d (MonoidAlgebra F G) where
  toFun := coeffMatrix φ
  map_one' := coeffMatrix_one φ
  map_mul' := coeffMatrix_mul φ
  map_zero' := coeffMatrix_zero φ
  map_add' := coeffMatrix_add φ

theorem coeffMatrix_injective (φ : K →+* Matrix d d F) (hφ : Function.Injective φ) :
    Function.Injective (coeffMatrixHom (G := G) φ) := by
  intro a b hab
  ext g
  apply hφ
  ext i j
  exact congrArg (fun A : Matrix d d (MonoidAlgebra F G) => (A i j).coeff g) hab

 theorem binary_matrix_of_finite_field (K H : Type) [Field K] [Finite K] [CharP K 2]
     [Group H] (a b : MonoidAlgebra K H) (hab : a * b = 1) (hba : b * a ≠ 1) :
     ∃ d : ℕ, 1 ≤ d ∧ ∃ X Y : Matrix (Fin d) (Fin d) (MonoidAlgebra (ZMod 2) H),
       X * Y = 1 ∧ Y * X ≠ 1 := by
   let : Algebra (ZMod 2) K := (ZMod.castHom (by simp) K).toAlgebra
   let d := Module.finrank (ZMod 2) K
   let φ : K →+* Matrix (Fin d) (Fin d) (ZMod 2) :=
     (Algebra.leftMulMatrix (Module.finBasis (ZMod 2) K)).toRingHom
   have hφ : Function.Injective φ := Algebra.leftMulMatrix_injective _
   let f : MonoidAlgebra K H →+* Matrix (Fin d) (Fin d) (MonoidAlgebra (ZMod 2) H) :=
     coeffMatrixHom φ
   refine ⟨d, Module.finrank_pos, f a, f b, ?_, ?_⟩
   · rw [← map_mul, hab, map_one]
   · intro h
     apply hba
     apply coeffMatrix_injective φ hφ
     simpa [f] using h

end FiniteFieldPassage

end GroupRingDeterminant

end

end OAI
