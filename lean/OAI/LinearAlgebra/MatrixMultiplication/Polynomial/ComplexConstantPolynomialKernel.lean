import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialLocalConstruction

namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

namespace MatrixMultiplication.Foundation.PolynomialLocalConstruction

open Tensor LocalMaps

variable {X Y Z AX AY AZ OX OY OZ : Type*}
variable [Fintype AX] [Fintype AY] [Fintype AZ]

def constantMatrix (M : X → OX → AX → ℂ) : X → OX → AX → Polynomial ℂ :=
  fun x u i => Polynomial.C (M x u i)

omit [Fintype AX] in
theorem constantMatrix_degree (M : X → OX → AX → ℂ) (x : X) (u : OX) (i : AX) :
    (constantMatrix M x u i).degree ≤ (0 : ℕ) := by
  simpa only [constantMatrix, Nat.cast_zero] using
    (Polynomial.degree_C_le (a := M x u i))

theorem fiberTransform_constantMatrix
    (MX : X → OX → AX → ℂ) (MY : Y → OY → AY → ℂ)
    (MZ : Z → OZ → AZ → ℂ)
    (T : Tensor ℂ (X × AX) (Y × AY) (Z × AZ)) :
    fiberTransform (constantMatrix MX) (constantMatrix MY) (constantMatrix MZ)
      (fun x y z => Polynomial.C (T x y z)) =
      fun x y z => Polynomial.C (fiberTransform MX MY MZ T x y z) := by
  funext x y z
  simp only [fiberTransform, constantMatrix, map_sum, map_mul]

theorem kernel_constantMatrix (auxiliary : Tensor ℂ AX AY AZ)
    (MX : X → OX → AX → ℂ) (MY : Y → OY → AY → ℂ)
    (MZ : Z → OZ → AZ → ℂ) :
    kernel auxiliary (constantMatrix MX) (constantMatrix MY) (constantMatrix MZ) =
      fun x y z => Polynomial.C
        (fiberTransform MX MY MZ (fun x y z => auxiliary x.2 y.2 z.2) x y z) :=
  fiberTransform_constantMatrix MX MY MZ _

theorem kernel_constantMatrix_degree (auxiliary : Tensor ℂ AX AY AZ)
    (MX : X → OX → AX → ℂ) (MY : Y → OY → AY → ℂ)
    (MZ : Z → OZ → AZ → ℂ) (x : X × OX) (y : Y × OY) (z : Z × OZ) :
    (kernel auxiliary (constantMatrix MX) (constantMatrix MY) (constantMatrix MZ)
      x y z).degree ≤ (0 : ℕ) := by
  rw [kernel_constantMatrix]
  exact Polynomial.degree_C_le

@[simp] theorem kernel_constantMatrix_coeff_zero (auxiliary : Tensor ℂ AX AY AZ)
    (MX : X → OX → AX → ℂ) (MY : Y → OY → AY → ℂ)
    (MZ : Z → OZ → AZ → ℂ) (x : X × OX) (y : Y × OY) (z : Z × OZ) :
    (kernel auxiliary (constantMatrix MX) (constantMatrix MY) (constantMatrix MZ)
      x y z).coeff 0 =
      fiberTransform MX MY MZ (fun x y z => auxiliary x.2 y.2 z.2) x y z := by
  rw [kernel_constantMatrix]
  exact Polynomial.coeff_C_zero

theorem kernel_constantMatrix_coeff_ne_zero (auxiliary : Tensor ℂ AX AY AZ)
    (MX : X → OX → AX → ℂ) (MY : Y → OY → AY → ℂ)
    (MZ : Z → OZ → AZ → ℂ) (x : X × OX) (y : Y × OY) (z : Z × OZ)
    {j : ℕ} (hj : j ≠ 0) :
    (kernel auxiliary (constantMatrix MX) (constantMatrix MY) (constantMatrix MZ)
      x y z).coeff j = 0 := by
  rw [kernel_constantMatrix]
  exact Polynomial.coeff_C_of_ne_zero hj

theorem constantMatrix_product_substitution
    (original : Tensor ℂ X Y Z) (auxiliary : Tensor ℂ AX AY AZ)
    (MX : X → OX → AX → ℂ) (MY : Y → OY → AY → ℂ)
    (MZ : Z → OZ → AZ → ℂ) :
    fiberTransform (constantMatrix MX) (constantMatrix MY) (constantMatrix MZ)
      (fun x y z => Polynomial.C (Tensor.product original auxiliary x y z)) =
      originalScale (fun x y z => Polynomial.C (original x y z))
        (kernel auxiliary (constantMatrix MX) (constantMatrix MY) (constantMatrix MZ)) := by
  have h := fiberTransform_originalScale
    (constantMatrix MX) (constantMatrix MY) (constantMatrix MZ)
    (fun x y z => Polynomial.C (original x y z))
    (fun x y z => Polynomial.C (auxiliary x.2 y.2 z.2))
  have hinput :
      (fun x y z => Polynomial.C (Tensor.product original auxiliary x y z)) =
        originalScale (fun x y z => Polynomial.C (original x y z))
          (fun x y z => Polynomial.C (auxiliary x.2 y.2 z.2)) := by
    funext x y z
    simp only [Tensor.product, originalScale, map_mul]
  rw [hinput]
  simpa only [kernel] using h

section CoordinateSelectors

variable [DecidableEq AX] [DecidableEq AY] [DecidableEq AZ]

def weightedCoordinateMatrix (select : X × OX → AX) (weight : X × OX → ℂ) :
    X → OX → AX → ℂ :=
  fun x u i => if i = select (x, u) then weight (x, u) else 0

def coordinateMatrix (select : X × OX → AX) : X → OX → AX → ℂ :=
  weightedCoordinateMatrix select (fun _ => 1)

def weightedCoordinatePolynomialMatrix
    (select : X × OX → AX) (weight : X × OX → ℂ) :
    X → OX → AX → Polynomial ℂ :=
  constantMatrix (weightedCoordinateMatrix select weight)

def coordinatePolynomialMatrix (select : X × OX → AX) :
    X → OX → AX → Polynomial ℂ :=
  constantMatrix (coordinateMatrix select)

omit [Fintype AX] in
theorem weightedCoordinatePolynomialMatrix_degree
    (select : X × OX → AX) (weight : X × OX → ℂ) (x : X) (u : OX) (i : AX) :
    (weightedCoordinatePolynomialMatrix select weight x u i).degree ≤ (0 : ℕ) :=
  constantMatrix_degree _ x u i

omit [Fintype AX] in
theorem coordinatePolynomialMatrix_degree
    (select : X × OX → AX) (x : X) (u : OX) (i : AX) :
    (coordinatePolynomialMatrix select x u i).degree ≤ (0 : ℕ) :=
  constantMatrix_degree _ x u i

theorem fiberTransform_weightedCoordinateMatrix
    (fx : X × OX → AX) (fy : Y × OY → AY) (fz : Z × OZ → AZ)
    (wx : X × OX → ℂ) (wy : Y × OY → ℂ) (wz : Z × OZ → ℂ)
    (T : Tensor ℂ (X × AX) (Y × AY) (Z × AZ)) :
    fiberTransform (weightedCoordinateMatrix fx wx) (weightedCoordinateMatrix fy wy)
        (weightedCoordinateMatrix fz wz) T =
      fun x y z => wx x * wy y * wz z * T (x.1, fx x) (y.1, fy y) (z.1, fz z) := by
  funext x y z
  simp [fiberTransform, weightedCoordinateMatrix, ite_mul, mul_ite]

theorem fiberTransform_coordinateMatrix
    (fx : X × OX → AX) (fy : Y × OY → AY) (fz : Z × OZ → AZ)
    (T : Tensor ℂ (X × AX) (Y × AY) (Z × AZ)) :
    fiberTransform (coordinateMatrix fx) (coordinateMatrix fy) (coordinateMatrix fz) T =
      Tensor.pullback (fun x => (x.1, fx x)) (fun y => (y.1, fy y))
        (fun z => (z.1, fz z)) T := by
  funext x y z
  have h := fiberTransform_weightedCoordinateMatrix fx fy fz
    (fun _ => 1) (fun _ => 1) (fun _ => 1) T
  simpa only [coordinateMatrix, one_mul, Tensor.pullback] using
    congrFun (congrFun (congrFun h x) y) z

theorem kernel_weightedCoordinatePolynomialMatrix (auxiliary : Tensor ℂ AX AY AZ)
    (fx : X × OX → AX) (fy : Y × OY → AY) (fz : Z × OZ → AZ)
    (wx : X × OX → ℂ) (wy : Y × OY → ℂ) (wz : Z × OZ → ℂ) :
    kernel auxiliary (weightedCoordinatePolynomialMatrix fx wx)
        (weightedCoordinatePolynomialMatrix fy wy) (weightedCoordinatePolynomialMatrix fz wz) =
      fun x y z => Polynomial.C
        (wx x * wy y * wz z * auxiliary (fx x) (fy y) (fz z)) := by
  unfold weightedCoordinatePolynomialMatrix
  rw [kernel_constantMatrix, fiberTransform_weightedCoordinateMatrix]

theorem kernel_coordinatePolynomialMatrix (auxiliary : Tensor ℂ AX AY AZ)
    (fx : X × OX → AX) (fy : Y × OY → AY) (fz : Z × OZ → AZ) :
    kernel auxiliary (coordinatePolynomialMatrix fx)
        (coordinatePolynomialMatrix fy) (coordinatePolynomialMatrix fz) =
      fun x y z => Polynomial.C (auxiliary (fx x) (fy y) (fz z)) := by
  simpa only [coordinatePolynomialMatrix, coordinateMatrix,
    weightedCoordinatePolynomialMatrix, one_mul] using
    kernel_weightedCoordinatePolynomialMatrix auxiliary fx fy fz
      (fun _ => 1) (fun _ => 1) (fun _ => 1)

@[simp] theorem kernel_weightedCoordinatePolynomialMatrix_coeff_zero
    (auxiliary : Tensor ℂ AX AY AZ)
    (fx : X × OX → AX) (fy : Y × OY → AY) (fz : Z × OZ → AZ)
    (wx : X × OX → ℂ) (wy : Y × OY → ℂ) (wz : Z × OZ → ℂ)
    (x : X × OX) (y : Y × OY) (z : Z × OZ) :
    (kernel auxiliary (weightedCoordinatePolynomialMatrix fx wx)
      (weightedCoordinatePolynomialMatrix fy wy) (weightedCoordinatePolynomialMatrix fz wz)
      x y z).coeff 0 = wx x * wy y * wz z * auxiliary (fx x) (fy y) (fz z) := by
  rw [kernel_weightedCoordinatePolynomialMatrix]
  exact Polynomial.coeff_C_zero

@[simp] theorem kernel_coordinatePolynomialMatrix_coeff_zero
    (auxiliary : Tensor ℂ AX AY AZ)
    (fx : X × OX → AX) (fy : Y × OY → AY) (fz : Z × OZ → AZ)
    (x : X × OX) (y : Y × OY) (z : Z × OZ) :
    (kernel auxiliary (coordinatePolynomialMatrix fx)
      (coordinatePolynomialMatrix fy) (coordinatePolynomialMatrix fz) x y z).coeff 0 =
      auxiliary (fx x) (fy y) (fz z) := by
  rw [kernel_coordinatePolynomialMatrix]
  exact Polynomial.coeff_C_zero

theorem kernel_coordinatePolynomialMatrix_coeff_ne_zero
    (auxiliary : Tensor ℂ AX AY AZ)
    (fx : X × OX → AX) (fy : Y × OY → AY) (fz : Z × OZ → AZ)
    (x : X × OX) (y : Y × OY) (z : Z × OZ) {j : ℕ} (hj : j ≠ 0) :
    (kernel auxiliary (coordinatePolynomialMatrix fx)
      (coordinatePolynomialMatrix fy) (coordinatePolynomialMatrix fz) x y z).coeff j = 0 := by
  rw [kernel_coordinatePolynomialMatrix]
  exact Polynomial.coeff_C_of_ne_zero hj

end CoordinateSelectors

section ExactDegeneration

variable [Fintype X] [Fintype Y] [Fintype Z]

def constantFiberDegeneration (original : Tensor ℂ X Y Z)
    (auxiliary : Tensor ℂ AX AY AZ)
    (MX : X → OX → AX → ℂ) (MY : Y → OY → AY → ℂ)
    (MZ : Z → OZ → AZ → ℂ) :
    PolynomialRestrictionDegeneration (Tensor.product original auxiliary)
      (fiberTransform MX MY MZ (Tensor.product original auxiliary)) 0 0 0 0 := by
  classical
  refine {
    leftMap := fiberMatrix (constantMatrix MX)
    middleMap := fiberMatrix (constantMatrix MY)
    rightMap := fiberMatrix (constantMatrix MZ)
    left_degree := ?_
    middle_degree := ?_
    right_degree := ?_
    vanishes := ?_
    leading := ?_
  }
  · intro x i
    by_cases h : x.1 = i.1
    · simpa only [fiberMatrix, ite_eq_left h] using constantMatrix_degree MX x.1 x.2 i.2
    · simp only [fiberMatrix, ite_eq_right h, Polynomial.degree_zero]
      exact bot_le
  · intro y j
    by_cases h : y.1 = j.1
    · simpa only [fiberMatrix, ite_eq_left h] using constantMatrix_degree MY y.1 y.2 j.2
    · simp only [fiberMatrix, ite_eq_right h, Polynomial.degree_zero]
      exact bot_le
  · intro z k
    by_cases h : z.1 = k.1
    · simpa only [fiberMatrix, ite_eq_left h] using constantMatrix_degree MZ z.1 z.2 k.2
    · simp only [fiberMatrix, ite_eq_right h, Polynomial.degree_zero]
      exact bot_le
  · intro x y z j hj
    exact (Nat.not_lt_zero j hj).elim
  · intro x y z
    rw [← fiberTransform_eq_restrict, fiberTransform_constantMatrix]
    exact Polynomial.coeff_C_zero

end ExactDegeneration

end MatrixMultiplication.Foundation.PolynomialLocalConstruction

end

end OAI
