import OAI.Algebra.DepthFive.TraceExpansion

namespace OAI

/-! Bridge from finite-basis operator actions to the path trace formulas. -/

noncomputable section
open scoped BigOperators Matrix
open Module

namespace Problem335

section General
variable {I J P K V W : Type*}
  [Fintype I] [Fintype J] [Fintype P] [DecidableEq I] [DecidableEq J]
  [CommSemiring K] [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]

/-- An operator action described by weighted basis shifts has exactly the
corresponding path-shift matrix. No orthonormal structure is required here. -/
theorem toMatrix_eq_pathShiftMatrix
    (b : Basis I K V) (c : Basis J K W) (F : V →ₗ[K] W)
    (shift : I → P → J) (weight : I → P → K)
    (haction : ∀ i, F (b i) = ∑ p, weight i p • c (shift i p)) :
    LinearMap.toMatrix b c F = pathShiftMatrix shift weight := by
  classical
  ext j i
  rw [LinearMap.toMatrix_apply, haction]
  simp [pathShiftMatrix, map_sum, map_smul, Finsupp.single_apply]

end General

variable {I J P V W : Type*}
  [Fintype I] [Fintype J] [Fintype P] [DecidableEq I] [DecidableEq J]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- First trace for a finite-basis operator with collision-free path action. -/
theorem operator_first_trace_of_path_action
    (b : Basis I ℝ V) (c : Basis J ℝ W) (F : V →ₗ[ℝ] W)
    (shift : I → P → J) (weight : I → P → ℝ)
    (haction : ∀ i, F (b i) = ∑ p, weight i p • c (shift i p))
    (hdisjoint : ∀ i p q, p ≠ q → shift i p = shift i q →
      weight i p * weight i q = 0) :
    let A := LinearMap.toMatrix b c F
    Matrix.trace (A.transpose * A) = ∑ i, ∑ p, weight i p ^ 2 := by
  dsimp
  rw [toMatrix_eq_pathShiftMatrix b c F shift weight haction]
  exact pathShiftMatrix_first_trace shift weight hdisjoint

/-- First trace for the square-root occupation coefficients of the Fock basis. -/
theorem operator_first_trace_of_sqrt_path_action
    (b : Basis I ℝ V) (c : Basis J ℝ W) (F : V →ₗ[ℝ] W)
    (shift : I → P → J) (mass : I → P → ℝ)
    (haction : ∀ i, F (b i) = ∑ p, Real.sqrt (mass i p) • c (shift i p))
    (hnonneg : ∀ i p, 0 ≤ mass i p)
    (hdisjoint : ∀ i p q, p ≠ q → shift i p = shift i q →
      mass i p = 0 ∨ mass i q = 0) :
    let A := LinearMap.toMatrix b c F
    Matrix.trace (A.transpose * A) = ∑ i, ∑ p, mass i p := by
  dsimp
  rw [toMatrix_eq_pathShiftMatrix b c F shift (fun i p => Real.sqrt (mass i p)) haction]
  exact pathShiftMatrix_first_trace_sqrt shift mass hnonneg hdisjoint

/-- Exact second trace for an operator described on a finite basis by paths. -/
theorem operator_second_trace_of_path_action
    (b : Basis I ℝ V) (c : Basis J ℝ W) (F : V →ₗ[ℝ] W)
    (shift : I → P → J) (weight : I → P → ℝ)
    (haction : ∀ i, F (b i) = ∑ p, weight i p • c (shift i p)) :
    let A := LinearMap.toMatrix b c F
    Matrix.trace ((A.transpose * A) ^ 2) =
      ∑ i, ∑ k, ∑ p, ∑ q, ∑ r, ∑ s,
        if shift i p = shift k q ∧ shift i r = shift k s then
          weight i p * weight k q * weight i r * weight k s else 0 := by
  dsimp
  rw [toMatrix_eq_pathShiftMatrix b c F shift weight haction]
  exact pathShiftMatrix_second_trace_four_paths shift weight

/-- Coordinates after separate unit rescalings of the source and target bases. -/
theorem path_toMatrix_unitsSMul_apply {I : Type u_1} {J : Type u_2}
    {V : Type u_4} {W : Type u_5}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (b : Basis I ℝ V) (c : Basis J ℝ W) (F : V →ₗ[ℝ] W)
    (sourceScale : I → ℝˣ) (targetScale : J → ℝˣ) (j : J) (i : I) :
    LinearMap.toMatrix (b.unitsSMul sourceScale) (c.unitsSMul targetScale) F j i =
      (targetScale j : ℝ)⁻¹ * (sourceScale i : ℝ) * LinearMap.toMatrix b c F j i := by
  simp [LinearMap.toMatrix_apply, Basis.unitsSMul_apply, Basis.repr_unitsSMul,
    Units.smul_def, map_smul, Finsupp.smul_apply, mul_assoc, mul_left_comm]

/-- The path coefficient changes by the source/target normalization ratio.
This applies in particular to factorial-normalized monomial bases. -/
theorem toMatrix_normalized_path_action
    (b : Basis I ℝ V) (c : Basis J ℝ W) (F : V →ₗ[ℝ] W)
    (shift : I → P → J) (weight : I → P → ℝ)
    (haction : ∀ i, F (b i) = ∑ p, weight i p • c (shift i p))
    (sourceScale : I → ℝˣ) (targetScale : J → ℝˣ) :
    LinearMap.toMatrix (b.unitsSMul sourceScale) (c.unitsSMul targetScale) F =
      pathShiftMatrix shift (fun i p =>
        (targetScale (shift i p) : ℝ)⁻¹ * (sourceScale i : ℝ) * weight i p) := by
  classical
  ext j i
  rw [path_toMatrix_unitsSMul_apply, toMatrix_eq_pathShiftMatrix b c F shift weight haction]
  simp only [pathShiftMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : shift i p = j
  · simp [h]
  · simp [h]

end Problem335

end

end OAI
