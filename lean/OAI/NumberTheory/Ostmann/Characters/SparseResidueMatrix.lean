import OAI.NumberTheory.Ostmann.Preliminaries.FiniteBlockMatrix

namespace OAI

/-! # Matrix form of the concrete local sparse kernel -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def sparseResidueMatrix {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (u v : ℂ) : Option (ZMod p) → Option (ZMod p) → ℂ :=
  finiteBlockMatrix (polydiscSparseScalar S E (u + v) (u * v))
    (polydiscSparseSide (Finset.univ \ S) S E (conj (u + v)) (conj (u * v)))
    (polydiscSparseSide S (Finset.univ \ S) E (u + v) (u * v))
    (polydiscLowerLinearMap S (Finset.univ \ S) E (u + v) (u * v))

noncomputable def residuePointCoordinates {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (a : ZMod p) : Option (ZMod p) → ℂ
  | none => 1
  | some x => centeredSupportProjection S (residuePointVector a) x

theorem sparseResidueMatrix_energy_le {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (hp : (100 : ℝ) ≤ p)
    (hlo : (1 / 3 : ℝ) ≤ residueDensity S) (hhi : residueDensity S ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform S b‖ ≤ ε ^ 2)
    (u v : ℂ) (hu : ‖u‖ ≤ 103 / 100) (hv : ‖v‖ ≤ 103 / 100)
    (f : Option (ZMod p) → ℂ) :
    let E := largeTransformSpectrum (normalizedResidueTransform S)
    (∑ x, ‖∑ y, sparseResidueMatrix S E u v x y * f y‖ ^ 2) ≤
      (1 + 3 / (p : ℝ)) ^ 2 * ∑ y, ‖f y‖ ^ 2 := by
  intro E
  rw [sparseResidueMatrix, finiteBlockMatrix_energy]
  simp only [polydiscLowerLinearMap_apply]
  have hh := local_sparse_polydisc S hS hSp hp hlo hhi ε hε hεsmall hL1 u v hu hv
    (f none) (fun y => f (some y))
  simpa only [Fintype.sum_option, ← residueVectorNorm_sq] using hh

theorem sparseResidueMatrix_point_identity {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (a b : ZMod p) (ha : a ∈ S) (hb : b ∈ Finset.univ \ S)
    (u v : ℂ) :
    (∑ x, conj (residuePointCoordinates S a x) *
      ∑ y, sparseResidueMatrix S E u v x y * residuePointCoordinates (Finset.univ \ S) b y) =
      (1 + u * localSparseKernel E (a - b)) * (1 + v * localSparseKernel E (a - b)) := by
  rw [sparseResidueMatrix, Fintype.sum_option, finiteBlockMatrix_apply_none]
  simp only [residuePointCoordinates, map_one, one_mul, mul_one]
  simp_rw [finiteBlockMatrix_apply_some, polydiscLowerLinearMap_apply]
  simp only [one_mul, mul_add, Finset.sum_add_distrib]
  linear_combination (polynomial_kernel_coordinate_identity S E a b ha hb u v).symm

/-- The sharper local estimate at `(1,1)` in the same finite matrix coordinates. -/
theorem sparseResidueMatrix_contraction {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (hp : (100 : ℝ) ≤ p)
    (hlo : (1 / 3 : ℝ) ≤ residueDensity S) (hhi : residueDensity S ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform S b‖ ≤ ε ^ 2)
    (f : Option (ZMod p) → ℂ) :
    let E := largeTransformSpectrum (normalizedResidueTransform S)
    let U := sparseKernelUnitFactor p ((E.card : ℝ) / p)
    (∑ x, ‖∑ y, sparseResidueMatrix S E 1 1 x y * f y‖ ^ 2) ≤
      (U * (1 - (8 / 5) / p)) ^ 2 * ∑ y, ‖f y‖ ^ 2 := by
  intro E U
  rw [sparseResidueMatrix, finiteBlockMatrix_energy]
  simp only [polydiscLowerLinearMap_apply]
  have hh := (local_sparse_kernel_contraction S hS hSp hp hlo hhi ε hε hεsmall hL1).2.2
    (f none) (fun y => f (some y))
  simpa only [polydiscSparseScalar, polydiscSparseSide, polydiscSparseLower,
    one_add_one_eq_two, one_mul, map_ofNat, map_one, localSparseScalar, localSparseSide,
    localSparseLower, Fintype.sum_option, ← residueVectorNorm_sq] using hh

end Ostmann

end OAI
