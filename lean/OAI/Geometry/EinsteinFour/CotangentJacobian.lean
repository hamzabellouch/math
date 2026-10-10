import OAI.Geometry.EinsteinFour.CotangentHamiltonian
import OAI.Geometry.EinsteinFour.FourDeterminantDerivative
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Topology.Algebra.Module.Determinant

namespace OAI

/-! The eight-coordinate Jacobian calculation for the cotangent flow.
The variational equation is kept explicit here; it will be supplied by
the derivative of the actual flow with respect to its initial value. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

abbrev CotangentIndex := Fin 4 ⊕ Fin 4
abbrev CotangentMatrix := Matrix CotangentIndex CotangentIndex ℝ

def cotangentComponent (z : CotangentCoordinates) : CotangentIndex → ℝ :=
  Sum.elim (fun r => z.1 r) (fun r => z.2 r)

def cotangentDirection : CotangentIndex → CotangentCoordinates :=
  Sum.elim positionDirection momentumDirection

def cotangentBasis : Module.Basis CotangentIndex ℝ CotangentCoordinates :=
  (PiLp.basisFun 2 ℝ (Fin 4)).prod (PiLp.basisFun 2 ℝ (Fin 4))

theorem cotangentBasis_apply (i : CotangentIndex) :
    cotangentBasis i = cotangentDirection i := by
  cases i <;>
    simp [cotangentBasis, cotangentDirection, Module.Basis.prod_apply,
      positionDirection, momentumDirection, coordinateVector]

theorem cotangentBasis_repr (z : CotangentCoordinates) (i : CotangentIndex) :
    cotangentBasis.repr z i = cotangentComponent z i := by
  cases i <;> simp [cotangentBasis, cotangentComponent]

private def cotangentProjection (i : CotangentIndex) :
    CotangentCoordinates →L[ℝ] ℝ :=
  (cotangentBasis.coord i).toContinuousLinearMap

private theorem cotangentProjection_apply (i : CotangentIndex)
    (z : CotangentCoordinates) :
    cotangentProjection i z = cotangentComponent z i :=
  cotangentBasis_repr z i

def cotangentJacobian (X : CotangentCoordinates → CotangentCoordinates)
    (z : CotangentCoordinates) : CotangentMatrix :=
  fun i j => fderiv ℝ (fun w => cotangentComponent (X w) i) z
    (cotangentDirection j)

theorem cotangentJacobian_eq_toMatrix
    (X : CotangentCoordinates → CotangentCoordinates) (z : CotangentCoordinates)
    (hX : DifferentiableAt ℝ X z) :
    cotangentJacobian X z =
      LinearMap.toMatrix cotangentBasis cotangentBasis (fderiv ℝ X z).toLinearMap := by
  ext i j
  have h := (cotangentProjection i).hasFDerivAt.comp z hX.hasFDerivAt
  have he : (cotangentProjection i) ∘ X =
      fun w => cotangentComponent (X w) i := by
    funext w
    exact cotangentProjection_apply i (X w)
  rw [he] at h
  have hd : fderiv ℝ (fun w => cotangentComponent (X w) i) z =
      (cotangentProjection i).comp (fderiv ℝ X z) := by
    exact h.fderiv
  change fderiv ℝ (fun w => cotangentComponent (X w) i) z (cotangentDirection j) = _
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply, cotangentProjection_apply,
    LinearMap.toMatrix_apply, cotangentBasis_apply, cotangentBasis_repr]
  rfl

theorem cotangentJacobian_det
    (X : CotangentCoordinates → CotangentCoordinates) (z : CotangentCoordinates)
    (hX : DifferentiableAt ℝ X z) :
    (cotangentJacobian X z).det = (fderiv ℝ X z).det := by
  rw [cotangentJacobian_eq_toMatrix X z hX]
  exact LinearMap.det_toMatrix cotangentBasis (fderiv ℝ X z).toLinearMap

theorem cotangentJacobian_trace (X : CotangentCoordinates → CotangentCoordinates)
    (z : CotangentCoordinates) :
    (cotangentJacobian X z).trace = cotangentDivergence X z := by
  simp only [Matrix.trace, Matrix.diag, cotangentJacobian, Fintype.sum_sum_type,
    cotangentComponent, cotangentDirection, Sum.elim_inl, Sum.elim_inr]
  exact (Finset.sum_add_distrib).symm

theorem cotangentHamiltonian_jacobian_trace
    (H : CotangentCoordinates → ℝ) (z : CotangentCoordinates)
    (hH : ContDiffAt ℝ ∞ H z) :
    (cotangentJacobian (cotangentHamiltonianField H) z).trace = 0 := by
  rw [cotangentJacobian_trace]
  exact cotangentHamiltonian_divergence_zero H z hH

private def indexDeterminantForm {n : Type*} [Fintype n] [DecidableEq n] :
    (n → ℝ) [⋀^n]→L[ℝ] ℝ :=
  { (Matrix.detRowAlternating :
      (n → ℝ) [⋀^n]→ₗ[ℝ] ℝ) with
    cont := continuous_id.matrix_det }

private def indexDeterminantDifferential {n : Type*} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℝ) : Matrix n n ℝ →L[ℝ] ℝ :=
  indexDeterminantForm.toContinuousMultilinearMap.linearDeriv J

private theorem indexDeterminantDifferential_left {n : Type*} [Fintype n] [DecidableEq n]
    (J A : Matrix n n ℝ) :
    indexDeterminantDifferential J (A * J) = A.trace * J.det := by
  have hform : indexDeterminantDifferential J (A * J) =
      ∑ i, (J.updateRow i ((A * J) i)).det := by
    calc
      _ = ∑ i, indexDeterminantForm (Function.update J i ((A * J) i)) :=
        ContinuousMultilinearMap.linearDeriv_apply
          indexDeterminantForm.toContinuousMultilinearMap J (A * J)
      _ = _ := by
        simp only [Matrix.updateRow]
        rfl
  rw [hform]
  have hrow (i : n) : (A * J) i = ∑ r, A i r • J r := by
    ext j
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [hrow, Matrix.det_updateRow_sum, smul_eq_mul]
  exact (Finset.sum_mul _ _ _).symm

private theorem hasDerivAt_indexDeterminant {n : Type*} [Fintype n] [DecidableEq n]
    (J : ℝ → Matrix n n ℝ) (A : Matrix n n ℝ) (t : ℝ)
    (hJ : ∀ i j, HasDerivAt (fun s => J s i j) ((A * J t) i j) t) :
    HasDerivAt (fun s => (J s).det) (A.trace * (J t).det) t := by
  have hd : HasDerivAt J (A * J t) t :=
    hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mpr (hJ i))
  have h := (indexDeterminantForm.hasFDerivAt (J t)).comp_hasDerivAt t hd
  change HasDerivAt (fun s => (J s).det)
    (indexDeterminantDifferential (J t) (A * J t)) t at h
  rwa [indexDeterminantDifferential_left] at h

/-- Liouville's determinant identity in exactly the eight coordinates
needed for the cotangent bundle. No inverse of the Jacobian is needed. -/
theorem hasDerivAt_cotangentDeterminant (J : ℝ → CotangentMatrix)
    (A : CotangentMatrix) (t : ℝ)
    (hJ : ∀ i j, HasDerivAt (fun s => J s i j) ((A * J t) i j) t) :
    HasDerivAt (fun s => (J s).det) (A.trace * (J t).det) t :=
  hasDerivAt_indexDeterminant J A t hJ

/-- Once the actual flow derivative satisfies its variational equation,
the Hamiltonian mixed-derivative identity makes its determinant constant. -/
theorem cotangentHamiltonian_variational_det
    (H : CotangentCoordinates → ℝ) (γ : ℝ → CotangentCoordinates)
    (J : ℝ → CotangentMatrix) (a b s t : ℝ)
    (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b)
    (hH : ∀ r ∈ Set.Ioo a b, ContDiffAt ℝ ∞ H (γ r))
    (hJ : ∀ r ∈ Set.Ioo a b, ∀ i j,
      HasDerivAt (fun u => J u i j)
        ((cotangentJacobian (cotangentHamiltonianField H) (γ r) * J r) i j) r) :
    (J s).det = (J t).det := by
  have hd (r : ℝ) (hr : r ∈ Set.Ioo a b) :=
    hasDerivAt_cotangentDeterminant J
      (cotangentJacobian (cotangentHamiltonianField H) (γ r)) r (hJ r hr)
  have hz (r : ℝ) (hr : r ∈ Set.Ioo a b) :
      HasDerivAt (fun u => (J u).det) 0 r := by
    simpa only [cotangentHamiltonian_jacobian_trace H (γ r) (hH r hr), zero_mul]
      using hd r hr
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun r hr => (hz r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hz r hr).deriv) hs ht

/-- The derivative with respect to the initial point starts at the
identity matrix, so the constant Jacobian determinant is exactly one. -/
theorem cotangentHamiltonian_variational_det_one
    (H : CotangentCoordinates → ℝ) (γ : ℝ → CotangentCoordinates)
    (J : ℝ → CotangentMatrix) (a b t : ℝ)
    (hzero : 0 ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b)
    (hH : ∀ r ∈ Set.Ioo a b, ContDiffAt ℝ ∞ H (γ r))
    (hJ : ∀ r ∈ Set.Ioo a b, ∀ i j,
      HasDerivAt (fun u => J u i j)
        ((cotangentJacobian (cotangentHamiltonianField H) (γ r) * J r) i j) r)
    (hinit : J 0 = 1) : (J t).det = 1 := by
  have h := cotangentHamiltonian_variational_det H γ J a b 0 t hzero ht hH hJ
  rw [hinit, Matrix.det_one] at h
  exact h.symm

end
end PositiveEinsteinFour.Geometry

end OAI
