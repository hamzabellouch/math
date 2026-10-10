import Mathlib

namespace OAI

/-!
# The determinant-one linear substitution in the stabilization construction

This module formalizes the `L,N` change of variables in Section 2 of the source.
It uses six genuinely independent polynomial generators, in the order
`p,s,u,F,J,w`.  All results hold over any commutative coefficient ring.
-/

noncomputable section

namespace StableCoordinate.Linearization

open MvPolynomial

variable (k : Type*) [CommRing k]

abbrev P := MvPolynomial (Fin 6) k

/-- The part of the auxiliary quadratic not containing `p`. -/
def x0 : P k := X 1 ^ 2 - X 2 ^ 2

/-- The first new linear coordinate, denoted `L` in the manuscript. -/
def l : P k := x0 k ^ 2 * X 3 - (1 + 2 * X 1 * x0 k) * X 4

/-- The second new linear coordinate, denoted `N` in the manuscript. -/
def n : P k := (1 - 2 * X 1 * x0 k) * X 3 + 4 * X 1 ^ 2 * X 4

/-- The inverse formula for `F` in terms of the slots now called `L,N`. -/
def inverseF : P k := 4 * X 1 ^ 2 * X 3 + (1 + 2 * X 1 * x0 k) * X 4

/-- The inverse formula for `J` in terms of the slots now called `L,N`. -/
def inverseJ : P k := -(1 - 2 * X 1 * x0 k) * X 3 + x0 k ^ 2 * X 4

/-- Substitution `F ↦ L`, `J ↦ N`, fixing the other four generators. -/
def forward : P k →ₐ[k] P k :=
  aeval ![X 0, X 1, X 2, l k, n k, X 5]

/-- The inverse determinant-one substitution. -/
def backward : P k →ₐ[k] P k :=
  aeval ![X 0, X 1, X 2, inverseF k, inverseJ k, X 5]

@[simp] theorem forward_X (i : Fin 6) :
    forward k (X i) = ![X 0, X 1, X 2, l k, n k, X 5] i := by
  simp [forward]

@[simp] theorem backward_X (i : Fin 6) :
    backward k (X i) = ![X 0, X 1, X 2, inverseF k, inverseJ k, X 5] i := by
  simp [backward]

@[simp] theorem forward_x0 : forward k (x0 k) = x0 k := by
  simp [x0]

@[simp] theorem backward_x0 : backward k (x0 k) = x0 k := by
  simp [x0]

 theorem backward_comp_forward : (backward k).comp (forward k) = AlgHom.id k (P k) := by
  ext i : 1
  fin_cases i <;> simp [l, n, inverseF, inverseJ, map_ofNat] <;> ring

 theorem forward_comp_backward : (forward k).comp (backward k) = AlgHom.id k (P k) := by
  ext i : 1
  fin_cases i <;> simp [l, n, inverseF, inverseJ, map_ofNat] <;> ring

/-- The exact determinant-one `L,N` change is a polynomial algebra automorphism. -/
def equiv : P k ≃ₐ[k] P k :=
  AlgEquiv.ofAlgHom (forward k) (backward k)
    (forward_comp_backward k) (backward_comp_forward k)

@[simp] theorem equiv_apply (p : P k) : equiv k p = forward k p := rfl

@[simp] theorem equiv_symm_apply (p : P k) : (equiv k).symm p = backward k p := rfl

/-- The source's auxiliary quadratic including `p F`. -/
def x : P k := x0 k + X 0 * X 3

/-- The source hypersurface relation, extended by the independent variable `w`. -/
def h : P k := x k ^ 2 * X 3 - (1 + 2 * X 1 * x k) * X 4 - X 0 * X 4 ^ 2 - X 2

/-- The polynomial remainder `Q₀` in the source equation `H = L-u+p Q₀`. -/
def q0 : P k := 2 * x0 k * X 3 ^ 2 + X 0 * X 3 ^ 3 - 2 * X 1 * X 3 * X 4 - X 4 ^ 2

/-- The divisibility identity used to remove the nonlinear remainder. -/
theorem h_expansion : h k = l k - X 2 + X 0 * q0 k := by
  unfold h x l q0
  ring

/-- `Q₀` written in the new linear coordinates. -/
def qTrans : P k :=
  2 * x0 k * inverseF k ^ 2 + X 0 * inverseF k ^ 3 -
    2 * X 1 * inverseF k * inverseJ k - inverseJ k ^ 2

@[simp] theorem backward_q0 : backward k (q0 k) = qTrans k := by
  simp [q0, qTrans, map_ofNat]

@[simp] theorem backward_l : backward k (l k) = X 3 := by
  have hh := DFunLike.congr_fun (backward_comp_forward k) (X 3)
  simpa using hh

@[simp] theorem backward_n : backward k (n k) = X 4 := by
  have hh := DFunLike.congr_fun (backward_comp_forward k) (X 4)
  simpa using hh

/-- The source equation after the inverse `L,N` substitution. -/
theorem backward_h : backward k (h k) = X 3 - X 2 + X 0 * qTrans k := by
  rw [h_expansion]
  simp

/-- Subtract the transformed remainder from the independent new variable. -/
def minusShear : P k →ₐ[k] P k :=
  aeval ![X 0, X 1, X 2, X 3, X 4, X 5 - qTrans k]

/-- Inverse shear, adding the transformed remainder. -/
def plusShear : P k →ₐ[k] P k :=
  aeval ![X 0, X 1, X 2, X 3, X 4, X 5 + qTrans k]

@[simp] theorem minusShear_X (i : Fin 6) :
    minusShear k (X i) = ![X 0, X 1, X 2, X 3, X 4, X 5 - qTrans k] i := by
  simp [minusShear]

@[simp] theorem plusShear_X (i : Fin 6) :
    plusShear k (X i) = ![X 0, X 1, X 2, X 3, X 4, X 5 + qTrans k] i := by
  simp [plusShear]

@[simp] theorem minusShear_qTrans : minusShear k (qTrans k) = qTrans k := by
  simp [qTrans, inverseF, inverseJ, x0, map_ofNat]

@[simp] theorem plusShear_qTrans : plusShear k (qTrans k) = qTrans k := by
  simp [qTrans, inverseF, inverseJ, x0, map_ofNat]

 theorem plusShear_comp_minusShear :
    (plusShear k).comp (minusShear k) = AlgHom.id k (P k) := by
  ext i : 1
  fin_cases i <;> simp

 theorem minusShear_comp_plusShear :
    (minusShear k).comp (plusShear k) = AlgHom.id k (P k) := by
  ext i : 1
  fin_cases i <;> simp

/-- The independent-variable shear is a polynomial algebra automorphism. -/
def shearEquiv : P k ≃ₐ[k] P k :=
  AlgEquiv.ofAlgHom (minusShear k) (plusShear k)
    (minusShear_comp_plusShear k) (plusShear_comp_minusShear k)

@[simp] theorem shearEquiv_apply (p : P k) : shearEquiv k p = minusShear k p := rfl

/-- The full linearization automorphism, turning `H+p w` into an equation linear
in the slot formerly called `F`, while fixing `p`. -/
def normalization : P k ≃ₐ[k] P k :=
  (equiv k).symm.trans (shearEquiv k)

@[simp] theorem normalization_p : normalization k (X 0) = X 0 := by
  simp [normalization]

@[simp] theorem normalization_s : normalization k (X 1) = X 1 := by
  simp [normalization]

@[simp] theorem normalization_u : normalization k (X 2) = X 2 := by
  simp [normalization]

/-- The exact polynomial equation needed for the final variable elimination. -/
theorem normalization_stabilized_h :
    normalization k (h k + X 0 * X 5) = X 3 - X 2 + X 0 * X 5 := by
  change minusShear k (backward k (h k + X 0 * X 5)) = _
  simp [backward_h]
  ring

end StableCoordinate.Linearization

end

end OAI
