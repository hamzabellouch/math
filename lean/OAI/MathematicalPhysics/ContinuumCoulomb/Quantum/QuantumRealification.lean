import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumUnarySpectrum

namespace OAI

/-! One extra real qubit represents the real and imaginary coordinates of
an arbitrary complex Hamiltonian without changing its quadratic energy. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators

def qmaRebitMatrix {ι : Type*} (A : Matrix ι ι ℂ) : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ :=
  fun p q => if p.1 = q.1 then (A p.2 q.2).re else
    if p.1 = 0 then -(A p.2 q.2).im else (A p.2 q.2).im

def qmaRebitVector {ι : Type*} (u : ι → ℂ) : Fin 2 × ι → ℂ :=
  fun p => if p.1 = 0 then (u p.2).re else (u p.2).im

theorem qmaRebitMatrix_real {ι : Type*} (A : Matrix ι ι ℂ) (p q : Fin 2 × ι) :
    (qmaRebitMatrix A p q).im = 0 := by
  simp only [qmaRebitMatrix]
  split
  · rfl
  · split <;> simp

theorem qmaRebitMatrix_hermitian {ι : Type*} (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (qmaRebitMatrix A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  rintro ⟨a,i⟩ ⟨b,j⟩
  have h := hA.apply i j
  have hr : (A j i).re = (A i j).re := by simpa using congrArg Complex.re h
  have hi : -(A j i).im = (A i j).im := by simpa using congrArg Complex.im h
  fin_cases a <;> fin_cases b <;> simp [qmaRebitMatrix,hr]
  · exact_mod_cast (show (A j i).im = -(A i j).im by linarith)
  · exact_mod_cast hi

theorem qmaRebitVector_mass {ι : Type*} [Fintype ι] (u : ι → ℂ) :
    (∑ p : Fin 2 × ι, Complex.normSq (qmaRebitVector u p)) = ∑ i, Complex.normSq (u i) := by
  simp [qmaRebitVector,Fintype.sum_prod_type,Fin.sum_univ_two,Complex.normSq_apply,
    Finset.sum_add_distrib]

theorem qmaRebitVector_inner {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    (star (qmaRebitVector u) ⬝ᵥ qmaRebitVector v).re = (star u ⬝ᵥ v).re := by
  simp [qmaRebitVector,dotProduct,Fintype.sum_prod_type,Fin.sum_univ_two,
    Complex.re_sum,Complex.mul_re,Finset.sum_add_distrib]

theorem qmaRebitMatrix_mulVec {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (u : ι → ℂ) :
    (qmaRebitMatrix A).mulVec (qmaRebitVector u) = qmaRebitVector (A.mulVec u) := by
  funext p
  rcases p with ⟨b,i⟩
  fin_cases b <;> apply Complex.ext <;>
    simp [qmaRebitMatrix,qmaRebitVector,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
      Fin.sum_univ_two,Complex.re_sum,Complex.im_sum,Complex.mul_re,Complex.mul_im,
      Finset.sum_add_distrib,Finset.sum_sub_distrib]
  all_goals ring

theorem qmaRebitMatrix_quadratic {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (u : ι → ℂ) :
    qmaQuadratic (qmaRebitMatrix A) (qmaRebitVector u) = qmaQuadratic A u := by
  rw [qmaQuadratic,qmaRebitMatrix_mulVec,qmaRebitVector_inner]
  rfl

end ContinuumCoulomb

end

end OAI
