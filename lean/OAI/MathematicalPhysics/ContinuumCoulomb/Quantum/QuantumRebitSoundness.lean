import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRealification

namespace OAI

/-! Realification preserves lower quadratic bounds on all complex vectors,
not only on the real-coordinate encoding of a witness. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators

def qmaRealVector {ι : Type*} (u : ι → ℂ) : ι → ℂ := fun i => (u i).re

def qmaImagVector {ι : Type*} (u : ι → ℂ) : ι → ℂ := fun i => (u i).im

theorem qmaQuadratic_real_split {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ)
    (hM : ∀ i j, (M i j).im = 0) (u : ι → ℂ) :
    qmaQuadratic M u = qmaQuadratic M (qmaRealVector u)+qmaQuadratic M (qmaImagVector u) := by
  simp [qmaQuadratic,qmaRealVector,qmaImagVector,Matrix.mulVec,dotProduct,
    Complex.re_sum,Complex.mul_re,Complex.mul_im,hM,
    Finset.sum_add_distrib,Finset.mul_sum]

def qmaUnrebitReal {ι : Type*} (v : Fin 2 × ι → ℂ) : ι → ℂ :=
  fun i => ⟨(v (0,i)).re,(v (1,i)).re⟩

def qmaUnrebitImag {ι : Type*} (v : Fin 2 × ι → ℂ) : ι → ℂ :=
  fun i => ⟨(v (0,i)).im,(v (1,i)).im⟩

theorem qmaRebitVector_unrebitReal {ι : Type*} (v : Fin 2 × ι → ℂ) :
    qmaRebitVector (qmaUnrebitReal v) = qmaRealVector v := by
  funext p
  rcases p with ⟨b,i⟩
  fin_cases b <;> simp [qmaRebitVector,qmaUnrebitReal,qmaRealVector]

theorem qmaRebitVector_unrebitImag {ι : Type*} (v : Fin 2 × ι → ℂ) :
    qmaRebitVector (qmaUnrebitImag v) = qmaImagVector v := by
  funext p
  rcases p with ⟨b,i⟩
  fin_cases b <;> simp [qmaRebitVector,qmaUnrebitImag,qmaImagVector]

theorem qmaRebitMatrix_quadratic_split {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (v : Fin 2 × ι → ℂ) :
    qmaQuadratic (qmaRebitMatrix A) v =
      qmaQuadratic A (qmaUnrebitReal v)+qmaQuadratic A (qmaUnrebitImag v) := by
  rw [qmaQuadratic_real_split _ (qmaRebitMatrix_real A),
    ←qmaRebitVector_unrebitReal,←qmaRebitVector_unrebitImag,
    qmaRebitMatrix_quadratic,qmaRebitMatrix_quadratic]

theorem qmaRebitVector_mass_split {ι : Type*} [Fintype ι] (v : Fin 2 × ι → ℂ) :
    (∑ p, Complex.normSq (v p)) =
      (∑ i, Complex.normSq (qmaUnrebitReal v i))+
      ∑ i, Complex.normSq (qmaUnrebitImag v i) := by
  simp [qmaUnrebitReal,qmaUnrebitImag,Fintype.sum_prod_type,Fin.sum_univ_two,
    Complex.normSq_apply,Finset.sum_add_distrib]

theorem qmaRebitMatrix_lower {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (C D : ℝ)
    (hA : ∀ u : ι → ℂ, C*(∑ i, Complex.normSq (u i)) ≤ D*qmaQuadratic A u)
    (v : Fin 2 × ι → ℂ) :
    C*(∑ p, Complex.normSq (v p)) ≤ D*qmaQuadratic (qmaRebitMatrix A) v := by
  rw [qmaRebitVector_mass_split,qmaRebitMatrix_quadratic_split]
  have hr := hA (qmaUnrebitReal v)
  have hi := hA (qmaUnrebitImag v)
  nlinarith

end ContinuumCoulomb

end

end OAI
