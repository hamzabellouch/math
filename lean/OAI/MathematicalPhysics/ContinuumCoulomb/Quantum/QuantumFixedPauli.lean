import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumAlgebraicScalar
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliReal

namespace OAI

/-! Fixed-arity Pauli traces evaluated entirely in rational registers.
The interpretation is the actual complex Pauli coefficient, not an
assumed list of Hamiltonian coefficients. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFixedPauli
open QuantumAlgebraicScalar Matrix
open scoped BigOperators Classical

def enumerate (α : Type) [Fintype α] : List α :=
  List.ofFn (Fintype.equivFin α).symm

def finiteSum {α : Type} [Fintype α] (f : α → Scalar) : Scalar :=
  QuantumAlgebraicScalar.sum ((enumerate α).map f)

def finiteProduct {α : Type} [Fintype α] (f : α → Scalar) : Scalar :=
  QuantumAlgebraicScalar.product ((enumerate α).map f)

theorem value_finiteSum {α : Type} [Fintype α] (f : α → Scalar) :
    value (finiteSum f) = ∑ a, value (f a) := by
  simp only [finiteSum,value_sum,enumerate,List.map_ofFn,List.sum_ofFn]
  exact (Fintype.equivFin α).symm.sum_comp (fun a => value (f a))

theorem value_finiteProduct {α : Type} [Fintype α] (f : α → Scalar) :
    value (finiteProduct f) = ∏ a, value (f a) := by
  simp only [finiteProduct,value_product,enumerate,List.map_ofFn,List.prod_ofFn]
  exact (Fintype.equivFin α).symm.prod_comp (fun a => value (f a))

def pauli (μ : Fin 4) : Matrix (Fin 2) (Fin 2) Scalar :=
  ![!![rat 1,rat 0;rat 0,rat 1],
    !![rat 0,rat 1;rat 1,rat 0],
    !![rat 0,neg imaginary;imaginary,rat 0],
    !![rat 1,rat 0;rat 0,rat (-1)]] μ

theorem value_pauli (μ : Fin 4) (a b : Fin 2) :
    value (pauli μ a b) = qmaPauli μ a b := by
  fin_cases μ <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauli,qmaPauli,pauliX,pauliY,pauliZ]

def word {ι : Type} [Fintype ι] (w : ι → Fin 4) (s t : ι → Fin 2) : Scalar :=
  finiteProduct (fun i => pauli (w i) (s i) (t i))

theorem value_word {ι : Type} [Fintype ι] [DecidableEq ι]
    (w : ι → Fin 4) (s t : ι → Fin 2) :
    value (word w s t) = qmaPauliWord w s t := by
  rw [word,value_finiteProduct]
  simp only [value_pauli,qmaPauliWord]

def coefficient {ι : Type} [Fintype ι] (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar)
    (w : ι → Fin 4) : Scalar :=
  mul (rat ((2:ℚ)^Fintype.card ι)⁻¹)
    (finiteSum (fun s => finiteSum (fun t => mul (A s t) (word w t s))))

theorem value_coefficient {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar) (w : ι → Fin 4) :
    value (coefficient A w) = qmaPauliCoefficient (fun s t => value (A s t)) w := by
  simp only [coefficient,value_mul,value_rat,value_finiteSum,value_word,
    qmaPauliCoefficient,Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat]
  norm_num
  apply Finset.sum_congr (by ext; simp)
  intro s _
  apply Finset.sum_congr (by ext; simp)
  intro t _
  rfl

def realCoefficient {ι : Type} [Fintype ι]
    (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar) (w : ι → Fin 4) : RealScalar :=
  (coefficient A w).1

theorem realCoefficient_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar) (w : ι → Fin 4) :
    realValue (realCoefficient A w) =
      (qmaPauliCoefficient (fun s t => value (A s t)) w).re := by
  rw [← value_coefficient]
  exact (value_re _).symm

theorem realCoefficient_expansion {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar)
    (hA : Matrix.IsHermitian (fun s t => value (A s t))) :
    (∑ w : ι → Fin 4, (realValue (realCoefficient A w):ℂ) • qmaPauliWord w) =
      (fun s t => value (A s t)) := by
  simp only [realCoefficient_eq]
  exact qmaPauli_real_expansion _ hA

/-- This entrywise attachment applies to the actual local core of an
ordered history term once its six-site table has been constructed. -/
theorem coefficient_of_entries {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar)
    (H : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (hA : ∀ s t, value (A s t) = H s t) (w : ι → Fin 4) :
    realValue (realCoefficient A w) = (qmaPauliCoefficient H w).re := by
  rw [realCoefficient_eq]
  have he : (fun s t => value (A s t)) = H := funext (fun s => funext (hA s))
  rw [he]

theorem sample_error {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar) (w : ι → Fin 4) (k : ℕ) :
    |(QuantumAlgebraicScalar.sample k (realCoefficient A w):ℝ)-
      (qmaPauliCoefficient (fun s t => value (A s t)) w).re| ≤
        |((realCoefficient A w).2:ℝ)| * (2:ℝ)⁻¹^k := by
  rw [← realCoefficient_eq]
  exact QuantumAlgebraicScalar.sample_error k _

end ContinuumCoulomb.QuantumFixedPauli

end

end OAI
