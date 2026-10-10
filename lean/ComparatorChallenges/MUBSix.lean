import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

abbrev Coord := Fin 6
abbrev CMatrix := Matrix Coord Coord ℂ
abbrev Charge := Coord → ℤ

def IsHadamard (H : CMatrix) : Prop :=
  (∀ i j, Complex.normSq (H i j) = 1) ∧
  H.conjTranspose * H = (6 : ℂ) • (1 : CMatrix)

def character (x : Coord → ℂ) (a : Charge) : ℂ := ∏ i, x i ^ a i

def g (H : CMatrix) (a : Charge) : ℂ :=
  (6 : ℂ)⁻¹ * ∑ k, character (fun i => H i k) a

def alpha : Charge := ![1, 1, 1, -1, -1, -1]

def permuteCharge (π : Equiv.Perm Coord) (a : Charge) : Charge := a ∘ π

/-- Full Hadamard equivalence, with arbitrary unit complex phases. -/
def Equivalent (H K : CMatrix) : Prop :=
  ∃ (r c : Equiv.Perm Coord) (u v : Coord → ℂ),
    (∀ i, Complex.normSq (u i) = 1) ∧ (∀ j, Complex.normSq (v j) = 1) ∧
    ∀ i j, K i j = u i * H (r i) (c j) * v j

def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

/-- The five-cycle exponent matrix in equation (cubic-matrix).
The entries 2 represent the exponents -1 modulo three. -/
def taoExponent : Matrix Coord Coord ℕ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 1, 2, 2, 1;
     0, 1, 0, 1, 2, 2;
     0, 2, 1, 0, 1, 2;
     0, 2, 2, 1, 0, 1;
     0, 1, 2, 2, 1, 0]

def tao : CMatrix := fun i j => omega ^ taoExponent i j

abbrev Space := EuclideanSpace ℂ Coord
abbrev Basis := OrthonormalBasis Coord ℂ Space

def IsMUBFamily {n : ℕ} (B : Fin n → Basis) : Prop :=
  ∀ r s, r ≠ s → ∀ i j,
    Complex.normSq (inner ℂ (B r i) (B s j)) = (1 : ℝ) / 6

def Attainable (n : ℕ) : Prop := ∃ B : Fin n → Basis, IsMUBFamily B

theorem fourier_and_family_bound :
    (∀ H : CMatrix, IsHadamard H → ¬Equivalent H tao →
      ∀ π : Equiv.Perm Coord, g H (permuteCharge π alpha) = 0) ∧
    (∀ n : ℕ, Attainable n → n ≤ 5) := by
  sorry

end MUB6

end

end OAI
