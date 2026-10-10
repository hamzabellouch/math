import Mathlib
import OAI.Analysis.LaughlinFock.NormalOrdering

namespace OAI

/-! Creation Rows. -/
noncomputable section
namespace LaughlinFock
open scoped Matrix ComplexOrder Kronecker BigOperators

 

theorem creationRow_product (Q : ℕ) (i k : Orbital Q) (X Y : FockMatrix Q) :
    ((annihilator Q i)ᴴ * X)ᴴ * ((annihilator Q k)ᴴ * Y) =
      (if i = k then Xᴴ * Y else 0) -
        (annihilator Q k * X)ᴴ * (annihilator Q i * Y) := by
  have hCAR := eq_sub_of_add_eq (annihilator_adjoint_anticommute Q i k)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_mul]
  calc
    _ = Xᴴ * (annihilator Q i * (annihilator Q k)ᴴ) * Y := by
      simp only [Matrix.mul_assoc]
    _ = Xᴴ * ((if i = k then 1 else 0) - (annihilator Q k)ᴴ * annihilator Q i) * Y := by
      rw [hCAR]
    _ = _ := by
      split_ifs <;> simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
        Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_assoc]

 

theorem square_sum_expansion {β : Type*} [Fintype β] (Q : ℕ) (B : FockMatrix Q)
    (Y : β → FockMatrix Q) (ℓ : ℝ) (a : β → ℝ) :
    (ℓ • B + ∑ b, a b • Y b)ᴴ * (ℓ • B + ∑ b, a b • Y b) =
      ℓ^2 • (Bᴴ * B) +
      ∑ b, (ℓ * a b) • (Bᴴ * Y b + (Y b)ᴴ * B) +
      ∑ b, ∑ c, (a b * a c) • ((Y b)ᴴ * Y c) := by
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sum, star_trivial, Matrix.add_mul, Matrix.mul_add,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    smul_add, Finset.sum_add_distrib, Finset.smul_sum, pow_two]
  have hcomm : ∑ c, ∑ b, (a c * a b) • ((Y b)ᴴ * Y c) =
      ∑ b, ∑ c, (a b * a c) • ((Y b)ᴴ * Y c) := by
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [hcomm]
  simp only [mul_comm ℓ]
  abel

 

def auxiliaryRow {β : Type*} [Fintype β] (Q t : ℕ) (ℓ : ℝ)
    (p : β → ℕ) (i j : β → Orbital Q) (a : β → ℝ) : FockMatrix Q :=
  ℓ • pairAnnihilator Q t + ∑ b, a b •
    ((annihilator Q (i b))ᴴ * (annihilator Q (j b) * pairAnnihilator Q (p b)))

 
def rowTwoBody (Q t : ℕ) (ℓ : ℝ) : FockMatrix Q :=
  ℓ^2 • ((pairAnnihilator Q t)ᴴ * pairAnnihilator Q t)

 
def rowThreeBody {β : Type*} [Fintype β] (Q t : ℕ) (ℓ : ℝ)
    (p : β → ℕ) (i j : β → Orbital Q) (a : β → ℝ) : FockMatrix Q :=
  (∑ b, (ℓ*a b) •
    ((annihilator Q (i b) * pairAnnihilator Q t)ᴴ *
      (annihilator Q (j b) * pairAnnihilator Q (p b)) +
    (annihilator Q (j b) * pairAnnihilator Q (p b))ᴴ *
      (annihilator Q (i b) * pairAnnihilator Q t))) +
    ∑ b, ∑ c, (a b*a c) •
      (if i b = i c then
        (annihilator Q (j b) * pairAnnihilator Q (p b))ᴴ *
          (annihilator Q (j c) * pairAnnihilator Q (p c)) else 0)

 
def rowFourBody {β : Type*} [Fintype β] (Q : ℕ)
    (p : β → ℕ) (i j : β → Orbital Q) (a : β → ℝ) : FockMatrix Q :=
  -(∑ b, ∑ c, (a b*a c) •
    (annihilator Q (i c) * (annihilator Q (j b) * pairAnnihilator Q (p b)))ᴴ *
      (annihilator Q (i b) * (annihilator Q (j c) * pairAnnihilator Q (p c))))

 

theorem auxiliaryRow_square {β : Type*} [Fintype β] (Q t : ℕ) (ℓ : ℝ)
    (p : β → ℕ) (i j : β → Orbital Q) (a : β → ℝ) :
    (auxiliaryRow Q t ℓ p i j a)ᴴ * auxiliaryRow Q t ℓ p i j a =
      rowTwoBody Q t ℓ + rowThreeBody Q t ℓ p i j a + rowFourBody Q p i j a := by
  rw [auxiliaryRow, square_sum_expansion]
  simp_rw [creationRow_product]
  simp only [rowTwoBody, rowThreeBody, rowFourBody,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc, Matrix.smul_mul, smul_sub, Finset.sum_sub_distrib]
  abel

 

theorem rowTwoBody_mem (Q t : ℕ) (ℓ : ℝ) : rowTwoBody Q t ℓ ∈ BodySpace Q 2 :=
  Submodule.smul_of_tower_mem _ _ (bodySpace_product Q 2
    (pairAnnihilator_mem Q t) (pairAnnihilator_mem Q t))

theorem orbitalPair_mem (Q p : ℕ) (j : Orbital Q) :
    annihilator Q j * pairAnnihilator Q p ∈ AnnihilationSpace Q 3 :=
  annihilationSpace_mul Q 2 1 (pairAnnihilator_mem Q p) (annihilator_mem Q j)

theorem rowThreeBody_mem {β : Type*} [Fintype β] (Q t : ℕ) (ℓ : ℝ)
    (p : β → ℕ) (i j : β → Orbital Q) (a : β → ℝ) :
    rowThreeBody Q t ℓ p i j a ∈ BodySpace Q 3 := by
  classical
  apply Submodule.add_mem
  · apply Submodule.sum_mem
    intro b _
    apply Submodule.smul_of_tower_mem
    exact Submodule.add_mem _
      (bodySpace_product Q 3 (orbitalPair_mem Q t _) (orbitalPair_mem Q (p b) _))
      (bodySpace_product Q 3 (orbitalPair_mem Q (p b) _) (orbitalPair_mem Q t _))
  · apply Submodule.sum_mem
    intro b _
    apply Submodule.sum_mem
    intro c _
    apply Submodule.smul_of_tower_mem
    split_ifs
    · exact bodySpace_product Q 3 (orbitalPair_mem Q (p b) _) (orbitalPair_mem Q (p c) _)
    · exact Submodule.zero_mem _

theorem rowFourBody_mem {β : Type*} [Fintype β] (Q : ℕ)
    (p : β → ℕ) (i j : β → Orbital Q) (a : β → ℝ) :
    rowFourBody Q p i j a ∈ BodySpace Q 4 := by
  classical
  apply Submodule.neg_mem
  apply Submodule.sum_mem
  intro b _
  apply Submodule.sum_mem
  intro c _
  rw [Matrix.smul_mul]
  apply Submodule.smul_of_tower_mem
  apply bodySpace_product
  · exact annihilationSpace_mul Q 3 1 (orbitalPair_mem Q (p b) (j b))
      (annihilator_mem Q (i c))
  · exact annihilationSpace_mul Q 3 1 (orbitalPair_mem Q (p c) (j c))
      (annihilator_mem Q (i b))

 

theorem auxiliaryRow_decomposition_posSemidef {β : Type*} [Fintype β]
    (Q t : ℕ) (ℓ : ℝ) (p : β → ℕ) (i j : β → Orbital Q) (a : β → ℝ) :
    (rowTwoBody Q t ℓ + rowThreeBody Q t ℓ p i j a + rowFourBody Q p i j a).PosSemidef := by
  rw [← auxiliaryRow_square]
  exact Matrix.posSemidef_conjTranspose_mul_self _

 

def rowsComparison {ρ β : Type*} [Fintype ρ] [Fintype β]
    (Q : ℕ) (t : ρ → ℕ) (ℓ : ρ → ℝ) (p : ρ → β → ℕ)
    (i j : ρ → β → Orbital Q) (a : ρ → β → ℝ) : FockMatrix Q :=
  ∑ r, (auxiliaryRow Q (t r) (ℓ r) (p r) (i r) (j r) (a r))ᴴ *
    auxiliaryRow Q (t r) (ℓ r) (p r) (i r) (j r) (a r)

theorem rowsComparison_posSemidef {ρ β : Type*} [Fintype ρ] [Fintype β]
    (Q : ℕ) (t : ρ → ℕ) (ℓ : ρ → ℝ) (p : ρ → β → ℕ)
    (i j : ρ → β → Orbital Q) (a : ρ → β → ℝ) :
    (rowsComparison Q t ℓ p i j a).PosSemidef :=
  Matrix.posSemidef_sum _ (fun _ _ => Matrix.posSemidef_conjTranspose_mul_self _)

theorem rowsComparison_decomposition {ρ β : Type*} [Fintype ρ] [Fintype β]
    (Q : ℕ) (t : ρ → ℕ) (ℓ : ρ → ℝ) (p : ρ → β → ℕ)
    (i j : ρ → β → Orbital Q) (a : ρ → β → ℝ) :
    rowsComparison Q t ℓ p i j a = (∑ r, rowTwoBody Q (t r) (ℓ r)) +
      (∑ r, rowThreeBody Q (t r) (ℓ r) (p r) (i r) (j r) (a r)) +
      (∑ r, rowFourBody Q (p r) (i r) (j r) (a r)) := by
  simp only [rowsComparison, auxiliaryRow_square, Finset.sum_add_distrib]

end LaughlinFock
end

end OAI
