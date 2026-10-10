import OAI.Algebra.DepthFive.FactorialPositive
import OAI.Algebra.DepthFive.FourPathLocal

namespace OAI

/-! The actual local four-path table has bounded nonnegative factorial expansions. -/
namespace Problem335

open scoped BigOperators

namespace FactorialExpansion

variable {σ : Type*} [Fintype σ]

/-- Enlarge the permitted support and total-order bound. -/
def weaken {f : (σ → ℕ) → ℕ} {S T : Finset σ} {D E : ℕ}
    (F : FactorialExpansion f S D) (hS : S ⊆ T) (hD : D ≤ E) :
    FactorialExpansion f T E where
  Index := F.Index
  indexFintype := F.indexFintype
  coeff := F.coeff
  degree := F.degree
  order_le := fun j => (F.order_le j).trans hD
  supported := fun j i hi => F.supported j i (fun h => hi (hS h))
  eval_eq := F.eval_eq

end FactorialExpansion

namespace LocalMoments

variable {σ : Type*} [DecidableEq σ]

/-- Natural-valued version of the exact local table. -/
def localPolynomialNat (derivative : Bool) (M : σ → ℕ) (p q r : σ) : ℕ :=
  if p = q then
    if derivative then M p * M r else (M p + 1) * (M r + 1)
  else if derivative then M p * (M q + 1) else (M p + 1) * M q

@[simp] theorem localPolynomialNat_cast (derivative : Bool) (M : σ → ℕ) (p q r : σ) :
    (localPolynomialNat derivative M p q r : ℝ) = localPolynomial derivative M p q r := by
  cases derivative <;> by_cases h : p = q <;> simp [localPolynomialNat, localPolynomial, mass, h]

/-- All branches of the local four-path table have total factorial order at most two.
The normal branch includes coincident coordinates and their first-order corrections. -/
def localPolynomialExpansion [Fintype σ] (derivative : Bool) (p q r : σ) :
    FactorialExpansion (fun M => localPolynomialNat derivative M p q r) {p, q, r} 2 := by
  have hpr : ({p, r} : Finset σ) ⊆ {p, q, r} := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at *
    tauto
  have hpq : ({p, q} : Finset σ) ⊆ {p, q, r} := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at *
    tauto
  cases derivative
  · by_cases h : p = q
    · exact (FactorialExpansion.normalMultiplication p r).reframe
        (by intro M; simp [localPolynomialNat, h]) hpr (le_refl 2)
    · exact (FactorialExpansion.distinctMultiplication p q h).reframe
        (by intro M; simp [localPolynomialNat, h]) hpq (le_refl 2)
  · by_cases h : p = q
    · exact (FactorialExpansion.normalDerivative p r).reframe
        (by intro M; simp [localPolynomialNat, h]) hpr (le_refl 2)
    · exact (FactorialExpansion.distinctDerivative p q h).reframe
        (by intro M; simp [localPolynomialNat, h]) hpq (le_refl 2)

/-- The natural polynomial for a finite set of layers. -/
def localProductNat {ι : Type*} (layers : Finset ι) (derivative : ι → Bool)
    (p q r : ι → σ) (M : σ → ℕ) : ℕ :=
  ∏ t ∈ layers, localPolynomialNat (derivative t) M (p t) (q t) (r t)

@[simp] theorem localProductNat_cast {ι : Type*} (layers : Finset ι)
    (derivative : ι → Bool) (p q r : ι → σ) (M : σ → ℕ) :
    (localProductNat layers derivative p q r M : ℝ) =
      ∏ t ∈ layers, localPolynomial (derivative t) M (p t) (q t) (r t) := by
  simp [localProductNat]

/-- This finite product is the exact nonnegative factorial expansion required
by the occupation-moment comparison, rather than an assumed positivity property. -/
theorem localProduct_expansion {ι : Type*} [Fintype σ] (layers : Finset ι)
    (derivative : ι → Bool) (p q r : ι → σ)
    (hdis : (layers : Set ι).Pairwise fun i j =>
      Disjoint ({p i, q i, r i} : Finset σ) {p j, q j, r j}) :
    Nonempty (FactorialExpansion (localProductNat layers derivative p q r)
      (layers.biUnion fun i => {p i, q i, r i}) (2 * layers.card)) := by
  have h := FactorialExpansion.nonempty_prod layers
    (fun i M => localPolynomialNat (derivative i) M (p i) (q i) (r i))
    (fun i => {p i, q i, r i}) (fun _ => 2)
    (fun i => localPolynomialExpansion (derivative i) (p i) (q i) (r i)) hdis
  convert h using 1
  simp [Nat.mul_comm]
  congr 1

/-- Layer-labelled coordinates automatically have disjoint local supports. -/
theorem layered_support_disjoint {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (layers : Finset ι) (p q r : ι → κ) :
    (layers : Set ι).Pairwise fun i j =>
      Disjoint ({(i, p i), (i, q i), (i, r i)} : Finset (ι × κ))
        {(j, p j), (j, q j), (j, r j)} := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hx' : x.1 = i := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h <;> simp [h]
  have hy' : x.1 = j := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h | h <;> simp [h]
  exact hij (hx'.symm.trans hy')

/-- Specialization to the actual matrix-layer coordinate shape. -/
theorem layered_localProduct_expansion {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (layers : Finset ι) (derivative : ι → Bool) (p q r : ι → κ) :
    Nonempty (FactorialExpansion
      (localProductNat layers derivative (fun i => (i, p i))
        (fun i => (i, q i)) (fun i => (i, r i)))
      (layers.biUnion fun i => {(i, p i), (i, q i), (i, r i)}) (2 * layers.card)) :=
  localProduct_expansion layers derivative _ _ _ (layered_support_disjoint layers p q r)

end LocalMoments
end Problem335

end OAI
