import Mathlib

namespace OAI

namespace ElementaryPositivity

structure NaturalUnitIntervalGraph (n : ℕ) where
  h : Fin n → Fin n
  increasing : Monotone h
  extensive : ∀ i, i ≤ h i

namespace NaturalUnitIntervalGraph

variable {n : ℕ} (G : NaturalUnitIntervalGraph n)

def Edge (i j : Fin n) : Prop :=
  (i < j ∧ j ≤ G.h i) ∨ (j < i ∧ i ≤ G.h j)

instance (i j : Fin n) : Decidable (G.Edge i j) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

def Nondescent (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, i.val + 1 = j.val → σ j < σ i → G.Edge (σ i) (σ j)

instance (σ : Equiv.Perm (Fin n)) : Decidable (G.Nondescent σ) :=
  inferInstanceAs (Decidable (∀ i j : Fin n,
    i.val + 1 = j.val → σ j < σ i → G.Edge (σ i) (σ j)))

def graphInversions (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun ij : Fin n × Fin n =>
    ij.1 < ij.2 ∧ σ ij.2 < σ ij.1 ∧ G.Edge (σ ij.1) (σ ij.2)).card

def Proper {r : ℕ} (f : Fin n → Fin r) : Prop :=
  ∀ i j : Fin n, G.Edge i j → f i ≠ f j

instance {r : ℕ} (f : Fin n → Fin r) : Decidable (G.Proper f) :=
  inferInstanceAs (Decidable (∀ i j : Fin n, G.Edge i j → f i ≠ f j))

def coloringAscents {r : ℕ} (f : Fin n → Fin r) : ℕ :=
  (Finset.univ.filter fun ij : Fin n × Fin n =>
    ij.1 < ij.2 ∧ G.Edge ij.1 ij.2 ∧ f ij.1 < f ij.2).card

noncomputable def chromatic (r : ℕ) : MvPolynomial (Fin r) (Polynomial ℕ) :=
  ∑ f ∈ Finset.univ.filter (G.Proper (r := r)),
    MvPolynomial.C (Polynomial.X ^ G.coloringAscents f) *
      ∏ i : Fin n, MvPolynomial.X (f i)

structure PermutationWitness where
  theta : {σ : Equiv.Perm (Fin n) // G.Nondescent σ} → Nat.Partition n
  expansion : ∀ r : ℕ, G.chromatic r =
    ∑ σ : {σ : Equiv.Perm (Fin n) // G.Nondescent σ},
      MvPolynomial.C (Polynomial.X ^ G.graphInversions σ.val) *
        MvPolynomial.esymmPart (Fin r) (Polynomial ℕ) (theta σ)

end NaturalUnitIntervalGraph
end ElementaryPositivity

def elementaryPositivityWitness (n : ℕ)
    (G : ElementaryPositivity.NaturalUnitIntervalGraph n) :
    G.PermutationWitness := by
  sorry

end OAI
