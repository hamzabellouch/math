import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationCentered

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem centeredProduct_intCast {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (n : ℤ) :
    centeredProduct p hcop S (n : ZMod (∏ i, p i)) =
      ∏ i, (Supply.centeredIndicator (S i) (n : ZMod (p i)) : ℂ) := by
  unfold centeredProduct
  simp only [map_intCast, Pi.intCast_apply]

theorem subset_pairwise_coprime {ι : Type*} (p : ι → ℕ)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j))) (U : Finset ι) :
    Pairwise (fun i j : U => (p i).Coprime (p j)) := by
  intro i j hij
  exact hcop (fun h => hij (Subtype.ext h))

def subsetCenteredProduct {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (U : Finset ι) : ZMod (∏ i : U, p i) → ℂ :=
  centeredProduct (fun i : U => p i) (subset_pairwise_coprime p hcop U) (fun i => S i)

theorem subsetCenteredProduct_intCast {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (U : Finset ι) (n : ℤ) :
    subsetCenteredProduct p hcop S U (n : ZMod (∏ i : U, p i)) =
      ∏ i ∈ U, (Supply.centeredIndicator (S i) (n : ZMod (p i)) : ℂ) := by
  rw [subsetCenteredProduct, centeredProduct_intCast]
  exact Finset.prod_coe_sort U (fun i => (Supply.centeredIndicator (S i) (n : ZMod (p i)) : ℂ))

theorem amplifier_subset_expansion {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (lam : ℝ) (n : ℤ) :
    (amplifier p hcop S lam (n : ZMod (∏ i, p i)) : ℂ) =
      ∑ U : Finset ι, (lam : ℂ) ^ U.card *
        subsetCenteredProduct p hcop S U (n : ZMod (∏ i : U, p i)) := by
  classical
  unfold amplifier
  simp only [map_intCast, Pi.intCast_apply, Complex.ofReal_prod, Complex.ofReal_add,
    Complex.ofReal_one, Complex.ofReal_mul]
  rw [Finset.prod_one_add]
  simp only [Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro U hU
  rw [subsetCenteredProduct_intCast, Finset.prod_mul_distrib, Finset.prod_const]

theorem subset_modulus_pos {ι : Type*} (p : ι → ℕ) [∀ i, NeZero (p i)] (U : Finset ι) :
    0 < ∏ i : U, p i := by
  exact Finset.prod_pos (fun i _ => Nat.pos_of_neZero (p i))

end Ostmann.QuadraticCenter

end

end OAI
