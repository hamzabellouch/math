import Mathlib
import OAI.Analysis.Commutator.Pairings

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.Pairing

variable {J : Type*} [LinearOrder J]

abbrev Representatives (σ : Pairing J) := {j : J // j < σ j}

@[simp] theorem repr_representative (σ : Pairing J) (r : Representatives σ) :
    repr σ r = r := min_eq_left (le_of_lt r.property)

def pairEquiv (σ : Pairing J) : Representatives σ × Bool ≃ J :=
  Equiv.ofBijective (fun rb => if rb.2 then σ rb.1.1 else rb.1.1) (by
    constructor
    · rintro ⟨r, b⟩ ⟨s, c⟩ he
      have hr : r = s := by
        apply Subtype.ext
        have hh := congrArg (repr σ) he
        cases b <;> cases c <;> simpa only [Bool.false_eq_true, ↓reduceIte,
          repr_apply, repr_representative] using hh
      subst s
      congr 1
      cases b <;> cases c <;> simp_all only [Bool.false_eq_true, ↓reduceIte]
      · exact (σ.apply_ne r he.symm).elim
      · exact (σ.apply_ne r he).elim
    · intro j
      by_cases hj : j < σ j
      · exact ⟨(⟨j, hj⟩, false), rfl⟩
      · have hj' : σ j < j := lt_of_le_of_ne (le_of_not_gt hj) (σ.apply_ne j)
        refine ⟨(⟨σ j, ?_⟩, true), ?_⟩
        · simpa only [apply_apply] using hj'
        · exact σ.apply_apply j)

@[simp] theorem pairEquiv_false (σ : Pairing J) (r : Representatives σ) :
    pairEquiv σ (r, false) = r := rfl

@[simp] theorem pairEquiv_true (σ : Pairing J) (r : Representatives σ) :
    pairEquiv σ (r, true) = σ r := rfl

theorem prod_pairs [Fintype J] {R : Type*} [CommMonoid R]
    (σ : Pairing J) (f : J → R) :
    (∏ j, f j) = ∏ r : Representatives σ, f r * f (σ r) := by
  classical
  rw [← (pairEquiv σ).prod_comp f, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro r _
  rw [Fintype.prod_bool]
  simp only [pairEquiv_true, pairEquiv_false, mul_comm]

def pairFunctionEquiv (σ : Pairing J) (I : Type*) :
    (J → I) ≃ (Representatives σ → Bool → I) :=
  (Equiv.arrowCongr (pairEquiv σ).symm (Equiv.refl I)).trans
    (Equiv.curry (Representatives σ) Bool I)

@[simp] theorem pairFunctionEquiv_apply (σ : Pairing J) {I : Type*}
    (b : J → I) (r : Representatives σ) (v : Bool) :
    pairFunctionEquiv σ I b r v = b (pairEquiv σ (r, v)) := rfl

theorem sum_prod_pairs [Fintype J] {I R : Type*} [Fintype I] [CommSemiring R]
    (σ : Pairing J) (A : J → I → I → R) :
    (∑ b : J → I, ∏ j, A j (b (σ j)) (b j)) =
      ∏ r : Representatives σ, ∑ i : I, ∑ j : I, A r j i * A (σ r) i j := by
  classical
  calc
    _ = ∑ b : J → I, ∏ r : Representatives σ,
        A r (b (σ r)) (b r) * A (σ r) (b r) (b (σ r)) := by
      apply Finset.sum_congr rfl
      intro b _
      simpa only [apply_apply] using prod_pairs σ (fun j => A j (b (σ j)) (b j))
    _ = ∑ b : Representatives σ → Bool → I, ∏ r : Representatives σ,
        A r (b r true) (b r false) * A (σ r) (b r false) (b r true) := by
      apply Fintype.sum_equiv (pairFunctionEquiv σ I)
      intro b
      simp only [pairFunctionEquiv_apply, pairEquiv_true, pairEquiv_false]
    _ = ∏ r : Representatives σ, ∑ b : Bool → I,
        A r (b true) (b false) * A (σ r) (b false) (b true) := by
      exact (Fintype.prod_sum (fun (r : Representatives σ) (b : Bool → I) =>
        A r (b true) (b false) * A (σ r) (b false) (b true))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro r _
      have he := Fintype.sum_equiv (Equiv.boolArrowEquivProd I)
        (fun b : Bool → I => A r (b true) (b false) * A (σ r) (b false) (b true))
        (fun b : I × I => A r b.2 b.1 * A (σ r) b.1 b.2) (fun b => rfl)
      rw [Fintype.sum_prod_type] at he
      exact he

end Kadison.Pairing
end

end OAI
