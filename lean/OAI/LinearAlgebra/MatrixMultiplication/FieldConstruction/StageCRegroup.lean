import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.CommonDimensions
import Mathlib.Data.Fintype.BigOperators

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation
open MatrixMultiplication.CommonDimensions

namespace MatrixMultiplication.AllFieldStageCRegroup

attribute [local instance] Classical.propDecidable Classical.decEq

variable {H B W F : Type*}

abbrev Positions (count : H → B → Bool → ℕ) (h : H) :=
  Σ b : B, Fin (count h b false)

abbrev PairedWords (count : H → B → Bool → ℕ) (W : Type*) :=
  ∀ h, Positions count h → W × W

abbrev SplitWords (count : H → B → Bool → ℕ) (W : Type*) :=
  ∀ h b r, Fin (count h b r) → W

def unpair (count : H → B → Bool → ℕ)
    (hc : ∀ h b r, count h b r = count h b false)
    (x : PairedWords count W) : SplitWords count W :=
  fun h b r i =>
    if r then (x h ⟨b, Fin.cast (hc h b r) i⟩).2
    else (x h ⟨b, Fin.cast (hc h b r) i⟩).1

def pair (count : H → B → Bool → ℕ)
    (hc : ∀ h b r, count h b r = count h b false)
    (x : SplitWords count W) : PairedWords count W :=
  fun h p => (x h p.1 false p.2, x h p.1 true (Fin.cast (hc h p.1 true).symm p.2))

theorem pair_unpair (count : H → B → Bool → ℕ)
    (hc : ∀ h b r, count h b r = count h b false)
    (x : PairedWords count W) : pair count hc (unpair count hc x) = x := by
  funext h p
  rfl

theorem unpair_pair (count : H → B → Bool → ℕ)
    (hc : ∀ h b r, count h b r = count h b false)
    (x : SplitWords count W) : unpair count hc (pair count hc x) = x := by
  funext h b r i
  cases r <;> rfl

def unpairEquiv (count : H → B → Bool → ℕ)
    (hc : ∀ h b r, count h b r = count h b false) :
    PairedWords count W ≃ SplitWords count W where
  toFun := unpair count hc
  invFun := pair count hc
  left_inv := pair_unpair count hc
  right_inv := unpair_pair count hc

variable [Fintype H] [Fintype B] [CommSemiring F]

def splitTensor (count : H → B → Bool → ℕ) (T : H → B → Bool → Tensor F W W W) :
    Tensor F (SplitWords count W) (SplitWords count W) (SplitWords count W) :=
  familyProduct fun h => familyProduct fun b => familyProduct fun r =>
    Tensor.power (T h b r) (count h b r)

def pairedTensor (count : H → B → Bool → ℕ) (T : H → B → Bool → Tensor F W W W) :
    Tensor F (PairedWords count W) (PairedWords count W) (PairedWords count W) :=
  familyProduct fun h => familyProduct fun p : Positions count h =>
    Tensor.product (T h p.1 false) (T h p.1 true)

private theorem prod_fin_cast {m n : ℕ} (e : m = n) (f : Fin n → F) :
    (∏ i : Fin m, f (Fin.cast e i)) = ∏ i : Fin n, f i := by
  subst n
  rfl

theorem pullback_unpair (count : H → B → Bool → ℕ)
    (hc : ∀ h b r, count h b r = count h b false)
    (T : H → B → Bool → Tensor F W W W) :
    Tensor.pullback (unpair count hc) (unpair count hc) (unpair count hc)
      (splitTensor count T) = pairedTensor count T := by
  funext x y z
  simp only [Tensor.pullback, splitTensor, pairedTensor, familyProduct]
  apply Finset.prod_congr rfl
  intro h _
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro b _
  rw [Fintype.prod_bool]
  change
    (∏ j : Fin (count h b true), T h b true
      (x h ⟨b, Fin.cast (hc h b true) j⟩).2
      (y h ⟨b, Fin.cast (hc h b true) j⟩).2
      (z h ⟨b, Fin.cast (hc h b true) j⟩).2) *
    (∏ j : Fin (count h b false), T h b false
      (x h ⟨b, j⟩).1 (y h ⟨b, j⟩).1 (z h ⟨b, j⟩).1) =
    ∏ j : Fin (count h b false),
      T h b false (x h ⟨b, j⟩).1 (y h ⟨b, j⟩).1 (z h ⟨b, j⟩).1 *
      T h b true (x h ⟨b, j⟩).2 (y h ⟨b, j⟩).2 (z h ⟨b, j⟩).2
  rw [prod_fin_cast (hc h b true) (fun j =>
    T h b true (x h ⟨b, j⟩).2 (y h ⟨b, j⟩).2 (z h ⟨b, j⟩).2),
    Finset.prod_mul_distrib]
  exact mul_comm _ _

end MatrixMultiplication.AllFieldStageCRegroup

end

end OAI
