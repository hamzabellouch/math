import OAI.NumberTheory.Ostmann.Construction.IntegerPivotExtension

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

def externalPivotWeight (G : ℝ) (p : ℕ) : ℝ :=
  Real.exp (-G)*Ostmann.smoothPartition (Real.log p-G)

theorem externalPivotWeight_nonneg (G : ℝ) (p : ℕ) : 0≤externalPivotWeight G p :=
  mul_nonneg (Real.exp_pos _).le (Ostmann.smoothPartition_nonneg _)

theorem externalPivotWeight_mass_le {G : ℝ} (hG : 0≤G) :
    (∑p∈integerPivotCell G,externalPivotWeight G p)≤Real.exp 1+1 := by
  calc
    _ ≤ ∑_p∈integerPivotCell G,Real.exp (-G) := by
      apply Finset.sum_le_sum
      intro p hp
      exact (mul_le_mul_of_nonneg_left (Ostmann.smoothPartition_le_one _) (Real.exp_pos _).le).trans_eq (mul_one _)
    _ = (⌈Real.exp (G+1)⌉₊:ℝ)*Real.exp (-G) := by
      simp only [Finset.sum_const,integerPivotCell,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul]
    _ ≤ (Real.exp (G+1)+1)*Real.exp (-G) :=
      mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (Real.exp_pos _).le).le (Real.exp_pos _).le
    _ = Real.exp 1+Real.exp (-G) := by
      rw [add_mul,one_mul,←Real.exp_add]
      congr 1
      congr 1
      ring
    _ ≤ Real.exp 1+1 := add_le_add (le_refl _) ((Real.exp_le_exp.mpr (neg_nonpos.mpr hG)).trans_eq Real.exp_zero)

theorem counterpart_scalar_extraction (G B Δ C H U φ κ : ℝ) :
    U*φ*(C/H*κ)=C*Real.exp (-Δ)*(Real.exp (-G)*φ)*
      ((Real.exp (G+B+Δ)/H)*(U/Real.exp B)*κ) := by
  have he : Real.exp (-Δ)*Real.exp (-G)*Real.exp (G+B+Δ)=Real.exp B := by
    rw [←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  calc
    _ = C*φ*(U/H)*κ := by ring
    _ = C*φ*(U/H)*κ*(Real.exp B/(Real.exp B)) := by rw [div_self (Real.exp_ne_zero _),mul_one]
    _ = C*φ*(U/H)*κ*((Real.exp (-Δ)*Real.exp (-G)*Real.exp (G+B+Δ))/(Real.exp B)) := by rw [he]
    _ = _ := by ring

end Ostmann.Construction

end

end OAI
