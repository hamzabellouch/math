import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.NonpRegradeFaithful

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M:Type*} [CommRing R] [AddCommGroup M]
variable (v:Rˣ) (Ω:M →+ M →+ ℤ)
local instance rootCoefficientsRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance rootCoefficientsAddCommMonoid : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance rootCoefficientsAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

def actualRootCoefficient (τ:M →+ ℤ) (f:PowerSeries (Torus v Ω)) (m:M) : R :=
  if 0≤τ m then coeff (τ m).toNat f m else 0

lemma actualRootCoefficient_read (τ:M →+ ℤ) (f:PowerSeries (Torus v Ω)) (n:ℕ) (m:M)
    (hm:τ m=(n:ℤ)) : actualRootCoefficient v Ω τ f m=coeff n f m := by
  simp only [actualRootCoefficient,hm,Int.natCast_nonneg,ite_true,Int.toNat_natCast]

lemma regrade_actualRootCoefficient (τ δ:M →+ ℤ) (B:ℕ) (f:PowerSeries (Torus v Ω))
    (hf:RegradeBound v Ω δ B f) (hτ:FullHomogeneous v Ω τ f) (m:M) :
    actualRootCoefficient v Ω δ (regrade v Ω δ B f) m=actualRootCoefficient v Ω τ f m := by
  classical
  by_cases ht:0≤τ m
  · by_cases hd:0≤δ m
    · simp only [actualRootCoefficient,ite_eq_left ht,ite_eq_left hd]
      exact regrade_read v Ω δ B τ hf hτ _ m (Int.toNat_of_nonneg ht).symm
    · have hz:coeff (τ m).toNat f m=0:=by
        by_contra hh
        exact hd (hf _ m hh).1
      simp only [actualRootCoefficient,ite_eq_left ht,ite_eq_right hd,hz]
  · have hz:∀n,coeff n f m=0:=by
      intro n
      by_contra hh
      have H:=hτ n m hh
      exact ht (H ▸ Int.natCast_nonneg n)
    simp only [actualRootCoefficient,ite_eq_right ht,regrade_coeff_eval]
    split_ifs <;> simp only [hz,Finset.sum_const_zero]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
