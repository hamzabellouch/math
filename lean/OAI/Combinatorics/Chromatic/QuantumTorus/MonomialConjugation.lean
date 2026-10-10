import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.RationalPureCoefficients
import OAI.Combinatorics.Chromatic.GradedAlgebra.NonpRegradeFaithful

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {K M:Type*} [Field K] [AddCommGroup M]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
local instance monomialConjugationRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance monomialConjugationAddCommMonoid : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance monomialConjugationAddGroup : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup

include hΩ
lemma X_mul_X_neg (b:M) : Torus.X v Ω b*Torus.X v Ω (-b)=1 := by
  rw [Torus.X_mul_X_of_pairing_zero v Ω b (-b) (by simp only [map_neg,hΩ,neg_zero])]
  simp only [add_neg_cancel]
  rfl

def monomialConjugate (b:M) (f:PowerSeries (Torus v Ω)) : PowerSeries (Torus v Ω):=
  PowerSeries.C (Torus.X v Ω b)*f*PowerSeries.C (Torus.X v Ω (-b))

lemma monomialConjugate_coeff (b:M) (f:PowerSeries (Torus v Ω)) (n:ℕ) (r:M) :
    coeff n (monomialConjugate v Ω b f) r=coeff n f r*(↑(v^(2*Ω b r)):K) := by
  rw [monomialConjugate,coeff_mul_C,coeff_C_mul]
  have H:=mul_X_coeff v Ω (Torus.X v Ω b*coeff n f) (r+b) (-b)
  rw [add_neg_cancel_right,X_mul_coeff] at H
  rw [H,map_add,AddMonoidHom.add_apply,map_neg,map_neg,hΩ,neg_zero,add_zero,
    alternating_skew Ω hΩ r b,neg_neg,mul_assoc,←Units.val_mul,←zpow_add]
  congr 3
  ring

lemma monomialConjugate_coeff_ne_iff (b:M) (f:PowerSeries (Torus v Ω)) (n:ℕ) (r:M) :
    coeff n (monomialConjugate v Ω b f) r≠0 ↔ coeff n f r≠0 := by
  rw [monomialConjugate_coeff v Ω hΩ]
  exact mul_ne_zero_iff.trans (and_iff_left (Units.ne_zero _))

lemma monomialConjugate_one (b:M) : monomialConjugate v Ω b 1=1 := by
  rw [monomialConjugate,mul_one,←map_mul,X_mul_X_neg v Ω hΩ,map_one]

lemma monomialConjugate_mul (b:M) (f g:PowerSeries (Torus v Ω)) :
    monomialConjugate v Ω b (f*g)=monomialConjugate v Ω b f*monomialConjugate v Ω b g := by
  have H:PowerSeries.C (Torus.X v Ω (-b))*PowerSeries.C (Torus.X v Ω b)=
      (1:PowerSeries (Torus v Ω)):=by
    rw [←map_mul]
    simpa only [neg_neg,map_one] using congrArg
      (PowerSeries.C : Torus v Ω → PowerSeries (Torus v Ω)) (X_mul_X_neg v Ω hΩ (-b))
  simp only [monomialConjugate]
  calc
    _=PowerSeries.C (Torus.X v Ω b)*f*1*g*PowerSeries.C (Torus.X v Ω (-b)):=by simp only [mul_one,mul_assoc]
    _= _ :=by rw [←H]; simp only [mul_assoc]

lemma monomialConjugate_regradeBound (b:M) (δ:M →+ ℤ) (B:ℕ) {f:PowerSeries (Torus v Ω)}
    (hf:RegradeBound v Ω δ B f) : RegradeBound v Ω δ B (monomialConjugate v Ω b f) := by
  intro n m hm
  exact hf n m ((monomialConjugate_coeff_ne_iff v Ω hΩ b f n m).mp hm)

lemma regrade_monomialConjugate (b:M) (δ:M →+ ℤ) (B:ℕ) (f:PowerSeries (Torus v Ω)) :
    regrade v Ω δ B (monomialConjugate v Ω b f)=
      monomialConjugate v Ω b (regrade v Ω δ B f) := by
  classical
  apply PowerSeries.ext
  intro d
  ext r
  rw [regrade_coeff_eval,monomialConjugate_coeff v Ω hΩ,regrade_coeff_eval]
  split_ifs
  · simp only [monomialConjugate_coeff v Ω hΩ,Finset.sum_mul]
  · rw [zero_mul]

end
end ElementaryPositivity.QuantumTorus
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I]
variable (v:(LaurentSeries ℚ)ˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
include hΩ in
lemma monomialConjugate_graded (C:(I → ℤ) →+ M) (b:M) {f:PowerSeries (Torus v Ω)}
    (hf:SeriesGraded v Ω C f) : SeriesGraded v Ω C (monomialConjugate v Ω b f) := by
  intro n m hm
  rw [monomialConjugate_coeff v Ω hΩ,hf n m hm,zero_mul]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
