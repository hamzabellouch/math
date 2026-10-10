import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.RationalCenteredAction

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open WallUnits
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)

lemma centeredCrossing_zero (p m : M) : centeredCrossing v Ω p m 0 = Torus.X v Ω m := by
  simp [centeredCrossing,centeredPolynomial,Torus.X]

lemma centeredCrossing_one (p m : M) : centeredCrossing v Ω p m 1 =
    Torus.X v Ω m + Torus.X v Ω (m+p) := by
  simp [centeredCrossing,centeredPolynomial,centeredExponent,Fin.sum_univ_two,Torus.X,Polynomial.coeff_one]
end
end ElementaryPositivity.QuantumTorus

namespace ElementaryPositivity.RationalFiber
open QuantumTorus WallUnits
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀ m, Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
include hΩ in
lemma pureAction_pairing_zero (m : M) (hm : Ω p m=0) :
    pureAction v (complementOmega k Ω) (complementAlpha k p Ω)
      (embed v Ω hΩ k p hp (Torus.X v Ω m)) =
      embed v Ω hΩ k p hp (Torus.X v Ω m) := by
  simpa only [centeredCrossing_zero] using pureAction_centered v Ω hΩ k p hp m 0 hm

include hΩ in
lemma pureAction_pairing_one (m : M) (hm : Ω p m=1) :
    pureAction v (complementOmega k Ω) (complementAlpha k p Ω)
      (embed v Ω hΩ k p hp (Torus.X v Ω m)) =
      embed v Ω hΩ k p hp (Torus.X v Ω m + Torus.X v Ω (m+p)) := by
  simpa only [centeredCrossing_one] using pureAction_centered v Ω hΩ k p hp m 1 hm

lemma pureRatio_neg_one_cancel : (pureRatio v (-1):RatFunc K) *
    (1+RatFunc.C (v:K)*RatFunc.X)=1 := by
  have H := congrArg (fun a : (RatFunc K)ˣ => (a:RatFunc K)) (pureRatio_add v (-1) 1)
  simp only [neg_add_cancel,pureRatio_zero,Units.val_one,Units.val_mul,scaleAction_val,
    pureRatio_one] at H
  change 1=(pureRatio v (-1):RatFunc K)*
    scale (v^(-2*(-1:ℤ))) (1+RatFunc.C (↑(v⁻¹):K)*RatFunc.X) at H
  have HH : scale (v^(-2*(-1:ℤ))) (1+RatFunc.C (↑(v⁻¹):K)*RatFunc.X)=
      1+RatFunc.C (v:K)*RatFunc.X := by
    rw [map_add,map_one,map_mul,scale_constant,scale_X,←mul_assoc,←map_mul,
      ←Units.val_mul,←zpow_neg_one,←zpow_add]
    norm_num
  rw [HH] at H
  exact H.symm

include hΩ in
lemma pureAction_pairing_neg_one (m : M) (hm : Ω p m= -1) :
    pureAction v (complementOmega k Ω) (complementAlpha k p Ω)
      (embed v Ω hΩ k p hp (Torus.X v Ω m + Torus.X v Ω (m+p))) =
      embed v Ω hΩ k p hp (Torus.X v Ω m) := by
  have H0 := embed_pure_row_term v Ω hΩ k p hp m 0 1
  have H1 := embed_pure_row_term v Ω hΩ k p hp m 1 1
  simp only [zero_smul,add_zero,map_one,mul_one,pow_zero,one_smul,pow_one,hm,
    neg_neg,zpow_one] at H0 H1
  rw [map_add,map_add,Torus.X,Torus.X,H0,H1,pureAction_monomial,pureAction_monomial,
    complement_pairing Ω hΩ k p hp m,hm,←FiberTorus.monomial_add]
  congr 1
  have H := pureRatio_neg_one_cancel v
  calc
    _ = centeredScalar v (k m) (-1) *
        ((pureRatio v (-1):RatFunc K)*(1+RatFunc.C (v:K)*RatFunc.X)) := by ring
    _ = _ := by rw [H,mul_one]
end
end ElementaryPositivity.RationalFiber

end

end OAI
