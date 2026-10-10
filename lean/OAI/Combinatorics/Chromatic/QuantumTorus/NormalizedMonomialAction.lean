import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.MonomialConjugation

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint
noncomputable section
variable {K M:Type*} [Field K] [AddCommGroup M]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
local instance : Ring (Torus v Ω) := Torus.instRing v Ω
local instance : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

def normalizedMonomialAction (f:PowerSeries (Torus v Ω)) (b:M) : PowerSeries (Torus v Ω):=
  f*monomialConjugate v Ω b (invOfUnit f 1)

include hΩ in
lemma adjoint_monomial_normalized (f:PowerSeries (Torus v Ω)) (b:M) :
    adjoint f (PowerSeries.C (Torus.X v Ω b))=
      normalizedMonomialAction v Ω f b*PowerSeries.C (Torus.X v Ω b) := by
  have H:PowerSeries.C (Torus.X v Ω (-b))*PowerSeries.C (Torus.X v Ω b)=
      (1:PowerSeries (Torus v Ω)):=by
    rw [←map_mul]
    simpa only [neg_neg,map_one] using congrArg
      (PowerSeries.C : Torus v Ω → PowerSeries (Torus v Ω)) (X_mul_X_neg v Ω hΩ (-b))
  simp only [normalizedMonomialAction,monomialConjugate,adjoint,mul_assoc,H,mul_one]

include hΩ in
lemma normalizedMonomialAction_bound (δ:M →+ ℤ) (B:ℕ) (f:PowerSeries (Torus v Ω)) (b:M)
    (hf:RegradeBound v Ω δ B f) : RegradeBound v Ω δ B (normalizedMonomialAction v Ω f b) :=
  hf.mul v Ω δ B (monomialConjugate_regradeBound v Ω hΩ b δ B (hf.invOfUnit v Ω δ B))

include hΩ in
lemma normalizedMonomialAction_constant (f:PowerSeries (Torus v Ω)) (b:M)
    (hf:constantCoeff f=1) : constantCoeff (normalizedMonomialAction v Ω f b)=1 := by
  rw [normalizedMonomialAction,map_mul,hf,one_mul]
  rw [monomialConjugate,map_mul,map_mul,constantCoeff_C,constantCoeff_C,constantCoeff_invOfUnit]
  simp only [inv_one,Units.val_one,mul_one,X_mul_X_neg v Ω hΩ]

include hΩ in
lemma adjoint_monomial_coeff (f:PowerSeries (Torus v Ω)) (b r:M) (n:ℕ) :
    coeff n (adjoint f (PowerSeries.C (Torus.X v Ω b))) (r+b)=
      coeff n (normalizedMonomialAction v Ω f b) r*(↑(v^(Ω r b)):K) := by
  rw [adjoint_monomial_normalized v Ω hΩ,coeff_mul_C,mul_X_coeff]
end
end ElementaryPositivity.QuantumTorus
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I]
variable (v:(LaurentSeries ℚ)ˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
include hΩ in
lemma normalizedMonomialAction_graded (C:(I → ℤ) →+ M) (f:CompletedPositive v Ω C) (b:M) :
    SeriesGraded v Ω C (normalizedMonomialAction v Ω f.val b) :=
  SeriesGraded.mul v Ω C f.property.2 (monomialConjugate_graded v Ω hΩ C b
    (SeriesGraded.inverse v Ω C f.property.2))
end
end ElementaryPositivity.QuantumTorus

end

end OAI
