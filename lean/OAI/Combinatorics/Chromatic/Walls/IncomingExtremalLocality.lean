import Mathlib
import OAI.Combinatorics.Chromatic.Walls.PolynomialIncomingPerturbation
import OAI.Combinatorics.Chromatic.GradedAlgebra.RootSectionHalfspace

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
open Classical
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ))
local instance incomingExtremalLocalityTorusRing : Ring (Torus LaurentRay.vUnit Ω) :=
  Torus.instRing LaurentRay.vUnit Ω
local instance incomingExtremalLocalityTorusAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance incomingExtremalLocalityTorusAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

lemma inverse_pairing_nonnegative (m:M) (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (hf:∀k r,coeff k f r≠0 → 0 ≤ Ω r m) :
    ∀k r,coeff k (invOfUnit f 1) r≠0 → 0 ≤ Ω r m := by
  intro k r hr
  let P:=nonpositiveCone (-(incomingCovector Ω m))
  have H:=inverse_support_addSubmonoid LaurentRay.vUnit Ω P f (by
    intro d x hx
    change -(Ω x m:ℝ) ≤ 0
    have hh:0 ≤ (Ω x m:ℝ):=by exact_mod_cast hf d x hx
    linarith) k r hr
  change -(Ω r m:ℝ) ≤ 0 at H
  have hh:0 ≤ (Ω r m:ℝ):=by linarith
  exact_mod_cast hh

include hΩ in
lemma adjoint_pairing_nonnegative (m b:M) (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (hf0:constantCoeff f=1) (hf:∀k r,coeff k f r≠0 → 0 ≤ Ω r m)
    (hb:0 ≤ Ω b m) (N:ℕ) :
    coeff N (adjoint f (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b))) m=
      coeff N (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b)) m := by
  apply adjoint_target_cyclic LaurentRay.vUnit Ω hΩ f b m N hf0
  intro i j hij r hr s hs he
  have h1:=hf i r (Finsupp.mem_support_iff.mp hr)
  have h2:=inverse_pairing_nonnegative Ω m f hf j s (Finsupp.mem_support_iff.mp hs)
  have H:Ω (r+(s+b)) m=0:=by rw [he,hΩ]
  simp only [map_add,AddMonoidHom.add_apply] at H
  omega

include hΩ in
lemma actualMonomialAdjoint_extremal (τ:M →+ ℤ) (m b:M)
    (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (hf0:constantCoeff f=1) (hf:∀k r,coeff k f r≠0 → 0 ≤ Ω r m)
    (hb:0 ≤ Ω b m) :
    actualMonomialAdjointCoefficient Ω τ f b m=actualMonomialAdjointCoefficient Ω τ 1 b m := by
  unfold actualMonomialAdjointCoefficient actualRootCoefficient
  split_ifs
  · have H1:=adjoint_monomial_coeff LaurentRay.vUnit Ω hΩ f b (m-b) ((τ (m-b)).toNat)
    have H2:=adjoint_monomial_coeff LaurentRay.vUnit Ω hΩ 1 b (m-b) ((τ (m-b)).toNat)
    rw [sub_add_cancel] at H1 H2
    rw [←H1,←H2,adjoint_pairing_nonnegative Ω hΩ m b f hf0 hf hb]
    have hi:invOfUnit (1:PowerSeries (Torus LaurentRay.vUnit Ω)) 1=1:=by
      simpa only [mul_one] using (invOfUnit_mul (1:PowerSeries (Torus LaurentRay.vUnit Ω)) 1 (by simp))
    simp only [adjoint,hi,one_mul,mul_one]
  · rfl

include hΩ in
lemma polynomialSectionIncoming_extremal (F:Torus LaurentRay.vUnit Ω) (m:M)
    (hF:∀b∈F.support,0 ≤ Ω b m) : polynomialSectionIncoming Ω C coord F m=F m := by
  rw [←actualPolynomialAdjointCoefficient_one Ω hΩ (rootOrder coord) F m]
  unfold polynomialSectionIncoming polynomialSectionCoefficient actualPolynomialAdjointCoefficient Finsupp.sum
  apply Finset.sum_congr rfl
  intro b hb
  apply congrArg (fun x=>F b*x)
  apply actualMonomialAdjoint_extremal Ω hΩ (rootOrder coord) m b _
    (rootSectionChart Ω C (incomingCovector Ω m)).property.1 _ (hF b hb)
  intro k r hr
  have H:=rootSectionChart_nonnegative Ω C (incomingCovector Ω m) k r hr
  change 0 ≤ (Ω r m:ℝ) at H
  exact_mod_cast H
end
end ElementaryPositivity.QuantumTorus

end

end OAI
