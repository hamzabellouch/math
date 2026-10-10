import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.HalfspacePolynomialCoefficients

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits PowerSeriesSplit
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ))
local instance : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

lemma rootSectionChart_action (h:M →+ ℝ) (X:PowerSeries (Torus LaurentRay.vUnit Ω)) :
    adjoint (rootSectionChart Ω C h).val X=
      sectionValue LaurentRay.vUnit Ω C (simpleTotalTransport Ω C) h
        (adjoint (invOfUnit (simpleTotalTransport Ω C).val 1) X) := by
  exact adjoint_mul _ _ _ (chartNegative LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).property.1 (by simp)

def polynomialSectionOrderBound (F:Torus LaurentRay.vUnit Ω) (r:M) : ℕ :=
  F.support.sup (fun b=>(rootOrder coord (r-b)).toNat)

def polynomialSectionIncoming (F:Torus LaurentRay.vUnit Ω) (r:M) : LaurentSeries ℚ :=
  polynomialSectionCoefficient Ω C coord (incomingCovector Ω r) F r

include hΩ in
lemma monomialSection_incoming_perturbation (b r:M) (H:M →+ ℝ)
    (hs:∀n≤(rootOrder coord (r-b)).toNat,∀m,HasRootDegree C n m →
      (0 < incomingCovector Ω r m → 0<H m) ∧ (incomingCovector Ω r m<0 → H m<0)) :
    actualMonomialAdjointCoefficient Ω (rootOrder coord) (rootSectionChart Ω C H).val b r=
      actualMonomialAdjointCoefficient Ω (rootOrder coord)
        (rootSectionChart Ω C (incomingCovector Ω r)).val b r := by
  unfold actualMonomialAdjointCoefficient actualRootCoefficient
  by_cases ht:0≤rootOrder coord (r-b)
  · simp only [ite_eq_left ht]
    have hread (h:M →+ ℝ) :
        coeff (rootOrder coord (r-b)).toNat (adjoint (rootSectionChart Ω C h).val
          (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b))) r=
        coeff (rootOrder coord (r-b)).toNat (normalizedMonomialAction LaurentRay.vUnit Ω
          (rootSectionChart Ω C h).val b) (r-b)*
          (↑(LaurentRay.vUnit^(Ω (r-b) b)):LaurentSeries ℚ):=by
      simpa only [sub_add_cancel] using adjoint_monomial_coeff LaurentRay.vUnit Ω hΩ
        (rootSectionChart Ω C h).val b (r-b) (rootOrder coord (r-b)).toNat
    rw [←hread,←hread,rootSectionChart_action,rootSectionChart_action]
    apply section_incoming_perturbation LaurentRay.vUnit Ω C hΩ r H H
    intro n hn m hm
    exact ⟨(hs n hn m hm).1,(hs n hn m hm).2,fun _=>⟨id,id,id⟩⟩
  · simp only [ite_eq_right ht,zero_mul]

lemma actualPolynomialAdjointCoefficient_congr (τ:M →+ ℤ)
    (f g:PowerSeries (Torus LaurentRay.vUnit Ω)) (F:Torus LaurentRay.vUnit Ω) (r:M)
    (hh:∀b∈F.support,actualMonomialAdjointCoefficient Ω τ f b r=
      actualMonomialAdjointCoefficient Ω τ g b r) :
    actualPolynomialAdjointCoefficient Ω τ f F r=actualPolynomialAdjointCoefficient Ω τ g F r := by
  apply Finset.sum_congr rfl
  intro b hb
  exact congrArg (fun x=>F b*x) (hh b hb)

include hΩ in
lemma polynomialSection_incoming_perturbation (F:Torus LaurentRay.vUnit Ω) (r:M) (H:M →+ ℝ)
    (hs:∀n≤polynomialSectionOrderBound Ω coord F r,∀m,HasRootDegree C n m →
      (0 < incomingCovector Ω r m → 0<H m) ∧ (incomingCovector Ω r m<0 → H m<0)) :
    polynomialSectionCoefficient Ω C coord H F r=polynomialSectionIncoming Ω C coord F r := by
  apply actualPolynomialAdjointCoefficient_congr
  intro b hb
  apply monomialSection_incoming_perturbation Ω hΩ C coord b r H
  intro n hn m hm
  have hbnd:(rootOrder coord (r-b)).toNat≤polynomialSectionOrderBound Ω coord F r:=
    Finset.le_sup (f:=fun b=>(rootOrder coord (r-b)).toNat) hb
  exact hs n (hn.trans hbnd) m hm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
