import Mathlib
import OAI.Combinatorics.Chromatic.Walls.PolynomialIncomingPerturbation

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ))
local instance polynomialSectionRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance polynomialSectionAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance polynomialSectionAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

omit [DecidableEq I] in
include hΩ in
lemma actualMonomialAdjoint_support (τ:M →+ ℤ) (f:CompletedPositive LaurentRay.vUnit Ω C)
    (b m:M) (hm:actualMonomialAdjointCoefficient Ω τ f.val b m≠0) :
    ∃d,HasRootDegree C d (m-b) := by
  have H:=normalizedMonomialAction_graded LaurentRay.vUnit Ω hΩ C f b
  unfold actualMonomialAdjointCoefficient actualRootCoefficient at hm
  split_ifs at hm with ht
  · refine ⟨(τ (m-b)).toNat,?_⟩
    by_contra hn
    exact hm (by rw [H _ _ hn,zero_mul])
  · exact (hm (zero_mul _)).elim

omit [DecidableEq I] in
include hΩ in
lemma actualPolynomialAdjoint_support (τ:M →+ ℤ) (f:CompletedPositive LaurentRay.vUnit Ω C)
    (F:Torus LaurentRay.vUnit Ω) (m:M)
    (hm:actualPolynomialAdjointCoefficient Ω τ f.val F m≠0) :
    ∃b∈F.support,∃d,HasRootDegree C d (m-b) := by
  classical
  unfold actualPolynomialAdjointCoefficient Finsupp.sum at hm
  obtain ⟨b,hb,hb'⟩:=Finset.exists_ne_zero_of_sum_ne_zero hm
  refine ⟨b,hb,actualMonomialAdjoint_support Ω hΩ C τ f b m ?_⟩
  intro hh
  exact hb' (show F b * actualMonomialAdjointCoefficient Ω τ f.val b m = 0 from by simp only [hh,mul_zero])

include hΩ in
lemma polynomialSection_support (h:M →+ ℝ) (F:Torus LaurentRay.vUnit Ω) (m:M)
    (hm:polynomialSectionCoefficient Ω C coord h F m≠0) :
    ∃b∈F.support,∃d,HasRootDegree C d (m-b) :=
  actualPolynomialAdjoint_support Ω hΩ C (rootOrder coord) (rootSectionChart Ω C h) F m hm

lemma rootDegree_cut_bound (ell:M →+ ℤ) (hc:∀i,ell (simpleRoot C i)≤0)
    {d:ℕ} {m:M} (hm:HasRootDegree C d m) : ell m≤0 := by
  obtain ⟨a,_,rfl⟩:=hm
  have hex:(fun i=>(a i:ℤ))=∑i,Pi.single i (a i:ℤ):=by
    ext i
    simp
  rw [hex,map_sum,map_sum]
  apply Finset.sum_nonpos
  intro i _
  have H:C (Pi.single i (a i:ℤ))=(a i:ℤ) • simpleRoot C i:=by
    rw [simpleRoot,←map_zsmul]
    congr 1
    ext j
    simp only [Pi.smul_apply,Pi.single_apply,smul_eq_mul]
    split_ifs <;> simp
  rw [H,map_zsmul,smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) (hc i)

include hΩ in
lemma polynomialSection_cut_bound (h:M →+ ℝ) (F:Torus LaurentRay.vUnit Ω)
    (ell:M →+ ℤ) (K:ℤ) (hc:∀i,ell (simpleRoot C i)≤0)
    (hF:∀b∈F.support,ell b≤K) (m:M)
    (hm:polynomialSectionCoefficient Ω C coord h F m≠0) : ell m≤K := by
  obtain ⟨b,hb,d,hd⟩:=polynomialSection_support Ω hΩ C coord h F m hm
  have HH:=rootDegree_cut_bound C ell hc hd
  rw [map_sub] at HH
  have := hF b hb
  omega

include hΩ in
lemma polynomialIncoming_cut_bound (F:Torus LaurentRay.vUnit Ω)
    (ell:M →+ ℤ) (K:ℤ) (hc:∀i,ell (simpleRoot C i)≤0)
    (hF:∀b∈F.support,ell b≤K) (m:M)
    (hm:polynomialSectionIncoming Ω C coord F m≠0) : ell m≤K :=
  polynomialSection_cut_bound Ω hΩ C coord (incomingCovector Ω m) F ell K hc hF m hm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
