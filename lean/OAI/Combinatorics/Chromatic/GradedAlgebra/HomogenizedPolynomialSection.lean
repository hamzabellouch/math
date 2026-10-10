import Mathlib
import OAI.Combinatorics.Chromatic.Walls.SectionIncoming
import OAI.Combinatorics.Chromatic.Walls.PolynomialIncomingPerturbation

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries HahnSeries PowerSeriesAdjoint WallUnits
open Classical
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d)
local instance homogenizedPolynomialSectionRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance homogenizedPolynomialSectionAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance homogenizedPolynomialSectionAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance homogenizedPolynomialSectionNonUnitalSemiring : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance homogenizedPolynomialSectionNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring

lemma homogenize_hahn (τ:M →+ ℤ) (F:Torus LaurentRay.vUnit Ω)
    (hF:∀m,F m≠0 → 0 ≤ τ m) :
    HahnSeries.ofPowerSeries ℤ (Torus LaurentRay.vUnit Ω) (homogenize LaurentRay.vUnit Ω τ F)=
      latticeHahn LaurentRay.vUnit Ω τ F := by
  apply HahnSeries.ext
  funext j
  apply Finsupp.ext
  intro m
  rw [ofPowerSeries_coeff_int,latticeHahn_coeff]
  by_cases hf:F m=0
  · split_ifs <;> simp [homogenize_coeff,hf]
  · have hh:=hF m hf
    by_cases hj:0 ≤ j
    · rw [ite_eq_left hj,homogenize_coeff]
      have he:j.toNat=(τ m).toNat ↔ j=τ m:=by omega
      simp only [he]
    · rw [ite_eq_right hj]
      have he:j≠τ m:=by omega
      simp only [he,ite_false,Finsupp.zero_apply]

lemma ofPowerSeries_adjoint (f X:PowerSeries (Torus LaurentRay.vUnit Ω)) :
    HahnSeries.ofPowerSeries ℤ (Torus LaurentRay.vUnit Ω) (adjoint f X)=
      hahnAction f (HahnSeries.ofPowerSeries ℤ (Torus LaurentRay.vUnit Ω) X) := by
  simp only [adjoint,hahnAction,map_mul]

include hΩ in
lemma homogenize_adjoint_actual (τ:M →+ ℤ) (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (F:Torus LaurentRay.vUnit Ω) (hF:∀m,F m≠0 → 0 ≤ τ m) (m:M) (hm:0 ≤ τ m) :
    coeff (τ m).toNat (adjoint f (homogenize LaurentRay.vUnit Ω τ F)) m=
      actualPolynomialAdjointCoefficient Ω τ f F m := by
  rw [←hahnAction_actual_coeff Ω hΩ,←homogenize_hahn Ω τ F hF,←ofPowerSeries_adjoint,
    ofPowerSeries_coeff_int,ite_eq_left hm]

include hcoord in
omit [DecidableEq I] in
lemma homogenize_shiftGraded (base:M) (hb:rootOrder coord base=0)
    (F:Torus LaurentRay.vUnit Ω) (hF:∀m,F m≠0 → ∃d,HasRootDegree C d (m-base)) :
    ShiftGraded LaurentRay.vUnit Ω C base (homogenize LaurentRay.vUnit Ω (rootOrder coord) F) := by
  intro d m hm
  rw [homogenize_coeff]
  split_ifs with hd
  · by_contra hn
    obtain ⟨k,hk⟩:=hF m hn
    have H:=rootOrder_eq C coord hcoord hk
    rw [map_sub,hb,sub_zero] at H
    have he:d=k:=by rw [hd,H,Int.toNat_natCast]
    exact hm (by rw [he]; exact hk)
  · rfl

include hcoord in
omit [DecidableEq I] in
lemma conePolynomial_nonnegativeOrder (base:M) (hb:rootOrder coord base=0)
    (F:Torus LaurentRay.vUnit Ω) (hF:∀m,F m≠0 → ∃d,HasRootDegree C d (m-base)) :
    ∀m,F m≠0 → 0 ≤ rootOrder coord m := by
  intro m hm
  obtain ⟨d,hd⟩:=hF m hm
  have H:=rootOrder_eq C coord hcoord hd
  rw [map_sub,hb,sub_zero] at H
  rw [H]
  exact Int.natCast_nonneg _

def polynomialInitial (F:Torus LaurentRay.vUnit Ω) : PowerSeries (Torus LaurentRay.vUnit Ω) :=
  adjoint (invOfUnit (simpleTotalTransport Ω C).val 1) (homogenize LaurentRay.vUnit Ω (rootOrder coord) F)

include hcoord in
lemma polynomialInitial_graded (base:M) (hb:rootOrder coord base=0)
    (F:Torus LaurentRay.vUnit Ω) (hF:∀m,F m≠0 → ∃d,HasRootDegree C d (m-base)) :
    ShiftGraded LaurentRay.vUnit Ω C base (polynomialInitial Ω C coord F) :=
  (homogenize_shiftGraded Ω C coord hcoord base hb F hF).adjoint LaurentRay.vUnit Ω C
    (completedInverse LaurentRay.vUnit Ω C (simpleTotalTransport Ω C))

include hΩ hcoord in
lemma polynomialInitial_incoming (base:M) (hb:rootOrder coord base=0)
    (F:Torus LaurentRay.vUnit Ω) (hF:∀m,F m≠0 → ∃d,HasRootDegree C d (m-base))
    (d:ℕ) (m:M) (hm:HasRootDegree C d (m-base)) :
    sectionIncoming LaurentRay.vUnit Ω C (simpleTotalTransport Ω C) base d (polynomialInitial Ω C coord F) m=
      polynomialSectionIncoming Ω C coord F m := by
  rw [sectionIncoming_apply,ite_eq_left hm]
  change coeff d (sectionValue LaurentRay.vUnit Ω C (simpleTotalTransport Ω C)
    (incomingCovector Ω m) (polynomialInitial Ω C coord F)) m=_
  unfold polynomialInitial
  rw [←rootSectionChart_action]
  have H:=rootOrder_eq C coord hcoord hm
  rw [map_sub,hb,sub_zero] at H
  have he:d=(rootOrder coord m).toNat:=by rw [H,Int.toNat_natCast]
  rw [he]
  exact homogenize_adjoint_actual Ω hΩ (rootOrder coord) _ F
    (conePolynomial_nonnegativeOrder Ω C coord hcoord base hb F hF) m (by rw [H]; omega)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
