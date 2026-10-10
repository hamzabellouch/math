import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TriangularCommutativity

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits LaurentPositive
open Classical
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M)
local instance coneSectionDominationTorusRing : Ring (Torus LaurentRay.vUnit Ω) :=
  Torus.instRing LaurentRay.vUnit Ω
local instance coneSectionDominationTorusAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance coneSectionDominationTorusAddCommGroup : AddCommGroup (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toAddCommGroup
local instance coneSectionDominationTorusAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance coneSectionDominationTorusSub : Sub (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toSub
local instance coneSectionDominationTorusNonUnitalSemiring : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance coneSectionDominationTorusNonUnitalNonAssocSemiring :
    NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring
variable (F:CompletedPositive LaurentRay.vUnit Ω C) (base:M)

def coneDelta (d:ℕ) (m:M) (k:ℕ) : Torus LaurentRay.vUnit Ω :=
  if k=d then Torus.X LaurentRay.vUnit Ω m else 0
lemma coneDelta_graded (d:ℕ) (m:M) (hm:HasRootDegree C d (m-base)) (k:ℕ) :
    coneDelta Ω d m k ∈ shiftRootGrade LaurentRay.vUnit Ω C base k := by
  by_cases hk:k=d
  · subst k
    intro a ha
    change (if d=d then Torus.X LaurentRay.vUnit Ω m else 0) a=0
    rw [ite_eq_left rfl]
    exact Finsupp.single_eq_of_ne (by intro h; subst a; exact ha hm)
  · rw [coneDelta,ite_eq_right hk]
    exact (shiftRootGrade LaurentRay.vUnit Ω C base k).zero_mem

def coneThetaInitial (d:ℕ) (m:M) : PowerSeries (Torus LaurentRay.vUnit Ω) :=
  sectionSolution LaurentRay.vUnit Ω C F base (coneDelta Ω d m)
def coneThetaValue (d:ℕ) (m:M) (h:M →+ ℝ) : PowerSeries (Torus LaurentRay.vUnit Ω) :=
  sectionValue LaurentRay.vUnit Ω C F h (coneThetaInitial Ω C F base d m)
lemma coneThetaInitial_graded (d:ℕ) (m:M) (hm:HasRootDegree C d (m-base)) :
    ShiftGraded LaurentRay.vUnit Ω C base (coneThetaInitial Ω C F base d m) :=
  sectionSolution_graded _ _ _ _ _ _ (coneDelta_graded Ω C base d m hm)
lemma coneThetaInitial_prescription (d:ℕ) (m:M) (hm:HasRootDegree C d (m-base)) (k:ℕ) :
    sectionIncoming LaurentRay.vUnit Ω C F base k (coneThetaInitial Ω C F base d m)=coneDelta Ω d m k :=
  sectionSolution_prescription _ _ _ _ _ _ (coneDelta_graded Ω C base d m hm) k

lemma sectionIncoming_sub (k:ℕ) (X Y:PowerSeries (Torus LaurentRay.vUnit Ω)) :
    sectionIncoming LaurentRay.vUnit Ω C F base k (X-Y)=
      sectionIncoming LaurentRay.vUnit Ω C F base k X-sectionIncoming LaurentRay.vUnit Ω C F base k Y := by
  apply Finsupp.ext
  intro m
  simp only [sectionIncoming_apply,torus_sub_apply]
  split_ifs
  · simp only [sectionValue,adjoint_sub,map_sub,torus_sub_apply]
  · exact (sub_self (0:LaurentSeries ℚ)).symm
variable (e:M →+ E) (he:Function.Injective e)
variable (B:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB:∀x,B x x=0)
variable (hcomp:∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hB hcomp hdeg in
lemma coneThetaValue_positive (incoming:PositiveIncomingPrescription Ω C F)
    (d:ℕ) (m:M) (hm:HasRootDegree C d (m-base)) (h:Module.Dual ℝ E) :
    IntegralPositive Ω (coneThetaValue Ω C F base d m (h.toAddMonoidHom.comp e)) := by
  intro j
  apply positive_sections Ω C e he B hB hcomp L hdeg F incoming base
    (coneThetaInitial Ω C F base d m) (coneThetaInitial_graded Ω C F base d m hm) _ j h
  intro k
  rw [coneThetaInitial_prescription Ω C F base d m hm,coneDelta]
  split_ifs
  · exact torusPositive_monomial Ω m 1 positive_one
  · exact torusPositive_zero Ω

include he hB hcomp hdeg in

lemma coneTheta_domination (incoming:PositiveIncomingPrescription Ω C F)
    (X:PowerSeries (Torus LaurentRay.vUnit Ω)) (hX:ShiftGraded LaurentRay.vUnit Ω C base X)
    (d:ℕ) (m:M) (hm:HasRootDegree C d (m-base))
    (hinc:∀k,TorusPositive Ω
      (sectionIncoming LaurentRay.vUnit Ω C F base k X-coneDelta Ω d m k))
    (h:Module.Dual ℝ E) :
    IntegralPositive Ω (sectionValue LaurentRay.vUnit Ω C F (h.toAddMonoidHom.comp e) X-
      coneThetaValue Ω C F base d m (h.toAddMonoidHom.comp e)) := by
  have H:=positive_sections Ω C e he B hB hcomp L hdeg F incoming base
    (X-coneThetaInitial Ω C F base d m)
    (hX.sub _ _ _ (coneThetaInitial_graded Ω C F base d m hm))
    (by
      intro k
      rw [sectionIncoming_sub,coneThetaInitial_prescription Ω C F base d m hm]
      exact hinc k)
  simpa only [IntegralPositive,sectionValue,adjoint_sub,coneThetaValue] using (fun k=>H k h)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
