import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.HomogenizedPolynomialSection
import OAI.Combinatorics.Chromatic.Histories.LocalHistoryFormula

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus.LocalHistoryFormula
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit LaurentPositive WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]

def Leaf : LocalHistoryFormula M E → Type
  | .zero=>Empty
  | .stop _ _=>Unit
  | .add p q=>Sum (Leaf p) (Leaf q)
  | .jump _ _ _ _ p=>Leaf p

instance leafFintype (p:LocalHistoryFormula M E) : Fintype p.Leaf := by
  induction p with
  | zero=>exact inferInstanceAs (Fintype Empty)
  | stop _ _=>exact inferInstanceAs (Fintype Unit)
  | add p q ihp ihq=>letI:=ihp; letI:=ihq; exact inferInstanceAs (Fintype (Sum p.Leaf q.Leaf))
  | jump _ _ _ _ p ih=>exact ih

def leafDegree : (p:LocalHistoryFormula M E) → p.Leaf → ℕ
  | .zero,l=>nomatch l
  | .stop j _,_=>j
  | .add p _,.inl l=>leafDegree p l
  | .add _ q,.inr l=>leafDegree q l
  | .jump _ _ _ _ p,l=>leafDegree p l

def leafExponent : (p:LocalHistoryFormula M E) → p.Leaf → M
  | .zero,l=>nomatch l
  | .stop _ m,_=>m
  | .add p _,.inl l=>leafExponent p l
  | .add _ q,.inr l=>leafExponent q l
  | .jump _ _ _ _ p,l=>leafExponent p l

variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M) (e:M →+ E)
variable (F:CompletedPositive LaurentRay.vUnit Ω C)
def leafWeight : (p:LocalHistoryFormula M E) → p.Leaf → LaurentSeries ℚ
  | .zero,l=>nomatch l
  | .stop _ _,_=>1
  | .add p _,.inl l=>leafWeight p l
  | .add _ q,.inr l=>leafWeight q l
  | .jump d m r t p,l=>monomialJump Ω (t.operator Ω C e F) d m r*leafWeight p l

lemma leafWeight_positive (p:LocalHistoryFormula M E) (hp:p.Positive Ω C e F) (l:p.Leaf) :
    LaurentPositive.Positive (leafWeight Ω C e F p l) := by
  induction p with
  | zero=>exact l.elim
  | stop j m=>exact positive_one
  | add p q ihp ihq=>cases l with
    | inl l=>exact ihp hp.1 l
    | inr l=>exact ihq hp.2 l
  | jump d m r t p ih=>exact hp.1.mul (ih hp.2 l)

lemma leafBound (b:M) (N:ℕ) (p:LocalHistoryFormula M E) (hp:p.Bounded C b N) (l:p.Leaf) :
    p.leafDegree l≤N ∧ HasRootDegree C (p.leafDegree l) (p.leafExponent l-b) := by
  induction p generalizing N with
  | zero=>exact l.elim
  | stop j m=>exact hp
  | add p q ihp ihq=>cases l with
    | inl l=>exact ihp N hp.1 l
    | inr l=>exact ihq N hp.2 l
  | jump d m r t p ih=>
    obtain ⟨hd,j,hj,hp⟩:=hp
    obtain ⟨hl,hr⟩:=ih j hp l
    exact ⟨by dsimp [leafDegree]; omega,hr⟩

lemma eval_eq_sum_leaves (p:LocalHistoryFormula M E) (A:ℕ → M → LaurentSeries ℚ) :
    p.eval Ω C e F A=∑l:p.Leaf,leafWeight Ω C e F p l*A (p.leafDegree l) (p.leafExponent l) := by
  induction p with
  | zero=>
    change 0=∑l:Empty,_
    exact (Finset.sum_eq_zero (fun l _=>l.elim)).symm
  | stop j m=>
    change A j m=∑l:Unit,_
    rw [Fintype.sum_unique]
    simp [leafWeight,leafDegree,leafExponent]
  | add p q ihp ihq=>
    change p.eval Ω C e F A+q.eval Ω C e F A=∑l:Sum p.Leaf q.Leaf,_
    rw [Fintype.sum_sum_type,ihp,ihq]
    rfl
  | jump d m r t p ih=>
    change monomialJump Ω (t.operator Ω C e F) d m r*p.eval Ω C e F A=∑l:p.Leaf,_
    rw [ih,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    exact (mul_assoc _ _ _).symm
end
end ElementaryPositivity.QuantumTorus.LocalHistoryFormula

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits HahnSeries
open Classical
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d)
local instance commonHistoryLeavesRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance commonHistoryLeavesAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance commonHistoryLeavesAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hΩ hcoord in
lemma polynomialInitial_value (b:M) (hb:rootOrder coord b=0)
    (F:Torus LaurentRay.vUnit Ω) (hF:∀m,F m≠0 → ∃d,HasRootDegree C d (m-b))
    (d:ℕ) (m:M) (hm:HasRootDegree C d (m-b)) (h:M →+ ℝ) :
    coeff d (sectionValue LaurentRay.vUnit Ω C (simpleTotalTransport Ω C) h
      (polynomialInitial Ω C coord F)) m=polynomialSectionCoefficient Ω C coord h F m := by
  unfold polynomialInitial
  rw [←rootSectionChart_action]
  have H:=rootOrder_eq C coord hcoord hm
  rw [map_sub,hb,sub_zero] at H
  have he:d=(rootOrder coord m).toNat:=by rw [H,Int.toNat_natCast]
  rw [he]
  exact homogenize_adjoint_actual Ω hΩ (rootOrder coord) _ F
    (conePolynomial_nonnegativeOrder Ω C coord hcoord b hb F hF) m (by rw [H]; omega)

variable (e:M →+ E) (he:Function.Injective e)
variable (B:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB:∀x,B x x=0)
variable (hcomp:∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include hΩ hcoord he hB hcomp hdeg in
lemma polynomial_common_history (b:M) (hb:rootOrder coord b=0)
    (N:ℕ) (r:M) (hr:HasRootDegree C N (r-b)) :
    ∃p:LocalHistoryFormula M E,
      p.Positive Ω C e (simpleTotalTransport Ω C) ∧ p.Bounded C b N ∧
      ∀F:Torus LaurentRay.vUnit Ω,
        (∀m,F m≠0 → ∃d,HasRootDegree C d (m-b)) →
        F r=∑l:p.Leaf,p.leafWeight Ω C e (simpleTotalTransport Ω C) l *
          polynomialSectionIncoming Ω C coord F (p.leafExponent l) := by
  obtain ⟨p,hp,hbnd,hid⟩:=common_history_producer Ω C e he B hB hcomp L hdeg
    (simpleTotalTransport Ω C) (simpleTotalTransport_positive_prescription Ω C hΩ) b N (-L) r hr
  refine ⟨p,hp,hbnd,?_⟩
  intro F hF
  have H:=hid (polynomialInitial Ω C coord F) (polynomialInitial_graded Ω C coord hcoord b hb F hF)
  rw [polynomialInitial_value Ω hΩ C coord hcoord b hb F hF N r hr,
    polynomialSection_negative Ω hΩ C coord] at H
  · rw [LocalHistoryFormula.eval_eq_sum_leaves] at H
    rw [←H]
    apply Finset.sum_congr rfl
    intro l hl
    congr 1
    exact polynomialInitial_value Ω hΩ C coord hcoord b hb F hF _ _
      (p.leafBound C b N hbnd l).2 (incomingCovector Ω (p.leafExponent l))
  · intro k hk m hm
    change -(L (e m)) < 0
    rw [hdeg k m hm]
    exact neg_neg_of_pos (Nat.cast_pos.mpr hk)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
