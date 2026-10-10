import Mathlib
import OAI.Combinatorics.Chromatic.Walls.LaurentPositiveDomination

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint LaurentPositive
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}
local instance : Ring (Torus LaurentRay.vUnit (extendedOmega n)) := Torus.instRing LaurentRay.vUnit (extendedOmega n)
local instance : AddCommMonoid (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommMonoid
local instance : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
local instance : Sub (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toSub

lemma triangularConeDelta_apply (N d k:ℕ) (μ:Fin (n+1) → ℕ)
    (hm:HasRootDegree (extendedRoots n) d (includeVertices (natAnchor μ)-triangularBase N))
    (m:Extended (Vertex n (Cell n))) (hk:HasRootDegree (extendedRoots n) k (m-triangularBase N)) :
    coneDelta (extendedOmega n) d (includeVertices (natAnchor μ)) k m=
      if m=includeVertices (natAnchor μ) then 1 else 0 := by
  by_cases he:m=includeVertices (natAnchor μ)
  · subst m
    have H1:=rootOrder_eq (extendedRoots n) (extendedCoord n) extendedCoord_roots hm
    have H2:=rootOrder_eq (extendedRoots n) (extendedCoord n) extendedCoord_roots hk
    have hkd:k=d:=by omega
    subst k
    simp [coneDelta,Torus.X,Torus.monomial]
  · rw [ite_eq_right he,coneDelta]
    split_ifs
    · exact Finsupp.single_eq_of_ne he
    · rfl

lemma triangularMonomial_initial {N:ℕ} (f:ElementaryExpr N)
    (d:ℕ) (μ:Fin (n+1) → ℕ) (hμ:∑a,μ a=N) (hdom:∀i:Fin n,μ i.succ ≤ μ i.castSucc)
    (hm:HasRootDegree (extendedRoots n) d (includeVertices (natAnchor μ)-triangularBase N))
    (hp:∀ν:Fin (n+1) → ℤ,(∀i:Fin n,ν i.succ ≤ ν i.castSucc) →
      triangularExpression f (includeVertices (pureAnchor ν))=if ν=(fun a=>(μ a:ℤ)) then 1 else 0) :
    polynomialInitial (extendedOmega n) (extendedRoots n) (extendedCoord n) (triangularExpression f)=
      coneThetaInitial (extendedOmega n) (extendedRoots n) (simpleTotalTransport (extendedOmega n) (extendedRoots n))
        (triangularBase N) d (includeVertices (natAnchor μ)) := by
  let X:=polynomialInitial (extendedOmega n) (extendedRoots n) (extendedCoord n) (triangularExpression f)
  let T:=coneThetaInitial (extendedOmega n) (extendedRoots n) (simpleTotalTransport (extendedOmega n) (extendedRoots n))
        (triangularBase N) d (includeVertices (natAnchor μ))
  have hX:=triangularExpression_initial_graded (n:=n) f
  have hT:=coneThetaInitial_graded (extendedOmega n) (extendedRoots n) (simpleTotalTransport (extendedOmega n) (extendedRoots n)) (triangularBase N) d _ hm
  obtain ⟨L,hL⟩:=real_covector_prescribe (extendedRoots n) extendedCast extendedRoots_realIndependent (fun _=>1)
  let h:Module.Dual ℝ ((Vertex n (Cell n) → ℝ) × (Vertex n (Cell n) → ℝ)) := -L
  have hneg:∀k,0<k → ∀m,HasRootDegree (extendedRoots n) k m → h (extendedCast m)<0:=by
    intro k hk m hm
    change -L (extendedCast m)<0
    rw [covector_root_eval (extendedRoots n) extendedCast L hL hm]
    exact neg_neg_of_pos (Nat.cast_pos.mpr hk)
  have hval:sectionValue LaurentRay.vUnit (extendedOmega n) (extendedRoots n)
      (simpleTotalTransport (extendedOmega n) (extendedRoots n)) (h.toAddMonoidHom.comp extendedCast) X=
      homogenize LaurentRay.vUnit (extendedOmega n) (rootOrder (extendedCoord n)) (triangularExpression f) := by
    change sectionValue _ _ _ _ _ (adjoint _ _)=_
    rw [←rootSectionChart_action,rootSectionChart_negative _ _ _ hneg,adjoint_one_torus]
  apply PowerSeries.ext
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih=>
    apply Finsupp.ext
    intro m
    by_contra hne
    have hkm:HasRootDegree (extendedRoots n) k (m-triangularBase N):=by
      by_contra hh
      exact hne ((hX k m hh).trans (hT k m hh).symm)
    have H:=sectionIncoming_leading LaurentRay.vUnit (extendedOmega n) (extendedRoots n)
      (simpleTotalTransport (extendedOmega n) (extendedRoots n)) (triangularBase N) k X T
      ih (hX k) (hT k)
    have HI:(sectionIncoming LaurentRay.vUnit (extendedOmega n) (extendedRoots n)
        (simpleTotalTransport (extendedOmega n) (extendedRoots n)) (triangularBase N) k X) m -
        coneDelta (extendedOmega n) d (includeVertices (natAnchor μ)) k m ≠ 0 := by
      intro hz
      rw [←coneThetaInitial_prescription (extendedOmega n) (extendedRoots n) _ (triangularBase N) d _ hm k] at hz
      have HH:=congrArg (fun z:Torus LaurentRay.vUnit (extendedOmega n)=>z m) H
      rw [torus_sub_apply,torus_sub_apply] at HH
      exact hne (sub_eq_zero.mp (HH.symm.trans hz))
    rw [polynomialInitial_incoming (extendedOmega n) extendedOmega_self (extendedRoots n)
      (extendedCoord n) extendedCoord_roots (triangularBase N) (triangularBase_order N) _
      (by intro a ha; exact triangularSeed_in_rootCone f a (Finsupp.mem_support_iff.mpr ha)) k m hkm,
      triangularConeDelta_apply N d k μ hm m hkm] at HI
    have Hneg:=adjoint_leading
      (chartNegative LaurentRay.vUnit (extendedOmega n) (extendedRoots n) (h.toAddMonoidHom.comp extendedCast)
        (simpleTotalTransport (extendedOmega n) (extendedRoots n))).val X T
      (chartNegative _ _ _ _ _).property.1 k ih
    change coeff k (sectionValue _ _ _ _ _ X)-coeff k (sectionValue _ _ _ _ _ T)=_ at Hneg
    rw [hval] at Hneg
    have Hord:coeff k (homogenize LaurentRay.vUnit (extendedOmega n) (rootOrder (extendedCoord n))
      (triangularExpression f)) m - coeff k (triangularConeTheta N d μ (h.toAddMonoidHom.comp extendedCast)) m ≠0:=by
      intro hz
      have HH:=congrArg (fun z:Torus LaurentRay.vUnit (extendedOmega n)=>z m) Hneg
      rw [torus_sub_apply,torus_sub_apply] at HH
      exact hne (sub_eq_zero.mp (HH.symm.trans hz))
    have hs:triangularExpression f m≠0 ∨ triangularExpression (linearPower N) m≠0:=by
      by_cases hf:triangularExpression f m=0
      · right
        apply triangularTheta_support N d μ hμ hdom hm h hneg k m
        intro ht
        exact Hord (by simp [homogenize_coeff,hf,ht])
      · exact Or.inl hf
    have hdual:m.2=0:=hs.elim
      (fun hf=>triangularSeed_dual_zero f m (Finsupp.mem_support_iff.mpr hf))
      (fun hf=>triangularSeed_dual_zero (linearPower N) m (Finsupp.mem_support_iff.mpr hf))
    have hnon:∀b,0 ≤ m.1 (.inr b):=fun b=>hs.elim
      (fun hf=>triangularSeed_nonneg f m (Finsupp.mem_support_iff.mpr hf) (.inr b))
      (fun hf=>triangularSeed_nonneg (linearPower N) m (Finsupp.mem_support_iff.mpr hf) (.inr b))
    have he:m=includeVertices m.1:=Prod.ext rfl hdual
    have hpure:∃ν:Fin (n+1) → ℤ,m=includeVertices (pureAnchor ν):=by
      by_cases htarget:m=includeVertices (natAnchor μ)
      · exact ⟨fun a=>(μ a:ℤ),htarget⟩
      · rw [ite_eq_right htarget,sub_zero,he] at HI
        have hK:∀i,levelTotal cellLevel i m.1=0:=(triangularExpression_stationary f m.1 HI).1
        exact ⟨fun a=>m.1 (.inl a),he.trans (congrArg includeVertices (pureAnchor_of_bridges_zero m.1
          (bridges_zero_of_level_zero m.1 hnon hK)))⟩
    obtain ⟨ν,rfl⟩:=hpure
    change triangularIncoming f (pureAnchor ν)-(if includeVertices (pureAnchor ν)=includeVertices (natAnchor μ) then 1 else 0)≠0 at HI
    rw [triangularPureIncoming_delta f (fun a=>(μ a:ℤ)) (fun i=>Int.ofNat_le.mpr (hdom i)) hp] at HI
    have hh:includeVertices (pureAnchor ν)=includeVertices (natAnchor μ) ↔ ν=(fun a=>(μ a:ℤ)):=by
      constructor
      · exact fun H=>pureAnchor_injective (congrArg Prod.fst H)
      · intro H; rw [H]; rfl
    exact HI (by simp only [hh,sub_self])
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}
local instance : Ring (Torus LaurentRay.vUnit (extendedOmega n)) := Torus.instRing LaurentRay.vUnit (extendedOmega n)
local instance : AddCommMonoid (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommMonoid
local instance : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
local instance : Sub (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toSub

def anchorExponent : (Fin (n+1) →₀ ℕ) →+ Extended (Vertex n (Cell n)) where
  toFun d:=includeVertices (pureAnchor (fun a=>(d a:ℤ)))
  map_zero':=by apply Prod.ext; ext a; cases a <;> simp [pureAnchor_apply_anchor,pureAnchor_apply_bridge]; rfl
  map_add' d e:=by
    apply Prod.ext
    · ext a
      cases a <;> simp [pureAnchor_apply_anchor,pureAnchor_apply_bridge]
    · rfl
lemma anchorExponent_injective : Function.Injective (anchorExponent (n:=n)) := by
  intro d e he
  ext a
  have H:=congrArg (fun m:Extended (Vertex n (Cell n))=>m.1 (.inl a)) he
  change pureAnchor (fun a=>(d a:ℤ)) (.inl a)=pureAnchor (fun a=>(e a:ℤ)) (.inl a) at H
  rw [pureAnchor_apply_anchor,pureAnchor_apply_anchor] at H
  exact Int.ofNat_inj.mp H
lemma anchorExponent_pair (d e:Fin (n+1) →₀ ℕ) :
    extendedOmega n (anchorExponent d) (anchorExponent e)=0 := by
  change extendedOmega n (includeVertices _) (includeVertices _)=0
  rw [extendedOmega_original,pureAnchor_pair]

def anchorPolynomialAdd : MvPolynomial (Fin (n+1)) (LaurentSeries ℚ) →+
    Torus LaurentRay.vUnit (extendedOmega n) where
  toFun p:=Finsupp.mapDomain (anchorExponent (n:=n)) (AddMonoidAlgebra.coeff p)
  map_zero':=Finsupp.mapDomain_zero
  map_add' _ _:=Finsupp.mapDomain_add
lemma anchorPolynomial_monomial (d:Fin (n+1) →₀ ℕ) (r:LaurentSeries ℚ) :
    anchorPolynomialAdd (MvPolynomial.monomial d r)=Torus.monomial LaurentRay.vUnit (extendedOmega n) (anchorExponent d) r :=
  Finsupp.mapDomain_single
lemma anchorPolynomial_coeff (p:MvPolynomial (Fin (n+1)) (LaurentSeries ℚ)) (d:Fin (n+1) →₀ ℕ) :
    anchorPolynomialAdd p (anchorExponent d)=p.coeff d :=
  Finsupp.mapDomain_apply_of_injective anchorExponent_injective (AddMonoidAlgebra.coeff p) d
lemma anchorPolynomial_mul (p q:MvPolynomial (Fin (n+1)) (LaurentSeries ℚ)) :
    anchorPolynomialAdd (p*q)=anchorPolynomialAdd p*anchorPolynomialAdd q := by
  induction p using MvPolynomial.induction_on' with
  | add p p' hp hp'=>simp only [add_mul,map_add,hp,hp']
  | monomial d r=>
    induction q using MvPolynomial.induction_on' with
    | add q q' hq hq'=>simp only [mul_add,map_add,hq,hq']
    | monomial e s=>
      rw [MvPolynomial.monomial_mul_monomial,anchorPolynomial_monomial,anchorPolynomial_monomial,anchorPolynomial_monomial,
        Torus.monomial_mul_monomial,anchorExponent_pair,zpow_zero,Units.val_one,mul_one,map_add]

def anchorPolynomial : MvPolynomial (Fin (n+1)) (LaurentSeries ℚ) →+*
    Torus LaurentRay.vUnit (extendedOmega n) where
  __:=anchorPolynomialAdd
  map_one':=by
    change anchorPolynomialAdd (MvPolynomial.monomial 0 1)=_
    rw [anchorPolynomial_monomial,map_zero]
    rfl
  map_mul':=anchorPolynomial_mul
lemma anchorPolynomial_X (a:Fin (n+1)) :
    anchorPolynomial (MvPolynomial.X a)=Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (anchor a)) := by
  change anchorPolynomialAdd (MvPolynomial.monomial (Finsupp.single a 1) 1)=_
  rw [anchorPolynomial_monomial]
  congr 1
  apply Prod.ext
  · ext b
    cases b with
    | inl b=>simp [anchorExponent,pureAnchor_apply_anchor,anchor,Pi.single_apply,Finsupp.single_apply,eq_comm]
    | inr b=>simp [anchorExponent,pureAnchor_apply_bridge,anchor]
  · rfl
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
