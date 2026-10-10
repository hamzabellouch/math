import Mathlib
import OAI.Combinatorics.Chromatic.Walls.IncomingExtremalLocality
import OAI.Combinatorics.Chromatic.QuantumTorus.PolynomialThetaIdentification
import OAI.Combinatorics.Chromatic.Walls.TriangularLinearIncoming

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension PowerSeries PowerSeriesAdjoint
open Classical
noncomputable section
variable {n:ℕ}

lemma extendedCoord_anchor_zero : extendedCoord n (includeVertices (anchor 0))=0 := by
  ext g
  change forwardCoord (Pi.single (Sum.inl (0:Fin (n+1))) (1:ℤ)) g=0
  rw [forwardCoord_single]
  simp [afterGap]
lemma rootOrder_anchor_zero : rootOrder (extendedCoord n) (includeVertices (anchor 0))=0 := by
  change (∑g,extendedCoord n (includeVertices (anchor 0)) g)=0
  rw [extendedCoord_anchor_zero]
  simp
lemma triangularLinear_initial :
    polynomialInitial (extendedOmega n) (extendedRoots n) (extendedCoord n) (triangularExpression (.atom 1))=
      thetaInitial LaurentRay.vUnit (extendedOmega n) (extendedRoots n)
        (simpleTotalTransport (extendedOmega n) (extendedRoots n)) (includeVertices (anchor 0)) := by
  apply polynomialInitial_eq_theta (extendedOmega n) extendedOmega_self (extendedRoots n)
    (extendedCoord n) extendedCoord_roots (includeVertices (anchor 0)) (rootOrder_anchor_zero (n:=n))
  · intro m hm
    simpa only [Nat.cast_one,one_smul] using triangularSeed_in_rootCone (.atom 1) m (Finsupp.mem_support_iff.mpr hm)
  · intro m
    by_cases he:m=includeVertices (anchor 0)
    · simpa only [ite_eq_left he] using triangularLinear_fullIncoming m
    · simpa only [ite_eq_right he] using triangularLinear_fullIncoming m

lemma triangularLinear_theta (h:Extended (Vertex n (Cell n)) →+ ℝ) :
    adjoint (rootSectionChart (extendedOmega n) (extendedRoots n) h).val
      (homogenize LaurentRay.vUnit (extendedOmega n) (rootOrder (extendedCoord n)) (triangularExpression (.atom 1)))=
      thetaValue LaurentRay.vUnit (extendedOmega n) (extendedRoots n)
        (simpleTotalTransport (extendedOmega n) (extendedRoots n)) (includeVertices (anchor 0)) h := by
  rw [rootSectionChart_action]
  change sectionValue _ _ _ _ _ (polynomialInitial _ _ _ _)=_
  rw [triangularLinear_initial]
  rfl

lemma triangularLinear_negative_theta (h:Extended (Vertex n (Cell n)) →+ ℝ)
    (hh:∀k,0<k → ∀m,HasRootDegree (extendedRoots n) k m → h m<0) :
    homogenize LaurentRay.vUnit (extendedOmega n) (rootOrder (extendedCoord n)) (triangularExpression (.atom 1))=
      thetaValue LaurentRay.vUnit (extendedOmega n) (extendedRoots n)
        (simpleTotalTransport (extendedOmega n) (extendedRoots n)) (includeVertices (anchor 0)) h := by
  rw [←triangularLinear_theta h,rootSectionChart_negative _ _ h hh]
  have hi:invOfUnit (1:PowerSeries (Torus LaurentRay.vUnit (extendedOmega n))) 1=1:=by
    simpa only [mul_one] using (invOfUnit_mul (1:PowerSeries (Torus LaurentRay.vUnit (extendedOmega n))) 1 (by simp))
  simp only [adjoint,one_mul,hi,mul_one]
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

def pureAnchor (μ:Fin (n+1) → ℤ) : Lattice n (Cell n) :=
  ∑a,μ a • anchor a

lemma pureAnchor_apply_anchor (μ:Fin (n+1) → ℤ) (a:Fin (n+1)) : pureAnchor μ (.inl a)=μ a := by
  simp [pureAnchor,anchor,Finset.sum_apply,Pi.single_apply]
lemma pureAnchor_apply_bridge (μ:Fin (n+1) → ℤ) (b:Cell n) : pureAnchor μ (.inr b)=0 := by
  simp [pureAnchor,anchor,Finset.sum_apply]

lemma anchor_pair_pure (a:Fin (n+1)) (μ:Fin (n+1) → ℤ) :
    triangularOmega n (anchor a) (pureAnchor μ)=0 := by
  rw [pureAnchor,map_sum]
  simp only [map_zsmul,smul_eq_mul]
  apply Finset.sum_eq_zero
  intro b _
  have hh:triangularOmega n (anchor a) (anchor b)=0:=by
    change matrixPairing (chartMatrix cellLevel triangularBB) (Pi.single (.inl a) 1) (Pi.single (.inl b) 1)=0
    rw [matrixPairing_single]
    rfl
  rw [hh,mul_zero]

lemma bridge_pair_pure (b:Cell n) (μ:Fin (n+1) → ℤ) :
    triangularOmega n (bridge b) (pureAnchor μ)=μ b.1.castSucc-μ b.1.succ := by
  have hroot:bridge b=eventRoot cellLevel 0 b+anchor b.1.castSucc:=by
    simp [eventRoot,cellLevel]
  rw [hroot,map_add,AddMonoidHom.add_apply,anchor_pair_pure,add_zero,pureAnchor,map_sum]
  simp only [map_zsmul,smul_eq_mul,eventRoot_anchor,mul_sub,Finset.sum_sub_distrib,mul_ite,mul_one,mul_zero]
  simp

lemma triangularSeed_dominant_nonnegative {N:ℕ} (f:ElementaryExpr N) (μ:Fin (n+1) → ℤ)
    (hμ:∀i:Fin n,μ i.succ ≤ μ i.castSucc) (m:Extended (Vertex n (Cell n)))
    (hm:m∈(triangularExpression f).support) : 0 ≤ extendedOmega n m (includeVertices (pureAnchor μ)) := by
  let ell:Extended (Vertex n (Cell n)) →+ ℤ:=
    -(AddMonoidHom.flip (extendedOmega n) (includeVertices (pureAnchor μ)))
  have H:=f.cutSupported_scaled LaurentRay.vUnit (extendedOmega n) ell 0
    (vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge)) (by
      intro a
      rw [initial_vertexDisplay]
      change -(extendedOmega n (includeVertices (Pi.single a (1:ℤ))) (includeVertices (pureAnchor μ))) ≤ 0
      rw [extendedOmega_original]
      cases a with
      | inl a=> change -(triangularOmega n (anchor a) (pureAnchor μ)) ≤ 0; rw [anchor_pair_pure]; omega
      | inr b=> change -(triangularOmega n (bridge b) (pureAnchor μ)) ≤ 0; rw [bridge_pair_pure]; have := hμ b.1; omega) m hm
  change -(extendedOmega n m (includeVertices (pureAnchor μ))) ≤ (N:ℤ)*0 at H
  omega

lemma triangularPure_incoming {N:ℕ} (f:ElementaryExpr N) (μ:Fin (n+1) → ℤ)
    (hμ:∀i:Fin n,μ i.succ ≤ μ i.castSucc) :
    triangularIncoming f (pureAnchor μ)=triangularExpression f (includeVertices (pureAnchor μ)) := by
  apply polynomialSectionIncoming_extremal (extendedOmega n) extendedOmega_self (extendedRoots n) (extendedCoord n)
  intro m hm
  exact triangularSeed_dominant_nonnegative f μ hμ m hm
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension PowerSeries PowerSeriesAdjoint
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}
local instance triangularLinearSectionRing : Ring (Torus LaurentRay.vUnit (extendedOmega n)) := Torus.instRing LaurentRay.vUnit (extendedOmega n)
local instance triangularLinearSectionAddCommGroup : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup

local instance triangularLinearSectionAddGroup : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
local instance triangularLinearSectionSub : Sub (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toSub

local instance triangularLinearSectionNonUnitalSemiring : NonUnitalSemiring (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toNonUnitalSemiring
local instance triangularLinearSectionNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toNonUnitalNonAssocSemiring

lemma pureAnchor_of_bridges_zero (m:Lattice n (Cell n)) (hm:∀b,m (.inr b)=0) :
    m=pureAnchor (fun a=>m (.inl a)) := by
  ext a
  cases a with
  | inl a=>rw [pureAnchor_apply_anchor]
  | inr b=>rw [pureAnchor_apply_bridge,hm]

lemma bridges_zero_of_level_zero (m:Lattice n (Cell n))
    (hm:∀b,0 ≤ m (.inr b)) (hK:∀i,levelTotal cellLevel i m=0) : ∀b,m (.inr b)=0 := by
  intro b
  have H:=hK b.1
  change (∑c:Cell n,if cellLevel c=b.1 then m (.inr c) else 0)=0 at H
  have Hp:∀c:Cell n,0 ≤ if cellLevel c=b.1 then m (.inr c) else 0:=by
    intro c; split_ifs <;> first | exact hm c | omega
  have hh: (if cellLevel b=b.1 then m (.inr b) else 0) ≤
      ∑c:Cell n,if cellLevel c=b.1 then m (.inr c) else 0 :=
    Finset.single_le_sum (fun c _=>Hp c) (Finset.mem_univ b)
  rw [H] at hh
  simp only [cellLevel,ite_true] at hh
  exact le_antisymm hh (hm b)

lemma triangularSeed_order_nonnegative {N:ℕ} (f:ElementaryExpr N) :
    ∀m,triangularExpression (n:=n) f m≠0 → 0 ≤ rootOrder (extendedCoord n) m := by
  apply conePolynomial_nonnegativeOrder (extendedOmega n) (extendedRoots n) (extendedCoord n)
    extendedCoord_roots (includeVertices ((N:ℤ) • anchor 0))
  · rw [map_zsmul,map_zsmul,rootOrder_anchor_zero,zsmul_zero]
  · intro m hm
    exact triangularSeed_in_rootCone f m (Finsupp.mem_support_iff.mpr hm)

theorem triangularPure_detect {N:ℕ} (f:ElementaryExpr N)
    (hpure:∀μ:Fin (n+1) → ℤ,triangularExpression f (includeVertices (pureAnchor μ))=0) :
    triangularExpression (n:=n) f=0 := by
  let Y:=homogenize LaurentRay.vUnit (extendedOmega n) (rootOrder (extendedCoord n)) (triangularExpression f)
  have hY:∀k,coeff k Y=0:=by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih=>
      apply Finsupp.ext
      intro m
      by_contra hm
      have hs:triangularExpression f m≠0:=by
        intro hz
        exact hm (by simp [Y,homogenize_coeff,hz])
      have hd:k=(rootOrder (extendedCoord n) m).toNat:=by
        by_contra hd
        exact hm (by simp [Y,homogenize_coeff,hd])
      have hz:0 ≤ rootOrder (extendedCoord n) m:=triangularSeed_order_nonnegative f m hs
      have hdual:m.2=0:=triangularSeed_dual_zero f m (Finsupp.mem_support_iff.mpr hs)
      have hinc:polynomialSectionIncoming (extendedOmega n) (extendedRoots n) (extendedCoord n)
          (triangularExpression f) m=coeff k Y m:=by
        have H:=adjoint_leading
          (rootSectionChart (extendedOmega n) (extendedRoots n) (incomingCovector (extendedOmega n) m)).val
          Y 0 (rootSectionChart (extendedOmega n) (extendedRoots n) _).property.1 k
          (by intro j hj; rw [ih j hj]; rfl)
        simp only [adjoint,mul_zero,zero_mul] at H
        have H := sub_left_inj.mp H
        have hh:=congrArg (fun t:Torus LaurentRay.vUnit (extendedOmega n)=>t m) H
        change coeff k (adjoint _ Y) m=coeff k Y m at hh
        rw [hd,homogenize_adjoint_actual (extendedOmega n) extendedOmega_self
          (rootOrder (extendedCoord n)) _ (triangularExpression f) (triangularSeed_order_nonnegative f) m hz] at hh
        simpa only [polynomialSectionIncoming,polynomialSectionCoefficient,hd] using hh
      have he:m=includeVertices m.1:=Prod.ext rfl hdual
      have hi:triangularIncoming f m.1≠0:=by
        change polynomialSectionIncoming (extendedOmega n) (extendedRoots n) (extendedCoord n)
          (triangularExpression f) (includeVertices m.1)≠0
        rw [←he,hinc]
        exact hm
      have hK:∀i,levelTotal cellLevel i m.1=0:=(triangularExpression_stationary f m.1 hi).1
      have hb:=bridges_zero_of_level_zero m.1
        (fun b=>triangularSeed_nonneg f m (Finsupp.mem_support_iff.mpr hs) (.inr b)) hK
      have hp:=pureAnchor_of_bridges_zero m.1 hb
      apply hs
      rw [he,hp]
      exact hpure _
  apply Finsupp.ext
  intro m
  have H:=congrArg (fun t:Torus LaurentRay.vUnit (extendedOmega n)=>t m) (hY (rootOrder (extendedCoord n) m).toNat)
  simpa only [Y,homogenize_coeff,ite_true,Finsupp.zero_apply] using H
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
