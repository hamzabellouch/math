import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.ConeSectionDomination
import OAI.Combinatorics.Chromatic.Walls.TriangularPositivePowers

namespace OAI

section
namespace ElementaryPositivity.LaurentPositive
noncomputable section
lemma Positive.nonneg {f:LaurentSeries ℚ} (hf:Positive f) (j:ℤ) : 0 ≤ f.coeff j := by
  obtain ⟨k,hk⟩:=hf j
  rw [hk]
  positivity
lemma Positive.eq_zero_of_neg {f:LaurentSeries ℚ} (hf:Positive f) (hn:Positive (-f)) : f=0 := by
  apply HahnSeries.ext
  funext j
  have H:=hn.nonneg j
  simp only [HahnSeries.coeff_neg] at H
  simpa only [HahnSeries.coeff_zero] using (le_antisymm (by linarith) (hf.nonneg j))
lemma Positive.eq_zero_of_sub {f g:LaurentSeries ℚ} (hf:Positive f) (hgf:Positive (g-f))
    (hg:g=0) : f=0 := by
  apply hf.eq_zero_of_neg
  simpa only [hg,zero_sub] using hgf
lemma Positive.ne_zero_of_sub_one {f:LaurentSeries ℚ} (h:Positive (f-1)) : f≠0 := by
  intro hf
  have H:=h.nonneg 0
  simp only [hf,zero_sub,HahnSeries.coeff_neg,HahnSeries.coeff_one,ite_true] at H
  norm_num at H
end
end ElementaryPositivity.LaurentPositive

end
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

def triangularBase (N:ℕ) : Extended (Vertex n (Cell n)) := includeVertices ((N:ℤ) • anchor 0)
lemma triangularBase_order (N:ℕ) : rootOrder (extendedCoord n) (triangularBase N)=0 := by
  rw [triangularBase,map_zsmul,map_zsmul,rootOrder_anchor_zero,zsmul_zero]
lemma triangularExpression_initial_graded {N:ℕ} (f:ElementaryExpr N) :
    ShiftGraded LaurentRay.vUnit (extendedOmega n) (extendedRoots n) (triangularBase N)
      (polynomialInitial (extendedOmega n) (extendedRoots n) (extendedCoord n) (triangularExpression f)) := by
  apply polynomialInitial_graded (extendedOmega n) (extendedRoots n) (extendedCoord n)
    extendedCoord_roots (triangularBase N) (triangularBase_order N)
  intro m hm
  exact triangularSeed_in_rootCone f m (Finsupp.mem_support_iff.mpr hm)
lemma triangularPower_incoming_retain (N:ℕ) (μ:Fin (n+1) → ℕ) (hμ:∑a,μ a=N)
    (hdom:∀i:Fin n,μ i.succ ≤ μ i.castSucc) (d:ℕ)
    (hm:HasRootDegree (extendedRoots n) d (includeVertices (natAnchor μ)-triangularBase N)) (k:ℕ) :
    TorusPositive (extendedOmega n)
      (sectionIncoming LaurentRay.vUnit (extendedOmega n) (extendedRoots n)
        (simpleTotalTransport (extendedOmega n) (extendedRoots n)) (triangularBase N) k
        (polynomialInitial (extendedOmega n) (extendedRoots n) (extendedCoord n) (triangularExpression (linearPower N)))-
        coneDelta (extendedOmega n) d (includeVertices (natAnchor μ)) k) := by
  by_cases hk:k=d
  · subst k
    rw [coneDelta,ite_eq_left rfl]
    intro m
    rw [torus_sub_apply]
    by_cases he:m=includeVertices (natAnchor μ)
    · subst m
      rw [polynomialInitial_incoming (extendedOmega n) extendedOmega_self (extendedRoots n)
        (extendedCoord n) extendedCoord_roots (triangularBase N) (triangularBase_order N)
        (triangularExpression (linearPower N)) (by intro m hm; exact triangularSeed_in_rootCone _ m (Finsupp.mem_support_iff.mpr hm)) d _ hm]
      have H:=triangularPure_incoming (linearPower N) (fun a=>(μ a:ℤ)) (fun i=>Int.ofNat_le.mpr (hdom i))
      change polynomialSectionIncoming _ _ _ _ (includeVertices (natAnchor μ))=_ at H
      rw [H]
      simpa only [torus_sub_apply,natAnchor] using triangularPower_ordinary_retain N μ hμ (includeVertices (natAnchor μ))
    · have HX:Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (natAnchor μ)) m=0:=by
        exact Finsupp.single_eq_of_ne he
      rw [HX,sub_zero]
      exact triangularPower_incoming_positive N d m
  · rw [coneDelta,ite_eq_right hk,sub_zero]
    exact triangularPower_incoming_positive N k

def triangularConeTheta (N d:ℕ) (μ:Fin (n+1) → ℕ) (h:Extended (Vertex n (Cell n)) →+ ℝ) :=
  coneThetaValue (extendedOmega n) (extendedRoots n) (simpleTotalTransport (extendedOmega n) (extendedRoots n))
    (triangularBase N) d (includeVertices (natAnchor μ)) h

lemma triangularConeTheta_positive (N d:ℕ) (μ:Fin (n+1) → ℕ)
    (hm:HasRootDegree (extendedRoots n) d (includeVertices (natAnchor μ)-triangularBase N))
    (h:Module.Dual ℝ ((Vertex n (Cell n) → ℝ) × (Vertex n (Cell n) → ℝ))) :
    IntegralPositive (extendedOmega n) (triangularConeTheta N d μ (h.toAddMonoidHom.comp extendedCast)) := by
  obtain ⟨L,hL⟩:=real_covector_prescribe (extendedRoots n) extendedCast extendedRoots_realIndependent (fun _=>1)
  exact coneThetaValue_positive (extendedOmega n) (extendedRoots n)
    (simpleTotalTransport (extendedOmega n) (extendedRoots n)) (triangularBase N)
    extendedCast extendedCast_injective (triangularRealForm n) triangularRealForm_self triangularRealForm_compatible
    L (fun _ _ hm=>covector_root_eval (extendedRoots n) extendedCast L hL hm)
    (simpleTotalTransport_positive_prescription _ _ extendedOmega_self) d _ hm h

lemma triangularPower_domination (N d:ℕ) (μ:Fin (n+1) → ℕ) (hμ:∑a,μ a=N)
    (hdom:∀i:Fin n,μ i.succ ≤ μ i.castSucc)
    (hm:HasRootDegree (extendedRoots n) d (includeVertices (natAnchor μ)-triangularBase N))
    (h:Module.Dual ℝ ((Vertex n (Cell n) → ℝ) × (Vertex n (Cell n) → ℝ))) :
    IntegralPositive (extendedOmega n)
      (adjoint (rootSectionChart (extendedOmega n) (extendedRoots n) (h.toAddMonoidHom.comp extendedCast)).val
        (homogenize LaurentRay.vUnit (extendedOmega n) (rootOrder (extendedCoord n)) (triangularExpression (linearPower N)))-
        triangularConeTheta N d μ (h.toAddMonoidHom.comp extendedCast)) := by
  rw [rootSectionChart_action]
  obtain ⟨L,hL⟩:=real_covector_prescribe (extendedRoots n) extendedCast extendedRoots_realIndependent (fun _=>1)
  exact coneTheta_domination (extendedOmega n) (extendedRoots n)
    (simpleTotalTransport (extendedOmega n) (extendedRoots n)) (triangularBase N)
    extendedCast extendedCast_injective (triangularRealForm n) triangularRealForm_self triangularRealForm_compatible
    L (fun _ _ hm=>covector_root_eval (extendedRoots n) extendedCast L hL hm)
    (simpleTotalTransport_positive_prescription _ _ extendedOmega_self) _
    (triangularExpression_initial_graded (linearPower N)) d _ hm
    (triangularPower_incoming_retain N μ hμ hdom d hm) h

lemma adjoint_one_torus (X:PowerSeries (Torus LaurentRay.vUnit (extendedOmega n))) : adjoint 1 X=X := by
  have hi:invOfUnit (1:PowerSeries (Torus LaurentRay.vUnit (extendedOmega n))) 1=1:=by
    simpa only [mul_one] using (invOfUnit_mul (1:PowerSeries (Torus LaurentRay.vUnit (extendedOmega n))) 1 (by simp))
  simp only [adjoint,one_mul,hi,mul_one]

lemma triangularTheta_support (N d:ℕ) (μ:Fin (n+1) → ℕ) (hμ:∑a,μ a=N)
    (hdom:∀i:Fin n,μ i.succ ≤ μ i.castSucc)
    (hm:HasRootDegree (extendedRoots n) d (includeVertices (natAnchor μ)-triangularBase N))
    (h:Module.Dual ℝ ((Vertex n (Cell n) → ℝ) × (Vertex n (Cell n) → ℝ)))
    (hneg:∀k,0<k → ∀m,HasRootDegree (extendedRoots n) k m → h (extendedCast m)<0)
    (k:ℕ) (m:Extended (Vertex n (Cell n)))
    (hs:coeff k (triangularConeTheta N d μ (h.toAddMonoidHom.comp extendedCast)) m≠0) :
    triangularExpression (linearPower N) m≠0 := by
  intro hz
  have Hp:=triangularConeTheta_positive N d μ hm h k m
  have Hr:=triangularPower_domination N d μ hμ hdom hm h
  rw [rootSectionChart_negative _ _ _ hneg,adjoint_one_torus] at Hr
  have HH := Hr k m
  rw [map_sub,torus_sub_apply] at HH
  exact hs (Hp.eq_zero_of_sub HH (by simp [homogenize_coeff,hz]))
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension
open Classical
noncomputable section
variable {n:ℕ}
lemma pureAnchor_injective : Function.Injective (pureAnchor (n:=n)) := by
  intro μ ν he
  funext a
  have H:=congrArg (fun m:Lattice n (Cell n)=>m (.inl a)) he
  simpa only [pureAnchor_apply_anchor] using H

lemma stationary_pure_dominant (μ:Fin (n+1) → ℤ)
    (hxi:∀b:Cell n,0 ≤ triangularOmega n (eventRoot cellLevel 0 b) (pureAnchor μ)) :
    ∀i:Fin n,μ i.succ ≤ μ i.castSucc := by
  intro i
  let b:Cell n:=⟨i,⟨0,by omega⟩⟩
  have H:=hxi b
  simp only [eventRoot,Nat.cast_zero,zero_smul,add_zero,map_sub,AddMonoidHom.sub_apply,
    bridge_pair_pure,anchor_pair_pure,sub_zero] at H
  change 0 ≤ μ i.castSucc-μ i.succ at H
  omega

lemma triangularPureIncoming_dominant {N:ℕ} (f:ElementaryExpr N) (μ:Fin (n+1) → ℤ)
    (h:triangularIncoming f (pureAnchor μ)≠0) : ∀i:Fin n,μ i.succ ≤ μ i.castSucc :=
  stationary_pure_dominant μ (triangularExpression_stationary f (pureAnchor μ) h).2.1

lemma triangularPureIncoming_delta {N:ℕ} (f:ElementaryExpr N) (μ:Fin (n+1) → ℤ)
    (hμ:∀i:Fin n,μ i.succ ≤ μ i.castSucc)
    (hp:∀ν:Fin (n+1) → ℤ,(∀i:Fin n,ν i.succ ≤ ν i.castSucc) →
      triangularExpression f (includeVertices (pureAnchor ν))=if ν=μ then 1 else 0)
    (ν:Fin (n+1) → ℤ) :
    triangularIncoming f (pureAnchor ν)=if ν=μ then 1 else 0 := by
  by_cases hd:∀i:Fin n,ν i.succ ≤ ν i.castSucc
  · rw [triangularPure_incoming f ν hd,hp ν hd]
  · have hne:ν≠μ:=by intro h; subst ν; exact hd hμ
    rw [ite_eq_right hne]
    by_contra hh
    exact hd (triangularPureIncoming_dominant f ν hh)
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
