import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TriangularCommutativity

namespace OAI

section
namespace ElementaryPositivity.PowerSeriesAdjoint
open PowerSeries
noncomputable section
variable {A:Type*} [Ring A]
lemma adjoint_product (F X Y:PowerSeries A) (hF:constantCoeff F=1) :
    adjoint F (X*Y)=adjoint F X*adjoint F Y := by
  unfold adjoint
  calc
    _ = F*X*(invOfUnit F 1*F)*Y*invOfUnit F 1 := by rw [invOfUnit_mul F 1 hF]; simp only [mul_one,mul_assoc]
    _ = _ := by simp only [mul_assoc]
end
end ElementaryPositivity.PowerSeriesAdjoint

namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint LaurentPositive
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}
local instance triangularPositivePowersRing : Ring (Torus LaurentRay.vUnit (extendedOmega n)) := Torus.instRing LaurentRay.vUnit (extendedOmega n)
local instance triangularPositivePowersAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommMonoid
local instance triangularPositivePowersAddCommGroup : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance triangularPositivePowersAddGroup : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup

def linearPower : (N:ℕ) → ElementaryExpr N
  | 0 => .one
  | N+1 => .mul (linearPower N) (.atom 1)

lemma linearPower_eval (N:ℕ) :
    triangularExpression (n:=n) (linearPower N)=(triangularExpression (.atom 1))^N := by
  induction N with
  | zero=>rfl
  | succ N ih=>change triangularExpression (linearPower N)*triangularExpression (.atom 1)=_; rw [ih,pow_succ]

lemma homogenize_one_triangular :
    homogenize LaurentRay.vUnit (extendedOmega n) (rootOrder (extendedCoord n)) 1=1 := by
  change homogenize _ _ _ (Torus.monomial LaurentRay.vUnit (extendedOmega n) 0 1)=_
  rw [homogenize_monomial,map_zero,Int.toNat_zero,monomial_zero_eq_C_apply]
  exact map_one PowerSeries.C

lemma triangularLinear_positive (h:Module.Dual ℝ ((Vertex n (Cell n) → ℝ) × (Vertex n (Cell n) → ℝ))) :
    IntegralPositive (extendedOmega n)
      (adjoint (rootSectionChart (extendedOmega n) (extendedRoots n) (h.toAddMonoidHom.comp extendedCast)).val
        (homogenize LaurentRay.vUnit (extendedOmega n) (rootOrder (extendedCoord n)) (triangularExpression (.atom 1)))) := by
  obtain ⟨L,hL⟩:=real_covector_prescribe (extendedRoots n) extendedCast extendedRoots_realIndependent (fun _=>1)
  rw [triangularLinear_theta]
  exact thetaValue_positive (extendedOmega n) (extendedRoots n) extendedCast extendedCast_injective
    (triangularRealForm n) triangularRealForm_self triangularRealForm_compatible L
    (fun _ _ hm=>covector_root_eval (extendedRoots n) extendedCast L hL hm)
    (simpleTotalTransport (extendedOmega n) (extendedRoots n))
    (simpleTotalTransport_positive_prescription _ _ extendedOmega_self) _ h

lemma triangularPower_positive (N:ℕ)
    (h:Module.Dual ℝ ((Vertex n (Cell n) → ℝ) × (Vertex n (Cell n) → ℝ))) :
    IntegralPositive (extendedOmega n)
      (adjoint (rootSectionChart (extendedOmega n) (extendedRoots n) (h.toAddMonoidHom.comp extendedCast)).val
        (homogenize LaurentRay.vUnit (extendedOmega n) (rootOrder (extendedCoord n)) (triangularExpression (linearPower N)))) := by
  induction N with
  | zero=>
    change IntegralPositive _ (adjoint _ (homogenize _ _ _ 1))
    rw [homogenize_one_triangular]
    have H:adjoint (rootSectionChart (extendedOmega n) (extendedRoots n) (h.toAddMonoidHom.comp extendedCast)).val 1=1:=by
      simp only [adjoint,mul_one]
      exact mul_invOfUnit _ 1 (rootSectionChart _ _ _).property.1
    rw [H]
    simpa only [Torus.X_zero,map_one] using completedPositive_C_X (extendedOmega n) 0
  | succ N ih=>
    change IntegralPositive _ (adjoint _ (homogenize _ _ _
      (triangularExpression (linearPower N)*triangularExpression (.atom 1))))
    rw [homogenize_mul _ _ _ _ _ (triangularSeed_order_nonnegative _) (triangularSeed_order_nonnegative _),
      adjoint_product _ _ _ (rootSectionChart _ _ _).property.1]
    exact ih.mul _ (triangularLinear_positive h)

lemma triangularPower_incoming_positive (N k:ℕ) :
    TorusPositive (extendedOmega n)
      (sectionIncoming LaurentRay.vUnit (extendedOmega n) (extendedRoots n)
        (simpleTotalTransport (extendedOmega n) (extendedRoots n))
        (includeVertices ((N:ℤ) • anchor 0)) k
        (polynomialInitial (extendedOmega n) (extendedRoots n) (extendedCoord n)
          (triangularExpression (linearPower N)))) := by
  intro m
  rw [sectionIncoming_apply]
  split_ifs
  · have hcov:(((triangularRealForm n).flip (extendedCast m)).toAddMonoidHom.comp extendedCast) = incomingCovector (extendedOmega n) m := by
      ext a
      exact triangularRealForm_compatible a m
    have H:=triangularPower_positive (n:=n) N ((triangularRealForm n).flip (extendedCast m)) k m
    rw [hcov,rootSectionChart_action] at H
    exact H
  · exact positive_zero
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension PowerSeries PowerSeriesAdjoint LaurentPositive
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}
local instance triangularOrdinaryPowersRing : Ring (Torus LaurentRay.vUnit (extendedOmega n)) := Torus.instRing LaurentRay.vUnit (extendedOmega n)
local instance triangularOrdinaryPowersAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommMonoid
local instance triangularOrdinaryPowersAddCommGroup : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance triangularOrdinaryPowersAddGroup : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
local instance triangularOrdinaryPowersSub : Sub (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toSub

lemma triangularLinear_ordinary_positive : TorusPositive (extendedOmega n) (triangularExpression (.atom 1)) := by
  rw [triangularLinear_sum]
  exact TorusPositive.sum _ _ _ (fun a _=>torusPositive_monomial _ _ _ positive_one)

lemma triangularLinear_retain (a:Fin (n+1)) :
    TorusPositive (extendedOmega n)
      (triangularExpression (.atom 1)-Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (anchor a))) := by
  have H:(∑b∈(Finset.univ:Finset (Vertex n (Cell n))).erase (.inl a),
      Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (Pi.single b (1:ℤ))))=
      triangularExpression (.atom 1)-Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (anchor a)) := by
    apply Finsupp.ext
    intro m
    rw [torus_sub_apply,triangularLinear_sum]
    simp only [Finsupp.finsetSum_apply]
    have H:=Finset.sum_erase_add
      (s:=(Finset.univ:Finset (Vertex n (Cell n))))
      (fun b=>(Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (Pi.single b (1:ℤ)))) m)
      (Finset.mem_univ (.inl a))
    change _ = _ - (Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (Pi.single (.inl a) (1:ℤ)))) m
    rw [←H,add_sub_cancel_right]
    let ev:Torus LaurentRay.vUnit (extendedOmega n) →+ LaurentSeries ℚ :=
      {toFun:=fun f=>f m,map_zero':=rfl,map_add':=fun _ _=>rfl}
    exact map_sum ev _ _
  rw [←H]
  exact TorusPositive.sum _ _ _ (fun b _=>torusPositive_monomial _ _ _ positive_one)

def natAnchor (μ:Fin (n+1) → ℕ) : Lattice n (Cell n) := pureAnchor (fun a=>(μ a:ℤ))
lemma natAnchor_zero : natAnchor (n:=n) 0=0 := by
  ext a
  cases a <;> simp [natAnchor,pureAnchor_apply_anchor,pureAnchor_apply_bridge]

lemma natAnchor_step (μ:Fin (n+1) → ℕ) (a:Fin (n+1)) (ha:0<μ a) :
    natAnchor μ=natAnchor (Function.update μ a (μ a-1))+anchor a := by
  ext b
  cases b with
  | inl b=>
    simp only [natAnchor,pureAnchor_apply_anchor,Pi.add_apply,anchor,Pi.single_apply,Sum.inl.injEq]
    by_cases hb:b=a
    · subst b; simp only [Function.update_self,ite_true]; omega
    · rw [Function.update_of_ne hb,ite_eq_right hb]
      simp
  | inr b=>simp [natAnchor,pureAnchor_apply_bridge,anchor]

lemma natural_sum_step (μ:Fin (n+1) → ℕ) (a:Fin (n+1)) (ha:0<μ a) :
    (∑b,Function.update μ a (μ a-1) b)+1=∑b,μ b := by
  symm
  calc
    _ = ∑b,(Function.update μ a (μ a-1) b+(if b=a then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb:b=a
      · subst b; simp only [Function.update_self,ite_true]; omega
      · rw [Function.update_of_ne hb,ite_eq_right hb]; omega
    _ = _ := by rw [Finset.sum_add_distrib]; simp

lemma triangularPower_ordinary_retain (N:ℕ) (μ:Fin (n+1) → ℕ) (hμ:∑a,μ a=N) :
    TorusPositive (extendedOmega n)
      (triangularExpression (linearPower N)-Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (natAnchor μ))) := by
  induction N generalizing μ with
  | zero=>
    have hz:μ=0:=by
      ext a
      have H:μ a ≤ ∑b,μ b:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ a)
      have H':μ a=0:=by omega
      exact H'
    subst μ
    rw [natAnchor_zero,map_zero,Torus.X_zero,linearPower_eval,pow_zero,sub_self]
    exact torusPositive_zero _
  | succ N ih=>
    obtain ⟨a,_,ha⟩:=Finset.exists_ne_zero_of_sum_ne_zero (show (∑a,μ a)≠0 by omega)
    have ha':0<μ a:=Nat.pos_of_ne_zero ha
    let ν:=Function.update μ a (μ a-1)
    have hν:∑b,ν b=N:=by
      change (∑b,Function.update μ a (μ a-1) b)=N
      have :=natural_sum_step μ a ha'
      omega
    have hp:(triangularExpression (linearPower N)-Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (natAnchor ν)))*
        triangularExpression (.atom 1)+Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (natAnchor ν))*
        (triangularExpression (.atom 1)-Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (anchor a)))=
        triangularExpression (linearPower (N+1))-Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (natAnchor μ)):=by
      have hpair:extendedOmega n (includeVertices (natAnchor ν)) (includeVertices (anchor a))=0:=by
        rw [extendedOmega_original,triangularOmega_skew,natAnchor,anchor_pair_pure,neg_zero]
      have hm:Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (natAnchor ν))*
          Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (anchor a))=
          Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (natAnchor μ)):=by
        rw [Torus.X_mul_X_of_pairing_zero _ _ _ _ hpair,←map_add,←natAnchor_step μ a ha']
      change (_-_)*_+_*(_-_)=triangularExpression (linearPower N)*triangularExpression (.atom 1)-_
      calc
        _ = triangularExpression (linearPower N)*triangularExpression (.atom 1)-
            Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (natAnchor ν))*
            Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (anchor a)) := by noncomm_ring
        _ = _ := by rw [hm]
    rw [←hp]
    exact ((ih ν hν).mul _ triangularLinear_ordinary_positive).add _
      ((torusPositive_monomial _ _ _ positive_one).mul _ (triangularLinear_retain a))
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
