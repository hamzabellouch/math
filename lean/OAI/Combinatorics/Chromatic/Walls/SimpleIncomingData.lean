import Mathlib
import OAI.Combinatorics.Chromatic.Walls.GlobalWallPositive
import OAI.Combinatorics.Chromatic.Walls.OffCutJoint

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d)

def simpleDatum (i : I) : WallUnitDatum M := ⟨1,simpleRoot C i,0,-1⟩
def simpleIncomingList : List (WallUnitDatum M) := (Finset.univ.toList).map (simpleDatum C)
lemma simpleDatum_allowed (i : I) : (simpleDatum C i).Allowed C (fun _=>True) :=
  ⟨Nat.zero_lt_one,simpleRoot_degree C i,True.intro⟩
lemma simpleIncomingList_allowed : ∀u∈simpleIncomingList C,u.Allowed C (fun _=>True) := by
  intro u hu
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hu
  exact simpleDatum_allowed C i

def simpleTotalTransport : CompletedPositive LaurentRay.vUnit Ω C := literalTotalTransport Ω C (simpleIncomingList C)
lemma simpleTotalTransport_positive_prescription (hΩ : ∀m,Ω m m=0) :
    PositiveIncomingPrescription Ω C (simpleTotalTransport Ω C) :=
  literalTotalTransport_prescription Ω C hΩ _ (simpleIncomingList_allowed C)

omit [Fintype I] in
include hcoord in
lemma simpleRoot_coordinates (i j : I) : coord (simpleRoot C i) j= (Pi.single i 1 : I → ℤ) j := by
  exact congrFun (hcoord _) j
include hcoord in
lemma nonpDegree_simple_self (pc : I) : nonpDegree coord pc (simpleRoot C pc)=0 := by
  change (∑i∈Finset.univ.erase pc,coord (simpleRoot C pc) i)=0
  apply Finset.sum_eq_zero
  intro i hi
  rw [simpleRoot_coordinates C coord hcoord]
  simp [(Finset.mem_erase.mp hi).1]
include hcoord in
lemma simple_off_fiber (pc i : I) (hi : i≠pc) (α : I → ℤ) (σ : ℤ) :
    simpleRoot C i∈fiberCone coord pc α σ := by
  have hc : coord (simpleRoot C i) pc=0:=by rw [simpleRoot_coordinates C coord hcoord]; simp [hi.symm]
  constructor
  · rw [hc]
  · rw [hc]
    change 0≤∑j∈Finset.univ.erase pc,max 0 (-σ*α j)*coord (simpleRoot C i) j
    apply Finset.sum_nonneg
    intro j hj
    apply mul_nonneg (le_max_left _ _)
    rw [simpleRoot_coordinates C coord hcoord]
    by_cases hji : j=i
    · subst j; simp
    · simp [hji]
include hcoord in
lemma positive_nonp_not_simple_ray (pc : I) (r : M) (hr : 0<nonpDegree coord pc r) :
    ¬OnPositiveRay r (simpleRoot C pc) := by
  rintro ⟨a,b,ha,hb,he⟩
  have HH:=congrArg (nonpDegree coord pc) he
  simp only [map_nsmul,nonpDegree_simple_self C coord hcoord pc,nsmul_zero] at HH
  have hb' : 0<(b:ℤ):=by exact_mod_cast hb
  have Hpos : 0<(b:ℤ)*nonpDegree coord pc r:=mul_pos hb' hr
  rw [nsmul_eq_mul] at HH
  omega
include hcoord in
lemma simpleIncomingRay_fiber (pc : I) (r : M) (hr : 0<nonpDegree coord pc r)
    (α : I → ℤ) (σ : ℤ) :
    literalIncomingRay Ω (simpleIncomingList C) r∈literalRootProducts Ω C (fun m=>m∈fiberCone coord pc α σ) := by
  classical
  refine ⟨(simpleIncomingList C).filter (fun u=>OnPositiveRay r u.root),?_,rfl⟩
  intro u hu
  have hu':=List.mem_filter.mp hu
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hu'.1
  have hri : OnPositiveRay r (simpleRoot C i):=by exact of_decide_eq_true hu'.2
  have hip : i≠pc:=by intro hh; subst i; exact positive_nonp_not_simple_ray C coord hcoord pc r hr hri
  exact ⟨Nat.zero_lt_one,simpleRoot_degree C i,simple_off_fiber C coord hcoord pc i hip α σ⟩
include hcoord in
lemma simpleIncomingCompleted_fiber (pc : I) (r : M) (hr : 0<nonpDegree coord pc r)
    (α : I → ℤ) (σ : ℤ) :
    ∀j,coeff j (literalIncomingCompleted Ω C (simpleIncomingList C) (simpleIncomingList_allowed C) r).val∈
      supportedSubring LaurentRay.vUnit Ω (fiberCone coord pc α σ) := by
  intro j
  cases j with
  | zero=>
    rw [coeff_zero_eq_constantCoeff,(literalIncomingCompleted Ω C _ _ r).property.1]
    exact (supportedSubring LaurentRay.vUnit Ω _).one_mem
  | succ j=>
    exact literalRootProducts_strictSupport Ω C (fun m=>m∈fiberCone coord pc α σ)
      (fun a b ha hb=>(fiberCone coord pc α σ).add_mem ha hb)
      (simpleIncomingRay_fiber Ω C coord hcoord pc r hr α σ) j

omit [DecidableEq I] in
lemma literalTotalTransport_ray_prescription (hΩ : ∀m,Ω m m=0)
    (l : List (WallUnitDatum M)) (hl : ∀u∈l,u.Allowed C (fun _=>True)) (r : M) :
    ∀n m,OnPositiveRay r m →
      coeff n (FormalLog.log (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω m)
        (literalTotalTransport Ω C l)).val) m=
      coeff n (FormalLog.log (literalIncomingCompleted Ω C l hl r).val) m := by
  classical
  intro n m hm
  cases n with
  | zero=>simp only [coeff_zero_eq_constantCoeff,FormalLog.log_constant,Finsupp.zero_apply]
  | succ n=>
    by_cases hroot : HasRootDegree C (n+1) m
    · have H:=congrArg (fun x : Torus LaurentRay.vUnit Ω=>x m)
        (incomingSolution_prescription LaurentRay.vUnit Ω C hΩ _ (literalIncomingLog_graded Ω C l) n)
      rw [incomingCoefficient_apply,ite_eq_left hroot,literalIncomingLog_apply,ite_eq_left hroot] at H
      change coeff (n+1) (FormalLog.log (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω m)
        (literalTotalTransport Ω C l)).val) m=coeff (n+1) (FormalLog.log (literalIncomingRay Ω l r)) m
      rw [literalIncomingRay_eq Ω l hm]
      exact H
    · rw [root_graded_log LaurentRay.vUnit Ω C _ (n+1) m hroot,
        root_graded_log LaurentRay.vUnit Ω C (literalIncomingCompleted Ω C l hl r) (n+1) m hroot]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
