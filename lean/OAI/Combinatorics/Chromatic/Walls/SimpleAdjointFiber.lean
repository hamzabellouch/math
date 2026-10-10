import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TorusAdjointExpansion
import OAI.Combinatorics.Chromatic.GradedAlgebra.MutationRootMap
import OAI.Combinatorics.Chromatic.GradedAlgebra.SimpleBinomial

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance : AddCommGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommGroup
local instance : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance : Sub (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toSub

def simpleOriented (pos : Bool) (p : M) : PowerSeries (Torus LaurentRay.vUnit Ω) :=
  if pos then normalizedSimple Ω p else invOfUnit (normalizedSimple Ω p) 1

def sideSign (pos : Bool) : ℤ := if pos then 1 else -1
lemma sideSign_neg (pos : Bool) : sideSign (!pos)= -sideSign pos := by cases pos <;> rfl
lemma simpleOriented_support (hΩ : ∀m,Ω m m=0) (pos : Bool) (p m x : M)
    (N : ℕ) (htrend : 0≤ sideSign pos*Ω p m)
    (hx : coeff N (adjoint (simpleOriented Ω pos p)
      (PowerSeries.C (Torus.X LaurentRay.vUnit Ω m))) x≠0) :
    (N:ℤ)≤ sideSign pos*Ω p m ∧ x=m+N • p := by
  let t:=(sideSign pos*Ω p m).toNat
  have ht : (t:ℤ)=sideSign pos*Ω p m:=Int.toNat_of_nonneg htrend
  have HG : N≤t ∧ x=m+N • p:=by
    cases pos
    · apply normalizedSimple_inverse_adjoint_support Ω hΩ p m x t N ?_ hx
      simpa only [sideSign,Bool.false_eq_true,ite_false,neg_one_mul,Int.neg_neg] using congrArg Neg.neg ht.symm
    · apply normalizedSimple_adjoint_support Ω hΩ p m x t N ?_ hx
      simpa only [sideSign,ite_true,one_mul] using ht.symm
  exact ⟨by rw [←ht]; exact_mod_cast HG.1,HG.2⟩

include hcoord in
lemma simpleOriented_adjoint_fiber (hΩ : ∀m,Ω m m=0) (pos : Bool)
    (A : PowerSeries (Torus LaurentRay.vUnit Ω)) (N : ℕ) (n : ℤ)
    (hA : ∀j≤N,coeff j A∈rootGrade LaurentRay.vUnit Ω C j)
    (htrend : ∀j≤N,∀m,coeff j A m≠0 → 0≤ sideSign pos*Ω (simpleRoot C pc) m)
    (hbound : ∀j≤N,∀m,coeff j A m≠0 → nonpDegree coord pc m≤n →
      m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    ∀x,coeff N (adjoint (simpleOriented Ω pos (simpleRoot C pc)) A) x≠0 →
      nonpDegree coord pc x≤n →
      x∈fiberCone coord pc (mutationPairing Ω C pc) (-sideSign pos) := by
  classical
  intro x hx hxn
  rw [coeff_adjoint_expansion,torus_ring_eval_sum] at hx
  obtain ⟨j,hj,hterm⟩:=Finset.exists_ne_zero_of_sum_ne_zero hx
  have hjN : j≤N:=by have H:=Finset.mem_range.mp hj; omega
  rw [adjoint_torus_expansion] at hterm
  obtain ⟨m,hm,hterm⟩:=Finset.exists_ne_zero_of_sum_ne_zero hterm
  have hmA : coeff j A m≠0:=(mul_ne_zero_iff.mp hterm).1
  have hmAd:=(mul_ne_zero_iff.mp hterm).2
  have HS:=simpleOriented_support Ω hΩ pos (simpleRoot C pc) m x (N-j)
    (htrend j hjN m hmA) hmAd
  have hroot : HasRootDegree C j m:=by
    by_contra hh
    exact hmA (hA j hjN m hh)
  have hw : nonpDegree coord pc x=nonpDegree coord pc m:=by
    rw [HS.2,map_add,map_nsmul,nonpDegree_simple_self C coord hcoord,nsmul_zero,add_zero]
  rw [hw] at hxn
  rw [HS.2]
  exact fiber_shift_bound Ω C coord hcoord pc hΩ hroot (sideSign pos) (N-j) HS.1
    (hbound j hjN m hmA hxn)
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)

def mutationLinearPiece (pos : Bool) : M →+ M :=
  if pos then AddMonoidHom.id M else mutationShear Ω (simpleRoot C pc)

omit [Fintype I] in
include hcoord in
lemma mutationLinearPiece_coordinates (pos : Bool) (m : M) :
    coord (mutationLinearPiece Ω C pc pos m)=
      if pos then coord m else coord m-Ω (simpleRoot C pc) m • Pi.single pc 1 := by
  cases pos
  · simp only [mutationLinearPiece,Bool.false_eq_true,ite_false,mutationShear,
      AddMonoidHom.coe_mk,ZeroHom.coe_mk,map_sub,map_zsmul]
    congr 1
    change _ • coord (C (Pi.single pc 1))=_
    rw [hcoord]
  · rfl

include hcoord in
lemma mutatedCoordinate_off (pos : Bool) (m : M) (i : I) (hi : i≠pc) :
    mutatedCoordinates Ω C coord pc (mutationLinearPiece Ω C pc pos m) i=coord m i := by
  change mutatedCoefficientMap pc (mutationPairing Ω C pc)
    (coord (mutationLinearPiece Ω C pc pos m)) i=_
  rw [mutatedCoefficientMap_off pc _ _ i hi,mutationLinearPiece_coordinates Ω C coord hcoord]
  cases pos <;> simp [hi]

include hcoord in
lemma mutatedCoordinate_at (hΩ : ∀m,Ω m m=0) (pos : Bool) {n : ℕ} {m : M}
    (hm : HasRootDegree C n m) :
    mutatedCoordinates Ω C coord pc (mutationLinearPiece Ω C pc pos m) pc=
      fiberUpper coord pc (mutationPairing Ω C pc) (sideSign pos) m-coord m pc := by
  change mutatedCoefficientMap pc (mutationPairing Ω C pc)
    (coord (mutationLinearPiece Ω C pc pos m)) pc=_
  rw [mutatedCoefficientMap_at]
  have HH : (∑j∈Finset.univ.erase pc,max 0 (-mutationPairing Ω C pc j)*
      coord (mutationLinearPiece Ω C pc pos m) j)=
      ∑j∈Finset.univ.erase pc,max 0 (-mutationPairing Ω C pc j)*coord m j:=by
    apply Finset.sum_congr rfl
    intro j hj
    rw [mutationLinearPiece_coordinates Ω C coord hcoord]
    cases pos <;> simp [(Finset.mem_erase.mp hj).1]
  rw [HH,mutationLinearPiece_coordinates Ω C coord hcoord]
  cases pos
  · simp only [Bool.false_eq_true,ite_false,Pi.sub_apply,Pi.smul_apply,Pi.single_eq_same,
      smul_eq_mul,mul_one,sideSign]
    have Hflip:=fiberUpper_flip coord pc (mutationPairing Ω C pc) 1 m
    rw [←root_pairing_coordinates Ω C coord hcoord pc hΩ hm] at Hflip
    change fiberUpper coord pc (mutationPairing Ω C pc) (-1) m=
      fiberUpper coord pc (mutationPairing Ω C pc) 1 m+1*Ω (simpleRoot C pc) m at Hflip
    rw [Hflip]
    change -(coord m pc-Ω (simpleRoot C pc) m)+
        (∑j∈Finset.univ.erase pc,max 0 (-mutationPairing Ω C pc j)*coord m j)=_
    simp only [fiberUpper,AddMonoidHom.coe_mk,ZeroHom.coe_mk,neg_mul,one_mul]
    ring
  · simp only [ite_true,sideSign]
    change -coord m pc+(∑j∈Finset.univ.erase pc,max 0 (-mutationPairing Ω C pc j)*coord m j)=_
    simp only [fiberUpper,AddMonoidHom.coe_mk,ZeroHom.coe_mk,neg_mul,one_mul]
    ring

include hcoord in
lemma mutated_nonpDegree (pos : Bool) (m : M) :
    nonpDegree (mutatedCoordinates Ω C coord pc) pc (mutationLinearPiece Ω C pc pos m)=
      nonpDegree coord pc m := by
  change (∑i∈Finset.univ.erase pc,mutatedCoordinates Ω C coord pc (mutationLinearPiece Ω C pc pos m) i)=_
  apply Finset.sum_congr rfl
  intro i hi
  exact mutatedCoordinate_off Ω C coord hcoord pc pos m i (Finset.mem_erase.mp hi).1

include hcoord in
lemma mutationLinearPiece_span {n : ℕ} {m : M} (hm : HasRootDegree C n m) (pos : Bool) :
    C (coord (mutationLinearPiece Ω C pc pos m))=mutationLinearPiece Ω C pc pos m := by
  have hc : C (coord m)=m:=by
    obtain ⟨d,hd,hcd,hem⟩:=root_coordinates C coord hcoord hm
    rw [←hem,hcoord]
  rw [mutationLinearPiece_coordinates Ω C coord hcoord]
  cases pos
  · simp only [Bool.false_eq_true,ite_false,map_sub,map_zsmul,hc,mutationLinearPiece,mutationShear,
      AddMonoidHom.coe_mk,ZeroHom.coe_mk,simpleRoot]
  · exact hc

include hcoord in
lemma mutated_span {n : ℕ} {m : M} (hm : HasRootDegree C n m) (pos : Bool) :
    mutatedRoots Ω C pc (mutatedCoordinates Ω C coord pc (mutationLinearPiece Ω C pc pos m))=
      mutationLinearPiece Ω C pc pos m := by
  change C (mutatedCoefficientMap pc (mutationPairing Ω C pc)
    (mutatedCoefficientMap pc (mutationPairing Ω C pc) (coord (mutationLinearPiece Ω C pc pos m))))=_
  rw [mutatedCoefficientMap_involutive]
  exact mutationLinearPiece_span Ω C coord hcoord pc hm pos

include hcoord in
lemma mutation_root_image (hΩ : ∀m,Ω m m=0) (pos : Bool) {n : ℕ} {m : M}
    (hm : HasRootDegree C n m)
    (hb : m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    ∃d : ℕ,HasRootDegree (mutatedRoots Ω C pc) d (mutationLinearPiece Ω C pc pos m) ∧
      (d:ℤ)=nonpDegree coord pc m+
        fiberUpper coord pc (mutationPairing Ω C pc) (sideSign pos) m-coord m pc := by
  let q:=mutatedCoordinates Ω C coord pc (mutationLinearPiece Ω C pc pos m)
  have hq : ∀i,0≤q i:=by
    intro i
    by_cases hi : i=pc
    · subst i
      change 0 ≤ mutatedCoordinates Ω C coord pc (mutationLinearPiece Ω C pc pos m) pc
      rw [mutatedCoordinate_at Ω C coord hcoord pc hΩ pos hm]
      exact sub_nonneg.mpr hb.2
    · change 0 ≤ mutatedCoordinates Ω C coord pc (mutationLinearPiece Ω C pc pos m) i
      rw [mutatedCoordinate_off Ω C coord hcoord pc pos m i hi]
      obtain ⟨a,ha,hac,he⟩:=root_coordinates C coord hcoord hm
      rw [hac]
      exact Int.natCast_nonneg _
  refine ⟨∑i,(q i).toNat,⟨fun i=>(q i).toNat,rfl,?_⟩,?_⟩
  · have he : (fun i=>((q i).toNat:ℤ))=q:=funext (fun i=>Int.toNat_of_nonneg (hq i))
    rw [he]
    exact mutated_span Ω C coord hcoord pc hm pos
  · rw [Nat.cast_sum]
    simp only [Int.toNat_of_nonneg (hq _)]
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ pc)]
    have ha : q pc=fiberUpper coord pc (mutationPairing Ω C pc) (sideSign pos) m-coord m pc:=
      mutatedCoordinate_at Ω C coord hcoord pc hΩ pos hm
    have ho : (∑i∈Finset.univ.erase pc,q i)=nonpDegree coord pc m:=
      mutated_nonpDegree Ω C coord hcoord pc pos m
    rw [ha,ho]
    ring
end
end ElementaryPositivity.QuantumTorus

end

end OAI
