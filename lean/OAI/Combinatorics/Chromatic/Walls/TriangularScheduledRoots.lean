import Mathlib
import OAI.Combinatorics.Chromatic.Walls.FiniteLatticePairing

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators

variable {n : ℕ}

lemma triangularOmega_skew (m m' : Lattice n (Cell n)) :
    triangularOmega n m m' = -triangularOmega n m' m :=
  matrixPairing_skew _ (chartMatrix_skew cellLevel triangularBB triangularBB_skew) _ _

@[simp] lemma omega_anchors (i j : Fin (n+1)) :
    triangularOmega n (anchor i) (anchor j)=0 := by
  change matrixPairing (chartMatrix (@cellLevel n) (@triangularBB n))
    (Pi.single (.inl i) 1) (Pi.single (.inl j) 1)=0
  exact matrixPairing_single (chartMatrix cellLevel triangularBB) (.inl i) (.inl j)

@[simp] lemma omega_delta_anchor (b : Cell n) (i : Fin (n+1)) :
    triangularOmega n (delta cellLevel b) (anchor i)=0 := by
  simp only [delta,map_sub,AddMonoidHom.sub_apply,omega_anchors,sub_self]

@[simp] lemma omega_anchor_delta (i : Fin (n+1)) (b : Cell n) :
    triangularOmega n (anchor i) (delta cellLevel b)=0 := by
  simp only [delta,map_sub,omega_anchors,sub_self]

@[simp] lemma omega_delta_delta (b c : Cell n) :
    triangularOmega n (delta cellLevel b) (delta cellLevel c)=0 := by
  simp only [delta,map_sub,AddMonoidHom.sub_apply,omega_anchors,sub_self]

def levelCartan (i j : Fin n) : ℤ :=
  if i=j then 2 else if i.val+1=j.val ∨ j.val+1=i.val then -1 else 0

lemma levelCartan_comm (i j : Fin n) : levelCartan i j=levelCartan j i := by
  simp only [levelCartan,eq_comm,or_comm]

lemma omega_delta_bridge (b c : Cell n) :
    triangularOmega n (delta cellLevel b) (bridge c)=levelCartan b.1 c.1 := by
  simp only [delta,map_sub,AddMonoidHom.sub_apply]
  change matrixPairing _ (anchor b.1.succ) (bridge c)-
      matrixPairing _ (anchor b.1.castSucc) (bridge c)=_
  simp only [anchor,bridge,matrixPairing_single,chartMatrix]
  dsimp only [cellLevel]
  simp only [Fin.ext_iff,Fin.val_succ,Fin.val_castSucc,levelCartan]
  split_ifs <;> omega

lemma omega_event_delta (b c : Cell n) :
    triangularOmega n (eventRoot cellLevel 0 b) (delta cellLevel c)= -levelCartan b.1 c.1 := by
  rw [triangularOmega_skew]
  simp only [eventRoot,Nat.cast_zero,zero_smul,add_zero,map_sub,omega_delta_anchor,
    sub_zero,omega_delta_bridge,levelCartan_comm c.1 b.1]

def scheduledBridge (L : ℕ) (b c : Cell n) : Lattice n (Cell n) :=
  bridge c + ((L:ℤ)+(if phaseEarlier c b then 1 else 0)) • delta cellLevel c

@[simp] lemma scheduledBridge_self (L : ℕ) (b : Cell n) :
    scheduledBridge L b b=bridge b+(L:ℤ) • delta cellLevel b := by
  simp [scheduledBridge]

lemma scheduledRoot_anchor (L : ℕ) (b : Cell n) (a : Fin (n+1)) :
    triangularOmega n (eventRoot cellLevel L b) (anchor a)=
      (if a=b.1.castSucc then 1 else 0)-(if a=b.1.succ then 1 else 0) := by
  have he : eventRoot cellLevel L b=eventRoot cellLevel 0 b+(L:ℤ) • delta cellLevel b := by
    simp [eventRoot]
  rw [he,map_add,AddMonoidHom.add_apply,map_zsmul,AddMonoidHom.zsmul_apply,
    omega_delta_anchor,smul_zero,add_zero,eventRoot_anchor]

lemma scheduledRoot_bridge (L : ℕ) (b c : Cell n) :
    triangularOmega n (eventRoot cellLevel L b) (scheduledBridge L b c)=if c=b then 1 else 0 := by
  have he : eventRoot cellLevel L b=eventRoot cellLevel 0 b+(L:ℤ) • delta cellLevel b := by
    simp [eventRoot]
  rw [he,scheduledBridge]
  simp only [map_add,map_zsmul,AddMonoidHom.add_apply,AddMonoidHom.zsmul_apply,
    omega_delta_delta,omega_delta_bridge,omega_event_delta,
    eventRoot_bridge_value,smul_eq_mul]
  by_cases heq : c=b
  · subst c
    simp [levelCartan]
  · by_cases hl : c.1=b.1
    · have hl' := hl.symm
      by_cases hh : phaseEarlier c b
      · simp only [levelCartan,ite_eq_left hl,ite_eq_left hl',ite_eq_right heq]
        simp only [hh,ite_true]
        ring
      · simp only [levelCartan,ite_eq_left hl,ite_eq_left hl',ite_eq_right heq]
        simp only [hh,ite_false]
        ring
    · have hl' : b.1≠c.1 := Ne.symm hl
      by_cases ha : c.1.val+1=b.1.val ∨ b.1.val+1=c.1.val
      · have ha' : b.1.val+1=c.1.val ∨ c.1.val+1=b.1.val := ha.symm
        by_cases hh : phaseEarlier c b
        · simp only [levelCartan,ite_eq_right hl,ite_eq_right hl',ite_eq_right heq,ha,ha',hh,ite_true]
          ring
        · simp only [levelCartan,ite_eq_right hl,ite_eq_right hl',ite_eq_right heq,ha,ha',hh,ite_true,ite_false]
          ring
      · have ha' : ¬(b.1.val+1=c.1.val ∨ c.1.val+1=b.1.val) := by tauto
        simp only [levelCartan,ite_eq_right hl,ite_eq_right hl',ite_eq_right heq,ha,ha',ite_false]
        ring

end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.PathLattice
open scoped BigOperators
variable {R : Type*} [CommRing R] {d : ℕ}

def gap (i : Fin d) : Fin (d+1) → R := Pi.single i.succ 1 - Pi.single i.castSucc 1

def roots : (Fin d → R) →ₗ[R] (Fin (d+1) → R) :=
  ∑ i, (LinearMap.proj i).smulRight (gap i)

lemma roots_apply (c : Fin d → R) : roots c = ∑ i, c i • gap i := by
  simp [roots,LinearMap.sum_apply,LinearMap.smulRight_apply]

def coord : (Fin (d+1) → R) →ₗ[R] (Fin d → R) :=
  LinearMap.pi fun i => ∑ j : Fin (d+1), if i.val < j.val then LinearMap.proj j else 0

lemma coord_apply (m : Fin (d+1) → R) (i : Fin d) :
    coord m i = ∑ j : Fin (d+1), if i.val < j.val then m j else 0 := by
  simp only [coord,LinearMap.pi_apply,LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> rfl

lemma coord_single (a : Fin (d+1)) (r : R) (i : Fin d) :
    coord (Pi.single a r) i = if i.val < a.val then r else 0 := by
  rw [coord_apply,Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

lemma coord_gap (i : Fin d) : coord (gap (R:=R) i) = Pi.single i 1 := by
  ext j
  rw [gap,map_sub,Pi.sub_apply,coord_single,coord_single]
  simp only [Pi.single_apply,Fin.val_succ,Fin.val_castSucc]
  split_ifs with h h' he he <;> simp_all only [sub_self,sub_zero,zero_sub,Fin.ext_iff] <;> omega

@[simp] lemma coord_roots (c : Fin d → R) : coord (roots c) = c := by
  rw [roots_apply,map_sum]
  simp only [map_smul,coord_gap]
  ext j
  simp only [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

lemma roots_injective : Function.Injective (roots (R:=R) (d:=d)) := by
  intro x y h
  have := congrArg coord h
  simpa only [coord_roots] using this

lemma gaps_linearIndependent : LinearIndependent R (gap (R:=R) (d:=d)) := by
  have H := Pi.linearIndependent_single_one (Fin d) R
  have HH : LinearIndependent R (fun i : Fin d => coord (gap (R:=R) i)) := by
    simpa only [coord_gap] using H
  exact HH.of_comp coord

def weight : (Fin (d+1) → R) →ₗ[R] R := ∑ j, LinearMap.proj j
lemma weight_apply (m : Fin (d+1) → R) : weight m = ∑ j, m j := by simp [weight]
lemma weight_single (a : Fin (d+1)) (r : R) : weight (Pi.single a r)=r := by
  simp [weight_apply,Pi.single_apply]
@[simp] lemma weight_gap (i : Fin d) : weight (gap (R:=R) i)=0 := by
  rw [gap,map_sub,weight_single,weight_single,sub_self]
@[simp] lemma weight_roots (c : Fin d → R) : weight (roots c)=0 := by
  simp only [roots_apply,map_sum,map_smul,weight_gap,smul_zero,Finset.sum_const_zero]

end ElementaryPositivity.PathLattice

end

end OAI
