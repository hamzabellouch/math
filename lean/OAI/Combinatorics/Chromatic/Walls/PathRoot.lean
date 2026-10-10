import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TriangularScheduledRoots

namespace OAI

section
namespace ElementaryPositivity.PathLattice
open scoped BigOperators
variable {R : Type*} [CommRing R] {d : ℕ}

lemma roots_single (i : Fin d) (r : R) : roots (Pi.single i r)=r • gap i := by
  rw [roots_apply,Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

lemma roots_coord_single (a : Fin (d+1)) :
    roots (coord (Pi.single a (1:R))) = Pi.single a 1 - Pi.single 0 1 := by
  induction a using Fin.induction with
  | zero =>
    have hz : coord (Pi.single (0:Fin (d+1)) (1:R))=0 := by
      ext i
      simp only [coord_single,Fin.val_zero,not_lt_zero,ite_false,Pi.zero_apply]
    rw [hz,map_zero,sub_self]
  | succ i ih =>
    have H : roots (coord (Pi.single i.succ (1:R))) -
        roots (coord (Pi.single i.castSucc (1:R))) = gap i := by
      rw [←map_sub,←map_sub]
      change roots (coord (gap i))=gap i
      rw [coord_gap,roots_single,one_smul]
    rw [ih,gap] at H
    exact sub_eq_iff_eq_add.mp H |>.trans (by abel)

lemma roots_coord (m : Fin (d+1) → R) :
    roots (coord m) = m - weight m • Pi.single 0 1 := by
  have hm : m=∑ a : Fin (d+1),m a • Pi.single a 1 := by
    ext a
    simp only [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  calc
    roots (coord m) = ∑ a, m a • roots (coord (Pi.single a (1:R))) := by
      conv_lhs => rw [hm]
      simp only [map_sum,map_smul]
    _ = ∑ a, m a • (Pi.single a (1:R)-Pi.single 0 1) := by simp_rw [roots_coord_single]
    _ = (∑ a,m a • Pi.single a (1:R)) - (∑ a,m a • Pi.single 0 1) := by
      simp only [smul_sub,Finset.sum_sub_distrib]
    _ = m-weight m • Pi.single 0 1 := by rw [←hm,←Finset.sum_smul,weight_apply]

lemma coord_nonneg (m : Fin (d+1) → ℤ) (hm : ∀ a,0 ≤ m a) (i : Fin d) : 0≤coord m i := by
  rw [coord_apply]
  apply Finset.sum_nonneg
  intro a _
  split_ifs <;> first | exact hm a | omega

lemma vertex_support_rootDegree (m : Fin (d+1) → ℤ) (hm : ∀a,0 ≤ m a) :
    ∃ k, QuantumTorus.HasRootDegree (roots (R:=ℤ) (d:=d)).toAddMonoidHom k
      (m-weight m • Pi.single 0 1) := by
  let c : Fin d → ℕ := fun i => (coord m i).toNat
  have hc : (fun i => (c i:ℤ))=coord m := by
    ext i
    exact Int.toNat_of_nonneg (coord_nonneg m hm i)
  refine ⟨∑i,c i,c,rfl,?_⟩
  change roots (fun i => (c i:ℤ))=m-weight m • Pi.single 0 1
  rw [hc,roots_coord]

lemma gap_prefix_nonpositive (k : Fin (d+1)) (i : Fin d) :
    (∑ a : Fin (d+1), if a≤k then gap (R:=ℤ) i a else 0) ≤ 0 := by
  have H (b : Fin (d+1)) : (∑a : Fin (d+1),if a≤k then (Pi.single b (1:ℤ)) a else 0)=
      if b≤k then 1 else 0 := by
    rw [Finset.sum_eq_single b]
    · simp
    · intro a _ ha
      simp [Ne.symm ha]
    · simp
  have he : (∑ a : Fin (d+1),if a≤k then gap (R:=ℤ) i a else 0)=
      (if i.succ≤k then 1 else 0)-(if i.castSucc≤k then 1 else 0) := by
    rw [←H i.succ,←H i.castSucc,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simp only [gap,Pi.sub_apply]
    split_ifs <;> rfl
  rw [he]
  simp only [Fin.le_iff_val_le_val,Fin.val_succ,Fin.val_castSucc]
  split_ifs <;> omega
end ElementaryPositivity.PathLattice

end
section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators
open Classical
noncomputable section
variable {n : ℕ}
abbrev GapIndex (n : ℕ) := (i : Fin n) × Fin (i.val+2)

def levelNode (i : Fin n) (j : Fin (i.val+3)) : Vertex n (Cell n) :=
  if h0 : j.val=0 then .inl i.castSucc
  else if he : j.val=i.val+2 then .inl i.succ
  else .inr ⟨i,⟨i.val+1-j.val,by omega⟩⟩

def afterGap (g : GapIndex n) : Vertex n (Cell n) → Prop
  | .inl a => g.1.val < a.val
  | .inr b => g.1.val < b.1.val ∨
      (g.1=b.1 ∧ b.2.val+g.2.val < g.1.val+1)

lemma afterGap_node (g : GapIndex n) (i : Fin n) (j : Fin (i.val+3)) :
    afterGap g (levelNode i j) ↔ g.1.val < i.val ∨ (g.1=i ∧ g.2.val < j.val) := by
  unfold levelNode
  split_ifs with h0 he
  · simp only [afterGap,Fin.val_castSucc,h0,not_lt_zero,and_false,or_false]
  · simp only [afterGap,Fin.val_succ,he,Fin.ext_iff]
    have hg:=g.2.isLt
    omega
  · simp only [afterGap,Fin.ext_iff]
    have hj:=j.isLt
    omega

variable {R : Type*} [CommRing R]
def forwardGap (g : GapIndex n) : Vertex n (Cell n) → R :=
  Pi.single (levelNode g.1 g.2.succ) 1-Pi.single (levelNode g.1 g.2.castSucc) 1

def forwardCoord : (Vertex n (Cell n) → R) →ₗ[R] (GapIndex n → R) :=
  LinearMap.pi fun g => ∑ a : Vertex n (Cell n), if afterGap g a then LinearMap.proj a else 0

lemma forwardCoord_apply (m : Vertex n (Cell n) → R) (g : GapIndex n) :
    forwardCoord m g=∑a,if afterGap g a then m a else 0 := by
  simp only [forwardCoord,LinearMap.pi_apply,LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> rfl

lemma forwardCoord_single (a : Vertex n (Cell n)) (r : R) (g : GapIndex n) :
    forwardCoord (Pi.single a r) g=if afterGap g a then r else 0 := by
  rw [forwardCoord_apply,Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

lemma forwardCoord_gap (g : GapIndex n) :
    forwardCoord (forwardGap (R:=R) g)=Pi.single g 1 := by
  ext f
  rw [forwardGap,map_sub,Pi.sub_apply,forwardCoord_single,forwardCoord_single]
  simp only [afterGap_node,Fin.val_succ,Fin.val_castSucc,Pi.single_apply]
  by_cases hlev : f.1=g.1
  · simp only [lt_self_iff_false,false_or,hlev,true_and]
    have heq : f=g ↔ f.2.val=g.2.val := by
      constructor
      · intro h; subst f; rfl
      · intro h
        cases f with | mk i fi =>
          cases g with | mk j gj =>
            dsimp only at hlev
            subst j
            have hh:fi=gj:=Fin.ext h
            subst gj
            rfl
    simp only [heq]
    split_ifs <;> simp_all <;> omega
  · have heq : f≠g := by intro h; exact hlev (congrArg Sigma.fst h)
    simp only [hlev,false_and,or_false,ite_eq_right heq,sub_self]

def forwardRoots : (GapIndex n → R) →ₗ[R] (Vertex n (Cell n) → R) :=
  ∑ g, (LinearMap.proj g).smulRight (forwardGap g)
lemma forwardRoots_apply (c : GapIndex n → R) :
    forwardRoots c=∑g,c g • forwardGap g := by
  simp [forwardRoots,LinearMap.sum_apply,LinearMap.smulRight_apply]

@[simp] lemma forwardCoord_roots (c : GapIndex n → R) : forwardCoord (forwardRoots c)=c := by
  rw [forwardRoots_apply,map_sum]
  simp only [map_smul,forwardCoord_gap]
  ext g
  simp only [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
  rw [Finset.sum_eq_single g]
  · simp
  · intro f _ hf
    simp [Ne.symm hf]
  · simp

lemma forwardRoots_injective : Function.Injective (forwardRoots (R:=R) (n:=n)) := by
  intro a b h
  have H:=congrArg forwardCoord h
  simpa only [forwardCoord_roots] using H

lemma forwardGap_independent : LinearIndependent R (forwardGap (R:=R) (n:=n)) := by
  have H:=Pi.linearIndependent_single_one (GapIndex n) R
  have HH:LinearIndependent R (fun g : GapIndex n=>forwardCoord (forwardGap (R:=R) g)) := by
    simpa only [forwardCoord_gap] using H
  exact HH.of_comp forwardCoord

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
