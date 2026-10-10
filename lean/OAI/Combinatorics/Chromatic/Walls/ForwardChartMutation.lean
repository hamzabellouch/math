import Mathlib
import OAI.Combinatorics.Chromatic.Walls.ForwardInventoryRotation

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus
open Classical
noncomputable section
variable {n:ℕ} {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]

structure FreeChart (e:M →+ E) where
  roots : (I → ℤ) →+ M
  coord : M →+ (I → ℤ)
  retract : ∀d,coord (roots d)=d
  independent : LinearIndependent ℝ (fun i=>e (simpleRoot roots i))

def FreeChart.mutate (Ω:M →+ M →+ ℤ) {e:M →+ E} (ch:FreeChart (I:=I) e) (pc:I) : FreeChart (I:=I) e where
  roots := mutatedRoots Ω ch.roots pc
  coord := mutatedCoordinates Ω ch.roots ch.coord pc
  retract := mutatedCoordinates_retraction Ω ch.roots ch.coord ch.retract pc
  independent := mutatedRoots_realIndependent Ω ch.roots pc e ch.independent

variable (Ω:M →+ M →+ ℤ) {e:M →+ E}
lemma freeChart_inventory_step (ch:FreeChart (I:=I) e) (is:List I)
    (his:is.Nodup) (_hall:∀i,i∈is)
    (d:Fin (n+1) → M) (w:Cell n → M) (b:Cell n) (q:List (Cell n))
    (hb:b∉q) (hinv:(is.map (simpleRoot ch.roots)).Perm (forwardInventory d w (b::q)))
    (p:M) (hp:p=w b-d b.1.castSucc)
    (hd:∀j,Ω p (d j)=(if j=b.1.castSucc then 1 else 0)-(if j=b.1.succ then 1 else 0))
    (hw:∀c,Ω p (w c)=if c=b then 1 else 0) :
    ∃pc:I,simpleRoot ch.roots pc=p ∧
      (is.map (simpleRoot (ch.mutate Ω pc).roots)).Perm
        (forwardInventory d (Function.update w b (d b.1.succ+p)) (q++[b])) := by
  have hmem:p∈forwardInventory d w (b::q):=by rw [hp]; exact forwardInventory_root_mem d w b q
  have hm:p∈is.map (simpleRoot ch.roots):=hinv.mem_iff.mpr hmem
  obtain ⟨pc,_,hpc⟩:=List.mem_map.mp hm
  refine ⟨pc,hpc,?_⟩
  have hnd:(forwardInventory d w (b::q)).Nodup:=
    hinv.nodup_iff.mp (his.map (simpleRoot_injective ch.roots ch.coord ch.retract))
  change (is.map (simpleRoot (mutatedRoots Ω ch.roots pc))).Perm _
  rw [mutatedRoot_list Ω ch.roots ch.coord ch.retract pc,hpc]
  exact (hinv.map (rootMutation Ω p)).trans (forwardInventory_rotation Ω d w b q hb hnd p hp hd hw)
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.ForwardChain
variable {M : Type*} [AddCommGroup M]
lemma gaps_ofFn_nodes {k:ℕ} (x:Fin (k+2) → M) :
    gaps (x 0) (List.ofFn (fun j:Fin k=>x j.succ.castSucc)) (x (Fin.last (k+1)))=
      List.ofFn (fun j:Fin (k+1)=>x j.succ-x j.castSucc) := by
  induction k with
  | zero => simp [gaps,List.ofFn_succ]
  | succ k ih =>
    rw [List.ofFn_succ,gaps,List.ofFn_succ]
    congr 1
    exact ih (fun j=>x j.succ)
end ElementaryPositivity.ForwardChain

end
section
namespace ElementaryPositivity.TriangularDynamics
open Classical
noncomputable section
variable {n : ℕ} {R : Type*} [CommRing R]

@[simp] lemma levelNode_zero (i:Fin n) : levelNode i 0=.inl i.castSucc := by
  simp [levelNode]
@[simp] lemma levelNode_last (i:Fin n) : levelNode i (Fin.last (i.val+2))=.inl i.succ := by
  simp [levelNode]
lemma levelNode_middle (i:Fin n) (j:Fin (i.val+1)) :
    levelNode i j.succ.castSucc=.inr ⟨i,j.rev⟩ := by
  simp only [levelNode,Fin.val_castSucc,Fin.val_succ]
  rw [dite_eq_right (by omega),dite_eq_right (by have := j.isLt; omega)]
  congr 2

def gapIndices (n:ℕ) : List (GapIndex n) :=
  (List.finRange n).flatMap (fun i=>(List.finRange (i.val+2)).map (Sigma.mk i))
lemma mem_gapIndices (g:GapIndex n) : g∈gapIndices n := by
  rcases g with ⟨i,j⟩
  exact List.mem_flatMap.mpr ⟨i,List.mem_finRange _,List.mem_map.mpr ⟨j,List.mem_finRange _,rfl⟩⟩
lemma gapIndices_nodup : (gapIndices n).Nodup := by
  rw [gapIndices,List.nodup_flatMap]
  constructor
  · intro i _
    exact (List.nodup_finRange _).map (fun a b h=>by cases h; rfl)
  · apply (List.nodup_finRange n).pairwise_of_forall_ne
    intro i j _ _ hij g hg hg'
    obtain ⟨a,_,ha⟩:=List.mem_map.mp hg
    obtain ⟨b,_,hb⟩:=List.mem_map.mp hg'
    exact hij (by simpa using congrArg Sigma.fst (ha.trans hb.symm))

lemma initial_levelGaps (i:Fin n) :
    levelGaps (anchor (n:=n)) bridge (phaseCycle n) i=
      (List.finRange (i.val+2)).map (fun j=>forwardGap (R:=ℤ) ⟨i,j⟩) := by
  rw [levelGaps,phaseCycle_levelQueue,initialLevelQueue,List.map_ofFn]
  have H:=ForwardChain.gaps_ofFn_nodes (fun j:Fin (i.val+3)=>
    (Pi.single (levelNode i j) 1:Vertex n (Cell n) → ℤ))
  simpa only [levelNode_zero,levelNode_last,levelNode_middle,anchor,bridge,
    forwardGap,List.ofFn_eq_map,Function.comp_def] using H

lemma initial_forwardInventory :
    forwardInventory anchor bridge (phaseCycle n)=
      (gapIndices n).map (forwardGap (R:=ℤ)) := by
  rw [forwardInventory,gapIndices,List.map_flatMap]
  congr 1
  funext i
  rw [initial_levelGaps,List.map_map]
  rfl

lemma simpleRoot_forwardRoots (i:GapIndex n) :
    QuantumTorus.simpleRoot (forwardRoots (R:=ℤ)).toAddMonoidHom i=forwardGap i := by
  rw [QuantumTorus.simpleRoot,LinearMap.toAddMonoidHom_coe,forwardRoots_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.LatticeExtension
open scoped BigOperators
variable {V : Type*} [Fintype V]
abbrev Extended (V : Type*) := (V → ℤ) × (V → ℤ)

def dot (x : V → ℤ) : (V → ℤ) →+ ℤ where
  toFun y := ∑ i,x i*y i
  map_zero' := by simp
  map_add' y z := by simp [mul_add,Finset.sum_add_distrib]

lemma dot_apply (x y : V → ℤ) : dot x y=∑i,x i*y i := by simp [dot]
lemma dot_add (x y z : V → ℤ) : dot (x+y) z=dot x z+dot y z := by
  simp only [dot_apply,Pi.add_apply,add_mul,Finset.sum_add_distrib]
lemma dot_zero (y : V → ℤ) : dot 0 y=0 := by simp [dot_apply]
@[simp] lemma dot_single [DecidableEq V] (x : V → ℤ) (i : V) : dot x (Pi.single i 1)=x i := by
  simp [dot_apply,Pi.single_apply]

variable (Ω : (V → ℤ) →+ (V → ℤ) →+ ℤ)
def form : Extended V →+ Extended V →+ ℤ where
  toFun x := ((Ω x.1).comp (AddMonoidHom.fst _ _)) +
    ((dot x.2).comp (AddMonoidHom.fst _ _)) -
    ((dot x.1).comp (AddMonoidHom.snd _ _))
  map_zero' := by ext y; simp [dot_zero]
  map_add' x x' := by ext y; simp [dot_add]; abel

lemma form_apply (x y : Extended V) :
    form Ω x y=Ω x.1 y.1+dot x.2 y.1-dot x.1 y.2 := rfl

lemma form_self (hΩ : ∀m,Ω m m=0) (x : Extended V) : form Ω x x=0 := by
  rw [form_apply,hΩ,zero_add]
  have H : dot x.2 x.1=dot x.1 x.2 := by
    simp only [dot_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [H,sub_self]

def includeVertices : (V → ℤ) →+ Extended V := (AddMonoidHom.id _).prod 0
omit [Fintype V] in
@[simp] lemma includeVertices_apply (m : V → ℤ) : includeVertices m=(m,0) := rfl
omit [Fintype V] in
lemma includeVertices_injective : Function.Injective (includeVertices (V:=V)) := by
  intro a b h
  exact congrArg Prod.fst h
@[simp] lemma form_original (m m' : V → ℤ) :
    form Ω (includeVertices m) (includeVertices m')=Ω m m' := by
  simp [form_apply,dot_zero]

lemma form_nondegenerate [DecidableEq V] : ∀r≠0,∃m,form Ω r m≠0 := by
  intro r hr
  by_contra hh
  push Not at hh
  have hfirst : r.1=0 := by
    ext i
    have H:=hh (0,Pi.single i 1)
    simp only [form_apply,map_zero,dot_single,zero_add,zero_sub,neg_eq_zero] at H
    exact H
  have hsecond : r.2=0 := by
    ext i
    have H:=hh (Pi.single i 1,0)
    simp only [form_apply,hfirst,map_zero,AddMonoidHom.zero_apply,zero_add,
      dot_single,sub_zero] at H
    exact H
  exact hr (Prod.ext hfirst hsecond)
end ElementaryPositivity.LatticeExtension

end

end OAI
