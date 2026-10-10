import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TriangularGapOrthogonality

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open Classical
noncomputable section
variable {n : ℕ}

def levelQueue (q : List (Cell n)) (i : Fin n) : List (Cell n) := q.filter (fun b=>decide (b.1=i))
def initialLevelQueue (i : Fin n) : List (Cell n) := List.ofFn (fun j:Fin (i.val+1)=>⟨i,j.rev⟩)

lemma mem_levelQueue (q : List (Cell n)) (i : Fin n) (b : Cell n) :
    b∈levelQueue q i ↔ b∈q ∧ b.1=i := by simp [levelQueue]
lemma initialLevelQueue_mem (i : Fin n) (b : Cell n) :
    b∈initialLevelQueue i ↔ b.1=i := by
  rw [initialLevelQueue,List.mem_ofFn]
  constructor
  · rintro ⟨j,rfl⟩; rfl
  · intro hb
    cases b with | mk l r =>
      dsimp only at hb
      subst l
      exact ⟨r.rev,by simp⟩

lemma initialLevelQueue_nodup (i : Fin n) : (initialLevelQueue i).Nodup := by
  rw [initialLevelQueue,List.nodup_ofFn]
  intro j k h
  have hh:=congrArg cellRow h
  apply Fin.rev_injective
  exact Fin.ext hh

lemma initialLevelQueue_pairwise (i : Fin n) : (initialLevelQueue i).Pairwise phaseLE := by
  rw [initialLevelQueue,List.pairwise_ofFn]
  intro j k hjk
  apply Or.inl
  apply Or.inl
  change k.rev.val < j.rev.val
  simp only [Fin.val_rev]
  have := k.isLt
  omega

lemma phaseCycle_levelQueue (i : Fin n) : levelQueue (phaseCycle n) i=initialLevelQueue i := by
  apply List.Perm.eq_of_pairwise (fun a b _ _ hab hba=>Std.Antisymm.antisymm (r:=phaseLE) a b hab hba)
  · exact List.Pairwise.filter _ phaseCycle_pairwise
  · exact initialLevelQueue_pairwise i
  · apply (List.perm_ext_iff_of_nodup (List.Nodup.filter _ phaseCycle_nodup)
      (initialLevelQueue_nodup i)).mpr
    intro b
    simp only [List.mem_filter,decide_eq_true_eq,mem_phaseCycle,true_and,initialLevelQueue_mem]

lemma levelQueue_cons (b : Cell n) (q : List (Cell n)) (i : Fin n) :
    levelQueue (b::q) i=if b.1=i then b::levelQueue q i else levelQueue q i := by
  by_cases h:b.1=i <;> simp [levelQueue,h]
lemma levelQueue_append (q r : List (Cell n)) (i : Fin n) :
    levelQueue (q++r) i=levelQueue q i++levelQueue r i := by simp [levelQueue]
lemma levelQueue_rotate (b : Cell n) (q : List (Cell n)) (i : Fin n) :
    levelQueue (q++[b]) i=levelQueue q i++(if b.1=i then [b] else []) := by
  by_cases h:b.1=i <;> simp [levelQueue,h]

lemma queue_update_off {M : Type*} (w : Cell n → M) (b : Cell n) (w' : M)
    (q : List (Cell n)) (hb : b∉q) : q.map (Function.update w b w')=q.map w := by
  apply List.map_congr_left
  intro c hc
  have hcb:c≠b:=by intro h; subst c; exact hb hc
  exact Function.update_of_ne hcb _ _

end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.ForwardChain
open ElementaryPositivity.QuantumTorus
variable {M : Type*} [AddCommGroup M]

def gaps (a : M) : List M → M → List M
  | [],c => [c-a]
  | b::bs,c => (b-a)::gaps b bs c

lemma gaps_append (a c d : M) (bs : List M) :
    gaps a (bs++[c]) d=gaps a bs c++[d-c] := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih => simp only [List.cons_append,gaps,ih]

variable (Ω : M →+ M →+ ℤ) (p : M)
def positiveMutate (r : M) : M := r + max (-Ω p r) 0 • p

lemma positiveMutate_nonneg (r : M) (h : 0 ≤ Ω p r) : positiveMutate Ω p r=r := by
  simp only [positiveMutate,max_eq_right (by omega : -Ω p r≤0),zero_smul,add_zero]

lemma positiveMutate_minus_one (r : M) (h : Ω p r= -1) : positiveMutate Ω p r=r+p := by
  simp [positiveMutate,h]
lemma positiveMutate_minus_two (r : M) (h : Ω p r= -2) : positiveMutate Ω p r=r+p+p := by
  simp only [positiveMutate,h,neg_neg,show max (2:ℤ) 0=2 by decide]
  rw [show (2:ℤ) • p=p+p by simp [two_smul]]
  abel

lemma gaps_mutate_last (a c : M) (bs : List M)
    (ha : Ω p a=0) (hc : Ω p c= -1)
    (hb : ∀b∈bs,Ω p b=0) :
    (gaps a bs c).map (positiveMutate Ω p)=gaps a bs (c+p) := by
  induction bs generalizing a with
  | nil =>
    simp only [gaps,List.map_cons,List.map_nil,List.cons.injEq,and_true]
    rw [positiveMutate_minus_one Ω p (c-a) (by rw [map_sub,hc,ha,sub_zero])]
    abel
  | cons b bs ih =>
    have hb0:=hb b (by simp)
    have hr:Ω p (b-a)=0 := by rw [map_sub,hb0,ha,sub_self]
    simp only [gaps,List.map_cons]
    rw [positiveMutate_nonneg Ω p (b-a) (by omega),ih b hb0 (fun x hx=>hb x (by simp [hx]))]

lemma gaps_mutate_rotation (a b c : M) (bs : List M) (hp : p=b-a)
    (_ha : Ω p a=1) (hb : Ω p b=1) (hc : Ω p c= -1)
    (hs : ∀x∈bs,Ω p x=0) :
    (gaps b bs c).map (positiveMutate Ω p)=gaps a bs (c+p) := by
  cases bs with
  | nil =>
    simp only [gaps,List.map_cons,List.map_nil,List.cons.injEq,and_true]
    rw [positiveMutate_minus_two Ω p (c-b) (by rw [map_sub,hc,hb]; norm_num)]
    rw [hp]
    abel
  | cons x xs =>
    have hx:=hs x (by simp)
    simp only [gaps,List.map_cons]
    rw [positiveMutate_minus_one Ω p (x-b) (by rw [map_sub,hx,hb]; norm_num),
      gaps_mutate_last Ω p x c xs hx hc (fun z hz=>hs z (by simp [hz]))]
    congr 1
    rw [hp]
    abel

lemma gaps_rotation_perm (a b c : M) (bs : List M) (hp : p=b-a)
    (ha : Ω p a=1) (hb : Ω p b=1) (hc : Ω p c= -1)
    (hs : ∀x∈bs,Ω p x=0) :
    ((-p)::(gaps b bs c).map (positiveMutate Ω p)).Perm
      (gaps a (bs++[c+p]) c) := by
  rw [gaps_mutate_rotation Ω p a b c bs hp ha hb hc hs,gaps_append]
  have H:c-(c+p)= -p := by abel
  rw [H]
  simpa only [List.singleton_append] using (List.perm_append_comm (l₁ := [-p]) (l₂ := gaps a bs (c+p)))

lemma gaps_mutate_fixed (a c : M) (bs : List M)
    (ha : Ω p a≤0) (hc : 0≤Ω p c)
    (hb : ∀b∈bs,Ω p b=0) :
    (gaps a bs c).map (positiveMutate Ω p)=gaps a bs c := by
  induction bs generalizing a with
  | nil =>
    simp only [gaps,List.map_cons,List.map_nil]
    rw [positiveMutate_nonneg Ω p (c-a) (by rw [map_sub]; omega)]
  | cons b bs ih =>
    have hb0:=hb b (by simp)
    simp only [gaps,List.map_cons]
    rw [positiveMutate_nonneg Ω p (b-a) (by rw [map_sub,hb0]; omega),
      ih b (by omega) (fun x hx=>hb x (by simp [hx]))]
end ElementaryPositivity.ForwardChain

end

end OAI
