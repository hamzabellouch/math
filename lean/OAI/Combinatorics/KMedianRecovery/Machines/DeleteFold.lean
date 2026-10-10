import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.FiniteMachine

namespace OAI

namespace MetricKMedianRecovery.CanonicalDelete
open PhaseSequence CanonicalMergePath
variable {X : Type*} [DecidableEq X]
structure Acc (X : Type*) where
  remaining : List X
  extras : List X
  vertices : List (List X)
  deriving DecidableEq

def step (complete : Finset X → List X) (Q : Finset X) (C : List X) (ci : X)
    (s : Acc X) (_ : X) : Acc X :=
  let U:=s.remaining.tail
  let E:=s.extras++complete (Q∪(C++U++ci::s.extras).toFinset)
  ⟨U,E,s.vertices++[C++U++ci::E]⟩

lemma fold_result (complete : Finset X → List X) (Q : Finset X) (copy : X → X)
    (C : List X) (i : X) (U E : List X) (V : List (List X)) :
    U.foldl (step complete Q C (copy i)) ⟨U,E,V⟩=
      ⟨[],(deleteSuffix complete Q copy C i U E).1,V++(deleteSuffix complete Q copy C i U E).2⟩ := by
  induction U generalizing E V with
  | nil=>simp only [List.foldl_nil,deleteSuffix,List.append_nil]
  | cons u U ih=>
    simp only [List.foldl_cons,step,List.tail_cons]
    rw [ih]
    simp only [deleteSuffix,List.append_assoc,List.singleton_append]

structure Bounds (P : X → Prop) (N n : ℕ) (s : Acc X) : Prop where
  remaining : s.remaining.length≤N
  extras : s.extras.length≤N+n*N
  vertices : s.vertices.length≤N+n
  vertex : ∀ H∈s.vertices,H.length≤3*N+1+n*N
  rem_mem : ∀ x∈s.remaining,P x
  ext_mem : ∀ x∈s.extras,P x
  vert_mem : ∀ H∈s.vertices,∀ x∈H,P x

lemma Bounds.step {complete : Finset X → List X} {Q : Finset X} {C : List X} {ci : X}
    {P : X → Prop} {N n : ℕ} {s : Acc X} (hs : Bounds P N n s)
    (hC : C.length≤N) (hCm : ∀ x∈C,P x) (hi : P ci)
    (hc : ∀ W,(complete W).length≤N ∧ ∀ x∈complete W,P x) (a : X) :
    Bounds P N (n+1) (step complete Q C ci s a) := by
  let U:=s.remaining.tail
  let A:=complete (Q∪(C++U++ci::s.extras).toFinset)
  have hu : U.length≤N := (by simpa only [U,List.length_tail] using (Nat.sub_le s.remaining.length 1).trans hs.remaining)
  have ha : A.length≤N ∧ ∀ x∈A,P x := hc _
  have he : (s.extras++A).length≤N+(n+1)*N := by
    rw [List.length_append]
    have h:=hs.extras
    simp only [Nat.add_mul,one_mul] at *
    omega
  have hm : ∀ x∈C++U++ci::(s.extras++A),P x := by
    intro x hx
    simp only [List.mem_append,List.mem_cons] at hx
    rcases hx with (hx|hx)|hx|hx|hx
    · exact hCm x hx
    · exact hs.rem_mem x (List.mem_of_mem_tail hx)
    · simpa only [hx] using hi
    · exact hs.ext_mem x hx
    · exact ha.2 x hx
  refine ⟨hu,he,?_,?_,?_,?_,?_⟩
  · change (s.vertices++[_]).length≤_
    simp only [List.length_append,List.length_singleton]
    have h:=hs.vertices
    simp only [Nat.add_mul,one_mul] at *
    omega
  · intro H hH
    change H∈s.vertices++[_] at hH
    rcases List.mem_append.mp hH with hH|hH
    · exact (hs.vertex H hH).trans (by simp only [Nat.add_mul,one_mul]; omega)
    · obtain rfl:=List.mem_singleton.mp hH
      change (C++U++ci::(s.extras++A)).length≤_
      simp only [List.length_append,List.length_cons]
      have hh:=hs.extras
      simp only [Nat.add_mul,one_mul] at *
      omega
  · intro x hx
    exact hs.rem_mem x (List.mem_of_mem_tail hx)
  · intro x hx
    exact (List.mem_append.mp hx).elim (hs.ext_mem x) (ha.2 x)
  · intro H hH
    rcases List.mem_append.mp hH with hH|hH
    · exact hs.vert_mem H hH
    · obtain rfl:=List.mem_singleton.mp hH
      exact hm

lemma Bounds.fold {complete : Finset X → List X} {Q : Finset X} {C : List X} {ci : X}
    {P : X → Prop} {N n : ℕ} {s : Acc X} (hs : Bounds P N n s)
    (hC : C.length≤N) (hCm : ∀ x∈C,P x) (hi : P ci)
    (hc : ∀ W,(complete W).length≤N ∧ ∀ x∈complete W,P x) (xs : List X) :
    Bounds P N (n+xs.length) (xs.foldl (CanonicalDelete.step complete Q C ci) s) := by
  induction xs generalizing n s with
  | nil=>simpa only [List.length_nil,Nat.add_zero,List.foldl_nil] using hs
  | cons a xs ih=>
    simpa only [List.length_cons,List.foldl_cons,Nat.add_assoc,Nat.add_comm 1] using
      ih (hs.step hC hCm hi hc a)
end MetricKMedianRecovery.CanonicalDelete

namespace MetricKMedianRecovery.BitMachine.BinaryDelete
open WordOperations WordList RationalLeaves CanonicalDelete
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)

def accBits {m : ℕ} (s : Acc (Label (Fin m))) : List Bool :=
  encode [labels s.remaining,labels s.extras,historyBits s.vertices]
def contextBits (base C ci : List Bool) := encode [base,C,ci]

def cf (n : ℕ) (x : List Bool) : List Bool := field n (extractPrefix x)
def sf (n : ℕ) (x : List Bool) : List Bool := field n (discardPrefix (discardPrefix x))
noncomputable def cf_computes (n : ℕ) : PolyComputes (cf n) := extractPrefix_computes.comp (field_computes n)
noncomputable def sf_computes (n : ℕ) : PolyComputes (sf n) :=
  (discardPrefix_computes.comp discardPrefix_computes).comp (field_computes n)
noncomputable def rest (x : List Bool) : List Bool := WordList.tail (sf 0 x)
noncomputable def rest_computes : PolyComputes rest := (sf_computes 0).comp WordList.tail_computes
noncomputable def retained (x : List Bool) : List Bool := cf 1 x++rest x++WordList.cons (cf 2 x) (sf 1 x)
noncomputable def retained_computes : PolyComputes retained :=
  ((cf_computes 1).append rest_computes).append (cons_computes (cf_computes 2) (sf_computes 1))
noncomputable def openSet (x : List Bool) : List Bool :=
  BinaryFiniteContext.union (pairBits (field 3 (cf 0 x),retained x))
noncomputable def openSet_computes : PolyComputes openSet :=
  (((cf_computes 0).comp (field_computes 3)).pair retained_computes).comp BinaryFiniteContext.union_computes
noncomputable def extended (x : List Bool) : List Bool :=
  BinaryFiniteContext.replaceOpen (pairBits (cf 0 x,openSet x))
noncomputable def extended_computes : PolyComputes extended :=
  ((cf_computes 0).pair openSet_computes).comp BinaryFiniteContext.replaceOpen_computes
noncomputable def added : List Bool → List Bool := BinaryFiniteMachine.complete ∘ extended
noncomputable def added_computes : PolyComputes added :=
  PolyComputes.comp (f:=extended) (g:=BinaryFiniteMachine.complete) extended_computes BinaryFiniteMachine.complete_computes
noncomputable def extras (x : List Bool) : List Bool := sf 1 x++added x
noncomputable def extras_computes : PolyComputes extras := (sf_computes 1).append added_computes
noncomputable def vertex (x : List Bool) : List Bool := cf 1 x++rest x++WordList.cons (cf 2 x) (extras x)
noncomputable def vertex_computes : PolyComputes vertex :=
  ((cf_computes 1).append rest_computes).append (cons_computes (cf_computes 2) extras_computes)
noncomputable def vertices (x : List Bool) : List Bool := sf 2 x++WordList.cons (vertex x) []
noncomputable def vertices_computes : PolyComputes vertices :=
  (sf_computes 2).append (cons_computes vertex_computes (const_computes []))
noncomputable def step (x : List Bool) : List Bool := encode [rest x,extras x,vertices x]
noncomputable def step_computes : PolyComputes step :=
  list_computes [rest,extras,vertices] (by
    intro f hf
    refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨rest_computes⟩
    · exact ⟨extras_computes⟩
    · exact ⟨vertices_computes⟩)

lemma tail_labels {m : ℕ} (U : List (Label (Fin m))) : WordList.tail (labels U)=labels U.tail := by
  cases U with
  | nil=>rfl
  | cons u U=>exact WordList.tail_cons _ _

lemma base_open {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    field 3 (BinaryFiniteContext.pack distance loc F Q v z lam)=setBits Q := by
  simp only [BinaryFiniteContext.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

lemma step_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (C : List (Label (Fin m)))
    (ci a : Label (Fin m)) (s : Acc (Label (Fin m))) :
    step (pairBits (contextBits (BinaryFiniteContext.pack distance loc F Q v z lam) (labels C) (BinaryLabel.encode ci),
      pairBits (BinaryLabel.encode a,accBits s)))=
    accBits (CanonicalDelete.step (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q C ci s a) := by
  simp only [step,vertices,vertex,extras,added,Function.comp_apply,extended,openSet,retained,rest,cf,sf,
    extractPrefix_pairBits,discardPrefix_pairBits,contextBits,accBits,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,tail_labels]
  simp only [base_open]
  rw [←BinaryFiniteContext.labels_cons,←BinaryFiniteContext.labels_append,←BinaryFiniteContext.labels_append]
  rw [BinaryFiniteContext.union_list_pack,BinaryFiniteContext.replaceOpen_pack,BinaryFiniteMachine.complete_pack]
  simp only [CanonicalDelete.step,BinaryFiniteContext.labels_append,BinaryFiniteContext.labels_cons,
    BinaryFiniteMachine.historyBits_append,BinaryFiniteMachine.historyBits_cons,BinaryFiniteMachine.historyBits_nil]
end MetricKMedianRecovery.BitMachine.BinaryDelete

end OAI
