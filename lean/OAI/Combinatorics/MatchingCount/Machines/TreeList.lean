import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeFold
import OAI.Combinatorics.MatchingCount.Machines.TreeChoice

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B C : Type} [Codec A] [Codec B] [Codec C]
def Realizer.congr {f g : A → B} (F : Realizer f) (h : ∀ a,f a=g a) : Realizer g :=
  ⟨F.program,F.cost,fun a s=>by simpa only [h a] using F.correct a s⟩

def listCons : Realizer (fun ab : A×List A=>ab.1::ab.2) :=
  ⟨atom .halt,fun _=>1,fun _ _=>exec_atom .halt _ _ rfl⟩

def reverse : Realizer (List.reverse : List A → List A) :=
  (composition (pair identity (constant ([] : List A))) (fold listCons)).congr (by
    intro as
    change as.foldl (fun x y=>y::x) []=as.reverse
    simp)

def toBits : Realizer Nat.bits :=
  ⟨atom .halt,fun _=>1,fun _ _=>exec_atom .halt _ _ rfl⟩

def double : Realizer (fun n : ℕ=>2*n) :=
  (composition (pair identity identity) add).congr (fun value=>by
    change value+value=2*value
    omega)

def mulStep (x : Bool×(ℕ×ℕ)) : ℕ×ℕ :=
  (x.2.1,2*x.2.2+(if x.1 then x.2.1 else 0))

def mulStepRealizer : Realizer mulStep := by
  let bitP : Realizer (fun x : Bool×(ℕ×ℕ)=>x.1) := first
  let nP : Realizer (fun x : Bool×(ℕ×ℕ)=>x.2.1) := composition second first
  let cP : Realizer (fun x : Bool×(ℕ×ℕ)=>x.2.2) := composition second second
  let vP:=choose bitP nP (constant 0)
  let sumP:=composition (pair (composition cP double) vP) add
  exact (pair nP sumP).congr (fun _=>rfl)

lemma mulStep_fold (A : List Bool) (n c : ℕ) :
    A.reverse.foldl (fun z b=>mulStep (b,z)) (n,c)=
      (n,c*2^A.length+StackAddition.value A*n) := by
  induction A generalizing c with
  | nil => simp [StackAddition.value]
  | cons b A ih =>
    simp only [List.reverse_cons,List.foldl_append,ih,List.foldl_cons,List.foldl_nil,List.length_cons]
    cases b <;> simp only [mulStep,Bool.false_eq_true,↓reduceIte,StackAddition.value,
      Bool.toNat_false,Bool.toNat_true,Nat.zero_add,pow_succ] <;> congr 1 <;> ring

def multiply : Realizer (fun ab : ℕ×ℕ=>ab.1*ab.2) := by
  let bitsP : Realizer (fun ab : ℕ×ℕ=>ab.1.bits.reverse) := composition (composition first toBits) reverse
  let startP : Realizer (fun ab : ℕ×ℕ=>(ab.2,0)) := pair second (constant 0)
  let foldP:=composition (pair bitsP startP) (fold mulStepRealizer)
  exact (composition foldP second).congr (by
    intro ab
    change (ab.1.bits.reverse.foldl (fun z b=>mulStep (b,z)) (ab.2,0)).2=ab.1*ab.2
    rw [mulStep_fold]
    simp [StackAddition.value_bits])

lemma size_encode_list (as : List A) :
    TreeFunction.size (encode as) = 1+as.length+(as.map (fun a=>TreeFunction.size (encode a))).sum := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [encode_list_cons,size_cons,ih,List.length_cons,List.map_cons,List.sum_cons]; omega

lemma size_encode_mem {as : List A} {a : A} (ha : a ∈ as) :
    TreeFunction.size (encode a) ≤ TreeFunction.size (encode as) := by
  induction as with
  | nil => simp at ha
  | cons b bs ih =>
    simp only [List.mem_cons] at ha
    simp only [encode_list_cons,size_cons]
    rcases ha with rfl|ha
    · omega
    · have := ih ha; omega

lemma size_encode_tail (a : A) (as : List A) :
    TreeFunction.size (encode as) ≤ TreeFunction.size (encode (a::as)) := by
  simp only [encode_list_cons,size_cons]; omega

omit [Codec B] in
lemma Fold.cost_bound {f : A×B → B} (t : A×B → ℕ) (I : B → Prop) (as : List A) (b : B) (T S : ℕ)
    (hb : I b) (hs : TreeFunction.size (encode as) ≤ S)
    (hstep : ∀ a ∈ as,∀ z,I z → I (f (a,z)) ∧ t (a,z) ≤ T) :
    Fold.cost f t as b ≤ as.length*(T+14*S+34)+10 := by
  induction as generalizing b with
  | nil => simp [Fold.cost]
  | cons a as ih =>
    have ht:=hstep a (by simp) b hb
    have hs' := (size_encode_tail a as).trans hs
    have hb' : ∀ a ∈ as,∀ z,I z → I (f (a,z)) ∧ t (a,z) ≤ T := fun a ha z hz=>hstep a (by simp [ha]) z hz
    have hh:=ih (f (a,b)) ht.1 hs' hb'
    have ha:=(size_encode_mem (by simp : a ∈ a::as)).trans hs
    simp only [Fold.cost,List.length_cons]
    nlinarith
end MatchingFPRAS.TreeTyped

end OAI
