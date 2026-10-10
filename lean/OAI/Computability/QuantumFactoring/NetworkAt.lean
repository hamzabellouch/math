import Mathlib
import OAI.Computability.QuantumFactoring.FactorVerifierBounds
import OAI.Computability.QuantumFactoring.NetworkPolyResources
import OAI.Computability.QuantumFactoring.PolyAt

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic

def NetworkAt {α : Type*} (len : α→ℕ) {a b : α→ℕ}
    (f : ∀x,BooleanNetwork (a x) (b x)) : Prop := PolyAt len (fun x=>(f x).net.count)
namespace NetworkAt
variable {α : Type*} {len a b c : α→ℕ}
lemma select (h : ∀x,Fin (b x)→Fin (a x)) : NetworkAt len (fun x=>BooleanNetwork.select (h x)) := by
  simpa only [NetworkAt,count_select] using PolyAt.const len 0
lemma comp {f : ∀x,BooleanNetwork (a x) (b x)} {g : ∀x,BooleanNetwork (b x) (c x)}
    (hf : NetworkAt len f) (hg : NetworkAt len g) : NetworkAt len (fun x=>(f x).comp (g x)) := by
  simpa only [NetworkAt,count_comp] using PolyAt.add hf hg
lemma pair {f : ∀x,BooleanNetwork (a x) (b x)} {g : ∀x,BooleanNetwork (a x) (c x)}
    (hf : NetworkAt len f) (hg : NetworkAt len g) : NetworkAt len (fun x=>(f x).pair (g x)) := by
  simpa only [NetworkAt,count_pair] using PolyAt.add hf hg
lemma rewire {f : ∀x,BooleanNetwork (a x) (b x)} (hf : NetworkAt len f)
    (h : ∀x,Fin (c x)→Fin (b x)) : NetworkAt len (fun x=>(f x).rewire (h x)) := by
  simpa only [NetworkAt,count_rewire] using hf
lemma constant (h : α→Bool) : NetworkAt len (fun x=>BooleanNetwork.constant (n:=a x) (h x)) := by
  simpa only [NetworkAt,count_constant] using PolyAt.const len 1
lemma of_le {f : ∀x,BooleanNetwork (a x) (b x)} {bound : α→ℕ} (hb : PolyAt len bound)
    (h : ∀x,(f x).net.count≤bound x) : NetworkAt len f := hb.of_le h
lemma bnot {f : ∀x,BooleanNetwork (a x) 1} (hf : NetworkAt len f) :
    NetworkAt len (fun x=>(f x).bnot) := by
  simpa only [NetworkAt,count_bnot] using PolyAt.add hf (PolyAt.const len 1)
lemma band {f g : ∀x,BooleanNetwork (a x) 1} (hf : NetworkAt len f) (hg : NetworkAt len g) :
    NetworkAt len (fun x=>(f x).band (g x)) := by
  simpa only [NetworkAt,count_band] using (PolyAt.add hf hg).add (PolyAt.const len 1)
lemma bor {f g : ∀x,BooleanNetwork (a x) 1} (hf : NetworkAt len f) (hg : NetworkAt len g) :
    NetworkAt len (fun x=>(f x).bor (g x)) := by
  simpa only [NetworkAt,count_bor] using (PolyAt.add hf hg).add (PolyAt.const len 4)
lemma wordConstant (v : ∀x,BitVec (b x)) (hb : PolyAt len b) :
    NetworkAt len (fun x=>BitArithmetic.wordConstant (n:=a x) (v x)) := by
  simpa only [NetworkAt,wordConstant_count] using hb
lemma zeroWord {f : ∀x,BooleanNetwork (a x) (b x)} (hf : NetworkAt len f) (hb : PolyAt len b) :
    NetworkAt len (fun x=>BitArithmetic.zeroWord (f x)) :=
  of_le ((PolyAt.add hf ((PolyAt.const len 97).mul hb)).add (PolyAt.const len 21))
    fun x=>zeroWord_count (f x)
lemma equalOn {f g : ∀x,BooleanNetwork (a x) (b x)} (hf : NetworkAt len f)
    (hg : NetworkAt len g) (hb : PolyAt len b) : NetworkAt len (fun x=>BitArithmetic.equalOn (f x) (g x)) :=
  of_le (((PolyAt.add hf hg).add ((PolyAt.const len 96).mul hb)).add (PolyAt.const len 21))
    fun x=>equalOn_count (f x) (g x)
lemma resizeWord (ha : PolyAt len a) (hb : PolyAt len b) :
    NetworkAt len (fun x=>BitArithmetic.resizeWord (a x) (b x)) := by
  apply of_le (PolyAt.add ha hb)
  intro x
  have h:=BitArithmetic.resizeWord_count (a x) (b x)
  omega
lemma all {ls : ∀x,List (BooleanNetwork (a x) 1)} (hl : PolyAt len (fun x=>(ls x).length))
    (h : ∃p : Polynomial ℕ,∀ x f, f∈ls x → f.net.count≤p.eval (len x)) :
    NetworkAt len (fun x=>BooleanNetwork.all (ls x)) := by
  obtain ⟨p,hp⟩:=h
  have hc : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  exact of_le ((hl.mul (hc.add (PolyAt.const len 1))).add (PolyAt.const len 1))
    fun x=>all_count (ls x) (hp x)
lemma all_ofFn {k : α→ℕ} {f : ∀x,Fin (k x)→BooleanNetwork (a x) 1} (hk : PolyAt len k)
    (hf : NetworkAt (fun xi : Σx,Fin (k x)=>len xi.1) (fun xi=>f xi.1 xi.2)) :
    NetworkAt len (fun x=>BooleanNetwork.all (List.ofFn (f x))) := by
  obtain ⟨p,hp⟩:=hf
  apply all (by simpa only [List.length_ofFn] using hk)
  refine ⟨p,?_⟩
  intro x g hg
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hg
  exact hp ⟨x,i⟩
lemma pull {β : Type*} {f : ∀x,BooleanNetwork (a x) (b x)} (hf : NetworkAt len f) (g : β→α) :
    NetworkAt (fun y=>len (g y)) (fun y=>f (g y)) := PolyAt.pull hf g
lemma ofPoly {a b : ℕ→ℕ} {f : ∀n,BooleanNetwork (a n) (b n)} (hf : NetworkPoly f)
    (len : α→ℕ) : NetworkAt len (fun x=>f (len x)) := PolyAt.ofPoly hf len
end NetworkAt
end ExactQuantumFactoring

end



end OAI
