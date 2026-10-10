import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryRepeat
import OAI.Combinatorics.KMedian.Probability.BernoulliStepProgram
import OAI.Combinatorics.KMedian.Probability.BernoulliRunHeight

namespace OAI


                                           
section
namespace MetricKMedian.SparseBernoulli.Program
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.DependentProgram
open SparseIntegerLaw.BinarySparse (el ed)

def Input.state (x : Input) (d t : ℕ) : State := ⟨⟨x,t⟩,run (d:=d) x.p x.feasible t⟩
def Input.start (x : Input) : State := ⟨⟨x,0⟩,.dirac (fun _ => false)⟩

 theorem state_next (x : Input) (d t : ℕ) : State.step d (x.state d t)=x.state d (t+1) := by
  have hp (ht : t<x.n) : probability ⟨x,t⟩=(fun _ => x.p ⟨t,ht⟩) := by
    funext q; simp only [probability,dite_eq_left ht]
  have he (ht : t<x.n) : endpoint ⟨x,t⟩=(fun q b => SparseBernoulli.endpoint q ⟨t,ht⟩ b) := by
    funext q b i
    simp only [endpoint,SparseBernoulli.endpoint,Fin.ext_iff]
  unfold State.step Input.state
  by_cases ht : t<x.n
  · rw [ite_eq_left ht]
    change (⟨⟨x,t+1⟩, ((run (d:=d) x.p x.feasible t).branch
      (probability ⟨x,t⟩) (probability_unit ⟨x,t⟩) (endpoint ⟨x,t⟩)).compressAuto features⟩ : State)=_
    rw [run,dite_eq_left ht]
    apply congrArg (fun μ => (⟨⟨x,t+1⟩,μ⟩ : State))
    simp only [SparseIntegerLaw.step,hp ht,he ht]
  · rw [ite_eq_right ht,run,dite_eq_right ht]
    rfl

 theorem state_iterate (x : Input) (d t : ℕ) : (State.step d)^[t] x.start=x.state d t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,state_next]

noncomputable def startProgram : PolyProgram Input.encode State.encode Input.start := by
  let raw : PolyProgram qr (encodePair (encodePair qr Nat.bits) (ed er))
      (fun q : List ℚ => ((q,0),(((1:ℤ),[(1:ℤ)]),[q.map (fun _ => false)]))) := by
    apply Binary.Automatic.Poly.program
    have h : Binary.Automatic.Poly (fun q : List ℚ => q.map (fun _ => false)) := by
      apply Binary.Automatic.Poly.list_map <;> fun_prop
    fun_prop
  exact raw.recode (fun x => List.ofFn x.p) (fun _ => rfl) (fun x => by
    simp only [State.encode,Bundle.encode,Bundle.raw,Input.start,SparseIntegerLaw.dirac,
      Vector.toList_replicate,List.map_replicate,List.ofFn_const]
    change encodePair (encodePair qr Nat.bits) (ed er)
      ((List.ofFn x.p,0),((1,[1]),[(List.ofFn x.p).map (fun _ => false)])) = _
    simp only [List.map_const',List.length_ofFn]
    rfl)

noncomputable def countProgram : PolyProgram Input.encode Nat.bits Input.n :=
  (listLength Ratio.encode 0).recode (fun x => List.ofFn x.p) (fun _ => rfl) (fun x => by simp only [List.length_ofFn])

 theorem input_bounds (x : Input) : x.n ≤ x.encode.length ∧ ∀ i, HasHeight (x.p i) x.encode.length := by
  refine ⟨?_,?_⟩
  · simpa only [List.length_ofFn] using (EncodedList.length_le Ratio.encode (List.ofFn x.p))
  · intro i
    exact (Ratio.height_length _).mono (EncodedList.member_length _ _ _ (List.mem_ofFn.mpr ⟨i,rfl⟩))

def supportBound (d L : ℕ) := (L+1)^d+1
def heightBound (d L : ℕ) := SparseBernoulli.stepHeight L d L*L
def sizeBound (d L : ℕ) :=
  2*(3*L+2)+1+(2*(2*(heightBound d L+4)+1+supportBound d L*(2*(heightBound d L+4)+1))+1+
    supportBound d L*(2*(3*L)+1))
noncomputable def SPoly (d : ℕ) : Polynomial ℕ := (X+1)^d+1
noncomputable def HPoly (d : ℕ) : Polynomial ℕ :=
  (X*SPoly d+(2*((X+1)^d+1)*((X+1)^d+1+0*(2*SPoly d+1)))*(2*SPoly d+1)*(2*SPoly d))*X
noncomputable def sizePolynomial (d : ℕ) : Polynomial ℕ :=
  2*(3*X+2)+1+(2*(2*(HPoly d+4)+1+SPoly d*(2*(HPoly d+4)+1))+1+SPoly d*(2*(3*X)+1))
 theorem sizePolynomial_eval (d L : ℕ) : (sizePolynomial d).eval L=sizeBound d L := by
  simp only [sizePolynomial,sizeBound,heightBound,supportBound,HPoly,SPoly,SparseBernoulli.stepHeight,
    SparseIntegerLaw.stepHeight,eval_add,eval_mul,eval_ofNat,eval_X,eval_one,eval_pow,eval_zero]

 theorem state_size (x : Input) (d t : ℕ) (ht : t ≤ x.n) :
    (State.encode (x.state d t)).length ≤ (sizePolynomial d).eval x.encode.length := by
  let L := x.encode.length
  obtain ⟨hn,hp⟩ := input_bounds x
  have htL : t ≤ L := ht.trans hn
  have hc : (Context.encode ⟨x,t⟩).length ≤ 3*L+2 := by
    have hbits : t.bits.length ≤ t+1 := NatBinary.length_le_height (Nat.lt_two_pow_self.le)
    change (encodePair qr Nat.bits (List.ofFn x.p,t)).length ≤ _
    rw [encodePair_length]
    change 2*L+1+t.bits.length ≤ _
    omega
  have hN : (x.state d t).law.length ≤ supportBound d L := by
    apply (run_length x.p x.feasible t).trans
    unfold supportBound
    gcongr
  have hH : SparseBernoulli.stepHeight x.n d L*t ≤ heightBound d L := by
    unfold heightBound SparseBernoulli.stepHeight SparseIntegerLaw.stepHeight
    gcongr
  have hD : (x.state d t).law.law.denominator ≤ (2:ℤ)^(heightBound d L) :=
    (denominator_height x.p x.feasible L hp t).trans (pow_le_pow_right₀ (by norm_num) hH)
  have hs (q : Fin x.n → Bool) : (er (List.ofFn q)).length ≤ 3*L := by
    have hh := EncodedList.length_bound encodeBool (List.ofFn q) 1 (fun _ _ => by rfl)
    simp only [List.length_ofFn] at hh
    exact hh.trans (by omega)
  have hb := SparseIntegerLaw.encode_length_bound (fun q : Fin x.n → Bool => er (List.ofFn q))
    (run (d:=d) x.p x.feasible t) (supportBound d L) (heightBound d L) (3*L) hN hD (fun _ => hs _)
  have he : State.encode (x.state d t)=encodePair Context.encode
      (SparseIntegerLaw.BinarySparse.encode (fun q : Fin x.n → Bool => er (List.ofFn q)))
        (⟨x,t⟩,run (d:=d) x.p x.feasible t) := by
    simp only [State.encode,Bundle.encode,Bundle.raw,Input.state,Context.encode,
      SparseIntegerLaw.BinarySparse.encode,SparseIntegerLaw.BinarySparse.raw,ed,encodePair,RoundingProgram.encodeList_map]
  rw [sizePolynomial_eval,he,encodePair_length]
  unfold sizeBound
  dsimp only at ⊢
  simp only [L] at hc hb ⊢
  omega

noncomputable def runStateProgram (d : ℕ) : PolyProgram Input.encode State.encode (fun x => x.state d x.n) :=
  ((stepProgram d).repeatFrom startProgram countProgram X (sizePolynomial d)
    (fun x => by simpa using (input_bounds x).1)
    (fun x t ht => by rw [state_iterate]; exact state_size x d t ht)).congr _ (fun x => state_iterate x d _)

end MetricKMedian.SparseBernoulli.Program
end

end OAI
