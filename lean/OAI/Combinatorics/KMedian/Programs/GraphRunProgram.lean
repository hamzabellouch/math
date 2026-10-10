import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseIterationHeight
import OAI.Combinatorics.KMedian.Programs.GraphStepProgram
import OAI.Combinatorics.KMedian.Geometry.GraphRunHeight

namespace OAI


                                       
section
namespace MetricKMedian.SparseGraph.Program
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.DependentProgram SparseIntegerLaw.BinarySparse
open ListOperation (Row Table et)
local notation "erB" => ListOperation.er

def Input.state (x : Input) (t : ℕ) : State := ⟨⟨x,t⟩,run x.columns t⟩
def Input.start (x : Input) : State := ⟨⟨x,0⟩,.dirac (fun _ => ∅)⟩

theorem state_next (x : Input) (t : ℕ) : State.step (x.state t)=x.state (t+1) := by
  have he (ht : t < x.m) : update ⟨x,t⟩=(fun G S => next G S ⟨t,ht⟩) := by
    funext G S i
    by_cases h : i=⟨t,ht⟩
    · subst i; simp only [update,next,Function.update_self,ite_true]
    · have hv : i.val≠t := fun hh => h (Fin.ext hh)
      simp only [update,next,Function.update_of_ne h,ite_eq_right hv]
  unfold State.step Input.state
  by_cases ht : t < x.m
  · rw [ite_eq_left ht]
    change (⟨⟨x,t+1⟩,((run x.columns t).prod (column ⟨x,t⟩) (update ⟨x,t⟩)).compressAuto features⟩ : State)=_
    rw [run,dite_eq_left ht]
    simp only [column,dite_eq_left ht,he ht,SparseGraph.step,SparseIntegerLaw.prodCompress]
  · rw [ite_eq_right ht,run,dite_eq_right ht]
    rfl

theorem state_iterate (x : Input) (t : ℕ) : (State.step)^[t] x.start=x.state t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,state_next]

noncomputable def startProgram : PolyProgram Input.encode State.encode Input.start := by
  let raw : PolyProgram ei (encodePair (encodePair ei Nat.bits) (ed et))
      (fun x : InputRaw => ((x,0),(((1:ℤ),[(1:ℤ)]),[x.2.map (fun _ => x.1.map (fun _ => false))]))) := by
    apply Binary.Automatic.Poly.program
    have hs : Binary.Automatic.Poly (fun x : InputRaw => x.2.map (fun _ => x.1.map (fun _ => false))) := by
      apply Binary.Automatic.Poly.list_map
      · apply Binary.Automatic.Poly.list_map <;> fun_prop
      · fun_prop
    fun_prop
  exact raw.recode Input.raw (fun _ => rfl) (fun x => by
    simp only [State.encode,Bundle.encode,Bundle.raw,Input.start,SparseIntegerLaw.dirac,
      List.map_const',Input.raw,List.length_ofFn,List.map_replicate,
      Vector.toList_replicate,List.ofFn_const,view,ListOperation.view,Finset.notMem_empty,decide_false]
    rfl)

noncomputable def countProgram : PolyProgram Input.encode Nat.bits Input.m :=
  ((snd (encodeList (fun _ : Unit => [])) (encodeList (ed erB))).comp (listLength (ed erB) ((1,[1]),[]))).recode
    Input.raw (fun _ => rfl) (fun x => by simp only [Function.comp_def,Input.raw,List.length_ofFn])

theorem input_bounds (x : Input) :
    x.n≤x.encode.length ∧ x.m≤x.encode.length ∧
    (∀ i, (x.columns i).length≤x.encode.length) ∧
    (∀ i, (x.columns i).law.denominator≤(2:ℤ)^x.encode.length) := by
  let L := x.encode.length
  have he : L=2*(encodeList (fun _ : Unit => []) x.raw.1).length+1+
      (encodeList (ed erB) x.raw.2).length := encodePair_length _ _ _
  have hn := EncodedList.length_le (fun _ : Unit => []) x.raw.1
  have hm := EncodedList.length_le (ed erB) x.raw.2
  simp only [Input.raw,List.length_ofFn,List.length_replicate] at hn hm he
  have hcol (i : Fin x.m) : (ed erB (columnRaw (x.columns i))).length≤L := by
    have h := EncodedList.member_length (ed erB) x.raw.2 (columnRaw (x.columns i))
      (List.mem_ofFn.mpr ⟨i,rfl⟩)
    simp only [Input.raw] at h
    omega
  have hc (i : Fin x.m) : (ed erB (columnRaw (x.columns i))).length=
      2*(2*(Signed.encode (x.columns i).law.denominator).length+1+
        (encodeList Signed.encode (List.ofFn (x.columns i).law.numerator)).length)+1+
      (encodeList erB ((x.columns i).states.toList.map ListOperation.setView)).length := by
    simp only [columnRaw,ed,el,IntegerLaw.ListPivot.el,encodePair_length]
  refine ⟨by change x.n≤L; omega,by change x.m≤L; omega,?_,?_⟩
  · intro i
    have h := EncodedList.length_le Signed.encode (List.ofFn (x.columns i).law.numerator)
    simp only [List.length_ofFn] at h
    have hh := hcol i
    rw [hc i] at hh
    change (x.columns i).length≤L
    omega
  · intro i
    have hh := hcol i
    rw [hc i] at hh
    have hl : (Signed.encode (x.columns i).law.denominator).length≤L := by omega
    exact (le_abs_self _).trans ((Signed.height_length _).trans (pow_le_pow_right₀ (by norm_num) hl))

def supportBound (L : ℕ) := L*L+(L*L)*(L*L)+1
def heightBound (L : ℕ) := SparseGraph.stepHeight L L L L*L
def graphSize (L : ℕ) := L*(2*(3*L)+1)
def sizeBound (L : ℕ) :=
  2*(3*L+2)+1+(2*(2*(heightBound L+4)+1+supportBound L*(2*(heightBound L+4)+1))+1+
    supportBound L*(2*graphSize L+1))
noncomputable def SPoly : Polynomial ℕ := X*X+(X*X)*(X*X)+1
noncomputable def HPoly : Polynomial ℕ := (X+(2*SPoly*SPoly)*(SPoly*X+1)*(SPoly*X))*X
noncomputable def APoly : Polynomial ℕ := X*(2*(3*X)+1)
noncomputable def sizePolynomial : Polynomial ℕ :=
  2*(3*X+2)+1+(2*(2*(HPoly+4)+1+SPoly*(2*(HPoly+4)+1))+1+SPoly*(2*APoly+1))
theorem sizePolynomial_eval (L : ℕ) : sizePolynomial.eval L=sizeBound L := by
  simp only [sizePolynomial,sizeBound,heightBound,supportBound,graphSize,HPoly,SPoly,APoly,
    SparseGraph.stepHeight,eval_add,eval_mul,eval_ofNat,eval_X,eval_one]

theorem state_size (x : Input) (t : ℕ) (ht : t≤x.m) :
    (State.encode (x.state t)).length≤ sizePolynomial.eval x.encode.length := by
  let L := x.encode.length
  obtain ⟨hn,hm,hN,hD⟩ := input_bounds x
  have htL : t≤L := ht.trans hm
  have hc : (Context.encode ⟨x,t⟩).length≤3*L+2 := by
    have hbits : t.bits.length≤t+1 := NatBinary.length_le_height (Nat.lt_two_pow_self.le)
    change (encodePair Input.encode Nat.bits (x,t)).length≤_
    rw [encodePair_length]
    change 2*L+1+t.bits.length≤_
    omega
  have hsupport : (x.state t).law.length≤ supportBound L := by
    apply (run_length x.columns t).trans
    unfold supportBound
    gcongr
  have hheight : SparseGraph.stepHeight x.n x.m L L*t≤heightBound L := by
    unfold heightBound SparseGraph.stepHeight
    dsimp only
    gcongr
  have hden : (x.state t).law.law.denominator≤(2:ℤ)^(heightBound L) :=
    (denominator_height x.columns L L hN hD t).trans (pow_le_pow_right₀ (by norm_num) hheight)
  have hr (S : Finset (Fin x.n)) : (erB (ListOperation.setView S)).length≤3*L := by
    have h := EncodedList.length_bound encodeBool (ListOperation.setView S) 1 (fun _ _ => by rfl)
    simp only [ListOperation.setView,List.length_ofFn] at h
    exact h.trans (by omega)
  have hs (G : Graph x.n x.m) : (et (ListOperation.view G)).length≤graphSize L := by
    have h := EncodedList.length_bound erB (ListOperation.view G) (3*L) (by
      intro row hrow
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrow
      exact hr (G i))
    simp only [ListOperation.view,List.length_ofFn] at h
    apply h.trans
    unfold graphSize
    gcongr
  have hb := SparseIntegerLaw.encode_length_bound (fun G : Graph x.n x.m => et (ListOperation.view G))
    (run x.columns t) (supportBound L) (heightBound L) (graphSize L) hsupport hden (fun _ => hs _)
  have he : State.encode (x.state t)=encodePair Context.encode
      (SparseIntegerLaw.BinarySparse.encode (fun G : Graph x.n x.m => et (ListOperation.view G)))
        (⟨x,t⟩,run x.columns t) := by
    simp only [State.encode,Bundle.encode,Bundle.raw,Input.state,view,
      SparseIntegerLaw.BinarySparse.encode,SparseIntegerLaw.BinarySparse.raw,ed,encodePair,RoundingProgram.encodeList_map]
  rw [sizePolynomial_eval,he,encodePair_length]
  unfold sizeBound
  dsimp only at ⊢
  simp only [L] at hc hb ⊢
  omega

noncomputable def runStateProgram : PolyProgram Input.encode State.encode (fun x => x.state x.m) :=
  (stepProgram.repeatFrom startProgram countProgram X sizePolynomial
    (fun x => by simpa using (input_bounds x).2.1)
    (fun x t ht => by rw [state_iterate]; exact state_size x t ht)).congr _ (fun x => state_iterate x _)
end MetricKMedian.SparseGraph.Program
end

end OAI
