import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseIterationHeight
import OAI.Combinatorics.KMedian.Process.CountStepProgram
import OAI.Combinatorics.KMedian.Process.CountRunHeight

namespace OAI


                                       
section
namespace MetricKMedian.SparseCounts.Program
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.DependentProgram SparseIntegerLaw.BinarySparse
open ListOperation (Row Table et)
local notation "erB" => ListOperation.er

def Input.state (x : Input) (t : ℕ) : State := ⟨⟨x,t⟩,run x.columns t⟩
def Input.start (x : Input) : State := ⟨⟨x,0⟩,.dirac (fun _ _ => 0)⟩

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
    simp only [column,dite_eq_left ht,he ht,SparseCounts.step,SparseIntegerLaw.prodCompress]
  · rw [ite_eq_right ht,run,dite_eq_right ht]
    rfl

theorem state_iterate (x : Input) (t : ℕ) : (State.step)^[t] x.start=x.state t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,state_next]

noncomputable def startProgram : PolyProgram Input.encode State.encode Input.start := by
  let raw : PolyProgram ei (encodePair (encodePair ei Nat.bits) (ed et))
      (fun x : InputRaw => ((x,0),(((1:ℤ),[(1:ℤ)]),[x.2.map (fun _ => x.1.map (fun _ => (0:ℕ)))]))) := by
    apply Binary.Automatic.Poly.program
    have hs : Binary.Automatic.Poly (fun x : InputRaw => x.2.map (fun _ => x.1.map (fun _ => (0:ℕ)))) := by
      apply Binary.Automatic.Poly.list_map
      · apply Binary.Automatic.Poly.list_map <;> fun_prop
      · fun_prop
    fun_prop
  exact raw.recode Input.raw (fun _ => rfl) (fun x => by
    simp only [State.encode,Bundle.encode,Bundle.raw,Input.start,SparseIntegerLaw.dirac,
      List.map_const',Input.raw,List.length_ofFn,List.map_replicate,
      Vector.toList_replicate,List.ofFn_const,view,ListOperation.view]
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

theorem entry_bound (x : Input) : ∀ i, ∀ a : Fin (x.columns i).length, ∀ h,
    (x.columns i).states[a.val] h≤2^x.encode.length := by
  intro i a h
  have he := encodePair_length (encodeList (fun _ : Unit => [])) (encodeList (ed erB)) x.raw
  have hcol := EncodedList.member_length (ed erB) x.raw.2 (columnRaw (x.columns i))
    (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have hs := encodePair_length el (encodeList erB) (columnRaw (x.columns i))
  have hrow := EncodedList.member_length erB ((x.columns i).states.toList.map ListOperation.setView)
    (ListOperation.setView (x.columns i).states[a.val]) (by
      apply List.mem_map.mpr
      exact ⟨(x.columns i).states[a.val], by simp, rfl⟩)
  have hv := EncodedList.member_length Nat.bits (ListOperation.setView (x.columns i).states[a.val])
    ((x.columns i).states[a.val] h) (List.mem_ofFn.mpr ⟨h,rfl⟩)
  have hl : ((x.columns i).states[a.val] h).bits.length≤x.encode.length := by
    change x.encode.length=_ at he
    change (ed erB (columnRaw (x.columns i))).length=
      2*(el ((x.columns i).law.denominator,List.ofFn (x.columns i).law.numerator)).length+1+
        (encodeList erB ((x.columns i).states.toList.map ListOperation.setView)).length at hs
    change ((x.columns i).states[a.val] h).bits.length≤(erB (ListOperation.setView (x.columns i).states[a.val])).length at hv
    omega
  exact (NatBinary.le_two_pow_length _).trans (Nat.pow_le_pow_right (by decide) hl)

def supportBound (L : ℕ) := L*L+(L*L)*(L*L)+1
def heightBound (L : ℕ) := SparseCounts.stepHeight L L L L L*L
def graphSize (L : ℕ) := L*(2*(L*(2*(L+1)+1))+1)
def sizeBound (L : ℕ) :=
  2*(3*L+2)+1+(2*(2*(heightBound L+4)+1+supportBound L*(2*(heightBound L+4)+1))+1+
    supportBound L*(2*graphSize L+1))
noncomputable def SPoly : Polynomial ℕ := X*X+(X*X)*(X*X)+1
noncomputable def HPoly : Polynomial ℕ := (X+(2*SPoly*(SPoly+(X+X)*(SPoly*X+1)))*(SPoly*X+1)*(SPoly*X))*X
noncomputable def APoly : Polynomial ℕ := X*(2*(X*(2*(X+1)+1))+1)
noncomputable def sizePolynomial : Polynomial ℕ :=
  2*(3*X+2)+1+(2*(2*(HPoly+4)+1+SPoly*(2*(HPoly+4)+1))+1+SPoly*(2*APoly+1))
theorem sizePolynomial_eval (L : ℕ) : sizePolynomial.eval L=sizeBound L := by
  simp only [sizePolynomial,sizeBound,heightBound,supportBound,graphSize,HPoly,SPoly,APoly,
    SparseCounts.stepHeight,eval_add,eval_mul,eval_ofNat,eval_X,eval_one]

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
  have hheight : SparseCounts.stepHeight x.n x.m L L L*t≤heightBound L := by
    unfold heightBound SparseCounts.stepHeight
    dsimp only
    gcongr
  have hden : (x.state t).law.law.denominator≤(2:ℤ)^(heightBound L) :=
    (denominator_height x.columns L L L hN hD (entry_bound x) t).trans (pow_le_pow_right₀ (by norm_num) hheight)
  have hr (S : Fin x.n → ℕ) (hS : ∀ i,S i≤2^L) : (erB (ListOperation.setView S)).length≤L*(2*(L+1)+1) := by
    have h := EncodedList.length_bound Nat.bits (ListOperation.setView S) (L+1) (by
      intro z hz
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
      exact NatBinary.length_le_height (hS i))
    simp only [ListOperation.setView,List.length_ofFn] at h
    exact h.trans (Nat.mul_le_mul_right _ hn)
  have hs (a : Fin (run x.columns t).length) :
      (et (ListOperation.view (run x.columns t).states[a.val])).length≤graphSize L := by
    have hg := run_bound x.columns (2^L) (entry_bound x) t a
    have h := EncodedList.length_bound erB (ListOperation.view (run x.columns t).states[a.val]) (L*(2*(L+1)+1)) (by
      intro row hrow
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrow
      exact hr _ (hg i))
    simp only [ListOperation.view,List.length_ofFn] at h
    apply h.trans
    unfold graphSize
    gcongr
  have hb := SparseIntegerLaw.encode_length_bound (fun G : SparseCounts.Table x.n x.m => et (ListOperation.view G))
    (run x.columns t) (supportBound L) (heightBound L) (graphSize L) hsupport hden (fun i => hs _)
  have he : State.encode (x.state t)=encodePair Context.encode
      (SparseIntegerLaw.BinarySparse.encode (fun G : SparseCounts.Table x.n x.m => et (ListOperation.view G)))
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
end MetricKMedian.SparseCounts.Program
end

end OAI
