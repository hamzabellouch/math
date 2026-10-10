import OAI.NumberTheory.SingleFold.CounterRecords

namespace OAI

namespace SingleFold.Packed
lemma bits_pack {B w k : ℕ} (hB : B=2^w) (hw : 0 < w) (f g : ℕ → ℕ)
    (hf : ∀t < k,f t < B) (hg : ∀t < k,g t < B) (hfg : ∀t < k,Bits (f t) (g t)) :
    Bits (pack B k f) (pack B k g) := by
  rw [hB,bits_blocks hw]
  intro t
  by_cases ht : t < k
  · simpa only [←hB,digit_pack (by rw [hB]; positivity) hf,
      digit_pack (by rw [hB]; positivity) hg,ite_eq_left ht] using hfg t ht
  · simp only [←hB,digit_pack (by rw [hB]; positivity) hf,
      digit_pack (by rw [hB]; positivity) hg,ite_eq_right ht]
    exact bits_refl 0
lemma exists_scale {L : ℕ} (hL : 0 < L) : ∃ w b : ℕ, 0 < w ∧ 0 < b ∧ 2^w=4*b ∧ 2*L < 2^w ∧ b ≤ L := by
  obtain ⟨w,hl,hu⟩:=unique_scale hL
  have hw : 2 ≤ w := by
    by_contra hn
    have hw : w=0 ∨ w=1 := by omega
    rcases hw with hw|hw <;> simp [hw] at hl <;> omega
  refine ⟨w,2^(w-2),by omega,pow_pos (by omega) _,?_,hl.1,?_⟩
  · have hh : w=(w-2)+2 := by omega
    nth_rw 1 [hh]
    rw [pow_add]
    norm_num
    omega
  · have hh : 2^w=4*2^(w-2) := by
      have he : w=(w-2)+2 := by omega
      nth_rw 1 [he]
      rw [pow_add]
      norm_num
      omega
    rw [hh] at hl
    omega
end SingleFold.Packed

namespace SingleFold.Counter
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
def stateAt (c : Cfg Q J) (q : Q) : ℕ := if q=c.state then 1 else 0
def zeroAt (M : Machine Q J) (c : Cfg Q J) (q : Q) : ℕ :=
  match M.instr q with
  | .test j _ _ => if q=c.state ∧ c.value j=0 then 1 else 0
  | _ => 0
def decAt (M : Machine Q J) (c : Cfg Q J) (q : Q) : ℕ :=
  match M.instr q with
  | .test j _ _ => if q=c.state ∧ c.value j≠0 then 1 else 0
  | _ => 0
def arcAt (M : Machine Q J) (c : Cfg Q J) (q : Q) (b : Bool) : ℕ :=
  match M.instr q,b with
  | .inc _ _,false => stateAt c q
  | .test _ _ _,false => zeroAt M c q
  | .test _ _ _,true => decAt M c q
  | _,_ => 0
omit [DecidableEq J] in
lemma stateAt_le (c : Cfg Q J) (q : Q) : stateAt c q ≤ 1 := by unfold stateAt; split_ifs <;> omega
omit [DecidableEq J] in
lemma zeroAt_le (M : Machine Q J) (c : Cfg Q J) (q : Q) : zeroAt M c q ≤ stateAt c q := by
  unfold zeroAt stateAt
  split <;> split_ifs <;> simp_all
omit [DecidableEq J] in
lemma decAt_le (M : Machine Q J) (c : Cfg Q J) (q : Q) : decAt M c q ≤ stateAt c q := by
  unfold decAt stateAt
  split <;> split_ifs <;> simp_all
omit [DecidableEq J] in
lemma arcAt_inactive (M : Machine Q J) (c : Cfg Q J) (q : Q) (b : Bool) (hq : q≠c.state) : arcAt M c q b=0 := by
  cases hi : M.instr q <;> cases b <;> simp [arcAt,stateAt,zeroAt,decAt,hi,hq]
omit [DecidableEq J] in
lemma arcAt_halt (M : Machine Q J) (c : Cfg Q J) (hc : c.state=M.halt) (q : Q) (b : Bool) : arcAt M c q b=0 := by
  by_cases hq : q=c.state
  · have hi : M.instr q=.halt := (M.halt_iff q).mpr (hq.trans hc)
    cases b <;> simp [arcAt,hi]
  · exact arcAt_inactive M c q b hq
omit [DecidableEq J] in
lemma testAt_partition (M : Machine Q J) (c : Cfg Q J) (q : Q) (j : J) (p0 pd : Q)
    (hi : M.instr q=.test j p0 pd) : zeroAt M c q+decAt M c q=stateAt c q := by
  simp only [zeroAt,decAt,hi,stateAt]
  by_cases hq : q=c.state <;> by_cases hz : c.value j=0 <;> simp [hq,hz]
variable [Fintype Q]
def incomingAt (M : Machine Q J) (c : Cfg Q J) (p : Q) : ℕ :=
  ∑q,∑b : Bool,if dest M q b=some p then arcAt M c q b else 0
def incAt (M : Machine Q J) (c : Cfg Q J) (j : J) : ℕ :=
  ∑q,match M.instr q with | .inc i _=>if i=j then stateAt c q else 0 | _=>0
def subAt (M : Machine Q J) (c : Cfg Q J) (j : J) : ℕ :=
  ∑q,match M.instr q with | .test i _ _=>if i=j then decAt M c q else 0 | _=>0
omit [DecidableEq J] in
lemma incomingAt_active (M : Machine Q J) (c : Cfg Q J) (p : Q) :
    incomingAt M c p=∑b : Bool,if dest M c.state b=some p then arcAt M c c.state b else 0 := by
  apply Finset.sum_eq_single c.state
  · intro q hq hqc
    apply Finset.sum_eq_zero
    intro b hb
    simp [arcAt_inactive M c q b hqc]
  · simp
lemma incAt_active (M : Machine Q J) (c : Cfg Q J) (j : J) :
    incAt M c j=match M.instr c.state with | .inc i _=>if i=j then 1 else 0 | _=>0 := by
  unfold incAt
  rw [Finset.sum_eq_single c.state]
  · simp [stateAt]
  · intro q hq hqc
    cases hi : M.instr q <;> simp [stateAt,hqc]
  · simp
lemma subAt_active (M : Machine Q J) (c : Cfg Q J) (j : J) :
    subAt M c j=match M.instr c.state with | .test i _ _=>if i=j ∧ c.value i≠0 then 1 else 0 | _=>0 := by
  unfold subAt
  rw [Finset.sum_eq_single c.state]
  · cases hi : M.instr c.state <;> simp [decAt,hi,ite_and]
  · intro q hq hqc
    cases hi : M.instr q <;> simp [decAt,hi,hqc]
  · simp
lemma incAt_le (M : Machine Q J) (c : Cfg Q J) (j : J) : incAt M c j ≤ 1 := by
  rw [incAt_active]
  split <;> (try split_ifs) <;> omega
lemma subAt_le (M : Machine Q J) (c : Cfg Q J) (j : J) : subAt M c j ≤ 1 := by
  rw [subAt_active]
  split <;> (try split_ifs) <;> omega
lemma incomingAt_next (M : Machine Q J) (c : Cfg Q J) (hc : c.state≠M.halt) (p : Q) :
    incomingAt M c p=stateAt (next M c) p := by
  rw [incomingAt_active]
  cases hi : M.instr c.state with
  | halt => exact False.elim (hc ((M.halt_iff _).mp hi))
  | inc j q => simp [dest,arcAt,hi,stateAt,next,eq_comm]
  | test j p0 pd =>
    by_cases hz : c.value j=0 <;> simp [dest,arcAt,hi,stateAt,next,zeroAt,decAt,hz,eq_comm]
lemma counterAt_next (M : Machine Q J) (c : Cfg Q J) (j : J) :
    (next M c).value j+subAt M c j=c.value j+incAt M c j := by
  rw [incAt_active,subAt_active]
  cases hi : M.instr c.state with
  | halt => simp [next,hi]
  | inc i p =>
    by_cases hij : i=j
    · subst i; simp [next,hi]
    · simp [next,hi,hij,Ne.symm hij,Function.update_of_ne]
  | test i p0 pd =>
    by_cases hz : c.value i=0
    · simp [next,hi,hz]
    · by_cases hij : i=j
      · subst i; simp [next,hi,hz]; omega
      · simp [next,hi,hz,hij,Ne.symm hij,Function.update_of_ne]
lemma incAt_halt (M : Machine Q J) (c : Cfg Q J) (hc : c.state=M.halt) (j : J) : incAt M c j=0 := by
  rw [incAt_active,(M.halt_iff _).mpr hc]
lemma subAt_halt (M : Machine Q J) (c : Cfg Q J) (hc : c.state=M.halt) (j : J) : subAt M c j=0 := by
  rw [subAt_active,(M.halt_iff _).mpr hc]
end SingleFold.Counter

namespace SingleFold.Packed
lemma pack_ite_const (B k : ℕ) (p : Prop) [Decidable p] (f g : ℕ → ℕ) :
    pack B k (fun t=>if p then f t else g t)=if p then pack B k f else pack B k g := by
  by_cases hp : p <;> simp [hp]
end SingleFold.Packed
namespace SingleFold.Counter
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
def valueAt (M : Machine Q J) (d : J → ℕ) (j : Option J) (t : ℕ) : ℕ :=
  match j with | none=>baseC Q d+t | some i=>(run M d t).value i

def trace (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ) : Witness Q J where
  w:=w
  B:=B
  b:=b
  k:=T+1
  H:=B^(T+1)
  last:=B^T
  mask:=ones B (T+1)
  state:=fun q=>pack B (T+1) (fun t=>stateAt (run M d t) q)
  zeroBranch:=fun q=>pack B (T+1) (fun t=>zeroAt M (run M d t) q)
  decBranch:=fun q=>pack B (T+1) (fun t=>decAt M (run M d t) q)
  complement:=fun q=> match M.instr q with
    | .test _ _ _ => pack B (T+1) (fun t=>1-zeroAt M (run M d t) q)
    | _=>0
  counter:=fun j=>pack B (T+1) (valueAt M d j)
  final:=fun j=>valueAt M d j T
  rem:=fun j=>pack B T (valueAt M d j)
lemma trace_arc (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ) (q : Q) (a : Bool) :
    arc M (trace M d B w b T) q a=pack B (T+1) (fun t=>arcAt M (run M d t) q a) := by
  cases hi : M.instr q <;> cases a <;> simp [arc,arcAt,hi,trace,pack_const_zero]
lemma trace_incoming (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ) (q : Q) :
    incoming M (trace M d B w b T) q=pack B (T+1) (fun t=>incomingAt M (run M d t) q) := by
  simp only [incoming,incomingAt,pack_sum,pack_ite_const,pack_const_zero,trace_arc]
lemma trace_inc (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ) (j : J) :
    increments M (trace M d B w b T) j=pack B (T+1) (fun t=>incAt M (run M d t) j) := by
  simp only [increments,incAt,pack_sum]
  apply Finset.sum_congr rfl
  intro q hq
  cases hi : M.instr q <;> simp [trace,pack_const_zero,pack_ite_const]
lemma trace_sub (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ) (j : J) :
    decrements M (trace M d B w b T) j=pack B (T+1) (fun t=>subAt M (run M d t) j) := by
  simp only [decrements,subAt,pack_sum]
  apply Finset.sum_congr rfl
  intro q hq
  cases hi : M.instr q <;> simp [trace,pack_const_zero,pack_ite_const]
lemma trace_transition (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ) (hT : HaltsAt M d T) (q : Q) :
    (trace M d B w b T).state q=(if q=M.start then 1 else 0)+B*incoming M (trace M d B w b T) q := by
  rw [trace_incoming]
  have hlast : incomingAt M (run M d T) q=0 := by
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro b hb
    simp [arcAt_halt M _ hT.1]
  rw [pack_last hlast]
  change pack B (T+1) (fun t=>stateAt (run M d t) q)=_
  rw [pack_cons]
  congr 1
  apply congrArg (B*·)
  apply pack_congr
  intro t ht
  rw [incomingAt_next M _ (hT.2 t ht),run_succ]
lemma trace_update (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ) (hT : HaltsAt M d T) (j : J) :
    (trace M d B w b T).counter (some j)+B*decrements M (trace M d B w b T) j=
      d j+B*((trace M d B w b T).rem (some j)+increments M (trace M d B w b T) j) := by
  rw [trace_inc,trace_sub]
  have hi := pack_last (B:=B) (T:=T) (f:=fun t=>incAt M (run M d t) j)
    (incAt_halt M _ hT.1 j)
  have hs := pack_last (B:=B) (T:=T) (f:=fun t=>subAt M (run M d t) j)
    (subAt_halt M _ hT.1 j)
  rw [hi,hs]
  exact update_identity _ _ _ rfl (fun t _=>by simpa only [valueAt,run_succ] using counterAt_next M (run M d t) j)
omit [DecidableEq Q] in
lemma valueAt_bound (M : Machine Q J) (d : J → ℕ) (j : Option J) (t T : ℕ) (ht : t ≤ T) :
    valueAt M d j t ≤ baseC Q d+T := by
  cases j with
  | none => dsimp [valueAt]; omega
  | some j =>
    have hi : d j ≤ ∑i,d i := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)
    have hh := value_bound M d t j
    dsimp [valueAt,baseC]
    omega
end SingleFold.Counter

namespace SingleFold.Packed
lemma bits_of_le_one {x y : ℕ} (hxy : x ≤ y) (hy : y ≤ 1) : Bits x y := by
  interval_cases y
  · have hx : x=0 := by omega
    simpa [hx] using bits_refl 0
  · exact (bits_one x).mpr hxy
end SingleFold.Packed

namespace SingleFold.Counter
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
lemma trace_clock (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ) :
    (trace M d B w b T).counter none+B*(trace M d B w b T).last=
      baseC Q d+B*((trace M d B w b T).rem none+(trace M d B w b T).mask) := by
  have hh := update_identity (B:=B) (T:=T) (d:=baseC Q d)
    (fun t=>baseC Q d+t) (fun _=>1) (fun _=>0) (by omega) (by intros; omega)
  rw [pack_const_zero,mul_zero,add_zero] at hh
  change pack B (T+1) (fun t=>baseC Q d+t)+B*B^T=
    baseC Q d+B*(pack B T (fun t=>baseC Q d+t)+ones B (T+1))
  rw [hh,ones,pack_succ]
  ring

lemma trace_system (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ)
    (hT : HaltsAt M d T) (hB : B=2^w) (hw : 0 < w) (hb : 0 < b)
    (hbase : B=4*b) (hlarge : 2*(baseC Q d+T) < B) (hsmall : b ≤ baseC Q d+T) :
    System M d (trace M d B w b T) := by
  have hBpos : 0 < B := by omega
  have hBone : 1 < B := by omega
  have hhalf : 2*b=2^(w-1) := by
    have hh : 2^w=2^(w-1)*2 := by
      nth_rw 1 [show w=(w-1)+1 by omega]
      rw [pow_succ]
    omega
  have hv (j : Option J) (t : ℕ) (ht : t ≤ T) : valueAt M d j t < 2*b := by
    have := valueAt_bound M d j t T ht
    omega
  have hvl (j : Option J) (t : ℕ) (ht : t ≤ T) : valueAt M d j t < B := by
    have := hv j t ht
    omega
  have hs (t : ℕ) (q : Q) : stateAt (run M d t) q < B :=
    lt_of_le_of_lt (stateAt_le _ _) hBone
  refine ⟨hB,hbase,by dsimp [trace]; omega,by simp [trace],rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp [trace]; rw [pow_succ,mul_comm]
  · exact geometric hBone (T+1)
  · intro q
    exact bits_pack hB hw _ _ (fun t _=>hs t q) (fun _ _=>hBone)
      (fun t _=>(bits_one _).mpr (stateAt_le _ _))
  · change (∑q,pack B (T+1) (fun t=>stateAt (run M d t) q))=ones B (T+1)
    rw [←pack_sum]
    apply pack_congr
    intro t ht
    simp [stateAt]
  · intro q
    cases hi : M.instr q with
    | halt => simp [trace,zeroAt,decAt,hi,pack_const_zero]
    | inc j p => simp [trace,zeroAt,decAt,hi,pack_const_zero]
    | test j p0 pd =>
      have hz (t : ℕ) : zeroAt M (run M d t) q ≤ 1 := le_trans (zeroAt_le _ _ _) (stateAt_le _ _)
      have hn (t : ℕ) : decAt M (run M d t) q ≤ 1 := le_trans (decAt_le _ _ _) (stateAt_le _ _)
      change Packed.Bits _ _ ∧ Packed.Bits _ _ ∧ _ ∧ _
      refine ⟨?_,?_,?_,?_⟩
      · exact bits_pack hB hw _ _ (fun t _=>lt_of_le_of_lt (hz t) hBone) (fun t _=>hs t q)
          (fun t _=>bits_of_le_one (zeroAt_le _ _ _) (stateAt_le _ _))
      · exact bits_pack hB hw _ _ (fun t _=>lt_of_le_of_lt (hn t) hBone) (fun t _=>hs t q)
          (fun t _=>bits_of_le_one (decAt_le _ _ _) (stateAt_le _ _))
      · change pack B (T+1) _+pack B (T+1) _=pack B (T+1) _
        rw [←pack_add]
        apply pack_congr
        intro t ht
        exact testAt_partition _ _ _ _ _ _ hi
      · change pack B (T+1) _+(match M.instr q with | .test _ _ _=>_ | _=>0)=ones B (T+1)
        rw [hi,←pack_add]
        apply pack_congr
        intro t ht
        exact Nat.add_sub_of_le (hz t)
  · exact trace_transition M d B w b T hT
  · intro j
    refine ⟨?_,?_,?_⟩
    · change Packed.Bits (pack B (T+1) (valueAt M d j)) ((2*b-1)*ones B (T+1))
      rw [ones_mul]
      apply bits_pack hB hw _ _ (fun t ht=>hvl j t (by omega)) (by intros; omega)
      intro t ht
      rw [hhalf]
      exact (bits_full _ _).mpr (by rw [←hhalf]; exact hv j t (by omega))
    · change pack B (T+1) _=valueAt M d j T*B^T+pack B T _
      rw [pack_succ,add_comm]
    · exact pack_lt hBpos (fun t ht=>hvl j t (by omega))
  · exact trace_update M d B w b T hT
  · intro q
    cases hi : M.instr q with
    | halt => trivial
    | inc j p => trivial
    | test j p0 pd =>
      change Packed.Bits (pack B (T+1) (valueAt M d (some j))) ((B-1)*_)
      simp only [trace,hi]
      rw [←pack_mul]
      apply bits_pack hB hw _ _ (fun t ht=>hvl (some j) t (by omega))
      · intro t ht
        have hh : zeroAt M (run M d t) q ≤ 1 := le_trans (zeroAt_le _ _ _) (stateAt_le _ _)
        interval_cases hz : zeroAt M (run M d t) q <;> simp <;> omega
      · intro t ht
        by_cases hz : zeroAt M (run M d t) q=0
        · simp only [hz,Nat.sub_zero,mul_one]
          rw [hB]
          exact (bits_full _ _).mpr (by rw [←hB]; exact hvl (some j) t (by omega))
        · have hj : (run M d t).value j=0 := by
            simp only [zeroAt,hi] at hz
            split_ifs at hz with hc
            · exact hc.2
            · contradiction
          simp only [valueAt,hj]
          exact bits_zero_left _
  · exact trace_clock M d B w b T
  · exact hsmall
  · exact hlarge

theorem system_complete (M : Machine Q J) (d : J → ℕ) (h : Halts M d) :
    ∃v,System M d v := by
  obtain ⟨T,hT⟩ := h
  have hc : 0 < baseC Q d+T := by dsimp [baseC]; omega
  obtain ⟨w,b,hw,hb,hB,hlarge,hsmall⟩ := exists_scale hc
  exact ⟨trace M d (2^w) w b T,trace_system M d _ _ _ _ hT rfl hw hb hB hlarge hsmall⟩
end SingleFold.Counter

end OAI
