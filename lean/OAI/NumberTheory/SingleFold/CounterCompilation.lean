import OAI.NumberTheory.SingleFold.CounterBounds

namespace OAI

namespace SingleFold.Compiler.ScalarSF
variable {α ι : Type} {f g : (α → ℕ) → ℕ}
lemma finset_sum (s : Finset ι) (f : ι → (α → ℕ) → ℕ) (h : ∀i∈s,ScalarSF (f i)) :
    ScalarSF (fun z => ∑i∈s,f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (α:=α) 0
  | @insert i s hi ih =>
    have hh := (h i (Finset.mem_insert_self _ _)).add (ih (fun j hj=>h j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using hh
lemma sum [Fintype ι] (f : ι → (α → ℕ) → ℕ) (h : ∀i,ScalarSF (f i)) :
    ScalarSF (fun z => ∑i,f i z) := finset_sum Finset.univ f (fun i _=>h i)
lemma bits (hf : ScalarSF f) (hg : ScalarSF g) : SF (fun z=>Binary.Bits (f z) (g z)) := by
  have hv : MapSF (fun z=>![f z,g z]) := MapSF.vector (by intro i; fin_cases i <;> assumption)
  exact hv.pullback Binary.bits
end SingleFold.Compiler.ScalarSF

namespace SingleFold.CounterCompilation
open Compiler Counter
inductive Var (Q J : Type)
  | w | B | b | k | H | last | mask
  | state (q : Q) | zeroBranch (q : Q) | decBranch (q : Q) | complement (q : Q)
  | counter (j : Option J) | final (j : Option J) | rem (j : Option J)
  deriving DecidableEq, Fintype

def encode {Q J : Type} (v : Witness Q J) : Var Q J → ℕ
  | .w=>v.w | .B=>v.B | .b=>v.b | .k=>v.k | .H=>v.H | .last=>v.last | .mask=>v.mask
  | .state q=>v.state q | .zeroBranch q=>v.zeroBranch q | .decBranch q=>v.decBranch q
  | .complement q=>v.complement q | .counter j=>v.counter j | .final j=>v.final j | .rem j=>v.rem j

def decode {Q J : Type} (v : Var Q J → ℕ) : Witness Q J :=
  ⟨v .w,v .B,v .b,v .k,v .H,v .last,v .mask,
    fun q=>v (.state q),fun q=>v (.zeroBranch q),fun q=>v (.decBranch q),fun q=>v (.complement q),
    fun j=>v (.counter j),fun j=>v (.final j),fun j=>v (.rem j)⟩
@[simp] lemma decode_encode {Q J : Type} (v : Witness Q J) : decode (encode v)=v := rfl
@[simp] lemma encode_decode {Q J : Type} (v : Var Q J → ℕ) : encode (decode v)=v := by
  funext i; cases i <;> rfl
lemma decode_injective {Q J : Type} : Function.Injective (@decode Q J) := by
  intro a b h
  simpa using congrArg encode h

variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable (M : Machine Q J)
abbrev Input (Q J : Type) := J ⊕ Var Q J
abbrev inp (z : Input Q J → ℕ) : J → ℕ := z ∘ Sum.inl
abbrev wit (z : Input Q J → ℕ) : Witness Q J := decode (z ∘ Sum.inr)
omit [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J] in
lemma field_sf (i : Var Q J) : ScalarSF (fun z : Input Q J → ℕ => z (.inr i)) := ScalarSF.proj _
omit [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J] in
lemma input_sf (j : J) : ScalarSF (fun z : Input Q J → ℕ => inp z j) := ScalarSF.proj _
omit [DecidableEq Q] [DecidableEq J] in
lemma baseC_sf : ScalarSF (fun z : Input Q J → ℕ => baseC Q (inp z)) :=
  (ScalarSF.const (1+Fintype.card Q)).add (ScalarSF.sum _ input_sf)
omit [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J] in
lemma arc_sf (q : Q) (b : Bool) : ScalarSF (fun z : Input Q J → ℕ=>arc M (wit z) q b) := by
  cases hi : M.instr q <;> cases b <;> simp only [arc,hi] <;>
    first | exact field_sf _ | exact ScalarSF.const 0
omit [Fintype J] [DecidableEq J] in
lemma incoming_sf (p : Q) : ScalarSF (fun z : Input Q J → ℕ=>incoming M (wit z) p) := by
  apply ScalarSF.sum
  intro q
  apply ScalarSF.sum
  intro b
  by_cases h : dest M q b=some p
  · simpa only [ite_eq_left h] using arc_sf M q b
  · simpa only [ite_eq_right h] using (ScalarSF.const (α:=Input Q J) 0)
omit [Fintype J] [DecidableEq Q] in
lemma increments_sf (j : J) : ScalarSF (fun z : Input Q J → ℕ=>increments M (wit z) j) := by
  apply ScalarSF.sum
  intro q
  cases hi : M.instr q with
  | halt => exact ScalarSF.const 0
  | inc i p =>
    by_cases h : i=j
    · simpa only [ite_eq_left h,wit,decode,Function.comp_apply] using field_sf (Q:=Q) (J:=J) (.state q)
    · simpa only [ite_eq_right h] using (ScalarSF.const (α:=Input Q J) 0)
  | test i p0 pd => exact ScalarSF.const 0
omit [Fintype J] [DecidableEq Q] in
lemma decrements_sf (j : J) : ScalarSF (fun z : Input Q J → ℕ=>decrements M (wit z) j) := by
  apply ScalarSF.sum
  intro q
  cases hi : M.instr q with
  | halt => exact ScalarSF.const 0
  | inc i p => exact ScalarSF.const 0
  | test i p0 pd =>
    by_cases h : i=j
    · simpa only [ite_eq_left h,wit,decode,Function.comp_apply] using field_sf (Q:=Q) (J:=J) (.decBranch q)
    · simpa only [ite_eq_right h] using (ScalarSF.const (α:=Input Q J) 0)

omit [Fintype J] [DecidableEq Q] [DecidableEq J] in
lemma branch_sf : SF (fun z : Input Q J → ℕ=>∀q,match M.instr q with
    | .test _ _ _ => Bits ((wit z).zeroBranch q) ((wit z).state q) ∧
      Bits ((wit z).decBranch q) ((wit z).state q) ∧
      (wit z).zeroBranch q+(wit z).decBranch q=(wit z).state q ∧
      (wit z).zeroBranch q+(wit z).complement q=(wit z).mask
    | _ => (wit z).zeroBranch q=0 ∧ (wit z).decBranch q=0 ∧ (wit z).complement q=0) := by
  apply SF.all
  intro q
  cases hi : M.instr q with
  | halt =>
    exact ((field_sf (Q:=Q) (J:=J) (.zeroBranch q)).eq (ScalarSF.const 0)).and
      (((field_sf (Q:=Q) (J:=J) (.decBranch q)).eq (ScalarSF.const 0)).and ((field_sf (Q:=Q) (J:=J) (.complement q)).eq (ScalarSF.const 0)))
  | inc i p =>
    exact ((field_sf (Q:=Q) (J:=J) (.zeroBranch q)).eq (ScalarSF.const 0)).and
      (((field_sf (Q:=Q) (J:=J) (.decBranch q)).eq (ScalarSF.const 0)).and ((field_sf (Q:=Q) (J:=J) (.complement q)).eq (ScalarSF.const 0)))
  | test i p0 pd =>
    exact ((field_sf (Q:=Q) (J:=J) (.zeroBranch q)).bits (field_sf (Q:=Q) (J:=J) (.state q))).and
      (((field_sf (Q:=Q) (J:=J) (.decBranch q)).bits (field_sf (Q:=Q) (J:=J) (.state q))).and
      ((((field_sf (Q:=Q) (J:=J) (.zeroBranch q)).add (field_sf (Q:=Q) (J:=J) (.decBranch q))).eq (field_sf (Q:=Q) (J:=J) (.state q))).and
      (((field_sf (Q:=Q) (J:=J) (.zeroBranch q)).add (field_sf (Q:=Q) (J:=J) (.complement q))).eq (field_sf (Q:=Q) (J:=J) .mask))))

omit [Fintype J] [DecidableEq Q] [DecidableEq J] in
lemma zero_test_sf : SF (fun z : Input Q J → ℕ=>∀q,match M.instr q with
    | .test j _ _=>Bits ((wit z).counter (some j)) (((wit z).B-1)*(wit z).complement q)
    | _=>True) := by
  have ht : SF (fun _ : Input Q J → ℕ=>True) :=
    (SF.eq (Poly.const 0) (Poly.const 0)).congr (by simp)
  apply SF.all
  intro q
  cases hi : M.instr q with
  | halt => exact ht
  | inc i p => exact ht
  | test j p0 pd =>
    exact (field_sf (Q:=Q) (J:=J) (.counter (some j))).bits
      (((field_sf (Q:=Q) (J:=J) .B).sub (ScalarSF.const 1)).mul (field_sf (Q:=Q) (J:=J) (.complement q)))

lemma system_sf : SF (fun z : Input Q J → ℕ=>System M (inp z) (wit z)) := by
  let a (i : Var Q J) := field_sf i
  let c (k : ℕ) := ScalarSF.const (α:=Input Q J) k
  have hp : SF (fun z : Input Q J → ℕ=>(wit z).B=2^(wit z).w) :=
    ((c 2).powerRel (a .w) (a .B)).congr (by intro z; simp only [le_refl,true_and]; rfl)
  have hb := (a .B).eq ((c 4).mul (a .b))
  have hbound := ((c 2).mul (baseC_sf (Q:=Q) (J:=J))).lt (a .B)
  have hk := (c 0).lt (a .k)
  have hfull := (a .B).powerRel (a .k) (a .H)
  have hlast := ((a .B).mul (a .last)).eq (a .H)
  have hmask := (((a .B).sub (c 1)).mul (a .mask)).eq ((a .H).sub (c 1))
  have hstate := SF.all (fun q=> (a (.state q)).bits (a .mask))
  have hpart := (ScalarSF.sum _ (fun q=>a (.state q))).eq (a .mask)
  have htrans := SF.all (fun q=> (a (.state q)).eq
    ((c (if q=M.start then 1 else 0)).add ((a .B).mul (incoming_sf M q))))
  have hcounter := SF.all (fun j : Option J=>
    ((a (.counter j)).bits ((((c 2).mul (a .b)).sub (c 1)).mul (a .mask))).and
    (((a (.counter j)).eq (((a (.final j)).mul (a .last)).add (a (.rem j)))).and
      ((a (.rem j)).lt (a .last))))
  have hupdate := SF.all (fun j=> ((a (.counter (some j))).add ((a .B).mul (decrements_sf M j))).eq
    ((input_sf j).add ((a .B).mul ((a (.rem (some j))).add (increments_sf M j)))))
  have hclock := ((a (.counter none)).add ((a .B).mul (a .last))).eq
    ((baseC_sf (Q:=Q) (J:=J)).add ((a .B).mul ((a (.rem none)).add (a .mask))))
  have hlower := (a .b).le (a (.final none))
  have hupper := ((c 2).mul (a (.final none))).lt (a .B)
  have hh := hp.and (hb.and (hbound.and (hk.and (hfull.and (hlast.and (hmask.and
    (hstate.and (hpart.and ((branch_sf M).and (htrans.and (hcounter.and (hupdate.and
    ((zero_test_sf M).and (hclock.and (hlower.and hupper)))))))))))))))
  refine hh.congr ?_
  intro z
  constructor
  · rintro ⟨hp,hb,hbound,hk,⟨_,hfull⟩,hlast,hmask,hstate,hpart,hbranch,htrans,hcounter,hupdate,hzero,hclock,hlower,hupper⟩
    exact ⟨hp,hb,hbound,hk,hfull,hlast,hmask,hstate,hpart,hbranch,htrans,hcounter,hupdate,hzero,hclock,hlower,hupper⟩
  · intro h
    exact ⟨h.power,h.base,h.bound,h.length,⟨show 2≤(wit z).B from le_trans (by omega) h.Bfour,h.full⟩,h.last,h.mask,
      h.state_bits,h.partition,h.branch,h.transition,h.counter,h.update,h.zero_test,h.clock,h.scale_lower,h.scale_upper⟩

lemma halts_sf : SF (fun d : J → ℕ=>Counter.Halts M d) := by
  have hh := (system_sf M).ex (fun d v u hv hu=>decode_injective (system_unique hv hu))
  refine hh.congr ?_
  intro d
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨_,hv.haltsAt⟩
  · intro h
    obtain ⟨v,hv⟩:=system_complete M d h
    refine ⟨encode v,?_⟩
    simpa only [inp,wit,Function.comp_def,Sum.elim_inl,Sum.elim_inr,decode_encode] using hv
end SingleFold.CounterCompilation

end OAI
