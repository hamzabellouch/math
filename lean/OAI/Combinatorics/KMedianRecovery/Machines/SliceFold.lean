import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.CappedFold
import OAI.Combinatorics.KMedianRecovery.Encoding.LabelSize

namespace OAI

namespace MetricKMedianRecovery.CanonicalSlices
open CanonicalMergeRefinement
variable {X : Type*}
structure Acc (X : Type*) where
  front : List X
  rest : List X
  out : List (List X × X × List X)

def addFront (C : List X) (p : List X × X × List X) := (C++p.1,p.2.1,p.2.2)
def step (s : Acc X) (a : X) : Acc X :=
  ⟨s.front++[a],s.rest.tail,s.out++[(s.front,a,s.rest.tail)]⟩
lemma fold_result (C U : List X) (V : List (List X × X × List X)) :
    U.foldl step ⟨C,U,V⟩=⟨C++U,[],V++(cuts U).map (addFront C)⟩ := by
  induction U generalizing C V with
  | nil=>simp only [List.foldl_nil,cuts,List.map_nil,List.append_nil]
  | cons a U ih=>
    simp only [List.foldl_cons,step,List.tail_cons]
    rw [ih]
    simp only [cuts,List.map_cons,List.map_map,addFront,List.append_assoc,List.singleton_append,
      Function.comp_def,List.append_nil]
    have he : addFront (C++[a])=(fun p : List X × X × List X => (C++a::p.1,p.2.1,p.2.2)) := by
      funext p
      simp only [addFront,List.append_assoc,List.singleton_append]
    rw [he]
lemma addFront_nil (p : List X × X × List X) : addFront [] p=p := by
  rcases p with ⟨C,a,T⟩
  rfl
end MetricKMedianRecovery.CanonicalSlices

namespace MetricKMedianRecovery.BitMachine.WordList.Slices
open WordOperations CanonicalSlices
open BinaryOpeningPayment (field field_computes field_encode)

def itemsBits {X : Type*} (enc : X → List Bool) (xs : List X) : List Bool := encode (xs.map enc)
def cutBits {X : Type*} (enc : X → List Bool) (p : List X × X × List X) : List Bool :=
  encode [itemsBits enc p.1,enc p.2.1,itemsBits enc p.2.2]
def outBits {X : Type*} (enc : X → List Bool) (ps : List (List X × X × List X)) : List Bool := encode (ps.map (cutBits enc))
def accBits {X : Type*} (enc : X → List Bool) (s : Acc X) : List Bool :=
  encode [itemsBits enc s.front,itemsBits enc s.rest,outBits enc s.out]
lemma itemsBits_append {X : Type*} (enc : X → List Bool) (xs ys : List X) :
    itemsBits enc (xs++ys)=itemsBits enc xs++itemsBits enc ys := by simp only [itemsBits,List.map_append,encode_append]
lemma itemsBits_cons {X : Type*} (enc : X → List Bool) (x : X) (xs : List X) :
    itemsBits enc (x::xs)=cons (enc x) (itemsBits enc xs) := rfl
lemma itemsBits_nil {X : Type*} (enc : X → List Bool) : itemsBits enc []=[] := rfl
lemma itemsBits_tail {X : Type*} (enc : X → List Bool) (xs : List X) :
    tail (itemsBits enc xs)=itemsBits enc xs.tail := by
  cases xs with
  | nil=>rfl
  | cons x xs=>exact tail_cons _ _
lemma itemsBits_tail_le {X : Type*} (enc : X → List Bool) (xs : List X) :
    (itemsBits enc xs.tail).length≤(itemsBits enc xs).length := by
  cases xs with
  | nil=>rfl
  | cons x xs=>simp only [List.tail_cons,itemsBits_cons,length_cons]; omega
lemma outBits_append {X : Type*} (enc : X → List Bool) (ps qs : List (List X × X × List X)) :
    outBits enc (ps++qs)=outBits enc ps++outBits enc qs := by simp only [outBits,List.map_append,encode_append]

lemma outBits_singleton {X : Type*} (enc : X → List Bool) (p : List X × X × List X) :
    outBits enc [p]=cons (cutBits enc p) [] := rfl

def sf (n : ℕ) (x : List Bool) : List Bool := field n (discardPrefix (discardPrefix x))
def item (x : List Bool) : List Bool := extractPrefix (discardPrefix x)
noncomputable def sf_computes (n : ℕ) : PolyComputes (sf n) :=
  (discardPrefix_computes.comp discardPrefix_computes).comp (field_computes n)
noncomputable def item_computes : PolyComputes item := discardPrefix_computes.comp extractPrefix_computes
noncomputable def front (x : List Bool) : List Bool := sf 0 x++cons (item x) []
noncomputable def front_computes : PolyComputes front := (sf_computes 0).append (cons_computes item_computes (const_computes []))
noncomputable def rest (x : List Bool) : List Bool := tail (sf 1 x)
noncomputable def rest_computes : PolyComputes rest := (sf_computes 1).comp tail_computes
noncomputable def cut (x : List Bool) : List Bool := encode [sf 0 x,item x,rest x]
noncomputable def cut_computes : PolyComputes cut := list_computes [sf 0,item,rest] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨sf_computes _⟩
  · exact ⟨item_computes⟩
  · exact ⟨rest_computes⟩)
noncomputable def output (x : List Bool) : List Bool := sf 2 x++cons (cut x) []
noncomputable def output_computes : PolyComputes output := (sf_computes 2).append (cons_computes cut_computes (const_computes []))
noncomputable def step (x : List Bool) : List Bool := encode [front x,rest x,output x]
noncomputable def step_computes : PolyComputes step := list_computes [front,rest,output] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨front_computes⟩
  · exact ⟨rest_computes⟩
  · exact ⟨output_computes⟩)
lemma step_pack {X : Type*} (enc : X → List Bool) (s : Acc X) (a : X) :
    step (pairBits ([],pairBits (enc a,accBits enc s)))=accBits enc (CanonicalSlices.step s a) := by
  simp only [step,front,rest,output,cut,sf,item,extractPrefix_pairBits,discardPrefix_pairBits,accBits,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,itemsBits_tail]
  simp only [CanonicalSlices.step,itemsBits_append,itemsBits_cons,itemsBits_nil,outBits_append,outBits_singleton,cutBits]

structure Bounds {X : Type*} (enc : X → List Bool) (N n : ℕ) (s : Acc X) : Prop where
  front : (itemsBits enc s.front).length≤n*(2*N+2)
  rest : (itemsBits enc s.rest).length≤N
  count : s.out.length≤n
  each : ∀ p∈s.out,(cutBits enc p).length≤2*(n*(2*N+2)+N+N)+6
lemma Bounds.step {X : Type*} {enc : X → List Bool} {N n : ℕ} {s : Acc X} (hs : Bounds enc N n s)
    (a : X) (ha : (enc a).length≤N) : Bounds enc N (n+1) (CanonicalSlices.step s a) := by
  have ht:=(itemsBits_tail_le enc s.rest).trans hs.rest
  have hn : n*(2*N+2)≤(n+1)*(2*N+2) := Nat.mul_le_mul_right _ (Nat.le_succ n)
  refine ⟨?_,ht,?_,?_⟩
  · simp only [CanonicalSlices.step,itemsBits_append,itemsBits_cons,itemsBits_nil,List.length_append,length_cons,List.length_nil]
    have h:=hs.front
    simp only [Nat.add_mul,one_mul]
    omega
  · simp only [CanonicalSlices.step,List.length_append,List.length_singleton]
    exact Nat.add_le_add_right hs.count 1
  · intro p hp
    rcases List.mem_append.mp hp with hp|hp
    · exact (hs.each p hp).trans (by omega)
    · obtain rfl:=List.mem_singleton.mp hp
      simp only [cutBits,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
      have h:=hs.front
      omega
lemma Bounds.fold {X : Type*} {enc : X → List Bool} {N n : ℕ} {s : Acc X} (hs : Bounds enc N n s)
    (xs : List X) (hxs : ∀ x∈xs,(enc x).length≤N) :
    Bounds enc N (n+xs.length) (xs.foldl CanonicalSlices.step s) := by
  induction xs generalizing n s with
  | nil=>simpa only [List.foldl_nil,List.length_nil,Nat.add_zero] using hs
  | cons a xs ih=>
    simpa only [List.foldl_cons,List.length_cons,Nat.add_assoc,Nat.add_comm 1] using
      ih (hs.step a (hxs a (List.mem_cons_self ..))) (fun x hx=>hxs x (List.mem_cons_of_mem _ hx))
noncomputable def capacityPoly : Polynomial ℕ :=
  let X : Polynomial ℕ:=Polynomial.X
  2*(X*(2*X+2)+X+X*(2*(2*(X*(2*X+2)+X+X)+6)+2))+6
noncomputable def capacity : PolynomialCounter capacityPoly := PolynomialCounter.choose capacityPoly
lemma accBits_bound {X : Type*} {enc : X → List Bool} {N n : ℕ} {s : Acc X}
    (hs : Bounds enc N n s) (hn : n≤N) : (accBits enc s).length≤capacityPoly.eval N := by
  have hf := hs.front.trans (Nat.mul_le_mul_right _ hn)
  have ho := encode_le_bound (s.out.map (cutBits enc)) (2*(N*(2*N+2)+N+N)+6) (by
    intro w hw
    obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hw
    apply (hs.each p hp).trans
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) N) N)) 6)
  simp only [List.length_map] at ho
  have ho' : (outBits enc s.out).length≤N*(2*(2*(N*(2*N+2)+N+N)+6)+2) :=
    ho.trans (Nat.mul_le_mul_right _ (hs.count.trans hn))
  have hr:=hs.rest
  simp only [capacityPoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,accBits,
    length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  omega
noncomputable def initial (x : List Bool) : List Bool := Fold.pack x [] (encode [[],x,[]])
noncomputable def initial_computes : PolyComputes initial := Fold.pack_computes id_computes (const_computes [])
  (list_computes [fun _=>[],id,fun _=>[]] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨const_computes []⟩
    · exact ⟨id_computes⟩
    · exact ⟨const_computes []⟩))
noncomputable def result (x : List Bool) : List Bool := CappedFold.run step (pairBits (capacity.word x,initial x))
noncomputable def result_computes : PolyComputes result :=
  (capacity.computes.pair initial_computes).comp (CappedFold.run_computes step_computes)
noncomputable def run : List Bool → List Bool := field 2 ∘ result
noncomputable def run_computes : PolyComputes run := result_computes.comp (field_computes 2)
lemma result_items {X : Type*} (enc : X → List Bool) (xs : List X) :
    result (itemsBits enc xs)=accBits enc ⟨xs,[],CanonicalMergeRefinement.cuts xs⟩ := by
  let N:=(itemsBits enc xs).length
  have hlen : xs.length≤N := by
    change xs.length≤(encode (xs.map enc)).length
    simpa only [List.length_map] using length_le_encode (xs.map enc)
  have hm : ∀ x∈xs,(enc x).length≤N := fun x hx=>member_length (List.mem_map.mpr ⟨x,hx,rfl⟩)
  have hs : Bounds enc N 0 (⟨[],xs,[]⟩:Acc X) :=
    ⟨by simp only [itemsBits_nil,List.length_nil,Nat.zero_mul,Nat.le_refl],le_rfl,le_rfl,by intro p hp; exact False.elim (List.not_mem_nil hp)⟩
  have ht:=CappedFold.run_typed (accBits enc) enc CanonicalSlices.step step [] (capacity.word (itemsBits enc xs))
    (step_pack enc) (⟨[],xs,[]⟩:Acc X) xs
  have heq:=ht (by
    intro n
    rw [capacity.word_length]
    apply accBits_bound
    · simpa only [Nat.zero_add] using hs.fold (xs.take n) (fun x hx=>hm x (List.mem_of_mem_take hx))
    · simp only [List.length_take]; exact (Nat.min_le_right n xs.length).trans hlen)
  change result (itemsBits enc xs)=_ at heq
  have ha : (addFront ([] : List X))=id := funext CanonicalSlices.addFront_nil
  simpa only [CanonicalSlices.fold_result,List.nil_append,ha,List.map_id] using heq
lemma run_items {X : Type*} (enc : X → List Bool) (xs : List X) :
    run (itemsBits enc xs)=outBits enc (CanonicalMergeRefinement.cuts xs) := by
  simp only [run,Function.comp_apply,result_items,accBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
end MetricKMedianRecovery.BitMachine.WordList.Slices

end OAI
