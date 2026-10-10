import OAI.Computability.RandomMean.Preparation

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
namespace Counter
 theorem bounded_length (w : W) (cap : Count) : (bounded (w,cap)).length≤cap.length := by
  have hf : ∀ (xs : List Bool) (s : Address.State),
      (Fold.fold Address.step s xs).2.length ≤ s.2.length+xs.length := by
    intro xs
    induction xs with
    | nil => intro s; simp [Fold.fold]
    | cons b bs ih =>
      intro s
      have h := ih (Address.step (s,b))
      change (Fold.fold Address.step (Address.step (s,b)) bs).2.length≤_
      have hg : (Address.step (s,b)).2.length ≤ s.2.length+1 := by
        simp only [Address.step]
        split <;> simp
      simp only [List.length_cons]
      omega
  have h := hf (cap.map (fun _ => false)) (w,[])
  change (Fold.fold Address.step (w,[]) (cap.map (fun _ => false))).2.length≤_
  simpa using h
end Counter
namespace Chunks
noncomputable def split : Code (Digits×Count) (Digits×Digits) := by
  refine ⟨fun z => (⟨(Split.split (z.1.bits,z.2)).1⟩,⟨(Split.split (z.1.bits,z.2)).2⟩),
    Split.device.recode encode encode (fun z : Digits×Count => (z.1.bits,z.2))
      (fun z : Digits×Count => ((⟨(Split.split (z.1.bits,z.2)).1⟩ : Digits),(⟨(Split.split (z.1.bits,z.2)).2⟩ : Digits)))
      (fun _ => rfl) (fun _ => rfl), ?_⟩
  obtain ⟨K,d,h⟩ := Split.polynomial
  exact ⟨K,d,fun z => h (z.1.bits,z.2)⟩
noncomputable def positive : Code Digits W := by
  refine ⟨fun d => IntegerRead.positive d.bits, IntegerRead.positiveDevice.recode encode encode Digits.bits
    (fun d => IntegerRead.positive d.bits) (fun _ => rfl) (fun _ => rfl), ?_⟩
  obtain ⟨K,d,h⟩ := IntegerRead.positive_linear.polynomial
  exact ⟨K,d,fun z => h z.bits⟩
noncomputable def reverseDigits : Code Digits Digits := by
  refine ⟨fun d => ⟨d.bits.reverse⟩, (Lists.reverseDevice boolData).recode encode encode Digits.bits
    (fun d => (⟨d.bits.reverse⟩ : Digits)) (fun _ => rfl) (fun _ => rfl), ?_⟩
  obtain ⟨K,d,h⟩ := PolynomialCost.reverse boolData
  exact ⟨K,d,fun z => h z.bits⟩
abbrev State := (Count×Count)×(List Count×Digits)
noncomputable def params : Code State (Count×Count) := fst
noncomputable def acc : Code State (List Count) := snd ≫ₚ fst
noncomputable def bits : Code State Digits := snd ≫ₚ snd
noncomputable def pieces : Code State (Digits×Digits) := (bits ⋏ₚ (params ≫ₚ fst)) ≫ₚ split
noncomputable def sample : Code State Count := (((pieces ≫ₚ fst) ≫ₚ reverseDigits ≫ₚ positive) ⋏ₚ (params ≫ₚ snd)) ≫ₚ Counter.bounded
noncomputable def next : Code State State := params ⋏ₚ ((sample ⋏ₚ acc) ≫ₚ cons) ⋏ₚ (pieces ≫ₚ snd)
noncomputable def step : Code (State×Unit) State := fst ≫ₚ next
 theorem next_params (s : State) : (next s).1=s.1 := rfl
 theorem next_acc (s : State) : (next s).2.1=sample s::s.2.1 := rfl
 theorem next_bits (s : State) : (next s).2.2.bits=s.2.2.bits.drop s.1.1.length := by
  change (Split.split (s.2.2.bits,s.1.1)).2=_
  exact Split.rest _ _
 theorem sample_length (s : State) : (sample s).length ≤ s.1.2.length := Counter.bounded_length _ _
 theorem next_size (s : State) : treeSize (encode (next s))≤treeSize (encode s)+(2*s.1.2.length+2) := by
  have h := sample_length s
  have hr : treeSize (encode (next s).2.2)≤treeSize (encode s.2.2) := by
    change treeSize (listTree boolData (next s).2.2.bits) ≤ treeSize (listTree boolData s.2.2.bits)
    rw [next_bits]
    exact listTree_drop_le _ _ _
  have hshape (t : State) : treeSize (encode t)=
      treeSize (encode t.1)+(treeSize (encode t.2.1)+treeSize (encode t.2.2)+1)+1 := by
    rcases t with ⟨p,a,d⟩
    simp only [Size.pair]
  rw [hshape (next s),next_params,next_acc]
  have hc : treeSize (encode (sample s::s.2.1))=treeSize (encode (sample s))+treeSize (encode s.2.1)+1 :=
    treeSize_pair _ _
  rw [hc,Size.count,hshape s]
  omega
 theorem fold_params (s : State) (cs : Count) : (Fold.fold step.eval s cs).1=s.1 := by
  induction cs generalizing s with
  | nil => rfl
  | cons u cs ih => exact (ih (next s)).trans (next_params s)
 theorem fold_size (s : State) (cs : Count) : treeSize (encode (Fold.fold step.eval s cs))≤
    treeSize (encode s)+cs.length*(2*s.1.2.length+2) := by
  induction cs generalizing s with
  | nil => simp [Fold.fold]
  | cons u cs ih =>
    have h := ih (next s)
    rw [next_params] at h
    have hn := next_size s
    change treeSize (encode (Fold.fold step.eval (next s) cs))≤_
    rw [List.length_cons]
    nlinarith
 theorem prefix_size (s : State) (cs : Count) (k : ℕ) (hk : k≤cs.length) :
    treeSize (encode (Fold.fold step.eval s (cs.take k)))≤5*(treeSize (encode (s,cs))+1)^2 := by
  let N := treeSize (encode (s,cs))+1
  have hs : treeSize (encode s)≤N := (Size.fst (s,cs)).trans (Nat.le_succ _)
  have hc : cs.length≤N := (Size.length _).trans ((Size.snd (s,cs)).trans (Nat.le_succ _))
  have hp : s.1.2.length≤N := (Size.length _).trans ((Size.snd _).trans ((Size.fst _).trans hs))
  have h := fold_size s (cs.take k)
  have hl : (cs.take k).length≤N := (List.length_take_le _ _).trans (hk.trans hc)
  have hm := Nat.mul_le_mul hl (show 2*s.1.2.length+2≤2*N+2 by omega)
  have hn : 1≤N := Nat.le_add_left _ _
  change _≤5*N^2
  nlinarith
noncomputable def fold : Code (State×Count) State := foldPrefix step 5 2 prefix_size
noncomputable def run : Code ((Count×Count)×Digits×Count) (List Count) :=
  ((fst ⋏ₚ ((const [] : Code ((Count×Count)×Digits×Count) (List Count)) ⋏ₚ (snd ≫ₚ fst))) ⋏ₚ (snd ≫ₚ snd)) ≫ₚ fold ≫ₚ snd ≫ₚ fst ≫ₚ reverse
end Chunks
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.RandomTree
 theorem all_of_read {α : Type} (t : RandomTree α) (Q : α→Prop)
    (h : ∀ bits : ℕ→Bool, Q (t.read bits)) : t.All Q := by
  induction t with
  | leaf a => exact h (fun _ => false)
  | coin l r il ir =>
    constructor
    · apply il
      intro bits
      simpa only [read, Bool.false_eq_true, ↓reduceIte] using
        h (fun | 0 => false | j+1 => bits j)
    · apply ir
      intro bits
      simpa only [read, ↓reduceIte] using
        h (fun | 0 => true | j+1 => bits j)
end MeanPayoff.RandomTree
namespace MeanPayoff.RegisterBits
open RandomTree BinaryData.Take

def Traces {K : ℕ} (P : Program K) (c : Config P) (t : RandomTree (Config P)) : Prop :=
  ∀ (bits : ℕ→Bool) (pos : ℕ), advance P (fun j => bits (pos+j)) c
    ((t.consume bits pos).2-pos) = (t.consume bits pos).1
namespace Traces
variable {K : ℕ} {P : Program K} {c d : Config P} {t : RandomTree (Config P)}
 theorem leaf (c : Config P) : Traces P c (.leaf c) := by intro bits pos; simp [consume,advance]
 theorem wait (n : ℕ) (h : ∀ bits, advance P bits c n=d) (ht : Traces P d t) :
    Traces P c (RandomTree.wait n t) := by
  intro bits pos
  simp only [consume_wait]
  have hp := (consume_path t bits (pos+n)).1
  rw [show (t.consume bits (pos+n)).2-pos=n+((t.consume bits (pos+n)).2-(pos+n)) by omega,
    advance_add,h]
  simpa only [Nat.add_assoc] using ht bits (pos+n)
 theorem coin {l r : RandomTree (Config P)}
    (hl : Traces P (step P c false) l) (hr : Traces P (step P c true) r) :
    Traces P c (.coin l r) := by
  intro bits pos
  simp only [consume]
  split
  next hb =>
    have hp := (consume_path r bits (pos+1)).1
    rw [show (r.consume bits (pos+1)).2-pos=((r.consume bits (pos+1)).2-(pos+1))+1 by omega,
      advance_front]
    simp only [Nat.add_zero,hb]
    convert hr bits (pos+1) using 1
    congr 1
    funext j
    congr 1
    omega
  next hb =>
    have hp := (consume_path l bits (pos+1)).1
    have he : bits pos=false := Bool.eq_false_iff.mpr hb
    rw [show (l.consume bits (pos+1)).2-pos=((l.consume bits (pos+1)).2-(pos+1))+1 by omega,
      advance_front]
    simp only [Nat.add_zero,he]
    convert hl bits (pos+1) using 1
    congr 1
    funext j
    congr 1
    omega
 theorem bind {f : Config P→RandomTree (Config P)} (ht : Traces P c t)
    (hf : t.All (fun s => Traces P s (f s))) : Traces P c (t.bind f) := by
  intro bits pos
  simp only [consume_bind]
  let s := t.consume bits pos
  have hp : pos≤ s.2 := (consume_path t bits pos).1
  have hq : s.2≤((f s.1).consume bits s.2).2 := (consume_path (f s.1) bits s.2).1
  have hs := ((consume_path t bits pos).2).all hf
  change advance P (fun j => bits (pos+j)) c (((f s.1).consume bits s.2).2-pos)=_
  rw [show ((f s.1).consume bits s.2).2-pos=(s.2-pos)+(((f s.1).consume bits s.2).2-s.2) by omega,
    advance_add]
  rw [ht bits pos]
  have ha : ∀ j, pos+(s.2-pos+j)=s.2+j := by intro j; omega
  simpa only [ha] using hs bits s.2
 theorem padded (ht : Traces P c t) (hh : t.All (fun s => s.control=none))
    {N : ℕ} (hN : t.bitDepth≤N) (bits : ℕ→Bool) : advance P bits c N=t.read bits := by
  have hp := (consume_path t bits 0).2
  have hr : (t.consume bits 0).2≤N := by simpa only [Nat.sub_zero] using hp.depth_le.trans hN
  have hs := ht bits 0
  simp only [Nat.zero_add,Nat.sub_zero] at hs
  have hn := hp.all hh
  have ha := advance_pad P c (t.consume bits 0).1 bits hr hs hn
  simpa only [consume_read,Nat.zero_add] using ha
end Traces
 theorem read_tree {K : ℕ} (P : Program K) (n : ℕ) (c : Config P) (bits : ℕ→Bool) :
    (tree P n c).read bits=advance P bits c n := by
  induction n generalizing c bits with
  | zero => rfl
  | succ n ih =>
    rw [advance_front]
    simp only [tree,RandomTree.read]
    split <;> simp_all only
 theorem depth_tree {K : ℕ} (P : Program K) (n : ℕ) (c : Config P) : (tree P n c).bitDepth=n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [tree,bitDepth,ih,Nat.max_self]
 theorem Traces.tree_all {K : ℕ} {P : Program K} {c : Config P} {t : RandomTree (Config P)}
    (ht : Traces P c t) (hh : t.All (fun s => s.control=none)) {N : ℕ} (hN : t.bitDepth≤N) :
    (tree P N c).All (fun s => s.control=none) := by
  apply all_of_read
  intro bits
  rw [read_tree,ht.padded hh hN]
  have h := ((consume_path t bits 0).2).all hh
  simpa only [consume_read,Nat.zero_add] using h
 theorem Traces.expect {K : ℕ} {P : Program K} {c : Config P} {t : RandomTree (Config P)}
    (ht : Traces P c t) (hh : t.All (fun s => s.control=none)) {N : ℕ} (hN : t.bitDepth≤N)
    (f : Config P→ℚ) : (tree P N c).expect f=t.expect f := by
  have h1 := prefix_sum (tree P N c) f N (by rw [depth_tree])
  have h2 := prefix_sum t f N hN
  have he : ∀ bits : Fin N→Bool, (tree P N c).readPrefix bits=t.readPrefix bits := by
    intro bits
    exact (read_tree P N c (padBits bits)).trans (ht.padded hh hN _)
  simp_rw [he] at h1
  rw [h2] at h1
  exact mul_left_cancel₀ (by positivity : (2:ℚ)^N≠0) h1.symm

 theorem Flow.quiet_runs {K : ℕ} (F : Flow.Program K) (p : Fin F.nodes)
    (hq : CoinFree (F.block p)) (s t : Fin K→List Bool) (out out' : List Bool) (N : ℕ)
    (h : ∀ bits, advance (F.block p) bits ⟨some (F.block p).start,s,out⟩ N=⟨none,t,out'⟩) :
    ∃ d≤N, ∀ bits, advance (Flow.compile F) bits (Flow.state F p s out) d=Flow.edge F p t out' := by
  let c : Config (F.block p) := ⟨some (F.block p).start,s,out⟩
  obtain ⟨d,hd,hh,hn,he⟩ := first_termination (F.block p) c (fun _ => false) N (by rw [h])
  refine ⟨d,hd,?_⟩
  intro bits
  have hn' : ∀ j<d, (advance (F.block p) bits c j).control≠none := by
    intro j hj
    rw [advance_coinFree _ hq]
    exact hn j hj
  change advance _ bits (Flow.embed F p c) d=_
  rw [Flow.advance_inner F p c bits d hn',advance_coinFree _ hq,he,h]
  rfl
end MeanPayoff.RegisterBits

end

section
namespace MeanPayoff.RandomTree
@[simp] theorem map_leaf' {α β : Type} (f : α→β) (a : α) : (leaf a).map f=leaf (f a) := rfl
@[simp] theorem map_coin' {α β : Type} (f : α→β) (l r : RandomTree α) :
    (coin l r).map f=coin (l.map f) (r.map f) := rfl
 theorem map_congr_all {α β : Type} (t : RandomTree α) (f g : α→β)
    (h : t.All (fun a => f a=g a)) : t.map f=t.map g := by
  induction t with
  | leaf a => exact congrArg leaf h
  | coin l r il ir => exact congrArg₂ coin (il h.1) (ir h.2)
 theorem expect_congr_all {α : Type} (t : RandomTree α) (f g : α→ℚ)
    (h : t.All (fun a => f a=g a)) : t.expect f=t.expect g := by
  apply le_antisymm
  · exact expect_mono_all t f g (all_mono t h (by intro a ha; exact ha.le))
  · exact expect_mono_all t g f (all_mono t h (by intro a ha; exact ha.ge))
end MeanPayoff.RandomTree
namespace MeanPayoff.FairBits
open RandomTree

def draw : ℕ→RandomTree (List Bool)
  | 0 => .leaf []
  | n+1 => .coin ((draw n).map (false::·)) ((draw n).map (true::·))
def acc : ℕ→List Bool→RandomTree (List Bool)
  | 0,bs => .leaf bs
  | n+1,bs => .coin (acc n (false::bs)) (acc n (true::bs))
 theorem length (n : ℕ) : (draw n).All (fun bs => bs.length=n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    constructor <;> rw [all_map] <;> exact all_mono _ ih (by intro bs hb; simp [hb])
 theorem acc_eq (n : ℕ) (bs : List Bool) : acc n bs=(draw n).map (fun xs => xs.reverse++bs) := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih => simp only [acc,draw,map_coin',map_map,ih,List.reverse_cons,List.append_assoc,List.singleton_append]
 theorem append (a b : ℕ) : draw (a+b)=(draw a).bind (fun xs => (draw b).map (xs++·)) := by
  induction a with
  | zero => simp [draw,RandomTree.map]
  | succ a ih =>
    rw [show a+1+b=(a+b)+1 by omega]
    simp only [draw,ih,RandomTree.map_bind,RandomTree.bind,RandomTree.bind_map,map_map,List.cons_append]
 theorem prepend_value (b : Bool) (bs : List Bool) : BinaryStack.Addition.value (b::bs).reverse=
    BinaryStack.Addition.value bs.reverse + if b then 2^bs.length else 0 := by
  rw [List.reverse_cons,BinaryStack.Addition.value_append,List.length_reverse]
  cases b <;> simp [BinaryStack.Addition.value]
 theorem number (n : ℕ) : (draw n).map (fun bs => BinaryStack.Addition.value bs.reverse)=uniformBelow n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [draw,map_coin',map_map,uniformBelow]
    apply congrArg₂ coin
    · simpa only [prepend_value,Bool.false_eq_true,↓reduceIte,Nat.add_zero] using ih
    · rw [←ih,map_map]
      apply map_congr_all
      exact all_mono _ (length n) (by
        intro bs hb
        rw [prepend_value,hb]; rfl)
end MeanPayoff.FairBits

end

end OAI
