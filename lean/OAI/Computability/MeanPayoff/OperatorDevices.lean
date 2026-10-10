import OAI.Computability.MeanPayoff.LoopDevices

namespace OAI

section
namespace MeanPayoff.TreeDevice.Select
open RegisterBits BinaryData

def choose {α : Type} (z : Bool × (α × α)) : α := if z.1 then z.2.1 else z.2.2

noncomputable abbrev flow {α : Type} (ea : α → Data) : Flow.Program 5 where
  nodes := 9
  start := 0
  block := ![skip,skip,skip,skip,skip,skip,skip,(first ea ea).program,(second ea ea).program]
  read _ := 0
  next p top _ := match p.val with
    | 0 => some ⟨1,.pop,none⟩
    | 1 => some ⟨2,.pop,none⟩
    | 2 => some ⟨if top=some true then 3 else 6,.pop,none⟩
    | 3 => some ⟨4,.pop,none⟩
    | 4 => some ⟨5,.pop,none⟩
    | 5 => some ⟨7,.pop,none⟩
    | 6 => some ⟨8,.pop,none⟩
    | _ => none

noncomputable abbrev program {α : Type} (ea : α → Data) := Flow.compile (flow ea)
noncomputable abbrev cfg {α : Type} (ea : α → Data) (q : Fin 9) (s out : List Bool) :=
  Flow.state (flow ea) q (core s [] []) out

private theorem popHop {α : Type} (ea : α → Data) (p q : Fin 9) (b : Bool) (xs out : List Bool)
    (hblock : (flow ea).block p = skip)
    (hnext : ∀ bit, (flow ea).next p (some b) bit = some ⟨q,.pop,none⟩) :
    Reaches (program ea) (cfg ea p (b::xs) out) (cfg ea q xs out) 2 := by
  intro bits
  apply Flow.hop_update (flow ea) p q (core (b::xs) [] []) (core (b::xs) [] [])
    (core xs [] []) out bits 1 .pop (by rw [hblock]; rfl) hnext
  change Function.update (core _ _ _) 0 (BinaryStack.applyOp .pop _) = _
  simp only [core_zero,core_update]; rfl

noncomputable def limit {α : Type} (ea : α → Data) (z : Bool × (α × α)) :=
  13 + max ((first ea ea).limit z.2) ((second ea ea).limit z.2)

theorem runs {α : Type} (ea : α → Data) (z : Bool × (α × α)) (suffix out : List Bool) :
    Reaches (program ea)
      ⟨some (program ea).start,store (product Compare.bitTree (product ea ea) z) suffix,out⟩
      ⟨none,store (ea (choose z)) suffix,out⟩ (limit ea z) := by
  rcases z with ⟨b,x,y⟩
  let tail := encode (product ea ea (x,y))++suffix
  have ht : Reaches (program ea) (cfg ea 7 tail out)
      ⟨none,store (ea x) suffix,out⟩ ((first ea ea).limit (x,y)+1) := by
    intro bits
    exact Flow.finish (flow ea) 7 _ _ out bits _ ((first ea ea).correct (x,y) suffix out bits)
      (by intros; rfl)
  have hf : Reaches (program ea) (cfg ea 8 tail out)
      ⟨none,store (ea y) suffix,out⟩ ((second ea ea).limit (x,y)+1) := by
    intro bits
    exact Flow.finish (flow ea) 8 _ _ out bits _ ((second ea ea).correct (x,y) suffix out bits)
      (by intros; rfl)
  cases b
  · have h₀ := popHop ea 0 1 true (true::false::false::tail) out rfl (by intros; rfl)
    have h₁ := popHop ea 1 2 true (false::false::tail) out rfl (by intros; rfl)
    have h₂ := popHop ea 2 6 false (false::tail) out rfl (by intros; rfl)
    have h₃ := popHop ea 6 8 false tail out rfl (by intros; rfl)
    exact (h₀.trans (h₁.trans (h₂.trans (h₃.trans hf)))).mono (by
      dsimp only [limit]; have := le_max_right ((first ea ea).limit (x,y)) ((second ea ea).limit (x,y)); omega)
  · have h₀ := popHop ea 0 1 true (true::true::false::false::false::tail) out rfl (by intros; rfl)
    have h₁ := popHop ea 1 2 true (true::false::false::false::tail) out rfl (by intros; rfl)
    have h₂ := popHop ea 2 3 true (false::false::false::tail) out rfl (by intros; rfl)
    have h₃ := popHop ea 3 4 false (false::false::tail) out rfl (by intros; rfl)
    have h₄ := popHop ea 4 5 false (false::tail) out rfl (by intros; rfl)
    have h₅ := popHop ea 5 7 false tail out rfl (by intros; rfl)
    exact (h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans ht)))))).mono (by
      dsimp only [limit]; have := le_max_left ((first ea ea).limit (x,y)) ((second ea ea).limit (x,y)); omega)

noncomputable def device {α : Type} (ea : α → Data) :
    Device (product Compare.bitTree (product ea ea)) ea choose :=
  ofProgram _ _ _ (program ea) (limit ea) (fun z suffix out bits => (runs ea z suffix out).pad rfl bits)

end MeanPayoff.TreeDevice.Select
namespace MeanPayoff.TreeDevice
open BinaryData

def Device.extFun {α β : Type} {ea : α → Data} {eb : β → Data} {f g : α → β}
    (F : Device ea eb f) (h : ∀ x, f x = g x) : Device ea eb g where
  program := F.program
  limit := F.limit
  quiet := F.quiet
  correct x suffix out bits := by rw [← h x]; exact F.correct x suffix out bits

namespace Order

def low (ab : SignedBits.Word × SignedBits.Word) : SignedBits.Word :=
  if Compare.testPair ab then ab.1 else ab.2

def high (ab : SignedBits.Word × SignedBits.Word) : SignedBits.Word :=
  if Compare.testPair ab then ab.2 else ab.1

noncomputable def minDevice : Device (product wordData wordData) wordData low :=
  compose (fanout Compare.device (identity (product wordData wordData))) (Select.device wordData)

noncomputable def swapDevice : Device (product wordData wordData) (product wordData wordData)
    (fun z => (z.2,z.1)) := fanout (second wordData wordData) (first wordData wordData)

noncomputable def maxDevice : Device (product wordData wordData) wordData high :=
  compose (fanout Compare.device swapDevice) (Select.device wordData)

theorem low_val (ab : SignedBits.Word × SignedBits.Word) : (low ab).val = min ab.1.val ab.2.val := by
  unfold low
  rw [Compare.testPair_eq]
  by_cases h : ab.1.val < ab.2.val
  · simp [h,min_eq_left (le_of_lt h)]
  · simp [h,min_eq_right (le_of_not_gt h)]

theorem high_val (ab : SignedBits.Word × SignedBits.Word) : (high ab).val = max ab.1.val ab.2.val := by
  unfold high
  rw [Compare.testPair_eq]
  by_cases h : ab.1.val < ab.2.val
  · simp [h,max_eq_right (le_of_lt h)]
  · simp [h,max_eq_left (le_of_not_gt h)]

def clipped (z : SignedBits.Word × (SignedBits.Word × SignedBits.Word)) : SignedBits.Word :=
  low (z.2.1,high (z.1,z.2.2))

noncomputable def clipDevice :
    Device (product wordData (product wordData wordData)) wordData clipped :=
  compose (fanout (compose (second wordData (product wordData wordData)) (first wordData wordData))
    (compose (fanout (first wordData (product wordData wordData))
      (compose (second wordData (product wordData wordData)) (second wordData wordData))) maxDevice)) minDevice

theorem clipped_val (z : SignedBits.Word × (SignedBits.Word × SignedBits.Word)) :
    (clipped z).val = min z.2.1.val (max z.1.val z.2.2.val) := by
  simp only [clipped,low_val,high_val]

noncomputable def clipVectorDevice :
    Device (listTree (product wordData (product wordData wordData))) (listTree wordData)
      (List.map clipped) := Map.device clipDevice

theorem clipping_exact {n : ℕ} (a b p : Fin n → SignedBits.Word) :
    (fun i => (clipped (a i,b i,p i)).val) = clip (fun i => (a i).val) (fun i => (b i).val)
      (fun i => (p i).val) := by
  funext i
  exact clipped_val _

end Order
end MeanPayoff.TreeDevice
namespace MeanPayoff.TreeDevice.Add
open RegisterBits BinaryData
open BinaryData.Take (advance_add)

def pairWord (ab : SignedBits.Word × SignedBits.Word) : Data := .pair (wordData ab.1) (wordData ab.2)
def sumPair (ab : SignedBits.Word × SignedBits.Word) : SignedBits.Word := ArithmeticForest.addWord ab.1 ab.2

noncomputable abbrev flow : Flow.Program 5 where
  nodes := 3
  start := 0
  block := ![skip, ArithmeticForest.program, moveCode 1 0]
  read _ := 0
  next p _ _ := match p.val with
    | 0 => some ⟨1,.pop,none⟩
    | 1 => some ⟨2,.keep,none⟩
    | _ => none

noncomputable abbrev program := Flow.compile flow

def limit (ab : SignedBits.Word × SignedBits.Word) :=
  30*(ab.1.digits.length+ab.2.digits.length+3)+6*treeSize (wordData (sumPair ab))+7

theorem runs (ab : SignedBits.Word × SignedBits.Word) (suffix out : List Bool) :
    Reaches program ⟨some program.start,store (pairWord ab) suffix,out⟩
      ⟨none,store (wordData (sumPair ab)) suffix,out⟩ (limit ab) := by
  let s₀ := store (pairWord ab) suffix
  let s₁ := ArithmeticForest.store0 ab.1 ab.2 suffix []
  let s₂ := ArithmeticForest.store4 ab.1 ab.2 suffix []
  have h₀ : Reaches program (Flow.state flow 0 s₀ out) (Flow.state flow 1 s₁ out) 2 := by
    intro bits
    exact Flow.hop_update flow 0 1 s₀ s₀ s₁ out bits 1 .pop rfl (by intros; rfl) (by
      change Function.update (core (encode (pairWord ab)++suffix) [] []) 0
        (BinaryStack.applyOp .pop (encode (pairWord ab)++suffix)) = _
      rw [core_update]
      simp only [pairWord,BinaryData.encode,List.cons_append,BinaryStack.applyOp,List.tail_cons]
      rfl)
  have h₁ : Reaches program (Flow.state flow 1 s₁ out) (Flow.state flow 2 s₂ out)
      (30*(ab.1.digits.length+ab.2.digits.length+3)+1) := by
    intro bits
    obtain ⟨t,ht,he⟩ := ArithmeticForest.program_adds ab.1 ab.2 suffix [] out bits
    obtain ⟨d,hd,hdone⟩ := Flow.hop flow 1 2 s₁ s₂ out bits t he (by intros; rfl)
    exact ⟨d,by omega,hdone⟩
  have h₂ : Reaches program (Flow.state flow 2 s₂ out)
      ⟨none,store (wordData (sumPair ab)) suffix,out⟩ (6*treeSize (wordData (sumPair ab))+4) := by
    intro bits
    have h := Flow.finish flow 2 _ _ out bits _
      (move10 (wordData (sumPair ab)) [] suffix [] out bits) (by intros; rfl)
    simpa only [s₂,ArithmeticForest.store4,wordData,sumPair,List.append_nil,Nat.add_assoc,core,store] using h
  exact (h₀.trans (h₁.trans h₂)).mono (by simp only [limit]; omega)

noncomputable def device : Device pairWord wordData sumPair :=
  ofProgram pairWord wordData sumPair program limit (fun ab suffix out bits => (runs ab suffix out).pad rfl bits)

theorem sumPair_val (ab : SignedBits.Word × SignedBits.Word) :
    (sumPair ab).val = ab.1.val + ab.2.val := by
  simpa only [sumPair,ArithmeticForest.addWord,Bool.toNat_false,Nat.cast_zero,add_zero] using
    SignedBits.add_val ab.1.sign ab.2.sign false ab.1.digits ab.2.digits

end MeanPayoff.TreeDevice.Add

namespace MeanPayoff.TreeDevice
open BinaryData

theorem compose_limit {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α → β} {g : β → γ} (F : Device ea eb f) (G : Device eb ec g) (x : α) :
    (compose F G).limit x = F.limit x+G.limit (f x)+2 := rfl

theorem dup_limit {α : Type} (ea : α → Data) (x : α) :
    (dup ea).limit x = 13*treeSize (ea x)+12 := by
  dsimp [dup,Forest.toDevice,ofProgram,Forest.Segment.seq,Forest.duplicate,Forest.copy01,
    Forest.move10,Forest.pair]
  omega

theorem pairMap_limit {α β γ δ : Type} {ea : α → Data} {eb : β → Data}
    {ec : γ → Data} {ed : δ → Data} {f : α → β} {g : γ → δ}
    (F : Device ea eb f) (G : Device ec ed g) (x : α) (y : γ) :
    (pairMap F G).limit (x,y) = F.limit x+G.limit y+24*treeSize (eb (f x))+
      12*treeSize (ec y)+12*treeSize (ed (g y))+50 := by
  dsimp [pairMap,Forest.toDevice,ofProgram,Forest.Segment.seq,Forest.unpair,Forest.swap,
    Forest.move01,Forest.move02,Forest.move10,Forest.move20,Forest.applyDevice,Forest.pair]
  omega

theorem fanout_limit {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α → β} {g : α → γ} (F : Device ea eb f) (G : Device ea ec g) (x : α) :
    (fanout F G).limit x = F.limit x+G.limit x+25*treeSize (ea x)+24*treeSize (eb (f x))+
      12*treeSize (ec (g x))+64 := by
  rw [fanout,compose_limit,dup_limit,pairMap_limit]
  omega

theorem first_limit {α β : Type} (ea : α → Data) (eb : β → Data) (x : α) (y : β) :
    (first ea eb).limit (x,y) = 12*treeSize (ea x)+19*treeSize (eb y)+30 := by
  dsimp [first,Forest.toDevice,ofProgram,Forest.Segment.seq,Forest.unpair,Forest.swap,
    Forest.move01,Forest.move02,Forest.move10,Forest.move20,Forest.drop]
  omega

theorem second_limit {α β : Type} (ea : α → Data) (eb : β → Data) (x : α) (y : β) :
    (second ea eb).limit (x,y) = 7*treeSize (ea x)+10 := by
  dsimp [second,Forest.toDevice,ofProgram,Forest.Segment.seq,Forest.unpair,Forest.drop,Forest.move01]
  omega

theorem Select.limit_le {α : Type} (ea : α → Data) (z : Bool × (α × α)) :
    Select.limit ea z ≤ 19*(treeSize (ea z.2.1)+treeSize (ea z.2.2))+43 := by
  rcases z with ⟨b,x,y⟩
  dsimp only [Select.limit]
  rw [first_limit,second_limit]
  omega

theorem wordSize_bound (w : SignedBits.Word) : treeSize (wordData w) ≤ 4*w.digits.length+5 := by
  have h := encode_list_length_le (w.sign::w.digits)
  simpa [treeSize,wordData,Nat.mul_add,Nat.add_assoc] using h

theorem digits_le_wordSize (w : SignedBits.Word) : w.digits.length ≤ treeSize (wordData w) := by
  have h (xs : List Bool) : xs.length ≤ treeSize (listData xs) := by
    induction xs with
    | nil => simp
    | cons b bs ih =>
      cases b <;> simp only [listData,treeSize_pair,boolData,List.length_cons] <;> omega
  have := h (w.sign::w.digits)
  simpa only [List.length_cons,wordData] using le_trans (Nat.le_succ w.digits.length) this

theorem bitSize_bound (b : Bool) : treeSize (Compare.bitTree b) ≤ 5 := by cases b <;> decide

end MeanPayoff.TreeDevice

namespace MeanPayoff.TreeDevice.EdgeScan
open BinaryData

abbrev Pair := SignedBits.Word × SignedBits.Word

def maxScan (z : Pair × List Pair) : SignedBits.Word :=
  Fold.fold Order.high (Add.sumPair z.1) (z.2.map Add.sumPair)

def minScan (z : Pair × List Pair) : SignedBits.Word :=
  Fold.fold Order.low (Add.sumPair z.1) (z.2.map Add.sumPair)

noncomputable def maxDevice :
    Device (product (product wordData wordData) (listTree (product wordData wordData))) wordData maxScan :=
  compose (pairMap Add.device (Map.device Add.device)) (Fold.device Order.maxDevice)

noncomputable def minDevice :
    Device (product (product wordData wordData) (listTree (product wordData wordData))) wordData minScan :=
  compose (pairMap Add.device (Map.device Add.device)) (Fold.device Order.minDevice)

theorem high_mem (z : SignedBits.Word × SignedBits.Word) : Order.high z = z.1 ∨ Order.high z = z.2 := by
  unfold Order.high
  split <;> simp

theorem low_mem (z : SignedBits.Word × SignedBits.Word) : Order.low z = z.1 ∨ Order.low z = z.2 := by
  unfold Order.low
  split <;> simp

theorem fold_mem (f : SignedBits.Word × SignedBits.Word → SignedBits.Word)
    (hf : ∀ z, f z=z.1 ∨ f z=z.2) (a : SignedBits.Word) (xs : List SignedBits.Word) :
    Fold.fold f a xs ∈ a::xs := by
  induction xs generalizing a with
  | nil => simp [Fold.fold]
  | cons b bs ih =>
    change Fold.fold f (f (a,b)) bs ∈ a::b::bs
    rcases List.mem_cons.mp (ih (f (a,b))) with h | h
    · rw [h]
      rcases hf (a,b) with h | h <;> simp [h]
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem high_bounds (a : SignedBits.Word) (xs : List SignedBits.Word) :
    ∀ w ∈ a::xs, w.val ≤ (Fold.fold Order.high a xs).val := by
  induction xs generalizing a with
  | nil => intro w hw; simpa [Fold.fold] using List.mem_singleton.mp hw ▸ le_refl a.val
  | cons b bs ih =>
    intro w hw
    change w.val ≤ (Fold.fold Order.high (Order.high (a,b)) bs).val
    have hh := ih (Order.high (a,b)) _ (List.mem_cons_self ..)
    rcases List.mem_cons.mp hw with rfl | hw
    · exact (show w.val ≤ (Order.high (w,b)).val by rw [Order.high_val]; exact le_max_left _ _).trans hh
    rcases List.mem_cons.mp hw with rfl | hw
    · exact (show w.val ≤ (Order.high (a,w)).val by rw [Order.high_val]; exact le_max_right _ _).trans hh
    · exact ih _ _ (List.mem_cons_of_mem _ hw)

theorem low_bounds (a : SignedBits.Word) (xs : List SignedBits.Word) :
    ∀ w ∈ a::xs, (Fold.fold Order.low a xs).val ≤ w.val := by
  induction xs generalizing a with
  | nil => intro w hw; simpa [Fold.fold] using List.mem_singleton.mp hw ▸ le_refl a.val
  | cons b bs ih =>
    intro w hw
    change (Fold.fold Order.low (Order.low (a,b)) bs).val ≤ w.val
    have hh := ih (Order.low (a,b)) _ (List.mem_cons_self ..)
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hh.trans (by rw [Order.low_val]; exact min_le_left _ _)
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hh.trans (by rw [Order.low_val]; exact min_le_right _ _)
    · exact ih _ _ (List.mem_cons_of_mem _ hw)

def Represents (G : Game) (p : Vec (Fin G.n)) (v : Fin G.n) (z : Pair × List Pair) : Prop :=
  (∀ ab ∈ z.1::z.2, ∃ e ∈ outgoing G v,
    ab.1.val+ab.2.val = transformed G e+p (G.head e)) ∧
  (∀ e ∈ outgoing G v, ∃ ab ∈ z.1::z.2,
    ab.1.val+ab.2.val = transformed G e+p (G.head e))

theorem maxScan_exact (G : Game) (p : Vec (Fin G.n)) (v : Fin G.n) (z : Pair × List Pair)
    (hz : Represents G p v z) :
    (maxScan z).val = (outgoing G v).sup' (outgoing_nonempty G v)
      (fun e => transformed G e+p (G.head e)) := by
  apply le_antisymm
  · have hm := fold_mem Order.high high_mem (Add.sumPair z.1) (z.2.map Add.sumPair)
    change maxScan z ∈ (z.1::z.2).map Add.sumPair at hm
    obtain ⟨ab,hab,he⟩ := List.mem_map.mp hm
    obtain ⟨e,he',hev⟩ := hz.1 ab hab
    rw [← he,Add.sumPair_val,hev]
    exact Finset.le_sup' (fun e => transformed G e+p (G.head e)) he'
  · apply (Finset.sup'_le_iff _ _).2
    intro e he
    obtain ⟨ab,hab,hval⟩ := hz.2 e he
    have hb := high_bounds (Add.sumPair z.1) (z.2.map Add.sumPair) (Add.sumPair ab)
      (show Add.sumPair ab ∈ (z.1::z.2).map Add.sumPair from List.mem_map.mpr ⟨ab,hab,rfl⟩)
    simpa only [Add.sumPair_val,hval,maxScan] using hb

theorem minScan_exact (G : Game) (p : Vec (Fin G.n)) (v : Fin G.n) (z : Pair × List Pair)
    (hz : Represents G p v z) :
    (minScan z).val = (outgoing G v).inf' (outgoing_nonempty G v)
      (fun e => transformed G e+p (G.head e)) := by
  apply le_antisymm
  · apply (Finset.le_inf'_iff _ _).2
    intro e he
    obtain ⟨ab,hab,hval⟩ := hz.2 e he
    have hb := low_bounds (Add.sumPair z.1) (z.2.map Add.sumPair) (Add.sumPair ab)
      (show Add.sumPair ab ∈ (z.1::z.2).map Add.sumPair from List.mem_map.mpr ⟨ab,hab,rfl⟩)
    simpa only [Add.sumPair_val,hval,minScan] using hb
  · have hm := fold_mem Order.low low_mem (Add.sumPair z.1) (z.2.map Add.sumPair)
    change minScan z ∈ (z.1::z.2).map Add.sumPair at hm
    obtain ⟨ab,hab,he⟩ := List.mem_map.mp hm
    obtain ⟨e,he',hev⟩ := hz.1 ab hab
    rw [← he,Add.sumPair_val,hev]
    exact Finset.inf'_le (fun e => transformed G e+p (G.head e)) he'

theorem operator_exact (G : Game) (p : Vec (Fin G.n)) (v : Fin G.n) (z : Pair × List Pair)
    (hz : Represents G p v z) :
    (if G.maxOwner v then (maxScan z).val else (minScan z).val) = operator G p v := by
  simp only [operator,maxScan_exact G p v z hz,minScan_exact G p v z hz]

end MeanPayoff.TreeDevice.EdgeScan
end

end OAI
