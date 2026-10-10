import OAI.Computability.MeanPayoff.TreeDevices

namespace OAI

section

namespace MeanPayoff.TreeDevice
open BinaryData RegisterBits

theorem treeSize_pos (x : Data) : 0 < treeSize x := by
  cases x <;> simp

@[simp] theorem listTree_reverse_size {α : Type} (e : α → Data) (xs : List α) :
    treeSize (listTree e xs.reverse) = treeSize (listTree e xs) := by
  simp only [listTree_size,List.length_reverse,List.map_reverse,List.sum_reverse]

namespace Map

def resource {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (xs : List α) := treeSize (listTree ea xs)+(xs.map F.limit).sum

@[simp] theorem resource_nil {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) : resource F [] = 1 := rfl

@[simp] theorem resource_cons {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (x : α) (xs : List α) :
    resource F (x::xs) = resource F xs+treeSize (ea x)+F.limit x+1 := by
  simp only [resource,listTree_cons,treeSize_pair,List.map_cons,List.sum_cons]; omega

theorem input_size_le {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (xs : List α) : treeSize (listTree ea xs) ≤ resource F xs := Nat.le_add_right _ _

theorem output_size_le {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (xs : List α) : treeSize (listTree eb (xs.map f)) ≤ resource F xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have h := TreeDevice.output_size F x
    simp only [List.map_cons,listTree_cons,treeSize_pair,resource_cons]
    omega

theorem reverse_cost {β : Type} (e : β → Data) (xs : List β) :
    revTime e xs ≤ 52*treeSize (listTree e xs)^2 := by
  induction xs with
  | nil => norm_num [revTime]
  | cons x xs ih =>
    simp only [revTime,listTree_cons,treeSize_pair]
    have h := treeSize_pos (e x)
    nlinarith

theorem forward_cost {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (xs : List α) : frontTime F xs ≤ 64*(resource F xs)^2 := by
  induction xs with
  | nil => norm_num [frontTime]
  | cons x xs ih =>
    have h := TreeDevice.output_size F x
    have hY := input_size_le F xs
    simp only [frontTime,resource_cons,listTree_cons,treeSize_pair]
    nlinarith

theorem limit_le {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (xs : List α) : limit F xs ≤ 128*(resource F xs+1)^2 := by
  have hi := input_size_le F xs
  have ho := output_size_le F xs
  have hf := forward_cost F xs
  have hr := reverse_cost eb (xs.map f).reverse
  simp only [listTree_reverse_size] at hr
  have hs : treeSize (listTree eb (xs.map f))^2 ≤ (resource F xs)^2 := Nat.pow_le_pow_left ho 2
  simp only [limit,listTree_reverse_size]
  nlinarith

end Map
end MeanPayoff.TreeDevice

namespace MeanPayoff.RegisterBits

def quieten {K : ℕ} (P : Program K) : Program K where
  states := P.states
  start := P.start
  read := P.read
  transition q top _ := P.transition q top false

def quietConfig {K : ℕ} (P : Program K) (c : Config P) : Config (quieten P) :=
  ⟨c.control,c.stack,c.output⟩

theorem quieten_coinFree {K : ℕ} (P : Program K) : CoinFree (quieten P) := by intro q top bit; rfl

theorem quieten_step {K : ℕ} (P : Program K) (c : Config P) (bit : Bool) :
    step (quieten P) (quietConfig P c) bit = quietConfig P (step P c false) := by
  cases c with
  | mk control s out =>
    cases control with
    | none => rfl
    | some q =>
      simp only [step,quietConfig,quieten]
      cases P.transition q (s (P.read q)).head? false <;> rfl

theorem quieten_advance {K : ℕ} (P : Program K) (c : Config P) (bits : ℕ → Bool) (N : ℕ) :
    advance (quieten P) bits (quietConfig P c) N =
      quietConfig P (advance P (fun _ => false) c N) := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [advance,ih,quieten_step]

end MeanPayoff.RegisterBits

namespace MeanPayoff.TreeDevice
open BinaryData RegisterBits

def ofProgram {α β : Type} (ea : α → Data) (eb : β → Data) (f : α → β)
    (P : Program 5) (N : α → ℕ)
    (h : ∀ x suffix out bits,
      advance P bits ⟨some P.start,store (ea x) suffix,out⟩ (N x) =
        ⟨none,store (eb (f x)) suffix,out⟩) : Device ea eb f where
  program := quieten P
  limit := N
  quiet := quieten_coinFree P
  correct x suffix out bits := by
    change advance (quieten P) bits (quietConfig P ⟨some P.start,store (ea x) suffix,out⟩) (N x) = _
    rw [quieten_advance,h]; rfl

end MeanPayoff.TreeDevice

namespace MeanPayoff.WorkStack.RegisterCompile

theorem signed_compares (a b : SignedBits.Word) (out : List Bool) (bits : ℕ → Bool) :
    RegisterBits.advance (program SignedCompare.program) bits
      (lift SignedCompare.program out (SignedCompare.state .start (a.sign::a.digits) (b.sign::b.digits) []))
      (6*(max a.digits.length b.digits.length+3)) =
        lift SignedCompare.program out
          (SignedCompare.stopped (SignedBits.compare a.sign b.sign false a.digits b.digits) []) := by
  rw [advance_six,SignedCompare.program_compares]
end MeanPayoff.WorkStack.RegisterCompile

namespace MeanPayoff.ComparisonForest
open RegisterBits BinaryData WorkStack
open ArithmeticForest (placeA placeB placeAdd placeBox injectA injectB injectAdd injectBox
  installA installB installAdd installBox store0 store1 store2 unboxTime boxTime)
open BinaryData.Take (advance_add)

def test (a b : SignedBits.Word) := SignedBits.compare a.sign b.sign false a.digits b.digits

theorem test_eq (a b : SignedBits.Word) : test a b = decide (a.val < b.val) := by
  apply Bool.eq_iff_iff.mpr
  simp only [test,decide_eq_true_eq,SignedBits.compare_lt]

noncomputable abbrev flow : Flow.Program 5 where
  nodes := 4
  start := 0
  block q := match q with
    | 0 => rename Unbox.program placeA
    | 1 => rename Unbox.program placeB
    | 2 => rename (RegisterCompile.program SignedCompare.program) placeAdd
    | 3 => rename Box.program placeBox
  read _ := 4
  next q _ _ := match q with
    | 0 => some ⟨1,.keep,none⟩
    | 1 => some ⟨2,.keep,none⟩
    | 2 => some ⟨3,.keep,none⟩
    | 3 => none

noncomputable def program := Flow.compile flow

def store3 (a b : SignedBits.Word) (xs ys : List Bool) : Fin 5 → List Bool :=
  ![xs,ys,[test a b],[],[]]
def store4 (a b : SignedBits.Word) (xs ys : List Bool) : Fin 5 → List Bool :=
  ![xs,encode (listData [test a b])++ys,[],[],[]]

theorem stage2 (a b : SignedBits.Word) (xs ys out : List Bool) (bits : ℕ → Bool) :
    advance (flow.block 2) bits ⟨some (flow.block 2).start,store2 a b xs ys,out⟩
      (6*(max a.digits.length b.digits.length+3)) = ⟨none,store3 a b xs ys,out⟩ := by
  have h := rename_advance (RegisterCompile.program SignedCompare.program) placeAdd injectAdd
    (store2 a b xs ys) (RegisterCompile.lift SignedCompare.program out
      (SignedCompare.state .start (a.sign::a.digits) (b.sign::b.digits) []))
    bits (6*(max a.digits.length b.digits.length+3))
  rw [RegisterCompile.signed_compares] at h
  simp only [renamed,RegisterCompile.lift,SignedCompare.state,SignedCompare.stopped,
    installAdd,store2,Matrix.cons_val_zero,Matrix.cons_val_one] at h
  convert h using 1 <;> rfl

theorem stage3 (a b : SignedBits.Word) (xs ys out : List Bool) (bits : ℕ → Bool) :
    advance (flow.block 3) bits ⟨some (flow.block 3).start,store3 a b xs ys,out⟩
      (boxTime [test a b]) = ⟨none,store4 a b xs ys,out⟩ := by
  have h := rename_advance Box.program placeBox injectBox (store3 a b xs ys)
    (Box.cfg .reverse [test a b] ys [] out) bits (boxTime [test a b])
  rw [show boxTime [test a b] = 2*[test a b].length+2+feedCost [test a b]+1 by rfl,
    Box.boxes] at h
  simp only [renamed,Box.cfg,Box.stopped,installBox,store3,Matrix.cons_val_zero,Matrix.cons_val_three] at h
  convert h using 1 <;> rfl

theorem total_bound (a b : SignedBits.Word) :
    (unboxTime (a.sign::a.digits)+1)+(unboxTime (b.sign::b.digits)+1)+
      (6*(max a.digits.length b.digits.length+3)+1)+(boxTime [test a b]+1) ≤
        30*(a.digits.length+b.digits.length+3) := by
  have ha := Unbox.unboxes_bound (a.sign::a.digits)
  have hb := Unbox.unboxes_bound (b.sign::b.digits)
  have hc := Box.boxes_bound [test a b]
  simp only [List.length_cons,List.length_nil] at ha hb hc
  unfold unboxTime boxTime
  simp only [List.length_cons,List.length_nil]
  omega

theorem program_compares (a b : SignedBits.Word) (xs ys out : List Bool) (bits : ℕ → Bool) :
    ∃ t ≤ 30*(a.digits.length+b.digits.length+3),
      advance program bits ⟨some program.start,store0 a b xs ys,out⟩ t =
        ⟨none,store4 a b xs ys,out⟩ := by
  obtain ⟨t₀,h₀,e₀⟩ := Flow.hop flow 0 1 (store0 a b xs ys) (store1 a b xs ys) out bits
    (unboxTime (a.sign::a.digits)) (ArithmeticForest.stage0 a b xs ys out bits) (by intros; rfl)
  obtain ⟨t₁,h₁,e₁⟩ := Flow.hop flow 1 2 (store1 a b xs ys) (store2 a b xs ys) out
    (fun j => bits (t₀+j)) (unboxTime (b.sign::b.digits))
    (ArithmeticForest.stage1 a b xs ys out _) (by intros; rfl)
  obtain ⟨t₂,h₂,e₂⟩ := Flow.hop flow 2 3 (store2 a b xs ys) (store3 a b xs ys) out
    (fun j => bits (t₀+t₁+j)) (6*(max a.digits.length b.digits.length+3)) (stage2 a b xs ys out _)
    (by intros; rfl)
  obtain ⟨t₃,h₃,e₃⟩ := Flow.finish flow 3 (store3 a b xs ys) (store4 a b xs ys) out
    (fun j => bits (t₀+t₁+t₂+j)) (boxTime [test a b]) (stage3 a b xs ys out _) (by intros; rfl)
  refine ⟨t₀+t₁+t₂+t₃,le_trans (by omega) (total_bound a b),?_⟩
  change advance (Flow.compile flow) bits (Flow.state flow 0 (store0 a b xs ys) out) _ = _
  rw [BinaryData.Take.advance_add _ _ _ (t₀+t₁+t₂) t₃,BinaryData.Take.advance_add _ _ _ (t₀+t₁) t₂,
    BinaryData.Take.advance_add _ _ _ t₀ t₁,e₀,e₁,e₂,e₃]
  rfl

end MeanPayoff.ComparisonForest

namespace MeanPayoff.TreeDevice.Compare
open RegisterBits BinaryData
open BinaryData.Take (advance_add)

def pairWord (ab : SignedBits.Word × SignedBits.Word) : Data := .pair (wordData ab.1) (wordData ab.2)
def bitTree (b : Bool) : Data := listData [b]
def testPair (ab : SignedBits.Word × SignedBits.Word) : Bool := ComparisonForest.test ab.1 ab.2

noncomputable abbrev flow : Flow.Program 5 where
  nodes := 3
  start := 0
  block := ![skip, ComparisonForest.program, moveCode 1 0]
  read _ := 0
  next p _ _ := match p.val with
    | 0 => some ⟨1,.pop,none⟩
    | 1 => some ⟨2,.keep,none⟩
    | _ => none

noncomputable abbrev program := Flow.compile flow

def limit (ab : SignedBits.Word × SignedBits.Word) :=
  30*(ab.1.digits.length+ab.2.digits.length+3)+6*treeSize (bitTree (testPair ab))+7

theorem runs (ab : SignedBits.Word × SignedBits.Word) (suffix out : List Bool) :
    Reaches program ⟨some program.start,store (pairWord ab) suffix,out⟩
      ⟨none,store (bitTree (testPair ab)) suffix,out⟩ (limit ab) := by
  let s₀ := store (pairWord ab) suffix
  let s₁ := ArithmeticForest.store0 ab.1 ab.2 suffix []
  let s₂ := ComparisonForest.store4 ab.1 ab.2 suffix []
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
    obtain ⟨t,ht,he⟩ := ComparisonForest.program_compares ab.1 ab.2 suffix [] out bits
    obtain ⟨d,hd,hdone⟩ := Flow.hop flow 1 2 s₁ s₂ out bits t he (by intros; rfl)
    exact ⟨d,by omega,hdone⟩
  have h₂ : Reaches program (Flow.state flow 2 s₂ out)
      ⟨none,store (bitTree (testPair ab)) suffix,out⟩ (6*treeSize (bitTree (testPair ab))+4) := by
    intro bits
    have h := Flow.finish flow 2 _ _ out bits _
      (move10 (bitTree (testPair ab)) [] suffix [] out bits) (by intros; rfl)
    simpa only [s₂,ComparisonForest.store4,bitTree,testPair,List.append_nil,Nat.add_assoc,core,store] using h
  exact (h₀.trans (h₁.trans h₂)).mono (by simp only [limit]; omega)

noncomputable def device : Device pairWord bitTree testPair :=
  ofProgram pairWord bitTree testPair program limit (fun ab suffix out bits => (runs ab suffix out).pad rfl bits)

theorem limit_le (ab : SignedBits.Word × SignedBits.Word) :
    limit ab ≤ 40*(ab.1.digits.length+ab.2.digits.length+4) := by
  have h := encode_list_length_le [testPair ab]
  simp only [List.length_cons,List.length_nil] at h
  unfold limit treeSize bitTree
  omega

theorem testPair_eq (ab : SignedBits.Word × SignedBits.Word) :
    testPair ab = decide (ab.1.val < ab.2.val) := ComparisonForest.test_eq ab.1 ab.2

noncomputable def vectorDevice :
    Device (listTree pairWord) (listTree bitTree) (List.map testPair) := Map.device device

theorem vector_exact (threshold : SignedBits.Word) (coords : List SignedBits.Word) :
    List.map testPair (coords.map (fun w => (threshold,w))) =
      coords.map (fun w => decide (threshold.val < w.val)) := by
  simp only [List.map_map]
  congr 1
  funext w
  exact testPair_eq (threshold,w)

end MeanPayoff.TreeDevice.Compare
end

end OAI
