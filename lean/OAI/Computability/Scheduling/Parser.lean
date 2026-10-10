import OAI.Computability.Scheduling.OutputCosts

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7

section

namespace ThreeMachine.StackCompiler.Binary

def value : List Bool → ℕ
  | [] => 0
  | b :: bs => 2*value bs + if b then 1 else 0

def increment : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: increment bs

def leading (bs : List Bool) : ℕ := (bs.takeWhile id).length

@[simp] theorem leading_nil : leading [] = 0 := rfl
@[simp] theorem leading_false (bs : List Bool) : leading (false :: bs) = 0 := rfl
@[simp] theorem leading_true (bs : List Bool) : leading (true :: bs) = leading bs+1 := by
  simp only [leading,List.takeWhile_cons,id_eq,ite_true,List.length_cons]

theorem increment_formula (bs : List Bool) :
    increment bs = List.replicate (leading bs) false ++ true :: bs.drop (leading bs+1) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | false => rfl
    | true => simp only [increment,leading_true,List.replicate_succ,List.cons_append,
        List.drop_succ_cons,ih]

theorem increment_encodePosNum (p : PosNum) :
    increment (Computability.encodePosNum p) = Computability.encodePosNum p.succ := by
  induction p with
  | one => rfl
  | bit0 p ih => rfl
  | bit1 p ih => simpa only [Computability.encodePosNum,PosNum.succ,increment] using congrArg (List.cons false) ih

theorem increment_encodeNum (p : Num) :
    increment (Computability.encodeNum p) = Computability.encodeNum p.succ := by
  cases p with
  | zero => rfl
  | pos p => exact increment_encodePosNum p

theorem increment_encodeNat (n : ℕ) :
    increment (Computability.encodeNat n) = Computability.encodeNat (n+1) := by
  unfold Computability.encodeNat
  rw [increment_encodeNum]
  congr 1
  apply Num.to_nat_inj.mp
  simp only [Num.succ_to_nat,Num.to_of_nat]

theorem iterate_increment (n : ℕ) : increment^[n] [] = Computability.encodeNat n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,increment_encodeNat]

theorem value_encodePosNum (p : PosNum) : value (Computability.encodePosNum p) = (p : ℕ) := by
  induction p with
  | one => rfl
  | bit0 p ih => simp only [Computability.encodePosNum,value,ih,PosNum.cast_bit0,Bool.false_eq_true,ite_false]; omega
  | bit1 p ih => simp only [Computability.encodePosNum,value,ih,PosNum.cast_bit1,ite_true]; omega

theorem value_encodeNat (n : ℕ) : value (Computability.encodeNat n) = n := by
  have h : ∀ p : Num, value (Computability.encodeNum p) = (p : ℕ) := by
    intro p; cases p with
    | zero => rfl
    | pos p => exact value_encodePosNum p
  simpa only [Computability.encodeNat,Num.to_of_nat] using h (n : Num)

def leadingStep (x : Bool × (Bool × ℕ)) : Bool × ℕ :=
  if x.2.1 && x.1 then (true,x.2.2+1) else (false,x.2.2)

theorem leading_fold (bs : List Bool) (b : Bool) (k : ℕ) :
    (bs.foldl (fun s a => leadingStep (a,s)) (b,k)).2 = k+if b then leading bs else 0 := by
  induction bs generalizing b k with
  | nil => simp
  | cons a bs ih =>
    rw [List.foldl_cons]
    cases a <;> cases b
    · change (bs.foldl (fun s a => leadingStep (a,s)) (false,k)).2 = k+0
      rw [ih]; rfl
    · change (bs.foldl (fun s a => leadingStep (a,s)) (false,k)).2 = k+0
      rw [ih]; rfl
    · change (bs.foldl (fun s a => leadingStep (a,s)) (false,k)).2 = k+0
      rw [ih]; rfl
    · change (bs.foldl (fun s a => leadingStep (a,s)) (true,k+1)).2 = k+leading (true :: bs)
      rw [ih,leading_true]; simp only [ite_true]; omega

def takeStep {α : Type u1} (x : List α × List α) : List α × List α :=
  (x.1.tail,match x.1 with | [] => x.2 | a :: _ => a :: x.2)

theorem takeStep_iterate {α : Type u2} (n : ℕ) (xs ys : List α) :
    takeStep^[n] (xs,ys) = (xs.drop n,(xs.take n).reverse ++ ys) := by
  induction n generalizing xs ys with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil => simp only [takeStep,ih,List.tail_nil,List.drop_nil,List.take_nil,List.reverse_nil,List.nil_append]
    | cons a xs =>
      simp only [takeStep,List.tail_cons,ih,List.drop_succ_cons,List.take_succ_cons,List.reverse_cons,List.append_assoc,List.singleton_append]

def valueStep (x : Bool × ℕ) : ℕ := 2*x.2+if x.1 then 1 else 0

theorem value_fold (bs : List Bool) :
    bs.reverse.foldl (fun k b => valueStep (b,k)) 0 = value bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.reverse_cons,List.foldl_append]
    change valueStep (b,bs.reverse.foldl (fun k b => valueStep (b,k)) 0) = _
    rw [ih]; rfl

def readNat (bs : List Bool) : ℕ × List Bool :=
  let k := leading bs
  let tail := bs.drop (k+1)
  (value (tail.take k),tail.drop k)

theorem leading_encodeNat (n : ℕ) (rest : List Bool) :
    leading (ThreeMachine.encodeNat n ++ rest) = (Computability.encodeNat n).length := by
  have h : ∀ k, leading (List.replicate k true ++ false :: (Computability.encodeNat n ++ rest)) = k := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => simp only [List.replicate_succ,List.cons_append,leading_true,ih]
  simpa only [ThreeMachine.encodeNat,List.append_assoc,List.cons_append] using h (Computability.encodeNat n).length

theorem readNat_encodeNat (n : ℕ) (rest : List Bool) :
    readNat (ThreeMachine.encodeNat n ++ rest) = (n,rest) := by
  unfold readNat
  rw [leading_encodeNat]
  simp only [ThreeMachine.encodeNat,List.append_assoc,List.cons_append]
  have hdrop : (List.replicate (Computability.encodeNat n).length true ++
      false :: (Computability.encodeNat n ++ rest)).drop ((Computability.encodeNat n).length+1) =
      Computability.encodeNat n ++ rest := by
    rw [← List.drop_drop, List.drop_left' (by simp)]
    rfl
  rw [hdrop,List.take_left,List.drop_left,value_encodeNat]

end ThreeMachine.StackCompiler.Binary

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u3} {α : I → Type u4} [∀ i, Coding (α i)]

def replicate : Uniform (fun i (x : ℕ × α i) => List.replicate x.1 x.2) :=
  ((Realizer.unroll.uniform I).onFst.comp snd.map).congr (fun _ x => by
    simp only [Function.comp_apply,List.map_replicate])

def binaryLeadingStep : Uniform (fun (_ : I) => Binary.leadingStep) :=
  ((((snd.comp fst).pair fst).comp (Realizer.and.uniform I)).ite
    ((constant true).pair ((snd.comp snd).comp (Realizer.succ.uniform I)))
    (false.pair (snd.comp snd))).congr (fun _ _ => rfl)

def binaryLeading : Uniform (fun (_ : I) => Binary.leading) :=
  ((((id.pair ((constant true).pair zero)).comp binaryLeadingStep.fold).comp snd)).congr
    (fun _ bs => by simpa only [Function.comp_apply,Nat.zero_add,ite_true] using Binary.leading_fold bs true 0)

def takeStep : Uniform (fun i => @Binary.takeStep (α i)) := by
  let A : Uniform (fun i (x : List (α i) × List (α i)) => x.1.head?.map (fun a => a :: x.2)) := ((fst.comp head?).pair snd).comp cons.optionMap
  exact ((fst.comp tail).pair ((A.pair snd).comp getD)).congr (fun _ x => by
    rcases x with ⟨xs,ys⟩; cases xs <;> rfl)

def take : Uniform (fun i (x : List (α i) × ℕ) => x.1.take x.2) :=
  ((((snd.pair (fst.pair nil)).comp takeStep.iterate).comp (snd.comp reverse))).congr
    (fun _ x => by simp only [Function.comp_apply,Binary.takeStep_iterate,List.append_nil,List.reverse_reverse])

def binaryValueStep : Uniform (fun (_ : I) => Binary.valueStep) :=
  (((((snd.pair snd).comp (Realizer.add.uniform I)).pair
    (fst.ite (constant 1) zero)).comp (Realizer.add.uniform I))).congr (fun _ x => by
      dsimp only [Function.comp_apply,Binary.valueStep]; omega)

def binaryValue : Uniform (fun (_ : I) => Binary.value) :=
  (((reverse.pair zero).comp binaryValueStep.fold)).congr (fun _ bs => Binary.value_fold bs)

def binaryReadNat : Uniform (fun (_ : I) => Binary.readNat) := by
  let K : Uniform (fun (_ : I) => Binary.leading) := binaryLeading
  let Tail : Uniform (fun (_ : I) (bs : List Bool) => bs.drop (Binary.leading bs+1)) :=
    (id.pair (K.comp (Realizer.succ.uniform I))).comp drop
  exact ((((Tail.pair K).comp take).comp binaryValue).pair ((Tail.pair K).comp drop)).congr
    (fun _ _ => rfl)

def binaryIncrement : Uniform (fun (_ : I) => Binary.increment) := by
  let A : Uniform (fun (_ : I) (bs : List Bool) => List.replicate (Binary.leading bs) Bool.false) :=
    (binaryLeading.pair false).comp replicate
  let Tail : Uniform (fun (_ : I) (bs : List Bool) => bs.drop (Binary.leading bs+1)) :=
    (id.pair (binaryLeading.comp (Realizer.succ.uniform I))).comp drop
  exact ((A.pair (((constant true).pair Tail).comp cons)).comp append).congr
    (fun _ bs => (Binary.increment_formula bs).symm)

def rawEncodeNat : Uniform (fun (_ : I) => Computability.encodeNat) :=
  (((id.pair nil).comp binaryIncrement.iterate)).congr (fun _ n => Binary.iterate_increment n)

def binaryEncodeNat : Uniform (fun (_ : I) => ThreeMachine.encodeNat) :=
  (((((rawEncodeNat.comp length).pair (constant true)).comp replicate).pair
    ((false.pair rawEncodeNat).comp cons)).comp append).congr (fun _ _ => rfl)

def binaryEncodeList : Uniform (fun (_ : I) (xs : List ℕ) => ThreeMachine.encodeList ThreeMachine.encodeNat xs) :=
  (((length.comp binaryEncodeNat).pair (binaryEncodeNat.mapList.comp flatten)).comp append).congr
    (fun _ _ => rfl)

def binaryEncodeAnswer : Uniform (fun (_ : I) => ThreeMachine.encodeAnswer) := by
  let A := (((id.pair nil).comp getD).comp binaryEncodeList :
    Uniform (fun (_ : I) (o : Option (List ℕ)) => ThreeMachine.encodeList ThreeMachine.encodeNat (o.getD [])))
  exact (optionIsSome.ite (((constant true).pair A).comp cons) (constant [Bool.false])).congr
    (fun _ o => by cases o <;> rfl)

end ThreeMachine.StackCompiler.Uniform

namespace ThreeMachine.StackCompiler.Binary
variable {α : Type u5}

def readStep (reader : List Bool → α × List Bool) (x : List Bool × List α) : List Bool × List α :=
  let a := reader x.1
  (a.2,a.1 :: x.2)

def readMany (reader : List Bool → α × List Bool) (k : ℕ) (bs : List Bool) : List α × List Bool :=
  let x := (readStep reader)^[k] (bs,[])
  (x.2.reverse,x.1)

theorem readStep_iterate {encode : α → List Bool} {reader : List Bool → α × List Bool}
    (hr : ∀ a rest, reader (encode a ++ rest) = (a,rest)) (xs : List α) (rest : List Bool) (acc : List α) :
    (readStep reader)^[xs.length] (xs.flatMap encode ++ rest,acc) = (rest,xs.reverse ++ acc) := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    simp only [List.flatMap_cons,List.append_assoc,readStep,hr]
    rw [ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

theorem readMany_correct {encode : α → List Bool} {reader : List Bool → α × List Bool}
    (hr : ∀ a rest, reader (encode a ++ rest) = (a,rest)) (xs : List α) (rest : List Bool) :
    readMany reader xs.length (xs.flatMap encode ++ rest) = (xs,rest) := by
  simp only [readMany,readStep_iterate hr,List.append_nil,List.reverse_reverse]

def readList (reader : List Bool → α × List Bool) (bs : List Bool) : List α × List Bool :=
  let a := readNat bs
  readMany reader a.1 a.2

theorem readList_correct {α : Type} {encode : α → List Bool} {reader : List Bool → α × List Bool}
    (hr : ∀ a rest, reader (encode a ++ rest) = (a,rest)) (xs : List α) (rest : List Bool) :
    readList reader (ThreeMachine.encodeList encode xs ++ rest) = (xs,rest) := by
  simp only [readList,ThreeMachine.encodeList,List.append_assoc,readNat_encodeNat]
  exact readMany_correct hr xs rest

def encodeEdge (e : ℕ × ℕ) : List Bool := ThreeMachine.encodeNat (e.1+1) ++ ThreeMachine.encodeNat (e.2+1)

def readEdge (bs : List Bool) : (ℕ × ℕ) × List Bool :=
  let a := readNat bs
  let b := readNat a.2
  ((a.1-1,b.1-1),b.2)

theorem readEdge_correct (e : ℕ × ℕ) (rest : List Bool) :
    readEdge (encodeEdge e ++ rest) = (e,rest) := by
  simp only [readEdge,encodeEdge,List.append_assoc,readNat_encodeNat,Nat.add_sub_cancel]

def readHeader (bs : List Bool) : Option ℕ × List Bool :=
  if bs.head?.getD false then
    let a := readNat bs.tail
    (some a.1,a.2)
  else (none,bs.tail)

def encodeHeader : Option ℕ → List Bool
  | none => [false]
  | some T => true :: ThreeMachine.encodeNat T

theorem readHeader_correct (d : Option ℕ) (rest : List Bool) :
    readHeader (encodeHeader d ++ rest) = (d,rest) := by
  cases d with
  | none => rfl
  | some T =>
    simp only [encodeHeader,List.cons_append,readHeader,List.head?_cons,Option.getD_some,
      ite_true,List.tail_cons,readNat_encodeNat]

def parse (bs : List Bool) : ℕ × (List (ℕ × ℕ) × Option ℕ) :=
  let a := readHeader bs
  let v := readList readNat a.2
  let e := readList readEdge v.2
  (v.1.length,(e.1,a.1))

theorem encodeEdges_map {n : ℕ} (G : Instance n) :
    ThreeMachine.encodeList
      (fun e : Fin n × Fin n => ThreeMachine.encodeNat (e.1.val+1) ++ ThreeMachine.encodeNat (e.2.val+1)) G.edges =
    ThreeMachine.encodeList encodeEdge (G.edges.map (fun e => (e.1.val,e.2.val))) := by
  simp only [ThreeMachine.encodeList,List.length_map,List.flatMap_map,encodeEdge]

theorem parse_input {n : ℕ} (G : Instance n) (d : Option ℕ) :
    parse (ThreeMachine.encodeInput G d) = (n,(G.edges.map (fun e => (e.1.val,e.2.val)),d)) := by
  have he : ThreeMachine.encodeInput G d = encodeHeader d ++
      (ThreeMachine.encodeList ThreeMachine.encodeNat ((List.range n).map (·+1)) ++
        ThreeMachine.encodeList encodeEdge (G.edges.map (fun e => (e.1.val,e.2.val)))) := by
    rw [ThreeMachine.encodeInput.eq_def,encodeEdges_map]
    cases d <;> simp only [encodeHeader,List.append_assoc]
  rw [he]
  simp only [parse,readHeader_correct,readList_correct readNat_encodeNat]
  rw [← List.append_nil (ThreeMachine.encodeList encodeEdge _),readList_correct readEdge_correct]
  simp only [List.length_map,List.length_range]

end ThreeMachine.StackCompiler.Binary

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u6} {α : I → Type u7} [∀ i, Coding (α i)]

def binaryReadStep {reader : ∀ i, List Bool → α i × List Bool} (R : Uniform reader) :
    Uniform (fun i => Binary.readStep (reader i)) :=
  ((fst.comp (R.comp snd)).pair (((fst.comp (R.comp fst)).pair snd).comp cons)).congr
    (fun _ _ => rfl)

def binaryReadMany {reader : ∀ i, List Bool → α i × List Bool} (R : Uniform reader) :
    Uniform (fun i (x : ℕ × List Bool) => Binary.readMany (reader i) x.1 x.2) :=
  (((fst.pair (snd.pair nil)).comp R.binaryReadStep.iterate).comp
      ((snd.comp reverse).pair fst)).congr (fun _ _ => rfl)

def binaryReadList {reader : ∀ i, List Bool → α i × List Bool} (R : Uniform reader) :
    Uniform (fun i => Binary.readList (reader i)) :=
  (binaryReadNat.comp R.binaryReadMany).congr (fun _ _ => rfl)

def binaryReadEdge : Uniform (fun (_ : I) => Binary.readEdge) := by
  let A := binaryReadNat (I := I)
  let B := A.comp (snd.comp binaryReadNat)
  exact (((A.comp (fst.comp (Realizer.pred.uniform I))).pair
      (B.comp (fst.comp (Realizer.pred.uniform I)))).pair (B.comp snd)).congr (fun _ _ => rfl)

def binaryReadHeader : Uniform (fun (_ : I) => Binary.readHeader) := by
  let P : Uniform (fun (_ : I) (bs : List Bool) => bs.head?.getD Bool.false) :=
    (head?.pair false).comp getD
  let A := tail.comp (binaryReadNat (I := I))
  exact (P.ite ((A.comp (fst.comp some)).pair (A.comp snd)) (none.pair tail)).congr (fun _ _ => rfl)

def binaryParse : Uniform (fun (_ : I) => Binary.parse) := by
  let A := binaryReadHeader (I := I)
  let V := A.comp (snd.comp binaryReadNat.binaryReadList)
  let E := V.comp (snd.comp binaryReadEdge.binaryReadList)
  exact ((V.comp (fst.comp length)).pair ((E.comp fst).pair (A.comp fst))).congr (fun _ _ => rfl)

end ThreeMachine.StackCompiler.Uniform

namespace ThreeMachine.StackCompiler

structure Request (n : ℕ) where
  graph : Instance n
  deadline : Option ℕ

instance (n : ℕ) : Coding (Request n) :=
  ⟨fun x => enc (ThreeMachine.encodeInput x.graph x.deadline)⟩

namespace Uniform

def parseRequest : Uniform (fun n (x : Request n) => ((Cardinal.mk () : Cardinal n),(x.graph,x.deadline))) where
  transform := (binaryParse (I := ℕ)).transform
  charge := (binaryParse (I := ℕ)).charge
  routine := (binaryParse (I := ℕ)).routine
  correct n x := by
    change (binaryParse (I := ℕ)).transform (enc (ThreeMachine.encodeInput x.graph x.deadline)) = _
    rw [(binaryParse (I := ℕ)).correct n,Binary.parse_input]
    change Data.pair (enc n) (Data.pair (enc (x.graph.edges.map (fun e => (e.1.val,e.2.val)))) (enc x.deadline)) =
      Data.pair (enc n) (Data.pair (enc x.graph.edges) (enc x.deadline))
    congr 2
    exact enc_list_map (fun e : Fin n × Fin n => (e.1.val,e.2.val)) (fun _ => rfl) x.graph.edges

def requestAnswer : Uniform (fun n (x : Request n) => Algorithm.output x.graph x.deadline) :=
  ((parseRequest.comp (makeUniverse.onFst.comp unaryAnswer)).comp binaryEncodeAnswer).congr
    (fun _ x => answerMatrix_closure x.graph x.deadline)

end Uniform
end ThreeMachine.StackCompiler
end

end OAI
