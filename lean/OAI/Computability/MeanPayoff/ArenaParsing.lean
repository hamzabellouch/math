import OAI.Computability.MeanPayoff.ParserCosts

namespace OAI

section
namespace MeanPayoff.TreeDevice.ArenaRead
open BinaryData
abbrev Count := Median.Count
abbrev Fields := List Bool × Header.Result
abbrev Arena := Count × (List Bool × List EdgeRead.Edge)
def restData := listTree boolData
def countData := listTree Median.unitData
def edgesData := listTree EdgeRead.edgeData
def fieldsData := product restData Header.resultData
def arenaData := product countData (product restData edgesData)

def edgeArgs (p : Fields) : EdgesRead.Args := (p.1,(p.2.2.2.2,p.2.2.1))
def finish (p : Fields) : Arena := (p.2.1,(p.2.2.2.1,(EdgesRead.read (edgeArgs p)).1))
def read (xs : List Bool) := finish (xs,Header.read xs)

noncomputable def headerDevice : Device fieldsData Header.resultData (fun p : Fields => p.2) := second restData Header.resultData
noncomputable def nDevice : Device fieldsData countData (fun p : Fields => p.2.1) :=
  compose headerDevice (first countData (product countData (product restData restData)))
noncomputable def moreDevice : Device fieldsData (product countData (product restData restData)) (fun p : Fields => p.2.2) :=
  compose headerDevice (second countData (product countData (product restData restData)))
noncomputable def mDevice : Device fieldsData countData (fun p : Fields => p.2.2.1) :=
  compose moreDevice (first countData (product restData restData))
noncomputable def lastDevice : Device fieldsData (product restData restData) (fun p : Fields => p.2.2.2) :=
  compose moreDevice (second countData (product restData restData))
noncomputable def ownersDevice : Device fieldsData restData (fun p : Fields => p.2.2.2.1) :=
  compose lastDevice (first restData restData)
noncomputable def remainderDevice : Device fieldsData restData (fun p : Fields => p.2.2.2.2) :=
  compose lastDevice (second restData restData)
noncomputable def argsDevice : Device fieldsData EdgesRead.argsData edgeArgs :=
  fanout (first restData Header.resultData) (fanout remainderDevice mDevice)
noncomputable def parseDevice : Device fieldsData EdgesRead.outputData (fun p : Fields => EdgesRead.read (edgeArgs p)) :=
  compose argsDevice EdgesRead.device
noncomputable def edgesDevice : Device fieldsData edgesData (fun p : Fields => (EdgesRead.read (edgeArgs p)).1) :=
  compose parseDevice (first edgesData restData)
noncomputable def finishDevice : Device fieldsData arenaData finish :=
  fanout nDevice (fanout ownersDevice edgesDevice)
noncomputable def device : Device restData arenaData read :=
  compose (fanout (identity restData) Header.device) finishDevice

theorem code_length (es : List BinaryInput.Edge) : es.length≤(EdgesRead.code es).length := by
  induction es with
  | nil => simp [EdgesRead.code]
  | cons e es ih =>
    have he : 1≤(BinaryInput.encodeEdge e).length := by
      simp only [BinaryInput.encodeEdge,List.length_append,encodeNat_length,encodeInt_length]
      omega
    simp only [EdgesRead.code,List.map_cons,List.flatten_cons,List.length_append,List.length_cons] at *
    omega

theorem raw_exact (n : ℕ) (owners : List Bool) (es : List BinaryInput.Edge) (ho : owners.length=n)
    (hd : ∀ e∈es, e.1≤(encodeNat n++encodeNat es.length++owners++EdgesRead.code es).length ∧
      e.2.1≤(encodeNat n++encodeNat es.length++owners++EdgesRead.code es).length) :
    read (encodeNat n++encodeNat es.length++owners++EdgesRead.code es) =
      (List.replicate n (),(owners,es.map EdgesRead.lower)) := by
  let xs := encodeNat n++encodeNat es.length++owners++EdgesRead.code es
  have hm : es.length≤xs.length := by
    have h := code_length es
    simp only [xs,List.length_append]
    omega
  have hh := Header.exact n es.length owners (EdgesRead.code es) ho hm
  have he := EdgesRead.exact es xs [] hd
  simp only [List.append_nil] at he
  change finish (xs,Header.read xs)=_
  rw [hh]
  change (List.replicate n (),(owners,(EdgesRead.read (xs,(EdgesRead.code es,List.replicate es.length ()))).1))=_
  rw [he]

theorem game_exact (G : Game) :
    read (input G) = (List.replicate G.n (),(List.ofFn G.maxOwner,(BinaryInput.lower G).edges.map EdgesRead.lower)) := by
  let es := (BinaryInput.lower G).edges
  have hel : es.length=G.m := by simp [es,BinaryInput.lower]
  have hi : encodeNat G.n++encodeNat es.length++List.ofFn G.maxOwner++EdgesRead.code es = input G := by
    simpa [es,BinaryInput.rawCode,BinaryInput.lower,EdgesRead.code] using BinaryInput.rawCode_lower G
  rw [← hi]
  apply raw_exact _ _ _ (by simp)
  intro e he
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
  rw [hi]
  exact ⟨(Nat.le_of_lt (G.tail i).isLt).trans (input_n_le G),(Nat.le_of_lt (G.head i).isLt).trans (input_n_le G)⟩

theorem header_linear : LinearCost headerDevice := LinearCost.second _ _
theorem n_linear : LinearCost nDevice := LinearCost.compose header_linear (LinearCost.first _ _)
theorem more_linear : LinearCost moreDevice := LinearCost.compose header_linear (LinearCost.second _ _)
theorem m_linear : LinearCost mDevice := LinearCost.compose more_linear (LinearCost.first _ _)
theorem last_linear : LinearCost lastDevice := LinearCost.compose more_linear (LinearCost.second _ _)
theorem owners_linear : LinearCost ownersDevice := LinearCost.compose last_linear (LinearCost.first _ _)
theorem remainder_linear : LinearCost remainderDevice := LinearCost.compose last_linear (LinearCost.second _ _)
theorem args_linear : LinearCost argsDevice := LinearCost.fanout (LinearCost.first _ _) (LinearCost.fanout remainder_linear m_linear)
theorem parse_polynomial : PolynomialCost parseDevice := PolynomialCost.compose args_linear.polynomial EdgesRead.polynomial
theorem edges_polynomial : PolynomialCost edgesDevice := PolynomialCost.compose parse_polynomial (LinearCost.first _ _).polynomial
theorem finish_polynomial : PolynomialCost finishDevice :=
  PolynomialCost.fanout n_linear.polynomial (PolynomialCost.fanout owners_linear.polynomial edges_polynomial)

theorem polynomial : PolynomialCost device :=
  PolynomialCost.compose (PolynomialCost.fanout (LinearCost.identity _).polynomial Header.polynomial) finish_polynomial
end MeanPayoff.TreeDevice.ArenaRead
namespace MeanPayoff.TreeDevice.Scale
open BinaryData
abbrev W := SignedBits.Word
abbrev Count := Median.Count
abbrev State := W × W

def stateData := product wordData wordData
def countData := listTree Median.unitData

def step (z : State × Unit) : State := (z.1.1,Add.sumPair (z.1.2,z.1.1))
noncomputable def baseDevice : Device (product stateData Median.unitData) wordData (fun z : State × Unit => z.1.1) :=
  compose (first stateData Median.unitData) (first wordData wordData)
noncomputable def accDevice : Device (product stateData Median.unitData) wordData (fun z : State × Unit => z.1.2) :=
  compose (first stateData Median.unitData) (second wordData wordData)
noncomputable def stepDevice : Device (product stateData Median.unitData) stateData step :=
  fanout baseDevice (compose (fanout accDevice baseDevice) Add.device)

def scale (z : W × Count) : W := (Fold.fold step (z.1,z.1) z.2).2
noncomputable def initDevice : Device (product wordData countData) (product stateData countData)
    (fun z : W × Count => ((z.1,z.1),z.2)) :=
  fanout (fanout (first wordData countData) (first wordData countData)) (second wordData countData)
noncomputable def device : Device (product wordData countData) wordData scale :=
  @compose (W × Count) State W (product wordData countData) stateData wordData
    (fun z => Fold.fold step (z.1,z.1) z.2) (fun s => s.2)
    (compose initDevice (Fold.device stepDevice)) (second wordData wordData)

@[simp] theorem step_first (s : State) (b : Unit) : (step (s,b)).1=s.1 := rfl
@[simp] theorem step_val (s : State) (b : Unit) : (step (s,b)).2.val=s.2.val+s.1.val := Add.sumPair_val _
theorem fold_first (s : State) (xs : Count) : (Fold.fold step s xs).1=s.1 := by
  induction xs generalizing s with
  | nil => rfl
  | cons b bs ih => exact (ih (step (s,b))).trans rfl

theorem fold_val (s : State) (xs : Count) : (Fold.fold step s xs).2.val=s.2.val+xs.length*s.1.val := by
  induction xs generalizing s with
  | nil => simp [Fold.fold]
  | cons b bs ih =>
    change (Fold.fold step (step (s,b)) bs).2.val=_
    rw [ih,step_val,step_first,List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

theorem exact (w : W) (xs : Count) : (scale (w,xs)).val=(xs.length+1 : ℤ)*w.val := by
  rw [scale,fold_val]
  ring

theorem step_length (s : State) (b : Unit) :
    (step (s,b)).2.digits.length = max s.2.digits.length s.1.digits.length+1 :=
  SignedBits.add_length _ _ _ _ _

theorem fold_length (s : State) (xs : Count) :
    (Fold.fold step s xs).2.digits.length≤ max s.2.digits.length s.1.digits.length+xs.length := by
  induction xs generalizing s with
  | nil => simp only [Fold.fold,List.foldl_nil,List.length_nil,Nat.add_zero]; omega
  | cons b bs ih =>
    have h := ih (step (s,b))
    rw [step_first,step_length] at h
    change (Fold.fold step (step (s,b)) bs).2.digits.length≤_
    simp only [List.length_cons]
    omega

theorem base_linear : LinearCost baseDevice := LinearCost.compose (LinearCost.first _ _) (LinearCost.first _ _)
theorem acc_linear : LinearCost accDevice := LinearCost.compose (LinearCost.first _ _) (LinearCost.second _ _)
theorem step_linear : LinearCost stepDevice :=
  LinearCost.fanout base_linear (LinearCost.compose (LinearCost.fanout acc_linear base_linear) LinearCost.add)

theorem fold_polynomial : PolynomialCost (Fold.device stepDevice) := by
  apply Fold.polynomial_of_prefix step_linear.polynomial 32 1
  intro s xs k hk
  let N := treeSize (product stateData countData (s,xs))+1
  have hN : 1≤N := by dsimp [N]; omega
  have he : treeSize (wordData s.1)+treeSize (wordData s.2)+treeSize (countData xs)+3=N := by
    simp only [N,stateData,product,treeSize_pair]; omega
  have hw := digits_le_wordSize s.1
  have ha := digits_le_wordSize s.2
  have hl := list_length_le_size Median.unitData xs
  have hp := fold_length s (xs.take k)
  have ht := List.length_take_le k xs
  have him : (Fold.fold step s (xs.take k)).2.digits.length≤2*N := by dsimp only [countData] at he; omega
  have hb := wordSize_bound (Fold.fold step s (xs.take k)).2
  rw [pow_one]
  change treeSize (stateData (Fold.fold step s (xs.take k)))≤32*N
  simp only [stateData,product,treeSize_pair,fold_first]
  omega

theorem init_linear : LinearCost initDevice :=
  LinearCost.fanout (LinearCost.fanout (LinearCost.first _ _) (LinearCost.first _ _)) (LinearCost.second _ _)
theorem polynomial : PolynomialCost device := by
  exact PolynomialCost.compose (PolynomialCost.compose init_linear.polynomial fold_polynomial) (LinearCost.second _ _).polynomial

def oneWord : W := ⟨false,[true]⟩

def transform (z : W × Count) : W := Add.sumPair (scale z,oneWord)
noncomputable def transformDevice : Device (product wordData countData) wordData transform :=
  compose (fanout device (constant (product wordData countData) wordData oneWord)) Add.device

theorem transform_val (w : W) (xs : Count) :
    (transform (w,xs)).val=(xs.length+1 : ℤ)*w.val+1 := by
  rw [transform,Add.sumPair_val,exact]
  simp [oneWord,SignedBits.Word.val,BinaryStack.Addition.value]

theorem transform_polynomial : PolynomialCost transformDevice :=
  PolynomialCost.compose (PolynomialCost.fanout polynomial (LinearCost.constant _ _ _).polynomial) LinearCost.add.polynomial
end MeanPayoff.TreeDevice.Scale
namespace MeanPayoff.TreeDevice.CountTest
open BinaryData
abbrev Count := Median.Count
def countData := listTree Median.unitData

def emptyStep (_ : Bool × Unit) : Bool := false
noncomputable def emptyStepDevice : Device (product Compare.bitTree Median.unitData) Compare.bitTree emptyStep :=
  constant _ _ false

theorem fold_false (xs : Count) : Fold.fold emptyStep false xs=false := by
  induction xs with
  | nil => rfl
  | cons b bs ih => exact ih

theorem fold_empty (xs : Count) : Fold.fold emptyStep true xs=xs.isEmpty := by
  cases xs with
  | nil => rfl
  | cons b bs => exact fold_false bs

noncomputable def emptyDevice : Device countData Compare.bitTree (fun xs : Count => xs.isEmpty) :=
  (compose (fanout (constant countData Compare.bitTree true) (identity countData))
    (Fold.device emptyStepDevice)).extFun fold_empty

theorem emptyStep_polynomial : PolynomialCost emptyStepDevice := (LinearCost.constant _ _ _).polynomial

theorem empty_polynomial : PolynomialCost emptyDevice := by
  apply PolynomialCost.compose
    (LinearCost.fanout (LinearCost.constant _ _ _) (LinearCost.identity _)).polynomial
  apply Fold.polynomial emptyStep_polynomial
  intro b u
  cases b <;> simp [emptyStep,Compare.bitTree,listData,boolData,treeSize,Median.unitData,encode]

def equal (z : Count × Count) : Bool :=
  if (z.1.drop z.2.length).isEmpty then (z.2.drop z.1.length).isEmpty else false
noncomputable def forwardDevice : Device (product countData countData) Compare.bitTree
    (fun z : Count × Count => (z.1.drop z.2.length).isEmpty) :=
  compose (Median.dropDevice Median.unitData) emptyDevice
noncomputable def backwardDevice : Device (product countData countData) Compare.bitTree
    (fun z : Count × Count => (z.2.drop z.1.length).isEmpty) :=
  compose (pairSwap countData countData) forwardDevice
noncomputable def device : Device (product countData countData) Compare.bitTree equal :=
  branch forwardDevice backwardDevice (constant _ _ false)

theorem equal_eq (z : Count × Count) : equal z=decide (z.1.length=z.2.length) := by
  unfold equal
  have hh (a b : Count) : (a.drop b.length).isEmpty = decide (a.length≤b.length) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.isEmpty_iff, List.drop_eq_nil_iff, decide_eq_true_eq]
  rw [hh,hh]
  split <;> rename_i h
  · apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq] at *
    omega
  · symm
    exact decide_eq_false (by simp only [decide_eq_true_eq] at h; omega)

theorem forward_polynomial : PolynomialCost forwardDevice :=
  PolynomialCost.compose (Median.drop_polynomial _) empty_polynomial
theorem backward_polynomial : PolynomialCost backwardDevice :=
  PolynomialCost.compose (LinearCost.pairSwap _ _).polynomial forward_polynomial
theorem polynomial : PolynomialCost device :=
  PolynomialCost.branch forward_polynomial backward_polynomial (LinearCost.constant _ _ _).polynomial
end MeanPayoff.TreeDevice.CountTest

namespace MeanPayoff.TreeDevice.EnvFilter
open BinaryData
variable {α β : Type} {ea : α → Data} {eb : β → Data} {p : α × β → Bool}

def stateData (ea : α → Data) (eb : β → Data) := product ea (listTree eb)
def step (p : α × β → Bool) (z : (α × List β) × β) : α × List β :=
  (z.1.1,if p (z.1.1,z.2) then z.2::z.1.2 else z.1.2)

noncomputable def envDevice : Device (product (stateData ea eb) eb) ea (fun z : (α × List β) × β => z.1.1) :=
  compose (first (stateData ea eb) eb) (first ea (listTree eb))
noncomputable def accDevice : Device (product (stateData ea eb) eb) (listTree eb) (fun z : (α × List β) × β => z.1.2) :=
  compose (first (stateData ea eb) eb) (second ea (listTree eb))
noncomputable def testDevice (P : Device (product ea eb) Compare.bitTree p) :
    Device (product (stateData ea eb) eb) Compare.bitTree (fun z : (α × List β) × β => p (z.1.1,z.2)) :=
  compose (fanout envDevice (second (stateData ea eb) eb)) P
noncomputable def consDevice : Device (product (stateData ea eb) eb) (listTree eb)
    (fun z : (α × List β) × β => z.2::z.1.2) :=
  compose (fanout (second (stateData ea eb) eb) accDevice) (Lists.consDevice eb)
noncomputable def stepDevice (P : Device (product ea eb) Compare.bitTree p) :
    Device (product (stateData ea eb) eb) (stateData ea eb) (step p) :=
  fanout envDevice (branch (testDevice P) consDevice accDevice)

noncomputable def initDevice : Device (product ea (listTree eb)) (product (stateData ea eb) (listTree eb))
    (fun z : α × List β => ((z.1,[]),z.2)) :=
  fanout (fanout (first ea (listTree eb)) (constant _ (listTree eb) [])) (second ea (listTree eb))
noncomputable def rawDevice (P : Device (product ea eb) Compare.bitTree p) :
    Device (product ea (listTree eb)) (listTree eb)
      (fun z : α × List β => (Fold.fold (step p) (z.1,[]) z.2).2) :=
  @compose (α × List β) (α × List β) (List β) (product ea (listTree eb)) (stateData ea eb) (listTree eb)
    (fun z => Fold.fold (step p) (z.1,[]) z.2) (fun z => z.2)
    (compose initDevice (Fold.device (stepDevice P))) (second ea (listTree eb))

theorem fold_exact (a : α) (acc xs : List β) :
    Fold.fold (step p) (a,acc) xs = (a,((xs.filter (fun b => p (a,b))).reverse++acc)) := by
  induction xs generalizing acc with
  | nil => simp [Fold.fold]
  | cons b bs ih =>
    change Fold.fold (step p) (step p ((a,acc),b)) bs=_
    simp only [step]
    split <;> rename_i h
    · rw [ih]
      simp [h,List.reverse_cons,List.append_assoc]
    · rw [ih]
      simp [h]

noncomputable def device (P : Device (product ea eb) Compare.bitTree p) :
    Device (product ea (listTree eb)) (listTree eb) (fun z : α × List β => z.2.filter (fun b => p (z.1,b))) :=
  (compose (rawDevice P) (Lists.reverseDevice eb)).extFun (by intro z; simp [fold_exact])

theorem env_linear : LinearCost (envDevice (ea:=ea) (eb:=eb)) := LinearCost.compose (LinearCost.first _ _) (LinearCost.first _ _)
theorem acc_linear : LinearCost (accDevice (ea:=ea) (eb:=eb)) := LinearCost.compose (LinearCost.first _ _) (LinearCost.second _ _)
theorem cons_linear : LinearCost (consDevice (ea:=ea) (eb:=eb)) :=
  LinearCost.compose (LinearCost.fanout (LinearCost.second _ _) acc_linear) (LinearCost.cons _)
theorem test_polynomial {P : Device (product ea eb) Compare.bitTree p} (hP : PolynomialCost P) : PolynomialCost (testDevice P) :=
  PolynomialCost.compose (LinearCost.fanout env_linear (LinearCost.second _ _)).polynomial hP

theorem step_polynomial {P : Device (product ea eb) Compare.bitTree p} (hP : PolynomialCost P) : PolynomialCost (stepDevice P) :=
  PolynomialCost.fanout env_linear.polynomial (PolynomialCost.branch (test_polynomial hP) cons_linear.polynomial acc_linear.polynomial)
theorem fold_polynomial {P : Device (product ea eb) Compare.bitTree p} (hP : PolynomialCost P) : PolynomialCost (Fold.device (stepDevice P)) := by
  apply Fold.polynomial (step_polynomial hP)
  intro a b
  simp only [step]
  split <;> simp only [stateData,product,listTree,treeSize_pair] <;> omega

theorem init_linear : LinearCost (initDevice (ea:=ea) (eb:=eb)) :=
  LinearCost.fanout (LinearCost.fanout (LinearCost.first _ _) (LinearCost.constant _ _ _)) (LinearCost.second _ _)
theorem raw_polynomial {P : Device (product ea eb) Compare.bitTree p} (hP : PolynomialCost P) : PolynomialCost (rawDevice P) := by
  exact PolynomialCost.compose (PolynomialCost.compose init_linear.polynomial (fold_polynomial hP)) (LinearCost.second _ _).polynomial
theorem polynomial {P : Device (product ea eb) Compare.bitTree p} (hP : PolynomialCost P) : PolynomialCost (device P) :=
  PolynomialCost.compose (raw_polynomial hP) (PolynomialCost.reverse _)
end MeanPayoff.TreeDevice.EnvFilter
end

end OAI
