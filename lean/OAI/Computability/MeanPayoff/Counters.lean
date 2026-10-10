import OAI.Computability.MeanPayoff.WordDecoding

namespace OAI

section
namespace MeanPayoff.TreeDevice.Address
open BinaryData
abbrev W := SignedBits.Word
abbrev Count := Median.Count
abbrev State := W × Count
def countData := listTree Median.unitData
def stateData := product wordData countData
def inputData := product stateData boolData

def dec (w : W) : W := Add.sumPair (w,IntegerRead.minusOne)
def test (w : W) : Bool := Compare.testPair (Median.zeroWord,w)
def step (z : State × Bool) : State :=
  if test z.1.1 then (dec z.1.1,()::z.1.2) else z.1

theorem dec_val (w : W) : (dec w).val = w.val-1 := by
  rw [dec,Add.sumPair_val]
  simp [IntegerRead.minusOne,SignedBits.Word.val,sub_eq_add_neg,BinaryStack.Addition.value]
theorem test_eq (w : W) : test w = decide (0<w.val) := by
  rw [test,Compare.testPair_eq]
  rfl

noncomputable def wordDevice : Device inputData wordData (fun z : State × Bool => z.1.1) :=
  compose (first stateData boolData) (first wordData countData)
noncomputable def listDevice : Device inputData countData (fun z : State × Bool => z.1.2) :=
  compose (first stateData boolData) (second wordData countData)
noncomputable def decDevice : Device wordData wordData dec :=
  compose (fanout (identity wordData) (constant wordData wordData IntegerRead.minusOne)) Add.device
noncomputable def testDevice : Device inputData Compare.bitTree (fun z : State × Bool => test z.1.1) :=
  compose (fanout (constant inputData wordData Median.zeroWord) wordDevice) Compare.device
noncomputable def newWordDevice : Device inputData wordData (fun z : State × Bool => dec z.1.1) :=
  @compose _ _ _ inputData wordData wordData (fun z : State × Bool => z.1.1) dec wordDevice decDevice
noncomputable def newCountDevice : Device inputData countData (fun z : State × Bool => ()::z.1.2) :=
  compose listDevice Median.incrementDevice
noncomputable def nextDevice : Device inputData stateData
    (fun z : State × Bool => (dec z.1.1,()::z.1.2)) :=
  fanout newWordDevice newCountDevice
noncomputable def stepDevice : Device inputData stateData step :=
  branch testDevice nextDevice (first stateData boolData)

def read (z : W × List Bool) : Count := (Fold.fold step (z.1,[]) z.2).2
noncomputable def initDevice : Device (product wordData (listTree boolData))
    (product stateData (listTree boolData)) (fun z : W × List Bool => ((z.1,[]),z.2)) :=
  pairMap (Lists.nilSuffix wordData Median.unitData) (identity (listTree boolData))
noncomputable def finishDevice : Device (product stateData (listTree boolData)) countData
    (fun z : State × List Bool => (Fold.fold step z.1 z.2).2) :=
  @compose _ _ _ (product stateData (listTree boolData)) stateData countData
    (fun z : State × List Bool => Fold.fold step z.1 z.2) (fun s : State => s.2)
    (Fold.device stepDevice) (second wordData countData)
noncomputable def device : Device (product wordData (listTree boolData)) countData read :=
  @compose _ _ _ (product wordData (listTree boolData)) (product stateData (listTree boolData)) countData
    (fun z : W × List Bool => ((z.1,[]),z.2))
    (fun z : State × List Bool => (Fold.fold step z.1 z.2).2) initDevice finishDevice

theorem fold_stopped (w : W) (hw : w.val ≤ 0) (c : Count) (xs : List Bool) :
    Fold.fold step (w,c) xs = (w,c) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change Fold.fold step (step ((w,c),x)) xs = _
    simpa only [step,test_eq,decide_eq_true_eq,not_lt_of_ge hw,↓reduceIte] using ih

theorem fold_count (n : ℕ) (w : W) (hw : w.val=n) (c : Count) (xs : List Bool)
    (hn : n ≤ xs.length) :
    (Fold.fold step (w,c) xs).2 = List.replicate n ()++c := by
  induction n generalizing w c xs with
  | zero => simp [fold_stopped w (by omega) c xs]
  | succ n ih =>
    cases xs with
    | nil => simp at hn
    | cons x xs =>
      have hp : test w = true := by simp [test_eq,hw]
      change (Fold.fold step (step ((w,c),x)) xs).2 = _
      simp only [step,hp,↓reduceIte]
      rw [ih (dec w) (by rw [dec_val,hw]; omega) (()::c) xs (by simpa using hn)]
      apply List.ext_getElem <;> simp [Nat.add_comm,Nat.add_left_comm]

theorem exact (n : ℕ) (w : W) (hw : w.val=n) (xs : List Bool) (hn : n≤xs.length) :
    read (w,xs) = List.replicate n () := by
  simp only [read,fold_count n w hw [] xs hn,List.append_nil]

theorem word_linear : LinearCost wordDevice := LinearCost.compose (LinearCost.first _ _) (LinearCost.first _ _)
theorem list_linear : LinearCost listDevice := LinearCost.compose (LinearCost.first _ _) (LinearCost.second _ _)
theorem dec_linear : LinearCost decDevice :=
  LinearCost.compose (LinearCost.fanout (LinearCost.identity _) (LinearCost.constant _ _ _)) LinearCost.add
theorem test_linear : LinearCost testDevice :=
  LinearCost.compose (LinearCost.fanout (LinearCost.constant _ _ _) word_linear) LinearCost.compare
theorem newWord_linear : LinearCost newWordDevice := LinearCost.compose word_linear dec_linear
theorem newCount_linear : LinearCost newCountDevice := LinearCost.compose list_linear Prefix.increment_linear
theorem next_linear : LinearCost nextDevice := LinearCost.fanout newWord_linear newCount_linear
theorem step_linear : LinearCost stepDevice :=
  LinearCost.branch test_linear next_linear (LinearCost.first _ _)

theorem step_word_length (s : State) (b : Bool) :
    (step (s,b)).1.digits.length ≤ s.1.digits.length+1 := by
  unfold step
  split
  · change (SignedBits.add s.1.sign true false s.1.digits []).digits.length ≤ _
    rw [SignedBits.add_length]
    simp
  · simp

theorem step_count_length (s : State) (b : Bool) :
    (step (s,b)).2.length ≤ s.2.length+1 := by
  unfold step
  split <;> simp

theorem fold_length (s : State) (xs : List Bool) :
    (Fold.fold step s xs).1.digits.length ≤ s.1.digits.length+xs.length ∧
    (Fold.fold step s xs).2.length ≤ s.2.length+xs.length := by
  induction xs generalizing s with
  | nil => simp [Fold.fold]
  | cons x xs ih =>
    have hh := ih (step (s,x))
    have hw := step_word_length s x
    have hc := step_count_length s x
    change (Fold.fold step (step (s,x)) xs).1.digits.length ≤ _ ∧
      (Fold.fold step (step (s,x)) xs).2.length ≤ _
    simp only [List.length_cons]
    omega

theorem count_size (c : Count) : treeSize (countData c)=2*c.length+1 := by
  induction c with
  | nil => rfl
  | cons u c ih => simp only [countData,listTree,treeSize_pair,Median.unitData,treeSize_nil,List.length_cons] at *; omega

theorem fold_polynomial : PolynomialCost (Fold.device stepDevice) := by
  obtain ⟨K,hK⟩ := step_linear
  refine ⟨402+40*K,2,?_⟩
  rintro ⟨s,xs⟩
  let N := treeSize (product stateData (listTree boolData) (s,xs))+1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hs₀ : treeSize (wordData s.1)+treeSize (countData s.2)+treeSize (listTree boolData xs)+3 = N := by
    simp only [N,product,stateData,treeSize_pair]; omega
  have hw : s.1.digits.length ≤ N := by have := digits_le_wordSize s.1; omega
  have ha : s.2.length ≤ N := by have := count_size s.2; omega
  have hl : xs.length+1 ≤ N := by have := list_length_le_size boolData xs; omega
  have he : treeSize (listTree boolData xs) ≤ N := by omega
  have hp : ∀ k ≤ xs.length, treeSize (stateData (Fold.fold step s (xs.take k))) ≤ 32*N := by
    intro k hk
    have hw' := wordSize_bound (Fold.fold step s (xs.take k)).1
    have ha' := count_size (Fold.fold step s (xs.take k)).2
    have hd := fold_length s (xs.take k)
    have hx : (xs.take k).length ≤ k := List.length_take_le _ _
    simp only [stateData,product,treeSize_pair]
    omega
  have ht := Fold.time_of_prefix_bound stepDevice K 1 (32*N) N
    (by intro z; simpa only [pow_one,inputData] using hK z) s xs he hp
  have hc : 12*(32*N)+K*(32*N+N+2)^1+11 ≤ (400+40*K)*N := by
    simp only [pow_one]
    nlinarith
  have hbig := Nat.mul_le_mul hl hc
  have htime := ht.trans hbig
  have hpos : 1 ≤ N^2 := one_le_pow₀ hN
  change Fold.time stepDevice s xs+2 ≤ (402+40*K)*N^2
  rw [pow_two] at hpos ⊢
  nlinarith

theorem init_polynomial : PolynomialCost initDevice :=
  (LinearCost.pairMap (LinearCost.nilSuffix _ _) (LinearCost.identity _)).polynomial
theorem finish_polynomial : PolynomialCost finishDevice :=
  PolynomialCost.compose fold_polynomial (LinearCost.second _ _).polynomial
theorem polynomial : PolynomialCost device :=
  PolynomialCost.compose init_polynomial finish_polynomial
end MeanPayoff.TreeDevice.Address
namespace MeanPayoff.TreeDevice.Header
open BinaryData
abbrev W := SignedBits.Word
abbrev Count := Median.Count
abbrev Numbers := W × (W × List Bool)
abbrev Fields := List Bool × Numbers
abbrev Result := Count × (Count × (List Bool × List Bool))
def restData := listTree boolData
def countData := listTree Median.unitData
def numbersData := product wordData (product wordData restData)
def fieldsData := product restData numbersData
def resultData := product countData (product countData (product restData restData))

def numbers (xs : List Bool) : Numbers :=
  let p := IntegerRead.readNat xs
  (p.1,IntegerRead.readNat p.2)
def nCount (p : Fields) := Address.read (p.2.1,p.1)
def mCount (p : Fields) := Address.read (p.2.2.1,p.1)
def partition (p : Fields) := Split.split (p.2.2.2,nCount p)
def finish (p : Fields) : Result := (nCount p,(mCount p,partition p))
def read (xs : List Bool) := finish (xs,numbers xs)

noncomputable def numbersDevice : Device restData numbersData numbers :=
  compose IntegerRead.natDevice (pairMap (identity wordData) IntegerRead.natDevice)
noncomputable def inputDevice : Device fieldsData restData (fun p : Fields => p.1) := first restData numbersData
noncomputable def nWordDevice : Device fieldsData wordData (fun p : Fields => p.2.1) :=
  compose (second restData numbersData) (first wordData (product wordData restData))
noncomputable def moreDevice : Device fieldsData (product wordData restData) (fun p : Fields => p.2.2) :=
  compose (second restData numbersData) (second wordData (product wordData restData))
noncomputable def mWordDevice : Device fieldsData wordData (fun p : Fields => p.2.2.1) :=
  compose moreDevice (first wordData restData)
noncomputable def remainderDevice : Device fieldsData restData (fun p : Fields => p.2.2.2) :=
  compose moreDevice (second wordData restData)
noncomputable def nCountDevice : Device fieldsData countData nCount :=
  compose (fanout nWordDevice inputDevice) Address.device
noncomputable def mCountDevice : Device fieldsData countData mCount :=
  compose (fanout mWordDevice inputDevice) Address.device
noncomputable def partitionDevice : Device fieldsData (product restData restData) partition :=
  compose (fanout remainderDevice nCountDevice) Split.device
noncomputable def finishDevice : Device fieldsData resultData finish :=
  fanout nCountDevice (fanout mCountDevice partitionDevice)
noncomputable def device : Device restData resultData read :=
  compose (fanout (identity restData) numbersDevice) finishDevice

theorem numbers_exact (n m : ℕ) (suffix : List Bool) :
    numbers (encodeNat n++encodeNat m++suffix) =
      (IntegerRead.decrement (n+1).bits,(IntegerRead.decrement (m+1).bits,suffix)) := by
  simp [numbers,List.append_assoc,IntegerRead.nat_encode]

theorem word_val (n : ℕ) : (IntegerRead.decrement (n+1).bits).val = n := by
  rw [IntegerRead.decrement_val,BinaryStack.Addition.value_bits]
  simp

theorem exact (n m : ℕ) (owners suffix : List Bool) (ho : owners.length=n)
    (hm : m ≤ (encodeNat n++encodeNat m++owners++suffix).length) :
    read (encodeNat n++encodeNat m++owners++suffix) =
      (List.replicate n (),(List.replicate m (),(owners,suffix))) := by
  let xs := encodeNat n++encodeNat m++owners++suffix
  have hn : n≤xs.length := by simp only [xs,List.length_append]; omega
  have hn' := Address.exact n (IntegerRead.decrement (n+1).bits) (word_val n) xs hn
  have hm' := Address.exact m (IntegerRead.decrement (m+1).bits) (word_val m) xs hm
  have hnum : numbers xs = (IntegerRead.decrement (n+1).bits,(IntegerRead.decrement (m+1).bits,owners++suffix)) := by
    simpa only [xs,List.append_assoc] using numbers_exact n m (owners++suffix)
  change finish (xs,numbers xs)=_
  rw [hnum]
  change (Address.read (IntegerRead.decrement (n+1).bits,xs),
    Address.read (IntegerRead.decrement (m+1).bits,xs),
    Split.split (owners++suffix,Address.read (IntegerRead.decrement (n+1).bits,xs))) = _
  rw [hn',hm',Split.exact _ _ (by simp; omega)]
  simp [← ho]

theorem input_linear : LinearCost inputDevice := LinearCost.first _ _
theorem nWord_linear : LinearCost nWordDevice := LinearCost.compose (LinearCost.second _ _) (LinearCost.first _ _)
theorem more_linear : LinearCost moreDevice := LinearCost.compose (LinearCost.second _ _) (LinearCost.second _ _)
theorem mWord_linear : LinearCost mWordDevice := LinearCost.compose more_linear (LinearCost.first _ _)
theorem remainder_linear : LinearCost remainderDevice := LinearCost.compose more_linear (LinearCost.second _ _)
theorem nCount_polynomial : PolynomialCost nCountDevice :=
  PolynomialCost.compose (LinearCost.fanout nWord_linear input_linear).polynomial Address.polynomial
theorem mCount_polynomial : PolynomialCost mCountDevice :=
  PolynomialCost.compose (LinearCost.fanout mWord_linear input_linear).polynomial Address.polynomial
theorem partition_polynomial : PolynomialCost partitionDevice :=
  PolynomialCost.compose (PolynomialCost.fanout remainder_linear.polynomial nCount_polynomial) Split.polynomial
theorem finish_polynomial : PolynomialCost finishDevice :=
  PolynomialCost.fanout nCount_polynomial (PolynomialCost.fanout mCount_polynomial partition_polynomial)
theorem numbers_polynomial : PolynomialCost numbersDevice :=
  PolynomialCost.compose IntegerRead.nat_polynomial
    (PolynomialCost.pairMap (LinearCost.identity _).polynomial IntegerRead.nat_polynomial)
theorem polynomial : PolynomialCost device :=
  PolynomialCost.compose (PolynomialCost.fanout (LinearCost.identity _).polynomial numbers_polynomial) finish_polynomial

end MeanPayoff.TreeDevice.Header
namespace MeanPayoff.TreeDevice.EdgeRead
open BinaryData
abbrev W := SignedBits.Word
abbrev Count := Median.Count
abbrev Edge := Count × (Count × W)
abbrev Words := W × (W × (W × List Bool))
abbrev Fields := List Bool × Words
def restData := listTree boolData
def countData := listTree Median.unitData
def edgeData := product countData (product countData wordData)
def wordsData := product wordData (product wordData (product wordData restData))
def fieldsData := product restData wordsData

def words (xs : List Bool) : Words :=
  let p := IntegerRead.readNat xs
  let q := IntegerRead.readNat p.2
  (p.1,(q.1,IntegerRead.readInt q.2))
def source (p : Fields) := Address.read (Address.dec p.2.1,p.1)
def target (p : Fields) := Address.read (Address.dec p.2.2.1,p.1)
def edge (p : Fields) : Edge := (source p,(target p,p.2.2.2.1))
def finish (p : Fields) : Edge × List Bool := (edge p,p.2.2.2.2)
def read (z : List Bool × List Bool) := finish (z.1,words z.2)

noncomputable def wordsDevice : Device restData wordsData words :=
  compose IntegerRead.natDevice
    (pairMap (identity wordData) (compose IntegerRead.natDevice (pairMap (identity wordData) IntegerRead.intDevice)))
noncomputable def inputDevice : Device fieldsData restData (fun p : Fields => p.1) := first restData wordsData
noncomputable def sourceWordDevice : Device fieldsData wordData (fun p : Fields => p.2.1) :=
  compose (second restData wordsData) (first wordData (product wordData (product wordData restData)))
noncomputable def moreDevice : Device fieldsData (product wordData (product wordData restData)) (fun p : Fields => p.2.2) :=
  compose (second restData wordsData) (second wordData (product wordData (product wordData restData)))
noncomputable def targetWordDevice : Device fieldsData wordData (fun p : Fields => p.2.2.1) :=
  compose moreDevice (first wordData (product wordData restData))
noncomputable def lastDevice : Device fieldsData (product wordData restData) (fun p : Fields => p.2.2.2) :=
  compose moreDevice (second wordData (product wordData restData))
noncomputable def weightDevice : Device fieldsData wordData (fun p : Fields => p.2.2.2.1) :=
  compose lastDevice (first wordData restData)
noncomputable def remainderDevice : Device fieldsData restData (fun p : Fields => p.2.2.2.2) :=
  compose lastDevice (second wordData restData)
noncomputable def sourceDecDevice : Device fieldsData wordData (fun p : Fields => Address.dec p.2.1) :=
  @compose _ _ _ fieldsData wordData wordData (fun p : Fields => p.2.1) Address.dec sourceWordDevice Address.decDevice
noncomputable def targetDecDevice : Device fieldsData wordData (fun p : Fields => Address.dec p.2.2.1) :=
  @compose _ _ _ fieldsData wordData wordData (fun p : Fields => p.2.2.1) Address.dec targetWordDevice Address.decDevice
noncomputable def sourceDevice : Device fieldsData countData source :=
  compose (fanout sourceDecDevice inputDevice) Address.device
noncomputable def targetDevice : Device fieldsData countData target :=
  compose (fanout targetDecDevice inputDevice) Address.device
noncomputable def edgeDevice : Device fieldsData edgeData edge :=
  fanout sourceDevice (fanout targetDevice weightDevice)
noncomputable def finishDevice : Device fieldsData (product edgeData restData) finish :=
  fanout edgeDevice remainderDevice
noncomputable def device : Device (product restData restData) (product edgeData restData) read :=
  compose (pairMap (identity restData) wordsDevice) finishDevice

def encodedWord (z : ℤ) : W :=
  let w := IntegerRead.decrement (z.natAbs+1).bits
  if z<0 then Negate.negate w else w

theorem encodedWord_val (z : ℤ) : (encodedWord z).val = z := by
  unfold encodedWord
  split
  · rename_i hz
    rw [Negate.exact,IntegerRead.decrement_val,BinaryStack.Addition.value_bits]
    simp [abs_of_neg hz]
  · rename_i hz
    rw [IntegerRead.decrement_val,BinaryStack.Addition.value_bits]
    simp [abs_of_nonneg (by omega : 0≤z)]

theorem words_exact (a b : ℕ) (w : ℤ) (suffix : List Bool) :
    words (BinaryInput.encodeEdge (a,b,w)++suffix) =
      (IntegerRead.decrement (a+2).bits,(IntegerRead.decrement (b+2).bits,(encodedWord w,suffix))) := by
  simp [words,BinaryInput.encodeEdge,List.append_assoc,IntegerRead.nat_encode,
    IntegerRead.readInt,encodeInt,IntegerRead.signed,encodedWord,Nat.add_assoc]

theorem exact (a b : ℕ) (w : ℤ) (bound suffix : List Bool) (ha : a≤bound.length) (hb : b≤bound.length) :
    read (bound,BinaryInput.encodeEdge (a,b,w)++suffix) =
      ((List.replicate a (),(List.replicate b (),encodedWord w)),suffix) := by
  have ha' : (Address.dec (IntegerRead.decrement (a+2).bits)).val=a := by
    rw [Address.dec_val,IntegerRead.decrement_val,BinaryStack.Addition.value_bits]; push_cast; omega
  have hb' : (Address.dec (IntegerRead.decrement (b+2).bits)).val=b := by
    rw [Address.dec_val,IntegerRead.decrement_val,BinaryStack.Addition.value_bits]; push_cast; omega
  simp only [read,words_exact,finish,edge,source,target]
  rw [Address.exact a _ ha' _ ha,Address.exact b _ hb' _ hb]

theorem words_polynomial : PolynomialCost wordsDevice :=
  PolynomialCost.compose IntegerRead.nat_polynomial
    (PolynomialCost.pairMap (LinearCost.identity _).polynomial
      (PolynomialCost.compose IntegerRead.nat_polynomial (PolynomialCost.pairMap (LinearCost.identity _).polynomial IntegerRead.int_polynomial)))
theorem input_linear : LinearCost inputDevice := LinearCost.first _ _
theorem sourceWord_linear : LinearCost sourceWordDevice := LinearCost.compose (LinearCost.second _ _) (LinearCost.first _ _)
theorem more_linear : LinearCost moreDevice := LinearCost.compose (LinearCost.second _ _) (LinearCost.second _ _)
theorem targetWord_linear : LinearCost targetWordDevice := LinearCost.compose more_linear (LinearCost.first _ _)
theorem last_linear : LinearCost lastDevice := LinearCost.compose more_linear (LinearCost.second _ _)
theorem weight_linear : LinearCost weightDevice := LinearCost.compose last_linear (LinearCost.first _ _)
theorem remainder_linear : LinearCost remainderDevice := LinearCost.compose last_linear (LinearCost.second _ _)
theorem sourceDec_linear : LinearCost sourceDecDevice := LinearCost.compose sourceWord_linear Address.dec_linear
theorem targetDec_linear : LinearCost targetDecDevice := LinearCost.compose targetWord_linear Address.dec_linear
theorem source_polynomial : PolynomialCost sourceDevice :=
  PolynomialCost.compose (LinearCost.fanout sourceDec_linear input_linear).polynomial Address.polynomial
theorem target_polynomial : PolynomialCost targetDevice :=
  PolynomialCost.compose (LinearCost.fanout targetDec_linear input_linear).polynomial Address.polynomial
theorem edge_polynomial : PolynomialCost edgeDevice :=
  PolynomialCost.fanout source_polynomial (PolynomialCost.fanout target_polynomial weight_linear.polynomial)
theorem finish_polynomial : PolynomialCost finishDevice :=
  PolynomialCost.fanout edge_polynomial remainder_linear.polynomial
theorem polynomial : PolynomialCost device :=
  PolynomialCost.compose (PolynomialCost.pairMap (LinearCost.identity _).polynomial words_polynomial) finish_polynomial
end MeanPayoff.TreeDevice.EdgeRead
end

end OAI
