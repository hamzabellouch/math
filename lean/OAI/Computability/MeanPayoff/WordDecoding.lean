import OAI.Computability.MeanPayoff.OperatorCosts

namespace OAI

section

namespace MeanPayoff.TreeDevice.Multiply
open BinaryData

theorem step_length (s : State) (b : Bool) :
    (step (s,b)).2.digits.length ≤ max s.2.digits.length s.1.digits.length+2 := by
  cases b with
  | false => simp only [step,Bool.false_eq_true,↓reduceIte,double_length]; omega
  | true =>
    change (SignedBits.add (double s.2).sign s.1.sign false (double s.2).digits s.1.digits).digits.length ≤ _
    rw [SignedBits.add_length,double_length]
    omega

theorem fold_length (s : State) (bs : List Bool) :
    (Fold.fold step s bs).2.digits.length ≤ max s.2.digits.length s.1.digits.length+2*bs.length := by
  induction bs generalizing s with
  | nil => simp only [Fold.fold,List.foldl_nil,List.length_nil,Nat.mul_zero,Nat.add_zero]; omega
  | cons b bs ih =>
    have hh := ih (step (s,b))
    have hs := step_length s b
    rw [step_first] at hh
    change (Fold.fold step (step (s,b)) bs).2.digits.length ≤ _
    simp only [List.length_cons]
    omega

theorem fold_polynomial : PolynomialCost (Fold.device stepDevice) := by
  obtain ⟨K,hK⟩ := step_linear
  refine ⟨402+40*K,2,?_⟩
  rintro ⟨s,xs⟩
  let N := treeSize (product stateData (listTree boolData) (s,xs))+1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hs₀ : treeSize (wordData s.1)+treeSize (wordData s.2)+treeSize (listTree boolData xs)+3 = N := by
    simp only [N,product,stateData,treeSize_pair]; omega
  have hw : s.1.digits.length ≤ N := by have := digits_le_wordSize s.1; omega
  have ha : s.2.digits.length ≤ N := by have := digits_le_wordSize s.2; omega
  have hl : xs.length+1 ≤ N := by have := list_length_le_size boolData xs; omega
  have he : treeSize (listTree boolData xs) ≤ N := by omega
  have hp : ∀ k ≤ xs.length, treeSize (stateData (Fold.fold step s (xs.take k))) ≤ 32*N := by
    intro k hk
    have hw' := wordSize_bound (Fold.fold step s (xs.take k)).1
    have ha' := wordSize_bound (Fold.fold step s (xs.take k)).2
    rw [fold_first] at hw'
    have hd := fold_length s (xs.take k)
    have hx : (xs.take k).length ≤ k := List.length_take_le _ _
    have hm : max s.2.digits.length s.1.digits.length ≤ N := max_le ha hw
    have hlen : (Fold.fold step s (xs.take k)).2.digits.length ≤ 3*N := by omega
    simp only [stateData,product,treeSize_pair,fold_first]
    omega
  have ht := Fold.time_of_prefix_bound stepDevice K 1 (32*N) N
    (by intro z; simpa only [pow_one] using hK z) s xs he hp
  have hc : 12*(32*N)+K*(32*N+N+2)^1+11 ≤ (400+40*K)*N := by
    simp only [pow_one]
    nlinarith
  have hbig := (Nat.mul_le_mul hl hc)
  have htime := ht.trans hbig
  have hpos : 1 ≤ N^2 := one_le_pow₀ hN
  change Fold.time stepDevice s xs+2 ≤ (402+40*K)*N^2
  rw [pow_two] at hpos ⊢
  nlinarith

theorem init_polynomial : PolynomialCost initDevice :=
  PolynomialCost.fanout
    (LinearCost.fanout (LinearCost.first _ _) (LinearCost.constant _ _ _)).polynomial
    (PolynomialCost.compose (LinearCost.second _ _).polynomial (PolynomialCost.reverse _))

theorem polynomial : PolynomialCost device :=
  PolynomialCost.compose init_polynomial
    (PolynomialCost.compose fold_polynomial (LinearCost.second _ _).polynomial)

end MeanPayoff.TreeDevice.Multiply

namespace MeanPayoff.TreeDevice.Prefix
open BinaryData
abbrev Count := Median.Count
abbrev State := Bool × (Count × List Bool)
def countData := listTree Median.unitData
def listsData := product countData (listTree boolData)
def stateData := product Compare.bitTree listsData
def inputData := product stateData boolData

def step (z : State × Bool) : State :=
  if z.1.1 then (true,(z.1.2.1,z.2::z.1.2.2))
  else if z.2 then (false,(()::z.1.2.1,z.1.2.2)) else (true,z.1.2)

noncomputable def countDevice : Device inputData countData (fun z : State × Bool => z.1.2.1) :=
  compose (compose (first stateData boolData) (second Compare.bitTree listsData)) (first countData (listTree boolData))
noncomputable def restDevice : Device inputData (listTree boolData) (fun z : State × Bool => z.1.2.2) :=
  compose (compose (first stateData boolData) (second Compare.bitTree listsData)) (second countData (listTree boolData))
noncomputable def bitDevice : Device inputData boolData (fun z : State × Bool => z.2) := second stateData boolData
noncomputable def doneDevice : Device inputData Compare.bitTree (fun z : State × Bool => z.1.1) :=
  compose (first stateData boolData) (first Compare.bitTree listsData)
noncomputable def testDevice : Device inputData Compare.bitTree (fun z : State × Bool => z.2) :=
  (compose bitDevice Multiply.rawTest).extFun (by intro z; rfl)
noncomputable def putDevice : Device inputData stateData (fun z : State × Bool => (true,(z.1.2.1,z.2::z.1.2.2))) :=
  fanout (constant inputData Compare.bitTree true)
    (fanout countDevice (compose (fanout bitDevice restDevice) (Lists.consDevice boolData)))
noncomputable def incDevice : Device inputData stateData (fun z : State × Bool => (false,(()::z.1.2.1,z.1.2.2))) :=
  fanout (constant inputData Compare.bitTree false)
    (fanout (compose countDevice Median.incrementDevice) restDevice)
noncomputable def stopDevice : Device inputData stateData (fun z : State × Bool => (true,z.1.2)) :=
  fanout (constant inputData Compare.bitTree true)
    (compose (first stateData boolData) (second Compare.bitTree listsData))
noncomputable def stepDevice : Device inputData stateData step :=
  branch doneDevice putDevice (branch testDevice incDevice stopDevice)

def read (xs : List Bool) : Count × List Bool :=
  let s := Fold.fold step (false,([],[])) xs
  (s.2.1,s.2.2.reverse)

noncomputable def initDevice : Device (listTree boolData) (product stateData (listTree boolData))
    (fun xs : List Bool => ((false,([],[])),xs)) :=
  fanout (constant (listTree boolData) stateData (false,([],[]))) (identity (listTree boolData))
noncomputable def finishDevice : Device stateData listsData
    (fun s : State => (s.2.1,s.2.2.reverse)) :=
  compose (second Compare.bitTree listsData) (pairMap (identity countData) (Lists.reverseDevice boolData))
noncomputable def device : Device (listTree boolData) listsData read :=
  compose initDevice (compose (Fold.device stepDevice) finishDevice)

theorem read_from_done (c : Count) (r xs : List Bool) :
    Fold.fold step (true,(c,r)) xs = (true,(c,xs.reverse++r)) := by
  induction xs generalizing r with
  | nil => simp [Fold.fold]
  | cons b bs ih =>
    change Fold.fold step (true,(c,b::r)) bs = _
    rw [ih]
    simp [List.reverse_cons,List.append_assoc]

theorem length_prefix (n : ℕ) (c : Count) (xs : List Bool) :
    Fold.fold step (false,(c,[])) (List.replicate n true++false::xs) =
      (true,(List.replicate n ()++c,xs.reverse)) := by
  induction n generalizing c with
  | zero =>
    change Fold.fold step (true,(c,[])) xs = _
    rw [read_from_done]
    simp
  | succ n ih =>
    simp only [List.replicate_succ,List.cons_append,Fold.fold,List.foldl_cons]
    change Fold.fold step (false,(()::c,[])) (List.replicate n true++false::xs) = _
    rw [ih]
    congr 2
    apply List.ext_getElem <;> simp [Nat.add_assoc]

theorem exact (n : ℕ) (xs : List Bool) :
    read (List.replicate n true++false::xs) = (List.replicate n (),xs) := by
  simp [read,length_prefix]

theorem count_linear : LinearCost countDevice :=
  LinearCost.compose (LinearCost.compose (LinearCost.first _ _) (LinearCost.second _ _)) (LinearCost.first _ _)
theorem rest_linear : LinearCost restDevice :=
  LinearCost.compose (LinearCost.compose (LinearCost.first _ _) (LinearCost.second _ _)) (LinearCost.second _ _)
theorem bit_linear : LinearCost bitDevice := LinearCost.second _ _
theorem done_linear : LinearCost doneDevice := LinearCost.compose (LinearCost.first _ _) (LinearCost.first _ _)
theorem test_linear : LinearCost testDevice := LinearCost.compose bit_linear Multiply.rawTest_linear
theorem increment_linear : LinearCost Median.incrementDevice :=
  LinearCost.compose (LinearCost.fanout (LinearCost.constant _ _ _) (LinearCost.identity _)) (LinearCost.cons _)
theorem put_linear : LinearCost putDevice :=
  LinearCost.fanout (LinearCost.constant _ _ _) (LinearCost.fanout count_linear
    (LinearCost.compose (LinearCost.fanout bit_linear rest_linear) (LinearCost.cons _)))
theorem inc_linear : LinearCost incDevice :=
  LinearCost.fanout (LinearCost.constant _ _ _) (LinearCost.fanout
    (LinearCost.compose count_linear increment_linear) rest_linear)
theorem stop_linear : LinearCost stopDevice :=
  LinearCost.fanout (LinearCost.constant _ _ _) (LinearCost.compose (LinearCost.first _ _) (LinearCost.second _ _))
theorem step_linear : LinearCost stepDevice :=
  LinearCost.branch done_linear put_linear (LinearCost.branch test_linear inc_linear stop_linear)

theorem step_size (s : State) (b : Bool) :
    treeSize (stateData (step (s,b))) ≤ treeSize (stateData s)+treeSize (boolData b)+1 := by
  rcases s with ⟨flag,c,r⟩
  cases flag <;> cases b <;> simp only [step,Bool.false_eq_true,↓reduceIte,
    stateData,listsData,countData,product,listTree,Compare.bitTree,listData,boolData,
    treeSize_pair,treeSize_nil,Median.unitData] <;> omega

theorem polynomial : PolynomialCost device :=
  PolynomialCost.compose (LinearCost.fanout (LinearCost.constant _ _ _) (LinearCost.identity _)).polynomial
    (PolynomialCost.compose (Fold.polynomial step_linear.polynomial step_size)
      (PolynomialCost.compose (LinearCost.second _ _).polynomial
        (PolynomialCost.pairMap (LinearCost.identity _).polynomial (PolynomialCost.reverse _))))
end MeanPayoff.TreeDevice.Prefix

namespace MeanPayoff.TreeDevice.Split
open BinaryData
abbrev State := List Bool × List Bool
def stateData := product (listTree boolData) (listTree boolData)
def inputData := product stateData Median.unitData

def step (z : State × Unit) : State := (z.1.2.headD false::z.1.1,z.1.2.tail)
noncomputable def fstDevice : Device inputData (listTree boolData) (fun z : State × Unit => z.1.1) :=
  compose (first stateData Median.unitData) (first (listTree boolData) (listTree boolData))
noncomputable def sndDevice : Device inputData (listTree boolData) (fun z : State × Unit => z.1.2) :=
  compose (first stateData Median.unitData) (second (listTree boolData) (listTree boolData))
noncomputable def headDevice : Device inputData boolData (fun z : State × Unit => z.1.2.headD false) :=
  compose sndDevice (Head.device boolData false)
noncomputable def pushDevice : Device inputData (listTree boolData) (fun z : State × Unit => z.1.2.headD false::z.1.1) :=
  compose (fanout headDevice fstDevice) (Lists.consDevice boolData)
noncomputable def stepDevice : Device inputData stateData step := fanout pushDevice (compose sndDevice (Tail.device boolData))

def split (z : List Bool × Median.Count) : List Bool × List Bool :=
  let s := Fold.fold step ([],z.1) z.2
  (s.1.reverse,s.2)
noncomputable def initDevice : Device (product (listTree boolData) Prefix.countData)
    (product stateData Prefix.countData) (fun z : List Bool × Median.Count => (([],z.1),z.2)) :=
  fanout (compose (first (listTree boolData) Prefix.countData) (Lists.nilPrefix (listTree boolData) boolData))
    (second (listTree boolData) Prefix.countData)
noncomputable def finishDevice : Device stateData stateData (fun s : State => (s.1.reverse,s.2)) :=
  pairMap (Lists.reverseDevice boolData) (identity (listTree boolData))
noncomputable def device : Device (product (listTree boolData) Prefix.countData) stateData split :=
  compose initDevice (compose (Fold.device stepDevice) finishDevice)

theorem fold_exact (xs acc : List Bool) (ks : Median.Count) (hk : ks.length ≤ xs.length) :
    Fold.fold step (acc,xs) ks = ((xs.take ks.length).reverse++acc,xs.drop ks.length) := by
  induction ks generalizing xs acc with
  | nil => simp [Fold.fold]
  | cons u ks ih =>
    cases xs with
    | nil => simp at hk
    | cons b bs =>
      change Fold.fold step (b::acc,bs) ks = _
      rw [ih bs (b::acc) (by simpa using hk)]
      simp [List.take_succ_cons,List.reverse_cons,List.append_assoc]

theorem exact (xs : List Bool) (ks : Median.Count) (hk : ks.length ≤ xs.length) :
    split (xs,ks) = (xs.take ks.length,xs.drop ks.length) := by
  simp [split,fold_exact xs [] ks hk]

theorem fst_linear : LinearCost fstDevice := LinearCost.compose (LinearCost.first _ _) (LinearCost.first _ _)
theorem snd_linear : LinearCost sndDevice := LinearCost.compose (LinearCost.first _ _) (LinearCost.second _ _)
theorem head_linear : LinearCost headDevice := LinearCost.compose snd_linear (LinearCost.head _ _)
theorem push_linear : LinearCost pushDevice :=
  LinearCost.compose (LinearCost.fanout head_linear fst_linear) (LinearCost.cons _)
theorem step_linear : LinearCost stepDevice :=
  LinearCost.fanout push_linear (LinearCost.compose snd_linear (LinearCost.tail _))

theorem step_size (s : State) (u : Unit) :
    treeSize (stateData (step (s,u))) ≤ treeSize (stateData s)+treeSize (Median.unitData u)+1 := by
  rcases s with ⟨acc,xs⟩
  cases xs with
  | nil => simp [step,stateData,product,listTree,boolData,treeSize_pair,Median.unitData]; omega
  | cons b bs => simp [step,stateData,product,listTree,treeSize_pair,Median.unitData]; omega

theorem polynomial : PolynomialCost device :=
  PolynomialCost.compose
    (LinearCost.fanout (LinearCost.compose (LinearCost.first _ _) (LinearCost.nilPrefix _ _)) (LinearCost.second _ _)).polynomial
    (PolynomialCost.compose (Fold.polynomial step_linear.polynomial step_size)
      (PolynomialCost.pairMap (PolynomialCost.reverse _) (LinearCost.identity _).polynomial))
end MeanPayoff.TreeDevice.Split

namespace MeanPayoff.TreeDevice.IntegerRead
open BinaryData
abbrev W := SignedBits.Word
def positive (xs : List Bool) : W := ⟨false,xs⟩
def minusOne : W := ⟨true,[]⟩
def decrement (xs : List Bool) : W := Add.sumPair (positive xs,minusOne)

noncomputable def positiveDevice : Device (listTree boolData) wordData positive :=
  (Lists.nilPrefix (listTree boolData) boolData).recode (listTree boolData) wordData id positive
    (by intro xs; rfl)
    (by intro xs; simp only [id_eq,product,listTree,positive,wordData,listData,boolData,Halve.listTree_boolData])
noncomputable def decrementDevice : Device (listTree boolData) wordData decrement :=
  compose (fanout positiveDevice (constant (listTree boolData) wordData minusOne)) Add.device

theorem decrement_val (xs : List Bool) : (decrement xs).val = (BinaryStack.Addition.value xs : ℤ)-1 := by
  rw [decrement,Add.sumPair_val]
  simp [positive,minusOne,SignedBits.Word.val,BinaryStack.Addition.value,sub_eq_add_neg]

def readNat (xs : List Bool) : W × List Bool :=
  let p := Prefix.read xs
  let q := Split.split (p.2,p.1)
  (decrement q.1,q.2)

noncomputable def natFieldsDevice : Device (listTree boolData) Split.stateData
    (fun xs : List Bool => let p := Prefix.read xs; Split.split (p.2,p.1)) :=
  compose Prefix.device (compose (pairSwap Prefix.countData (listTree boolData)) Split.device)
noncomputable def natDevice : Device (listTree boolData) (product wordData (listTree boolData)) readNat :=
  compose natFieldsDevice (pairMap decrementDevice (identity (listTree boolData)))

theorem nat_encode (n : ℕ) (suffix : List Bool) :
    readNat (encodeNat n++suffix) = (decrement (n+1).bits,suffix) := by
  unfold readNat
  rw [show encodeNat n++suffix = List.replicate (n+1).bits.length true++false::((n+1).bits++suffix) by simp [encodeNat,List.append_assoc]]
  rw [Prefix.exact]
  dsimp only
  rw [Split.exact _ _ (by simp)]
  simp

theorem nat_value (n : ℕ) (suffix : List Bool) :
    (readNat (encodeNat n++suffix)).1.val = n := by
  rw [nat_encode,decrement_val,BinaryStack.Addition.value_bits]
  simp

abbrev Parsed := Bool × (W × List Bool)
def parsedData := product boolData (product wordData (listTree boolData))

def signed (z : Parsed) : W × List Bool := (if z.1 then Negate.negate z.2.1 else z.2.1,z.2.2)
def readInt (xs : List Bool) : W × List Bool := signed (xs.headD false,readNat xs.tail)

noncomputable def signTest : Device parsedData Compare.bitTree (fun z : Parsed => z.1) :=
  (compose (first boolData (product wordData (listTree boolData))) Multiply.rawTest).extFun (by intro z; rfl)
noncomputable def magnitude : Device parsedData wordData (fun z : Parsed => z.2.1) :=
  compose (second boolData (product wordData (listTree boolData))) (first wordData (listTree boolData))
noncomputable def remainder : Device parsedData (listTree boolData) (fun z : Parsed => z.2.2) :=
  compose (second boolData (product wordData (listTree boolData))) (second wordData (listTree boolData))
noncomputable def negativeMagnitude : Device parsedData wordData (fun z : Parsed => Negate.negate z.2.1) :=
  @compose Parsed W W parsedData wordData wordData (fun z => z.2.1) Negate.negate magnitude Negate.device
noncomputable def chosenMagnitude : Device parsedData wordData
    (fun z : Parsed => if z.1 then Negate.negate z.2.1 else z.2.1) :=
  branch signTest negativeMagnitude magnitude
noncomputable def signedDevice : Device parsedData (product wordData (listTree boolData)) signed :=
  fanout chosenMagnitude remainder
noncomputable def intFieldsDevice : Device (listTree boolData) parsedData
    (fun xs : List Bool => (xs.headD false,readNat xs.tail)) :=
  fanout (Head.device boolData false) (compose (Tail.device boolData) natDevice)
noncomputable def intDevice : Device (listTree boolData) (product wordData (listTree boolData)) readInt :=
  compose intFieldsDevice signedDevice

theorem int_remainder (z : ℤ) (suffix : List Bool) : (readInt (encodeInt z++suffix)).2 = suffix := by
  simp [readInt,encodeInt,nat_encode,signed]

theorem int_value (z : ℤ) (suffix : List Bool) : (readInt (encodeInt z++suffix)).1.val = z := by
  unfold readInt
  simp only [encodeInt,List.cons_append,List.headD_cons,List.tail_cons,nat_encode,signed]
  by_cases hz : z<0
  · simp [hz,Negate.exact,decrement_val,BinaryStack.Addition.value_bits,abs_of_neg hz]
  · simp [hz,decrement_val,BinaryStack.Addition.value_bits,abs_of_nonneg (le_of_not_gt hz)]

theorem positive_linear : LinearCost positiveDevice := by
  unfold positiveDevice
  apply LinearCost.recode
  exact LinearCost.nilPrefix _ _
theorem decrement_linear : LinearCost decrementDevice :=
  LinearCost.compose (LinearCost.fanout positive_linear (LinearCost.constant _ _ _)) LinearCost.add

theorem natFields_polynomial : PolynomialCost natFieldsDevice :=
  PolynomialCost.compose Prefix.polynomial
    (PolynomialCost.compose (LinearCost.pairSwap _ _).polynomial Split.polynomial)

theorem nat_polynomial : PolynomialCost natDevice :=
  PolynomialCost.compose natFields_polynomial
    (PolynomialCost.pairMap decrement_linear.polynomial (LinearCost.identity _).polynomial)

theorem signTest_linear : LinearCost signTest := LinearCost.compose (LinearCost.first _ _) Multiply.rawTest_linear
theorem magnitude_linear : LinearCost magnitude := LinearCost.compose (LinearCost.second _ _) (LinearCost.first _ _)
theorem remainder_linear : LinearCost remainder := LinearCost.compose (LinearCost.second _ _) (LinearCost.second _ _)
theorem negative_polynomial : PolynomialCost negativeMagnitude :=
  PolynomialCost.compose magnitude_linear.polynomial Negate.polynomial
theorem chosen_polynomial : PolynomialCost chosenMagnitude :=
  PolynomialCost.branch signTest_linear.polynomial negative_polynomial magnitude_linear.polynomial
theorem signed_polynomial : PolynomialCost signedDevice :=
  PolynomialCost.fanout chosen_polynomial remainder_linear.polynomial

theorem int_polynomial : PolynomialCost intDevice :=
  PolynomialCost.compose
    (PolynomialCost.fanout (LinearCost.head _ _).polynomial
      (PolynomialCost.compose (LinearCost.tail _).polynomial nat_polynomial)) signed_polynomial

end MeanPayoff.TreeDevice.IntegerRead
end

end OAI
