import OAI.Computability.MeanPayoff.BatchDevices

namespace OAI

section

namespace MeanPayoff.TreeDevice.Graph
open BinaryData

def outList (G : Game) (v : Fin G.n) : List (Fin G.m) := (List.finRange G.m).filter (fun e => G.tail e = v)

@[simp] theorem mem_outList (G : Game) (v : Fin G.n) (e : Fin G.m) :
    e ∈ outList G v ↔ e ∈ outgoing G v := by
  simp [outList,outgoing]

theorem outList_ne_nil (G : Game) (v : Fin G.n) : outList G v ≠ [] := by
  obtain ⟨e,he⟩ := G.total v
  have hm : e ∈ outList G v := by simp [outList,he]
  intro h; simp [h] at hm

noncomputable def firstEdge (G : Game) (v : Fin G.n) : Fin G.m := (outList G v).head (outList_ne_nil G v)

noncomputable def codeVertex (G : Game) (w : Fin G.m → W) (v : Fin G.n) : Vertex :=
  (G.maxOwner v,(codeEdge G w (firstEdge G v),(outList G v).tail.map (codeEdge G w)))

noncomputable def codeVertices (G : Game) (w : Fin G.m → W) : List Vertex :=
  List.ofFn (codeVertex G w)

theorem codeVertex_exact (G : Game) (p : Fin G.n → W) (w : Fin G.m → W)
    (hw : ∀ e, (w e).val = transformed G e) (v : Fin G.n) :
    (vertex (codePot p,codeVertex G w v)).val = operator G (fun i => (p i).val) v := by
  apply vertex_exact G p w hw v _ _
  intro f
  rw [show firstEdge G v :: (outList G v).tail = outList G v from List.cons_head_tail (outList_ne_nil G v)]
  exact mem_outList G v f

theorem operator_list_exact (G : Game) (p : Fin G.n → W) (w : Fin G.m → W)
    (hw : ∀ e, (w e).val = transformed G e) :
    ((codeVertices G w).map (fun v => vertex (codePot p,v))).map SignedBits.Word.val =
      List.ofFn (operator G (fun i => (p i).val)) := by
  simp only [codeVertices,List.map_ofFn]
  apply congrArg List.ofFn
  funext v
  exact codeVertex_exact G p w hw v

end MeanPayoff.TreeDevice.Graph

namespace MeanPayoff.SignedBits
open BinaryStack.Addition (value)

 theorem value_complement (xs : List Bool) :
    (value (xs.map Bool.not) : ℤ) + value xs = 2^xs.length-1 := by
  induction xs with
  | nil => simp [value]
  | cons b bs ih =>
    cases b <;> simp only [List.map_cons,value,Bool.not_false,Bool.not_true,
      Bool.toNat_true,Bool.toNat_false,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
      Nat.cast_zero, List.length_cons,pow_succ] <;> omega

def Word.complement (w : Word) : Word := ⟨!w.sign,w.digits.map Bool.not⟩

theorem Word.complement_val (w : Word) : w.complement.val = -w.val-1 := by
  have h := value_complement w.digits
  cases w with
  | mk s ds => cases s <;> simp [Word.complement,Word.val] at * <;> omega

end MeanPayoff.SignedBits
namespace MeanPayoff.TreeDevice.Negate
open BinaryData

def one : SignedBits.Word := ⟨false,[true]⟩
@[simp] theorem one_val : one.val = 1 := by rfl

noncomputable def rawNot : Device boolData boolData Bool.not := by
  let test : Device boolData Compare.bitTree id :=
    (Lists.nilSuffix boolData boolData).recode boolData Compare.bitTree id id (by intro b; rfl)
      (by intro b; cases b <;> rfl)
  exact (branch test (constant boolData boolData false) (constant boolData boolData true)).extFun
    (by intro b; cases b <;> rfl)

noncomputable def complement : Device wordData wordData SignedBits.Word.complement :=
  (Map.device rawNot).recode wordData wordData (fun w => w.sign::w.digits)
    SignedBits.Word.complement (by intro w; exact Halve.listTree_boolData _)
    (by intro w; simpa only [wordData,SignedBits.Word.complement,List.map_cons] using Halve.listTree_boolData ((w.sign::w.digits).map Bool.not))

def negate (w : SignedBits.Word) : SignedBits.Word := Add.sumPair (w.complement,one)

noncomputable def device : Device wordData wordData negate :=
  compose (fanout complement (constant wordData wordData one)) Add.device

theorem exact (w : SignedBits.Word) : (negate w).val = -w.val := by
  simp [negate,Add.sumPair_val,SignedBits.Word.complement_val]

theorem rawNot_linear : LinearCost rawNot :=
  LinearCost.branch
    (LinearCost.recode (LinearCost.nilSuffix _ _) _ _ _ _ _ _)
    (LinearCost.constant _ _ _) (LinearCost.constant _ _ _)

theorem complement_polynomial : PolynomialCost complement := by
  obtain ⟨K,d,h⟩ := PolynomialCost.map rawNot_linear.polynomial
  refine ⟨K,d,?_⟩
  intro w
  simpa only [complement,Device.recode,Halve.listTree_boolData,wordData] using h (w.sign::w.digits)

theorem polynomial : PolynomialCost device :=
  PolynomialCost.compose (PolynomialCost.fanout complement_polynomial
    (LinearCost.constant _ _ _).polynomial) LinearCost.add.polynomial

end MeanPayoff.TreeDevice.Negate

namespace MeanPayoff.TreeDevice.Fold
open BinaryData

theorem time_of_prefix_bound {α β : Type} {ea : α → Data} {eb : β → Data}
    {f : α × β → α} (F : Device (product ea eb) ea f) (K d M S : ℕ)
    (hF : ∀ z, F.limit z ≤ K*(treeSize (product ea eb z)+1)^d)
    (a : α) (xs : List β) (hs : treeSize (listTree eb xs) ≤ S)
    (ha : ∀ k ≤ xs.length, treeSize (ea (fold f a (xs.take k))) ≤ M) :
    time F a xs ≤ (xs.length+1)*(12*M+K*(M+S+2)^d+11) := by
  induction xs generalizing a with
  | nil =>
    have hh := ha 0 (by simp)
    simp only [List.take_zero,fold,List.foldl_nil] at hh
    simp only [time,List.length_nil,Nat.zero_add,Nat.one_mul]
    omega
  | cons b bs ih =>
    have ha₀ := ha 0 (by omega)
    simp only [List.take_zero,fold,List.foldl_nil] at ha₀
    have hb : treeSize (eb b) ≤ S := by
      simp only [listTree,treeSize_pair] at hs
      omega
    have hbs : treeSize (listTree eb bs) ≤ S := by
      simp only [listTree,treeSize_pair] at hs
      omega
    have hnext : ∀ k ≤ bs.length, treeSize (ea (fold f (f (a,b)) (bs.take k))) ≤ M := by
      intro k hk
      have hh := ha (k+1) (by simpa using Nat.add_le_add_right hk 1)
      simpa only [List.take_succ_cons,fold,List.foldl_cons] using hh
    have hlim := (hF (a,b)).trans (Nat.mul_le_mul_left K (Nat.pow_le_pow_left
      (show treeSize (product ea eb (a,b))+1 ≤ M+S+2 by simp only [product,treeSize_pair]; omega) d))
    have hrec := ih (f (a,b)) hbs hnext
    simp only [time,List.length_cons]
    nlinarith

end MeanPayoff.TreeDevice.Fold

namespace MeanPayoff.BinaryStack.Addition

theorem value_append (xs ys : List Bool) : value (xs++ys) = value xs+2^xs.length*value ys := by
  induction xs with
  | nil => simp [value]
  | cons b bs ih => simp only [List.cons_append,value,ih,List.length_cons,pow_succ]; ring

theorem value_bits (n : ℕ) : value n.bits = n := by
  have h (xs : List Bool) : value xs = BinaryInput.bitsValue xs := by
    induction xs with
    | nil => rfl
    | cons b bs ih => cases b <;> simp [value,BinaryInput.bitsValue,Nat.bit,ih] ; omega
  rw [h,BinaryInput.bitsValue_bits]

end MeanPayoff.BinaryStack.Addition
namespace MeanPayoff.TreeDevice.Multiply
open BinaryData
abbrev W := SignedBits.Word
abbrev State := W × W

def stateData := product wordData wordData

def double (w : W) := SignedBits.cons false w
@[simp] theorem double_val (w : W) : (double w).val = 2*w.val := by simp [double,SignedBits.val_cons]
@[simp] theorem double_length (w : W) : (double w).digits.length = w.digits.length+1 := rfl

noncomputable def doubleDevice : Device wordData wordData double := by
  let F := compose (fanout (constant (listTree boolData) boolData false) (identity (listTree boolData)))
    (Lists.consDevice boolData)
  exact (pairMap (identity boolData) F).recode wordData wordData
    (fun w => (w.sign,w.digits)) double
    (by intro w; simp only [product,Halve.listTree_boolData,wordData,listData])
    (by intro w; simp only [product,Halve.listTree_boolData,wordData,listData,double,SignedBits.cons,Function.comp_def,id_eq])

noncomputable def rawTest : Device boolData Compare.bitTree id :=
  (Lists.nilSuffix boolData boolData).recode boolData Compare.bitTree id id
    (by intro b; rfl) (by intro b; cases b <;> rfl)

def step (z : State × Bool) : State :=
  (z.1.1,if z.2 then Add.sumPair (double z.1.2,z.1.1) else double z.1.2)

noncomputable def baseDevice : Device (product stateData boolData) wordData (fun z : State × Bool => z.1.1) :=
  compose (first stateData boolData) (first wordData wordData)

noncomputable def accDevice : Device (product stateData boolData) wordData (fun z : State × Bool => double z.1.2) :=
  compose (compose (first stateData boolData) (second wordData wordData)) doubleDevice

noncomputable def testDevice : Device (product stateData boolData) Compare.bitTree (fun z : State × Bool => z.2) :=
  (compose (second stateData boolData) rawTest).extFun (by intro z; rfl)

noncomputable def sumDevice : Device (product stateData boolData) wordData (fun z : State × Bool => Add.sumPair (double z.1.2,z.1.1)) :=
  compose (fanout accDevice baseDevice) Add.device

noncomputable def choiceDevice : Device (product stateData boolData) wordData
    (fun z : State × Bool => if z.2 then Add.sumPair (double z.1.2,z.1.1) else double z.1.2) :=
  branch testDevice sumDevice accDevice

noncomputable def stepDevice : Device (product stateData boolData) stateData step :=
  fanout baseDevice choiceDevice

def multiply (z : W × List Bool) : W := (Fold.fold step (z.1,Median.zeroWord) z.2.reverse).2

noncomputable def initDevice : Device (product wordData (listTree boolData))
    (product stateData (listTree boolData)) (fun z : W × List Bool => ((z.1,Median.zeroWord),z.2.reverse)) :=
  fanout (fanout (first wordData (listTree boolData)) (constant (product wordData (listTree boolData)) wordData Median.zeroWord))
    (compose (second wordData (listTree boolData)) (Lists.reverseDevice boolData))

noncomputable def device : Device (product wordData (listTree boolData)) wordData multiply := by
  let P := compose initDevice (compose (Fold.device stepDevice) (second wordData wordData))
  exact P.extFun (by intro z; rfl)

@[simp] theorem step_first (s : State) (b : Bool) : (step (s,b)).1 = s.1 := rfl

theorem step_val (s : State) (b : Bool) : (step (s,b)).2.val = 2*s.2.val + b.toNat*s.1.val := by
  cases b <;> simp [step,Add.sumPair_val]

theorem fold_first (s : State) (bs : List Bool) : (Fold.fold step s bs).1 = s.1 := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih => exact (ih (step (s,b))).trans rfl

theorem fold_val (s : State) (bs : List Bool) :
    (Fold.fold step s bs).2.val = 2^bs.length*s.2.val + (BinaryStack.Addition.value bs.reverse : ℤ)*s.1.val := by
  induction bs generalizing s with
  | nil => simp [Fold.fold,BinaryStack.Addition.value]
  | cons b bs ih =>
    change (Fold.fold step (step (s,b)) bs).2.val = _
    rw [ih,step_val,step_first,List.reverse_cons,BinaryStack.Addition.value_append]
    simp only [List.length_reverse,BinaryStack.Addition.value,Nat.cast_add,Nat.cast_mul,
      Nat.cast_pow,Nat.cast_ofNat,List.length_cons,pow_succ]
    ring

theorem exact (w : W) (bs : List Bool) : (multiply (w,bs)).val = w.val*BinaryStack.Addition.value bs := by
  rw [multiply,fold_val,List.reverse_reverse]
  simp [Median.zeroWord,SignedBits.Word.val,BinaryStack.Addition.value,mul_comm]

theorem nat_exact (w : W) (n : ℕ) : (multiply (w,n.bits)).val = w.val*n := by
  rw [exact,BinaryStack.Addition.value_bits]

theorem double_linear : LinearCost doubleDevice := by
  unfold doubleDevice
  apply LinearCost.recode
  exact LinearCost.pairMap (LinearCost.identity _)
    (LinearCost.compose (LinearCost.fanout (LinearCost.constant _ _ _) (LinearCost.identity _))
      (LinearCost.cons _))

theorem rawTest_linear : LinearCost rawTest := LinearCost.recode (LinearCost.nilSuffix _ _) _ _ _ _ _ _

theorem base_linear : LinearCost baseDevice :=
  LinearCost.compose (LinearCost.first stateData boolData) (LinearCost.first wordData wordData)

theorem acc_linear : LinearCost accDevice :=
  LinearCost.compose (LinearCost.compose (LinearCost.first stateData boolData)
    (LinearCost.second wordData wordData)) double_linear

theorem test_linear : LinearCost testDevice := LinearCost.compose (LinearCost.second _ _) rawTest_linear

theorem sum_linear : LinearCost sumDevice :=
  LinearCost.compose (LinearCost.fanout acc_linear base_linear) LinearCost.add

theorem choice_linear : LinearCost choiceDevice := LinearCost.branch test_linear sum_linear acc_linear

theorem step_linear : LinearCost stepDevice := LinearCost.fanout base_linear choice_linear

end MeanPayoff.TreeDevice.Multiply
end

end OAI
