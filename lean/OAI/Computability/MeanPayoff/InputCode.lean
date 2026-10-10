import OAI.Computability.MeanPayoff.DriverExecution

namespace OAI

namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace Size
 theorem count (xs : Count) : treeSize (encode xs)=2*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change treeSize (Data.pair .nil (encode xs))=_
    rw [treeSize_pair,treeSize_nil,ih,List.length_cons]
    omega
end Size
end MeanPayoff.TreeDevice.Certified

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
namespace Word
noncomputable def digitCount : Code W Count := by
  let F := Map.device (TreeDevice.constant boolData Median.unitData ())
  let D : Code Digits Count := by
    refine ⟨fun d => d.bits.map (fun _ => ()), F.recode encode encode Digits.bits
      (fun d => d.bits.map (fun _ => ())) (fun _ => rfl) (fun _ => rfl), ?_⟩
    obtain ⟨K,d,h⟩ := PolynomialCost.map (LinearCost.constant boolData Median.unitData ()).polynomial
    exact ⟨K,d,fun z => h z.bits⟩
  exact digits ≫ₚ D
@[simp] theorem digitCount_length (w : W) : (digitCount w).length=w.digits.length := by
  change (w.digits.map (fun _ => ())).length=w.digits.length
  simp only [List.length_map]

theorem half_size (w : W) : treeSize (encode (half w)) ≤ treeSize (encode w) := by
  change treeSize (wordData (Halve.halve w)) ≤ treeSize (wordData w)
  rcases w with ⟨s,ds⟩
  cases ds with
  | nil => exact le_rfl
  | cons b bs =>
    simp only [Halve.halve,wordData,listData,List.tail_cons,treeSize_pair]
    omega
end Word
namespace NaturalLog
abbrev State := W×Count
noncomputable def positive : Code State Bool := (Word.constant 0 ⋏ₚ fst) ≫ₚ Word.lt
noncomputable def step : Code (State×Unit) State :=
  Code.branch (fst ≫ₚ positive) (((fst ≫ₚ fst ≫ₚ Word.half) ⋏ₚ (fst ≫ₚ snd ≫ₚ Counter.inc))) fst
@[simp] theorem step_eval (s : State) (u : Unit) : step (s,u)=
    if 0<s.1.val then (Word.half s.1,()::s.2) else s := by
  simp [step,positive,Counter.inc]
noncomputable def loop : Code (State×Count) State := fold step (by
  rintro ⟨w,c⟩ u
  rw [step_eval]
  dsimp only
  split
  · rw [Size.pair,Size.pair,Size.count,Size.count,List.length_cons]
    have := Word.half_size w
    change _ ≤ _+1+1
    omega
  · omega)
noncomputable def length : Code W Count :=
  (((Code.id ⋏ₚ const []) ⋏ₚ Word.digitCount) ≫ₚ loop) ≫ₚ snd

noncomputable def ceil : Code W Count :=
  ((Code.id ⋏ₚ Word.constant 1) ≫ₚ Word.sub) ≫ₚ length

theorem recurrence (n : ℕ) (h : 0<n) : Nat.clog 2 (n+1)=Nat.clog 2 (n/2+1)+1 := by
  rw [Nat.clog_of_one_lt (by decide : 1<2) (by omega : 1<n+1)]
  congr 2
  omega

theorem fold_stopped (w : W) (hw : w.val ≤ 0) (c xs : Count) :
    Fold.fold step.eval (w,c) xs = (w,c) := by
  induction xs with
  | nil => rfl
  | cons u us ih =>
    change Fold.fold step.eval (step ((w,c),u)) us = _
    rw [step_eval]
    dsimp only
    rw [ite_eq_right (by omega)]
    exact ih

theorem fold_length (w : W) (hw : 0 ≤ w.val) (c xs : Count) (hf : w.digits.length ≤ xs.length) :
    (Fold.fold step.eval (w,c) xs).2.length = c.length+Nat.clog 2 (w.val.toNat+1) := by
  induction xs generalizing w c with
  | nil =>
    have hd : w.digits=[] := List.length_eq_zero_iff.mp (by simpa using hf)
    have hs : w.sign=false := Bool.eq_false_iff.mpr (fun h => (not_lt_of_ge hw) ((SignedBits.val_negative w).mpr h))
    have hz : w.val=0 := by simp [SignedBits.Word.val,hd,hs,BinaryStack.Addition.value]
    simp [Fold.fold,hz]
  | cons u us ih =>
    by_cases hp : 0<w.val
    · have hd : w.digits ≠ [] := by
        intro hd
        have hb : w.val ≤ 0 := by
          cases hs : w.sign <;> simp [SignedBits.Word.val,hd,hs,BinaryStack.Addition.value]
        omega
      have hw' : 0 ≤ (Word.half w).val := by rw [Word.half_val]; omega
      have hf' : (Word.half w).digits.length ≤ us.length := by
        rw [Word.half_length]
        have : 0<w.digits.length := by simpa only [List.length_pos_iff] using hd
        simp only [List.length_cons] at hf
        omega
      change (Fold.fold step.eval (step ((w,c),u)) us).2.length = _
      rw [step_eval,ite_eq_left hp,ih (Word.half w) hw' (()::c) hf',List.length_cons]
      have hn : 0<w.val.toNat := by omega
      have he : (Word.half w).val.toNat=w.val.toNat/2 := by rw [Word.half_val]; omega
      rw [he,recurrence _ hn]
      omega
    · have hz : w.val=0 := by omega
      rw [fold_stopped w (by omega)]
      simp [hz]

theorem length_exact (w : W) (hw : 0 ≤ w.val) : (length w).length=Nat.clog 2 (w.val.toNat+1) := by
  change (Fold.fold step.eval (w,[]) (Word.digitCount w)).2.length=_
  simpa only [List.length_nil,Nat.zero_add] using fold_length w hw [] (Word.digitCount w) (by rw [Word.digitCount_length])

theorem ceil_exact (w : W) (hw : 0 < w.val) : (ceil w).length=Nat.clog 2 w.val.toNat := by
  change (length (Word.sub (w,Word.constant 1 w))).length=_
  rw [length_exact _ (by simp; omega)]
  congr 1
  simp only [Word.sub_val,Word.constant_val]
  omega
end NaturalLog
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
namespace Word
noncomputable def powerStep : Code (W×Unit) W := fst ≫ₚ double
noncomputable def powerFold : Code (W×Count) W := fold powerStep (by
  intro w u
  change treeSize (wordData (Multiply.double w)) ≤ treeSize (wordData w)+1+1
  simp only [Multiply.double,SignedBits.cons,wordData,listData,treeSize_pair,boolData,treeSize_nil]
  omega)
noncomputable def power : Code Count W := (Word.constant 1 ⋏ₚ Code.id) ≫ₚ powerFold

theorem powerFold_val (w : W) (cs : Count) : (powerFold (w,cs)).val=2^cs.length*w.val := by
  change (Fold.fold powerStep.eval w cs).val=_
  induction cs generalizing w with
  | nil => simp [Fold.fold]
  | cons u us ih =>
    change (Fold.fold powerStep.eval (double w) us).val=_
    rw [ih,Word.double_val,List.length_cons,pow_succ]
    ring
@[simp] theorem power_val (cs : Count) : (power cs).val=2^cs.length := by
  change (powerFold (Word.constant 1 cs,cs)).val=_
  rw [powerFold_val,Word.constant_val,mul_one]
end Word
namespace Counter

theorem false_data (cs : Count) : listTree boolData (cs.map (fun _ => false))=encode cs := by
  induction cs with
  | nil => rfl
  | cons u us ih =>
    change Data.pair .nil (listTree boolData (us.map (fun _ => false))) = Data.pair .nil (encode us)
    rw [ih]

noncomputable def bounded : Code (W×Count) Count := by
  refine ⟨fun z => Address.read (z.1,z.2.map (fun _ => false)),
    Address.device.recode encode encode (fun z : W×Count => (z.1,z.2.map (fun _ => false)))
      (fun z => Address.read (z.1,z.2.map (fun _ => false))) ?_ (fun _ => rfl), ?_⟩
  · intro z
    change Data.pair (encode z.1) (listTree boolData (z.2.map (fun _ => false)))=Data.pair (encode z.1) (encode z.2)
    rw [false_data]
  · obtain ⟨K,d,h⟩ := Address.polynomial
    refine ⟨K,d,fun z => ?_⟩
    have hh := h (z.1,z.2.map (fun _ => false))
    change Address.device.limit (z.1,z.2.map (fun _ => false)) ≤ K*(treeSize (product wordData (listTree Median.unitData) z)+1)^d
    change Address.device.limit (z.1,z.2.map (fun _ => false)) ≤ K*(treeSize (Data.pair (wordData z.1) (listTree boolData (z.2.map (fun _ => false))))+1)^d at hh
    rw [false_data] at hh
    exact hh
 theorem bounded_exact (w : W) (n : ℕ) (hw : w.val=n) (cap : Count) (hc : n≤cap.length) :
    bounded (w,cap)=List.replicate n () :=
  Address.exact n w hw _ (by simpa only [List.length_map] using hc)
noncomputable def power : Code (Count×Count) Count := ((fst ≫ₚ Word.power) ⋏ₚ snd) ≫ₚ bounded
 theorem power_exact (e cap : Count) (hc : 2^e.length ≤ cap.length) :
    power (e,cap)=List.replicate (2^e.length) () := by
  exact bounded_exact (Word.power e) _ (by simp) cap hc

theorem pow_clog_le (n : ℕ) (hn : 0<n) : 2^Nat.clog 2 n ≤ 2*n := by
  by_cases h : n≤1
  · have he : n=1 := by omega
    subst n
    norm_num
  · have hl : 0<Nat.clog 2 n := Nat.clog_pos (by decide) (by omega)
    have hh := Nat.pow_pred_clog_lt_self (by decide : 1<2) (show 1<n by omega)
    have he : Nat.clog 2 n=(Nat.clog 2 n).pred+1 := (Nat.succ_pred_eq_of_pos hl).symm
    rw [he,pow_succ]
    omega
end Counter
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair

structure Parsed where
  raw : Normalize.Arena
instance : Encoding Parsed := ⟨fun p => Normalize.arenaData p.raw⟩
namespace InputCode
noncomputable def parse : Code Digits Parsed := by
  refine ⟨fun d => ⟨Normalize.read d.bits⟩, Normalize.device.recode encode encode Digits.bits
    (fun d => (⟨Normalize.read d.bits⟩ : Parsed)) (fun _ => rfl) (fun _ => rfl), ?_⟩
  obtain ⟨K,d,h⟩ := Normalize.polynomial
  exact ⟨K,d,fun z => h z.bits⟩
noncomputable def n : Code Parsed Count := by
  refine ⟨fun p => p.raw.1, Normalize.nDevice.recode encode encode Parsed.raw (fun p => p.raw.1)
    (fun _ => rfl) (fun _ => rfl), ?_⟩
  obtain ⟨K,d,h⟩ := (LinearCost.first Normalize.countData (product Normalize.ownersData Normalize.edgesData)).polynomial
  exact ⟨K,d,fun p => h p.raw⟩
noncomputable def edges : Code Parsed (List EdgeRead.Edge) := by
  refine ⟨fun p => p.raw.2.2, Normalize.edgesDevice.recode encode encode Parsed.raw (fun p => p.raw.2.2)
    (fun _ => rfl) (fun _ => rfl), ?_⟩
  have hc : PolynomialCost Normalize.edgesDevice :=
    (LinearCost.compose (LinearCost.second _ _) (LinearCost.second _ _)).polynomial
  obtain ⟨K,d,h⟩ := hc
  exact ⟨K,d,fun p => h p.raw⟩
noncomputable def rows : Code Parsed RawBasic.Arena := by
  refine ⟨fun p => Rows.build p.raw, Rows.buildDevice.recode encode encode Parsed.raw (fun p => Rows.build p.raw)
    (fun _ => rfl) (fun _ => rfl), ?_⟩
  obtain ⟨K,d,h⟩ := Rows.build_polynomial
  exact ⟨K,d,fun p => h p.raw⟩

def game (G : Game) : Parsed := ⟨(List.replicate G.n (),(List.ofFn G.maxOwner,List.ofFn (Normalize.encodedEdge G)))⟩
@[simp] theorem parse_game (G : Game) : parse ⟨input G⟩=game G := by
  change Parsed.mk (Normalize.read (input G))=_
  rw [Normalize.exact]
  rfl
@[simp] theorem n_game (G : Game) : n (game G)=List.replicate G.n () := rfl
@[simp] theorem rows_game (G : Game) : rows (game G)=Graph.codeVertices G (Normalize.word G) := Rows.build_exact _

noncomputable def absolute : Code W W := (Code.id ⋏ₚ Word.neg) ≫ₚ Word.max
@[simp] theorem absolute_val (w : W) : (absolute w).val=|w.val| := by simp [absolute,abs_eq_max_neg]
noncomputable def maximumFold : Code (W×List W) W := fold Word.max (by
  intro w x
  change treeSize (wordData (Order.high (w,x))) ≤ treeSize (wordData w)+treeSize (wordData x)+1
  unfold Order.high
  split <;> dsimp only [Prod.fst,Prod.snd] <;> omega)
noncomputable def maximum : Code (List W) W := (Word.constant 1 ⋏ₚ Code.id) ≫ₚ maximumFold
noncomputable def bound : Code Parsed W := edges ≫ₚ map (snd ≫ₚ snd ≫ₚ absolute) ≫ₚ maximum
noncomputable def width : Code Parsed W := (((n ≫ₚ Counter.word) ⋏ₚ bound) ≫ₚ Word.mul) ≫ₚ RawBudget.times 8

 theorem fold_upper (a : W) (xs : List W) (M : ℤ) (ha : a.val ≤ M) (hx : ∀ x∈xs, x.val ≤ M) :
    (maximumFold (a,xs)).val ≤ M := by
  change (Fold.fold Word.max.eval a xs).val ≤ M
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    change (Fold.fold Word.max.eval (Word.max (a,x)) xs).val ≤ M
    exact ih _ (by simp only [Word.max_val]; exact max_le ha (hx _ (by simp))) (by intro y hy; exact hx y (by simp [hy]))
 theorem fold_lower (a : W) (xs : List W) : a.val ≤ (maximumFold (a,xs)).val := by
  change a.val ≤ (Fold.fold Word.max.eval a xs).val
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons x xs ih =>
    exact le_trans (show a.val ≤ (Word.max (a,x)).val by rw [Word.max_val]; exact le_max_left _ _) (ih (Word.max (a,x)))
 theorem fold_mem (a : W) (xs : List W) (x : W) (hx : x∈xs) : x.val ≤ (maximumFold (a,xs)).val := by
  change x.val ≤ (Fold.fold Word.max.eval a xs).val
  induction xs generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (show x.val ≤ (Word.max (a,x)).val by rw [Word.max_val]; exact le_max_right _ _) (fold_lower (Word.max (a,x)) ys)
    · exact ih (Word.max (a,y)) hx

 theorem bound_val (G : Game) : (bound (game G)).val=weightBound G := by
  let xs := (List.ofFn (Normalize.encodedEdge G)).map (fun e => absolute e.2.2)
  change (maximumFold (Word.constant 1 xs,xs)).val=weightBound G
  apply le_antisymm
  · apply fold_upper
    · rw [Word.constant_val]
      exact le_max_left _ _
    · intro x hx
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp he
      subst e
      simp only [Normalize.encodedEdge,absolute_val,Normalize.word_val]
      exact transformed_le_bound G i
  · have h1 : 1 ≤ (maximumFold (Word.constant 1 xs,xs)).val := by simpa only [Word.constant_val] using fold_lower (Word.constant 1 xs) xs
    apply max_le h1
    have hsup : Finset.univ.sup (fun e : Fin G.m => (transformed G e).natAbs) ≤ (maximumFold (Word.constant 1 xs,xs)).val.toNat := by
      apply Finset.sup_le
      intro i _
      have hmem : absolute (Normalize.word G i) ∈ xs := by
        apply List.mem_map.mpr
        exact ⟨Normalize.encodedEdge G i,List.mem_ofFn.mpr ⟨i,rfl⟩,rfl⟩
      have hh := fold_mem (Word.constant 1 xs) xs _ hmem
      rw [absolute_val,Normalize.word_val] at hh
      exact_mod_cast (show ((transformed G i).natAbs : ℤ) ≤ ((maximumFold (Word.constant 1 xs,xs)).val.toNat : ℤ) by
        rw [Int.natCast_natAbs,Int.toNat_of_nonneg (by omega)]; exact hh)
    have hh := Int.ofNat_le.mpr hsup
    rwa [Int.toNat_of_nonneg (by omega)] at hh
@[simp] theorem width_val (G : Game) : (width (game G)).val=topWidth G := by
  simp only [width,comp_eval,pair_eval,RawBudget.times_val,Word.mul_val,Counter.word_val,n_game,List.length_replicate,bound_val]
  unfold topWidth
  ring
end InputCode
end MeanPayoff.TreeDevice.Certified
end

end OAI
