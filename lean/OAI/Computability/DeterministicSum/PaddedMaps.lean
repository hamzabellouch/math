import Mathlib
import OAI.Computability.DeterministicSum.AxisMaps
import OAI.Computability.DeterministicSum.BilinearForms

namespace OAI

/-! Charged padded matrix maps and interleaved coordinate layouts. -/

namespace DeterministicThreeSum.Structured.Indexed.PaddedAxis
open Command Finset Axis
open scoped BigOperators

abbrev inputSize : Expr 8 := .parameter ⟨7,by omega⟩
def limitAddress : Expr 8 := .binary .add src inputSize

def term (q r u : ℕ) : Scalar 8 := .binary .mul (.input (coeffAddress q r u))
  (.branch (inputAddress q r u) limitAddress (.input (inputAddress q r u)) (.literal 0))
def row (q r : ℕ) : Scalar 8 := Scalar.sum (List.ofFn (fun u : Fin q => term q r u.val))
def pass (q r : ℕ) : Command := kernel ⟨0,by omega⟩ ⟨1,by omega⟩ ⟨3,by omega⟩ (row q r)
def pad (x : ℕ → ℕ) (N i : ℕ) : ℕ := if i<N then x i else 0

lemma addresses_valid {w T P S C A B q r N j u : ℕ}
    (hq : 0<q) (hr : 0<r) (hB : 0<B) (hj : j<A*r*B) (hu : u<q)
    (hN : A*r*B<wordModulus w) (hS : S+A*q*B<wordModulus w)
    (hC : C+r*q<wordModulus w) (hNs : N≤A*q*B) :
    (inputAddress q r u).Valid w (environment T (A*r*B) P S C B N j) ∧
    (coeffAddress q r u).Valid w (environment T (A*r*B) P S C B N j) ∧
    limitAddress.Valid w (environment T (A*r*B) P S C B N j) := by
  have hA : 0<A := by
    by_contra h
    have hzero : A=0 := by omega
    simp [hzero] at hj
  have hmB : B≤A*r*B := by
    have hp : 1≤A*r := Nat.mul_pos hA hr
    simpa using Nat.mul_le_mul_right B hp
  have hmq : q≤r*q := by simpa using Nat.mul_le_mul_right q hr
  have hmr : r≤r*q := by simpa using Nat.mul_le_mul_left r hq
  have hi:=sourceIndex_bound hB hr hj hu
  have hc:=coefficientIndex_bound (B:=B) (j:=j) hr hu
  have hf : (j/B/r)*q+u≤((j/B/r)*q+u)*B := by
    simpa using Nat.mul_le_mul_left ((j/B/r)*q+u) hB
  dsimp [sourceIndex] at hi
  dsimp [coefficientIndex] at hc
  refine ⟨?_,?_,?_⟩
  · simp only [inputAddress,outer,suffix,Expr.Valid,Expr.value,Arithmetic.Valid,Arithmetic.value]
    norm_num [environment]
    omega
  · simp only [coeffAddress,digit,Expr.Valid,Expr.value,Arithmetic.Valid,Arithmetic.value]
    norm_num [environment]
    omega
  · simp only [limitAddress,Expr.Valid,Expr.value,Arithmetic.Valid]
    norm_num [environment]
    omega

lemma limitAddress_value (T J P S C B N j : ℕ) :
    limitAddress.value (environment T J P S C B N j)=S+N := by
  simp [limitAddress,Expr.value,Arithmetic.value,environment]

lemma row_valid {w T P S C A B q r N j : ℕ} (mem : ℕ → Option ℕ) (x c : ℕ → ℕ)
    (hq : 0<q) (hr : 0<r) (hB : 0<B) (hj : j<A*r*B)
    (hN : A*r*B<wordModulus w) (hS : S+A*q*B<wordModulus w)
    (hC : C+r*q<wordModulus w) (hNs : N≤A*q*B)
    (hx : ∀ i, i<N → mem (S+i)=some (x i) ∧ x i<T)
    (hc : ∀ i, i<r*q → mem (C+i)=some (c i) ∧ c i<T) :
    (row q r).Valid w T (environment T (A*r*B) P S C B N j) mem := by
  apply Scalar.sum_valid
  intro e he
  obtain ⟨u,rfl⟩:=List.mem_ofFn.mp he
  obtain ⟨hsafe,csafe,lsafe⟩:=addresses_valid (T:=T) (P:=P) hq hr hB hj u.isLt hN hS hC hNs
  refine ⟨⟨csafe,c (coefficientIndex q r B j u.val),?_,?_⟩,hsafe,lsafe,?_⟩
  · rw [coeffAddress_value]
    exact (hc _ (coefficientIndex_bound hr u.isLt)).1
  · exact (hc _ (coefficientIndex_bound hr u.isLt)).2
  · simp only [inputAddress_value,limitAddress_value,Nat.add_lt_add_iff_left]
    split_ifs with h
    · exact ⟨hsafe,x (sourceIndex q r B j u.val),by rw [inputAddress_value]; exact (hx _ h).1,(hx _ h).2⟩
    · exact wordModulus_pos w

lemma row_value {T P S C A B q r N j : ℕ} (mem : ℕ → Option ℕ) (x c : ℕ → ℕ)
    (hr : 0<r) (hx : ∀ i, i<N → mem (S+i)=some (x i))
    (hc : ∀ i, i<r*q → mem (C+i)=some (c i)) :
    ((row q r).value T (environment T (A*r*B) P S C B N j) mem:ZMod T)=
      ∑ u : Fin q, (c (coefficientIndex q r B j u.val):ZMod T)*
        (pad x N (sourceIndex q r B j u.val):ZMod T) := by
  rw [row,Scalar.sum_cast_value,List.map_ofFn,List.sum_ofFn]
  apply sum_congr rfl
  intro u _
  simp only [Function.comp_apply,term,Scalar.value,RingOp.raw,coeffAddress_value,inputAddress_value,
    limitAddress_value,Nat.add_lt_add_iff_left,hc _ (coefficientIndex_bound hr u.isLt),Option.getD_some,pad]
  by_cases h : sourceIndex q r B j u.val<N
  · simp [h,hx _ h]
  · simp [h]

lemma row_reads_outside {T P S C A B q r N j : ℕ}
    (hr : 0<r) (hB : 0<B) (hj : j<A*r*B)
    (hS : S+A*q*B≤P ∨ P+A*r*B≤S) (hC : C+r*q≤P ∨ P+A*r*B≤C) :
    ∀ a∈(row q r).reads (environment T (A*r*B) P S C B N j), a<P ∨ P+A*r*B≤a := by
  apply Scalar.sum_reads
  intro e he a ha
  obtain ⟨u,rfl⟩:=List.mem_ofFn.mp he
  simp only [term,Scalar.reads,mem_union,mem_singleton,coeffAddress_value,inputAddress_value,
    limitAddress_value,Nat.add_lt_add_iff_left] at ha
  have hs:=sourceIndex_bound hB hr hj u.isLt
  have hc:=coefficientIndex_bound (B:=B) (j:=j) hr u.isLt
  rcases ha with rfl|ha
  · omega
  · split_ifs at ha with h
    · simp only [mem_singleton] at ha
      subst a
      omega
    · simp at ha

theorem pass_correct {w T P S C A B q r N : ℕ} (s : Data) (x c : ℕ → ℕ)
    (hq : 0<q) (hr : 0<r) (hB : 0<B) (hT : 0<T)
    (hadd : 2*T<wordModulus w) (hmul : T*T<wordModulus w)
    (hN : A*r*B+1<wordModulus w) (hP : P+A*r*B<wordModulus w)
    (hS : S+A*q*B<wordModulus w) (hC : C+r*q<wordModulus w) (hNs : N≤A*q*B)
    (hdisS : S+A*q*B≤P ∨ P+A*r*B≤S) (hdisC : C+r*q≤P ∨ P+A*r*B≤C)
    (hregs : ∀ a : Fin 8, s.registers a.val=environment T (A*r*B) P S C B N 0 a)
    (hx : ∀ i, i<N → s.memory (S+i)=some (x i) ∧ x i<T)
    (hc : ∀ i, i<r*q → s.memory (C+i)=some (c i) ∧ c i<T) :
    ∃ cost t, Eval w (pass q r) s cost t ∧ cost≤((row q r).cost+5)*(A*r*B)+1 ∧
      (∀ a, a<8 → a≠0 → t.registers a=s.registers a) ∧ t.registers 0=A*r*B ∧
      (∀ j, j<A*r*B → t.memory (P+j)=some (mapValue T q r B (pad x N) c j)) ∧
      (∀ a, a<P ∨ P+A*r*B≤a → t.memory a=s.memory a) := by
  have henv : (fun a : Fin 8 => s.registers a.val)=environment T (A*r*B) P S C B N 0 := funext hregs
  have hindex : s.registers 0=0 := by simpa [environment] using hregs ⟨0,by omega⟩
  have hbound : s.registers 1=A*r*B := by simpa [environment] using hregs ⟨1,by omega⟩
  have hbase : s.registers 3=P := by simpa [environment] using hregs ⟨3,by omega⟩
  have hmod : s.registers 2=T := by simpa [environment] using hregs ⟨2,by omega⟩
  have hv : ∀ i, i<A*r*B → (row q r).Valid w T
      (Function.update (fun a : Fin 8 => s.registers a.val) ⟨0,by omega⟩ i) s.memory := by
    intro i hi
    rw [henv,environment_update]
    exact row_valid s.memory x c hq hr hB hi (by omega) hS hC hNs hx hc
  have hd : ∀ i, i<A*r*B → ∀ a∈(row q r).reads
      (Function.update (fun a : Fin 8 => s.registers a.val) ⟨0,by omega⟩ i), a<P ∨ P+A*r*B≤a := by
    intro i hi
    rw [henv,environment_update]
    exact row_reads_outside hr hB hi hdisS hdisC
  obtain ⟨cost,t,he,hcost,hframe,ht,hm⟩:=kernel_correct
    (index:=⟨0,by omega⟩) (bound:=⟨1,by omega⟩) (base:=⟨3,by omega⟩) (row q r) s
    (by omega) hT hadd hmul hN hP
    (by intro h; have hv := congrArg Fin.val h; norm_num at hv)
    (by intro h; have hv := congrArg Fin.val h; norm_num at hv) (by norm_num)
    hbound hbase hmod hindex hv hd
  refine ⟨cost,t,he,hcost,hframe,ht,?_,?_⟩
  · intro j hj
    let v := (row q r).value T (environment T (A*r*B) P S C B N j) s.memory
    have hvT : v<T := (row q r).value_lt _ _ hT (row_valid s.memory x c hq hr hB hj (by omega) hS hC hNs hx hc)
    have hvc : (v:ZMod T)=(mapValue T q r B (pad x N) c j:ZMod T) :=
      (row_value s.memory x c hr (fun i hi => (hx i hi).1) (fun i hi => (hc i hi).1)).trans (mapValue_cast ..).symm
    have : NeZero T := ⟨by omega⟩
    apply_fun ZMod.val at hvc
    simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hvT,Nat.mod_eq_of_lt (mapValue_lt hT q r B (pad x N) c j)] at hvc
    rw [hm,henv]
    simp only [written,ite_eq_left (show P≤P+j ∧ P+j<P+A*r*B by omega),Nat.add_sub_cancel_left,environment_update]
    exact congrArg some hvc
  · intro a ha
    rw [hm]
    exact written_outside ha

end DeterministicThreeSum.Structured.Indexed.PaddedAxis
namespace DeterministicThreeSum.Structured.Indexed.MatrixLayout
open DeterministicThreeSum.Rectangular Axis Finset
open scoped BigOperators

def pairCode (a b : ℕ) : (d : ℕ) → DigitBox a d → DigitBox b d → ℕ
  | 0,_,_ => 0
  | d+1,u,v => (u.1.val*b+v.1.val)*(a*b)^d+pairCode a b d u.2 v.2

lemma digit_lt {a b : ℕ} (u : Fin a) (v : Fin b) : u.val*b+v.val < a*b := by
  have h:=Nat.mul_le_mul_right b u.isLt
  nlinarith only [h,v.isLt]

lemma pairCode_lt {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (d : ℕ)
    (u : DigitBox a d) (v : DigitBox b d) : pairCode a b d u v < (a*b)^d := by
  induction d with
  | zero => exact pow_pos (Nat.mul_pos ha hb) 0
  | succ d ih =>
    have hc:=digit_lt u.1 v.1
    have hi:=ih u.2 v.2
    have hm:=Nat.mul_le_mul_right ((a*b)^d) hc
    simp only [pairCode,pow_succ]
    nlinarith only [hm,hi]

lemma packed_div {B : ℕ} (hB : 0 < B) (u v : ℕ) (hv : v < B) : (u*B+v)/B=u := by
  simpa [Nat.add_comm,Nat.mul_comm,Nat.div_eq_of_lt hv] using Nat.add_mul_div_left v u hB
lemma packed_mod {B : ℕ} (u v : ℕ) (hv : v < B) : (u*B+v)%B=v := by
  simp [Nat.add_mod,Nat.mod_eq_of_lt hv]

lemma packed_lt {B : ℕ} (hB : 0 < B) (u v t : ℕ) (hv : v < B) :
    u*B+v < t*B ↔ u<t := by
  constructor
  · intro h
    exact (Nat.mul_lt_mul_right hB).mp (lt_of_le_of_lt (Nat.le_add_right _ _) h)
  · intro h
    have hp:=Nat.mul_le_mul_right B h
    nlinarith only [hp,hv]

lemma pairCode_injective {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (d : ℕ) :
    Function.Injective (fun uv : DigitBox a d × DigitBox b d => pairCode a b d uv.1 uv.2) := by
  induction d with
  | zero => intro x y h; exact Subsingleton.elim _ _
  | succ d ih =>
    rintro ⟨u,v⟩ ⟨u',v'⟩ h
    have hB : 0 < (a*b)^d := pow_pos (Nat.mul_pos ha hb) _
    have hd:=congrArg (fun n=>n/((a*b)^d)) h
    simp only [pairCode,packed_div hB _ _ (pairCode_lt ha hb d _ _)] at hd
    have ht:=congrArg (fun n=>n%((a*b)^d)) h
    simp only [pairCode,packed_mod _ _ (pairCode_lt ha hb d _ _)] at ht
    have htail : (u.2,v.2)=(u'.2,v'.2) := ih ht
    have hrow:=congrArg (fun n=>n/b) hd
    simp only [packed_div hb _ _ v.1.isLt,packed_div hb _ _ v'.1.isLt] at hrow
    have hcol:=congrArg (fun n=>n%b) hd
    simp only [packed_mod _ _ v.1.isLt,packed_mod _ _ v'.1.isLt] at hcol
    have htu : u.2=u'.2 := congrArg (@Prod.fst (DigitBox a d) (DigitBox b d)) htail
    have htv : v.2=v'.2 := congrArg (@Prod.snd (DigitBox a d) (DigitBox b d)) htail
    exact Prod.ext (Prod.ext (Fin.ext hrow) htu) (Prod.ext (Fin.ext hcol) htv)

noncomputable def pairIndex {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (d : ℕ) :
    DigitBox a d × DigitBox b d ≃ Fin ((a*b)^d) :=
  Equiv.ofBijective (fun uv => ⟨pairCode a b d uv.1 uv.2,pairCode_lt ha hb d uv.1 uv.2⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro x y h
      exact pairCode_injective ha hb d (congrArg Fin.val h),by
      simp [Fintype.card_prod,card_DigitBox,mul_pow]⟩)

def tripleIndex (k a b : ℕ) : (Fin k × Fin a × Fin b) ≃ Fin (k*(a*b)) :=
  (Equiv.prodCongr (Equiv.refl (Fin k)) finProdFinEquiv).trans finProdFinEquiv

lemma tripleIndex_val (k a b : ℕ) (i : Fin k × Fin a × Fin b) :
    (tripleIndex k a b i).val=i.1.val*(a*b)+(i.2.1.val*b+i.2.2.val) := by
  simp [tripleIndex,finProdFinEquiv,Nat.mul_comm,Nat.add_assoc,Nat.add_comm]

lemma sourceIndex_packed {q r B : ℕ} (hr : 0 < r) (hB : 0 < B)
    (g s v u : ℕ) (hs : s < r) (hv : v < B) :
    sourceIndex q r B ((g*r+s)*B+v) u=(g*q+u)*B+v := by
  simp only [sourceIndex,packed_div hB _ _ hv,packed_div hr _ _ hs,
    packed_mod _ _ hv]
lemma coefficientIndex_packed {q r B : ℕ} (hr : 0 < r) (hB : 0 < B)
    (g s v u : ℕ) (hs : s < r) (hv : v < B) :
    coefficientIndex q r B ((g*r+s)*B+v) u=s*q+u := by
  simp only [coefficientIndex,packed_div hB _ _ hv]
  rw [Nat.mod_eq_sub_mul_div,packed_div hr _ _ hs,Nat.mul_comm r g,
    Nat.add_sub_cancel_left]
end DeterministicThreeSum.Structured.Indexed.MatrixLayout
namespace DeterministicThreeSum.Structured.Indexed.MatrixLayout
open DeterministicThreeSum.Rectangular Axis Finset
open scoped BigOperators

lemma padded_left_read {T a b k r d t : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (x : LeftBatch (ZMod T) a b (d+1) t) (data : ℕ → ℕ)
    (hx : ∀ z u v, (data (z.val*((a*b)^(d+1))+pairCode a b (d+1) u v):ZMod T)=x z u v)
    (g : Fin (batchCount t k)) (s : Fin r) (i : Fin k × Fin a × Fin b)
    (u : DigitBox a d) (v : DigitBox b d) :
    (PaddedAxis.pad data (t*((a*b)^(d+1)))
      (sourceIndex (k*(a*b)) r ((a*b)^d)
        ((g.val*r+s.val)*((a*b)^d)+pairCode a b d u v) (tripleIndex k a b i).val):ZMod T)=
      paddedLeft x g i u v := by
  have hB : 0 < (a*b)^d := pow_pos (Nat.mul_pos ha hb) _
  have hc:=pairCode_lt ha hb d u v
  have hi : sourceIndex (k*(a*b)) r ((a*b)^d)
        ((g.val*r+s.val)*((a*b)^d)+pairCode a b d u v) (tripleIndex k a b i).val =
      (g.val*k+i.1.val)*((a*b)^(d+1))+pairCode a b (d+1) (i.2.1,u) (i.2.2,v) := by
    rw [sourceIndex_packed hr hB _ _ _ _ s.isLt hc,tripleIndex_val]
    simp only [pairCode,pow_succ]
    ring
  rw [hi]
  have hh:=packed_lt (pow_pos (Nat.mul_pos ha hb) (d+1)) (g.val*k+i.1.val)
    (pairCode a b (d+1) (i.2.1,u) (i.2.2,v)) t (pairCode_lt ha hb (d+1) (i.2.1,u) (i.2.2,v))
  by_cases h : g.val*k+i.1.val<t
  · unfold PaddedAxis.pad paddedLeft
    erw [ite_eq_left (hh.mpr h),dite_eq_left h]
    exact hx ⟨g.val*k+i.1.val,h⟩ (i.2.1,u) (i.2.2,v)
  · unfold PaddedAxis.pad paddedLeft
    erw [ite_eq_right (hh.not.mpr h),dite_eq_right h]
    simp only [Nat.cast_zero,Matrix.zero_apply]

theorem left_level_value {T a b k r d t : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (f : FixedFormula (ZMod T) a b k r) (x : LeftBatch (ZMod T) a b (d+1) t)
    (data co : ℕ → ℕ)
    (hx : ∀ z u v, (data (z.val*((a*b)^(d+1))+pairCode a b (d+1) u v):ZMod T)=x z u v)
    (hc : ∀ (s : Fin r) (i : Fin k × Fin a × Fin b),
      (co (s.val*(k*(a*b))+(tripleIndex k a b i).val):ZMod T)=f.left s i)
    (g : Fin (batchCount t k)) (s : Fin r) (u : DigitBox a d) (v : DigitBox b d) :
    (mapValue T (k*(a*b)) r ((a*b)^d) (PaddedAxis.pad data (t*((a*b)^(d+1)))) co
      ((g.val*r+s.val)*((a*b)^d)+pairCode a b d u v):ZMod T)=
      childLeft f x (finProdFinEquiv (g,s)) u v := by
  rw [mapValue_cast]
  rw [←(tripleIndex k a b).sum_comp (fun i =>
    (co (coefficientIndex (k*(a*b)) r ((a*b)^d)
      ((g.val*r+s.val)*((a*b)^d)+pairCode a b d u v) i.val):ZMod T)*
    (PaddedAxis.pad data (t*((a*b)^(d+1)))
      (sourceIndex (k*(a*b)) r ((a*b)^d)
        ((g.val*r+s.val)*((a*b)^d)+pairCode a b d u v) i.val):ZMod T))]
  simp only [childLeft,Equiv.symm_apply_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply sum_congr rfl
  intro i _
  rw [coefficientIndex_packed hr (pow_pos (Nat.mul_pos ha hb) d) _ _ _ _ s.isLt (pairCode_lt ha hb d u v),hc]
  rw [padded_left_read ha hb hr x data hx]
end DeterministicThreeSum.Structured.Indexed.MatrixLayout
namespace DeterministicThreeSum.Structured.Indexed.MatrixLayout
open DeterministicThreeSum.Rectangular Axis Finset
open scoped BigOperators

theorem right_level_value {T a b k r d t : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (f : FixedFormula (ZMod T) a b k r) (y : RightBatch (ZMod T) a b (d+1) t)
    (data co : ℕ → ℕ)
    (hy : ∀ z u v, (data (z.val*((b*a)^(d+1))+pairCode b a (d+1) u v):ZMod T)=y z u v)
    (hc : ∀ (s : Fin r) (i : Fin k × Fin b × Fin a),
      (co (s.val*(k*(b*a))+(tripleIndex k b a i).val):ZMod T)=f.right s i)
    (g : Fin (batchCount t k)) (s : Fin r) (u : DigitBox b d) (v : DigitBox a d) :
    (mapValue T (k*(b*a)) r ((b*a)^d) (PaddedAxis.pad data (t*((b*a)^(d+1)))) co
      ((g.val*r+s.val)*((b*a)^d)+pairCode b a d u v):ZMod T)=
      childRight f y (finProdFinEquiv (g,s)) u v := by
  let f' : FixedFormula (ZMod T) b a k r := ⟨f.right,f.left,fun _ _=>0⟩
  exact left_level_value hb ha hr f' y data co hy hc g s u v

lemma parent_packed {a k t d : ℕ} (hk : 0<k) (e : Fin t)
    (u v : DigitBox a (d+1)) :
    e.val*((a*a)^(d+1))+pairCode a a (d+1) u v =
      ((parentBatch hk e).val*(k*(a*a))+
        (tripleIndex k a a (parentSlot hk e,u.1,v.1)).val)*((a*a)^d)+
          pairCode a a d u.2 v.2 := by
  rw [tripleIndex_val]
  have hp:=parent_index hk e
  simp only [pairCode,pow_succ]
  calc
    _ = (((parentBatch hk e).val*k+(parentSlot hk e).val)*((a*a)^d*(a*a))+
      ((u.1.val*a+v.1.val)*(a*a)^d+pairCode a a d u.2 v.2)) := by rw [hp]
    _ = _ := by ring

theorem combine_level_value {T a b k r d t : ℕ} (ha : 0<a) (hk : 0<k)
    (f : FixedFormula (ZMod T) a b k r)
    (z : OutputBatch (ZMod T) a d (batchCount t k*r)) (data co : ℕ → ℕ)
    (hz : ∀ e u v, (data (e.val*((a*a)^d)+pairCode a a d u v):ZMod T)=z e u v)
    (hc : ∀ (s : Fin r) (i : Fin k × Fin a × Fin a),
      (co ((tripleIndex k a a i).val*r+s.val):ZMod T)=f.out s i)
    (e : Fin t) (u v : DigitBox a (d+1)) :
    (mapValue T r (k*(a*a)) ((a*a)^d) data co
      (e.val*((a*a)^(d+1))+pairCode a a (d+1) u v):ZMod T)=
      combineChildren f hk z e u v := by
  have hka : 0<k*(a*a) := Nat.mul_pos hk (Nat.mul_pos ha ha)
  have hB : 0<(a*a)^d := pow_pos (Nat.mul_pos ha ha) d
  have hi := (tripleIndex k a a (parentSlot hk e,u.1,v.1)).isLt
  have htail := pairCode_lt ha ha d u.2 v.2
  rw [mapValue_cast,parent_packed hk]
  unfold combineChildren
  apply sum_congr rfl
  intro s _
  rw [coefficientIndex_packed hka hB _ _ _ _ hi htail,hc,
    sourceIndex_packed hka hB _ _ _ _ hi htail]
  have heq : ((finProdFinEquiv (parentBatch hk e,s)) : Fin (batchCount t k*r)).val =
      (parentBatch hk e).val*r+s.val := by simp [finProdFinEquiv,Nat.add_comm,Nat.mul_comm]
  rw [←heq,hz]
end DeterministicThreeSum.Structured.Indexed.MatrixLayout
namespace DeterministicThreeSum.Structured.Indexed.MatrixLayout
open Command DeterministicThreeSum.Rectangular Axis Finset
open scoped BigOperators

lemma input_padding_bound {a b k d t : ℕ} (hk : 0<k) :
    t*(a*b)^(d+1) ≤ batchCount t k*(k*(a*b))*(a*b)^d := by
  have h := Nat.mul_le_mul_right ((a*b)^(d+1)) (batchCount_covers t k hk)
  convert h using 1
  simp only [pow_succ]
  ring

theorem left_level_correct {w T a b k r d t P S C : ℕ}
    (state : Data) (f : FixedFormula (ZMod T) a b k r)
    (x : LeftBatch (ZMod T) a b (d+1) t) (data co : ℕ → ℕ)
    (ha : 0<a) (hb : 0<b) (hk : 0<k) (hr : 0<r) (hT : 0<T)
    (hadd : 2*T<wordModulus w) (hmul : T*T<wordModulus w)
    (hN : batchCount t k*r*(a*b)^d+1<wordModulus w)
    (hP : P+batchCount t k*r*(a*b)^d<wordModulus w)
    (hS : S+batchCount t k*(k*(a*b))*(a*b)^d<wordModulus w)
    (hC : C+r*(k*(a*b))<wordModulus w)
    (hdisS : S+batchCount t k*(k*(a*b))*(a*b)^d≤P ∨ P+batchCount t k*r*(a*b)^d≤S)
    (hdisC : C+r*(k*(a*b))≤P ∨ P+batchCount t k*r*(a*b)^d≤C)
    (hregs : ∀ z : Fin 8, state.registers z.val=
      environment T (batchCount t k*r*(a*b)^d) P S C ((a*b)^d) (t*(a*b)^(d+1)) 0 z)
    (hx : ∀ i, i<t*(a*b)^(d+1) → state.memory (S+i)=some (data i) ∧ data i<T)
    (hc : ∀ i, i<r*(k*(a*b)) → state.memory (C+i)=some (co i) ∧ co i<T)
    (hsource : ∀ z u v, (data (z.val*(a*b)^(d+1)+pairCode a b (d+1) u v):ZMod T)=x z u v)
    (hformula : ∀ (s : Fin r) (i : Fin k × Fin a × Fin b),
      (co (s.val*(k*(a*b))+(tripleIndex k a b i).val):ZMod T)=f.left s i) :
    ∃ cost out, Eval w (PaddedAxis.pass (k*(a*b)) r) state cost out ∧
      cost≤((PaddedAxis.row (k*(a*b)) r).cost+5)*(batchCount t k*r*(a*b)^d)+1 ∧
      (∀ z, z<8 → z≠0 → out.registers z=state.registers z) ∧
      out.registers 0=batchCount t k*r*(a*b)^d ∧
      (∀ (g : Fin (batchCount t k)) (s : Fin r) (u : DigitBox a d) (v : DigitBox b d),
        ∃ value, out.memory (P+((g.val*r+s.val)*(a*b)^d+pairCode a b d u v))=some value ∧
          value<T ∧ (value:ZMod T)=childLeft f x (finProdFinEquiv (g,s)) u v) ∧
      (∀ addr, addr<P ∨ P+batchCount t k*r*(a*b)^d≤addr → out.memory addr=state.memory addr) := by
  have hB : 0<(a*b)^d := pow_pos (Nat.mul_pos ha hb) d
  obtain ⟨cost,out,hev,hcost,hreg,hzero,hmem,hframe⟩ := PaddedAxis.pass_correct state data co
    (Nat.mul_pos hk (Nat.mul_pos ha hb)) hr hB hT hadd hmul hN hP hS hC
    (input_padding_bound hk) hdisS hdisC hregs hx hc
  refine ⟨cost,out,hev,hcost,hreg,hzero,?_,hframe⟩
  intro g s u v
  have hi : (g.val*r+s.val)*(a*b)^d+pairCode a b d u v < batchCount t k*r*(a*b)^d :=
    (packed_lt hB _ _ _ (pairCode_lt ha hb d u v)).mpr (digit_lt g s)
  refine ⟨_,hmem _ hi,mapValue_lt hT _ _ _ _ _ _,?_⟩
  exact left_level_value ha hb hr f x data co hsource hformula g s u v

end DeterministicThreeSum.Structured.Indexed.MatrixLayout

end OAI
