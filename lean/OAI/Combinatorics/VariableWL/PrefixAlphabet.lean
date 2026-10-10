import OAI.Combinatorics.VariableWL.PortListing

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

theorem applyNat₂_number (P : Expr (n+2)) (I J : Expr n) (v : Env n) :
    (applyNat₂ P I J).number v=P.number (cons (List.replicate (I.number v) true)
      (cons (List.replicate (J.number v) true) v)) := by
  simp only [applyNat₂,applyNat_number,up_number]

def applyNat₃ (P : Expr (n+3)) (I J K : Expr n) : Expr n :=
  applyNat (applyNat₂ P I.up J.up) K

theorem applyNat₃_bit (P : Expr (n+3)) (I J K : Expr n) (v : Env n) :
    (applyNat₃ P I J K).bit v=P.bit (cons (List.replicate (I.number v) true)
      (cons (List.replicate (J.number v) true) (cons (List.replicate (K.number v) true) v))) := by
  simp only [applyNat₃,applyNat_bit,applyNat₂_bit,up_number]

theorem applyNat₃_number (P : Expr (n+3)) (I J K : Expr n) (v : Env n) :
    (applyNat₃ P I J K).number v=P.number (cons (List.replicate (I.number v) true)
      (cons (List.replicate (J.number v) true) (cons (List.replicate (K.number v) true) v))) := by
  simp only [applyNat₃,applyNat_number,applyNat₂_number,up_number]

theorem fixedNat_zero (N : ℕ) (f : Fin N → ℕ) (I : Expr n) (v : Env n)
    (h : N≤I.number v) : (fixedNat N f I).number v=0 := by
  induction N generalizing I with
  | zero => rfl
  | succ N ih =>
    rw [fixedNat,NumericProgram.choose_number,eq_bit,numeral_number,
      ite_eq_right (by simp only [decide_eq_true_eq]; omega)]
    exact ih _ _ (by simp only [sub_number,numeral_number]; omega)

def tableLookup {N : ℕ} (f : Fin N → ℕ) (i : ℕ) : ℕ := if h : i<N then f ⟨i,h⟩ else 0

theorem fixedNat_total (N : ℕ) (f : Fin N → ℕ) (I : Expr n) (v : Env n) :
    (fixedNat N f I).number v=tableLookup f (I.number v) := by
  unfold tableLookup
  split_ifs with h
  · exact fixedNat_number N f I v h
  · exact fixedNat_zero N f I v (Nat.le_of_not_gt h)

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Descriptor.Presentation
variable {A : Type uVariable1}

noncomputable def ofEncoding (N : ℕ) (P : ℕ → Bool) (f : A → ℕ)
    (hf : ∀a,f a<N) (hp : ∀a,P (f a)=true) (hi : Function.Injective f)
    (hs : ∀i,i<N → P i=true → ∃a,f a=i) : Presentation A where
  bound := N
  valid := P
  equiv := (Equiv.ofBijective (fun a=> (⟨⟨f a,hf a⟩,hp a⟩ : Valid N P)) (by
    constructor
    · intro a b he; exact hi (congrArg (fun a : Valid N P=>a.val.val) he)
    · intro i; obtain ⟨a,ha⟩ := hs i.val.val i.val.isLt i.property
      exact ⟨a,Subtype.ext (Fin.ext ha)⟩)).symm

theorem ofEncoding_encode (N : ℕ) (P : ℕ → Bool) (f : A → ℕ)
    (hf : ∀a,f a<N) (hp : ∀a,P (f a)=true) (hi : Function.Injective f)
    (hs : ∀i,i<N → P i=true → ∃a,f a=i) (a : A) :
    (ofEncoding N P f hf hp hi hs).encode a=f a := rfl

end VariableWL.Descriptor.Presentation

namespace VariableWL.Descriptor.PortData
open SubcubicRealization
variable {A : Type uVariable2}

theorem sound_of_equiv (D : PortData) (e : D.Owners ≃ A) (Y : PortGraph A)
    (hc : ∀a : D.Owners,D.color a.val.val≤D.colorBound)
    (he : ∀a b : D.Owners,∀i j : Fin 3,
      D.incidence (3*a.val.val+i.val) (3*b.val.val+j.val)=true ↔ Y.edge (e a,i) (e b,j)) :
    D.Sound := by
  refine ⟨hc,?_,?_,?_⟩
  · intro a b i j
    apply Bool.eq_iff_iff.mpr
    exact (he a b i j).trans ⟨fun h=>(he b a j i).mpr (Y.symm h),
      fun h=>Y.symm ((he b a j i).mp h)⟩
  · intro a b c i j k hb hc
    have h := Y.unique (he a b i j |>.mp hb) (he a c i k |>.mp hc)
    exact ⟨e.injective (congrArg Prod.fst h),congrArg Prod.snd h⟩
  · intro a b i j hab hab'
    exact Y.different ((he a b i j).mp hab) (congrArg e hab')

end VariableWL.Descriptor.PortData
namespace VariableWL.Descriptor.PortData
open SubcubicRealization
variable {A : Type uVariable3}
theorem sound_of_encoding (D : PortData) (f : A → D.Owners) (hf : Function.Bijective f) (Y : PortGraph A)
    (hc : ∀a,D.color (f a).val.val≤D.colorBound)
    (he : ∀a b i j,D.incidence (3*(f a).val.val+i.val) (3*(f b).val.val+j.val)=true ↔
      Y.edge (a,i) (b,j)) : D.Sound := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x; obtain ⟨a,rfl⟩ := hf.2 x; exact hc a
  · intro x y i j
    obtain ⟨a,rfl⟩ := hf.2 x
    obtain ⟨b,rfl⟩ := hf.2 y
    apply Bool.eq_iff_iff.mpr
    exact (he a b i j).trans ⟨fun h=>(he b a j i).mpr (Y.symm h),fun h=>Y.symm ((he b a j i).mp h)⟩
  · intro x y z i j k hxy hxz
    obtain ⟨a,rfl⟩ := hf.2 x
    obtain ⟨b,rfl⟩ := hf.2 y
    obtain ⟨c,rfl⟩ := hf.2 z
    have ht := Y.unique ((he a b i j).mp hxy) ((he a c i k).mp hxz)
    exact ⟨congrArg f (congrArg Prod.fst ht),congrArg Prod.snd ht⟩
  · intro x y i j hxy hx
    obtain ⟨a,rfl⟩ := hf.2 x
    obtain ⟨b,rfl⟩ := hf.2 y
    exact Y.different ((he a b i j).mp hxy) (hf.1 hx)
end VariableWL.Descriptor.PortData

namespace VariableWL.PrefixAlphabet
open VariableWL.Affine
attribute [local instance] Classical.propDecidable

abbrev Vector := Σa : Fin 7, Vec a.val
abbrev Order := Σa : Fin 7, Equiv.Perm (Fin a.val)
noncomputable instance vectorFintype : Fintype Vector := inferInstance
noncomputable instance orderFintype : Fintype Order := Fintype.ofFinite _
noncomputable def vectorNumber : Vector ≃ Fin (Fintype.card Vector) := Fintype.equivFin _
noncomputable def orderNumber : Order ≃ Fin (Fintype.card Order) := Fintype.equivFin _
noncomputable def vectorCount : ℕ := Fintype.card Vector
noncomputable def orderCount : ℕ := Fintype.card Order

noncomputable def encode {a : ℕ} (h : a≤6) (z : Vec a) : ℕ :=
  (vectorNumber ⟨⟨a,by omega⟩,z⟩).val
noncomputable def encodeOrder {a : ℕ} (h : a≤6) (p : Equiv.Perm (Fin a)) : ℕ :=
  (orderNumber ⟨⟨a,by omega⟩,p⟩).val

theorem encode_lt {a : ℕ} (h : a≤6) (z : Vec a) : encode h z<vectorCount :=
  (vectorNumber ⟨⟨a,by omega⟩,z⟩).isLt
 theorem order_lt {a : ℕ} (h : a≤6) (p : Equiv.Perm (Fin a)) : encodeOrder h p<orderCount :=
  (orderNumber ⟨⟨a,by omega⟩,p⟩).isLt
 theorem encode_injective {a : ℕ} (h : a≤6) : Function.Injective (@encode a h) := by
  intro z w he
  have hv := vectorNumber.injective (Fin.ext he)
  exact eq_of_heq (Sigma.mk.inj_iff.mp hv).2

noncomputable def dimension (i : ℕ) : ℕ :=
  if h : i<vectorCount then (vectorNumber.symm ⟨i,h⟩).1.val else 7

noncomputable def truncated (h : ℕ) (v : Vector) : Vector :=
  ⟨v.1,PrefixParts.Data.truncate h v.2⟩

noncomputable def permuted (p : Order) (v : Vector) : Vector :=
  if h : p.1=v.1 then ⟨v.1,v.2 ∘ (h ▸ p.2)⟩ else v

noncomputable def prefixCode (p h i : ℕ) : ℕ :=
  if hp : p<orderCount then if hi : i<vectorCount then
    (vectorNumber (truncated h (permuted (orderNumber.symm ⟨p,hp⟩) (vectorNumber.symm ⟨i,hi⟩)))).val
  else 0 else 0

noncomputable def bit (i h : ℕ) : ℕ :=
  if hi : i<vectorCount then
    let v := vectorNumber.symm ⟨i,hi⟩
    if hh : h<v.1.val then (v.2 ⟨h,hh⟩).val else 0
  else 0

noncomputable def paddedEqual (i j : ℕ) : Bool :=
  if hi : i<vectorCount then if hj : j<vectorCount then
    decide (PrefixParts.Wiring.pad (vectorNumber.symm ⟨i,hi⟩).2=
      PrefixParts.Wiring.pad (vectorNumber.symm ⟨j,hj⟩).2)
  else false else false

@[simp] theorem dimension_encode {a : ℕ} (h : a≤6) (z : Vec a) : dimension (encode h z)=a := by
  simp only [dimension,dite_eq_left (encode_lt h z)]
  change (vectorNumber.symm (vectorNumber ⟨⟨a,by omega⟩,z⟩)).1.val=a
  rw [Equiv.symm_apply_apply]

@[simp] theorem prefix_encode {a : ℕ} (ha : a≤6) (p : Equiv.Perm (Fin a)) (h : ℕ) (z : Vec a) :
    prefixCode (encodeOrder ha p) h (encode ha z)=encode ha (PrefixParts.Data.truncate h (z ∘ p)) := by
  simp only [prefixCode,dite_eq_left (order_lt ha p),dite_eq_left (encode_lt ha z)]
  change (vectorNumber (truncated h (permuted (orderNumber.symm (orderNumber ⟨⟨a,by omega⟩,p⟩))
    (vectorNumber.symm (vectorNumber ⟨⟨a,by omega⟩,z⟩))))).val=_
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  unfold permuted
  rw [dite_eq_left rfl]
  rfl

@[simp] theorem bit_encode {a : ℕ} (ha : a≤6) (z : Vec a) (i : Fin a) :
    bit (encode ha z) i.val=(z i).val := by
  simp only [bit,dite_eq_left (encode_lt ha z)]
  change (if h : i.val<(vectorNumber.symm (vectorNumber ⟨⟨a,by omega⟩,z⟩)).1.val then
    ((vectorNumber.symm (vectorNumber ⟨⟨a,by omega⟩,z⟩)).2 ⟨i.val,h⟩).val else 0)=_
  rw [Equiv.symm_apply_apply]
  exact dite_eq_left i.isLt

@[simp] theorem paddedEqual_encode {a b : ℕ} (ha : a≤6) (hb : b≤6) (z : Vec a) (w : Vec b) :
    paddedEqual (encode ha z) (encode hb w)=decide (PrefixParts.Wiring.pad z=PrefixParts.Wiring.pad w) := by
  simp only [paddedEqual,dite_eq_left (encode_lt ha z),dite_eq_left (encode_lt hb w)]
  change decide (PrefixParts.Wiring.pad (vectorNumber.symm (vectorNumber ⟨⟨a,by omega⟩,z⟩)).2=
    PrefixParts.Wiring.pad (vectorNumber.symm (vectorNumber ⟨⟨b,by omega⟩,w⟩)).2)=_
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]

end VariableWL.PrefixAlphabet

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def fixedNat₂ (N M : ℕ) (f : ℕ → ℕ → ℕ) (I J : Expr n) : Expr n :=
  fixedNat (N*M) (fun q=>f (q.val/M) (q.val%M)) (add (mul I (numeral M)) J)

theorem fixedNat₂_number (N M : ℕ) (f : ℕ → ℕ → ℕ) (I J : Expr n) (v : Env n)
    (hi : I.number v<N) (hj : J.number v<M) :
    (fixedNat₂ N M f I J).number v=f (I.number v) (J.number v) := by
  have hm : 0<M := by omega
  have hq : (add (mul I (numeral M)) J).number v<N*M := by
    simp only [add_number,mul_number,numeral_number]
    exact (Nat.add_lt_add_left hj _).trans_le (by rw [←Nat.succ_mul]; exact Nat.mul_le_mul_right M hi)
  rw [fixedNat₂,fixedNat_number _ _ _ _ hq]
  simp only [add_number,mul_number,numeral_number]
  rw [Nat.mul_comm (I.number v) M,Nat.mul_add_div hm,Nat.div_eq_of_lt hj,Nat.add_zero,
    Nat.mul_add_mod,Nat.mod_eq_of_lt hj]

def fixedNat₃ (N M K : ℕ) (f : ℕ → ℕ → ℕ → ℕ) (I J L : Expr n) : Expr n :=
  fixedNat₂ N (M*K) (fun i q=>f i (q/K) (q%K)) I (add (mul J (numeral K)) L)

theorem fixedNat₃_number (N M K : ℕ) (f : ℕ → ℕ → ℕ → ℕ) (I J L : Expr n) (v : Env n)
    (hi : I.number v<N) (hj : J.number v<M) (hk : L.number v<K) :
    (fixedNat₃ N M K f I J L).number v=f (I.number v) (J.number v) (L.number v) := by
  have hk' : 0<K := by omega
  have hq : (add (mul J (numeral K)) L).number v<M*K := by
    simp only [add_number,mul_number,numeral_number]
    exact (Nat.add_lt_add_left hk _).trans_le (by rw [←Nat.succ_mul]; exact Nat.mul_le_mul_right K hj)
  rw [fixedNat₃,fixedNat₂_number _ _ _ _ _ _ hi hq]
  simp only [add_number,mul_number,numeral_number]
  rw [Nat.mul_comm (J.number v) K,Nat.mul_add_div hk',Nat.div_eq_of_lt hk,Nat.add_zero,
    Nat.mul_add_mod,Nat.mod_eq_of_lt hk]

def fixedBool₂ (N M : ℕ) (f : ℕ → ℕ → Bool) (I J : Expr n) : Expr n :=
  eq (fixedNat₂ N M (fun i j=>if f i j then 1 else 0) I J) (numeral 1)

theorem fixedBool₂_bit (N M : ℕ) (f : ℕ → ℕ → Bool) (I J : Expr n) (v : Env n)
    (hi : I.number v<N) (hj : J.number v<M) :
    (fixedBool₂ N M f I J).bit v=f (I.number v) (J.number v) := by
  simp only [fixedBool₂,eq_bit,fixedNat₂_number _ _ _ _ _ _ hi hj,numeral_number]
  cases f (I.number v) (J.number v) <;> rfl

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.PrefixAlphabet.Program
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
variable {n : ℕ}

noncomputable def dimension (I : Expr n) : Expr n :=
  fixedNat vectorCount (fun q=>PrefixAlphabet.dimension q.val) I
noncomputable def prefixCode (P H I : Expr n) : Expr n :=
  fixedNat₃ orderCount 7 vectorCount PrefixAlphabet.prefixCode P H I
noncomputable def bit (I H : Expr n) : Expr n :=
  fixedNat₂ vectorCount 7 PrefixAlphabet.bit I H
noncomputable def paddedEqual (I J : Expr n) : Expr n :=
  fixedBool₂ vectorCount vectorCount PrefixAlphabet.paddedEqual I J

 theorem dimension_number (I : Expr n) (v : Env n) (h : I.number v<vectorCount) :
    (dimension I).number v=PrefixAlphabet.dimension (I.number v) := fixedNat_number _ _ _ _ h
 theorem prefixCode_number (P H I : Expr n) (v : Env n)
    (hp : P.number v<orderCount) (hh : H.number v<7) (hi : I.number v<vectorCount) :
    (prefixCode P H I).number v=PrefixAlphabet.prefixCode (P.number v) (H.number v) (I.number v) :=
  fixedNat₃_number _ _ _ _ _ _ _ _ hp hh hi
 theorem bit_number (I H : Expr n) (v : Env n) (hi : I.number v<vectorCount) (hh : H.number v<7) :
    (bit I H).number v=PrefixAlphabet.bit (I.number v) (H.number v) := fixedNat₂_number _ _ _ _ _ _ hi hh
 theorem paddedEqual_bit (I J : Expr n) (v : Env n) (hi : I.number v<vectorCount) (hj : J.number v<vectorCount) :
    (paddedEqual I J).bit v=PrefixAlphabet.paddedEqual (I.number v) (J.number v) := fixedBool₂_bit _ _ _ _ _ _ hi hj

end VariableWL.PrefixAlphabet.Program

namespace VariableWL.PrefixAlphabet
 theorem vectorCount_pos : 0<vectorCount := by
  let : Nonempty Vector := ⟨⟨0,0⟩⟩
  exact Fintype.card_pos
end VariableWL.PrefixAlphabet

namespace VariableWL.PrefixDescriptor
open VariableWL.Affine Descriptor PrefixParts
attribute [local instance] Classical.propDecidable

@[ext] structure Raw where
  block : ℕ
  kind : ℕ
  channel : ℕ
  height : ℕ
  vector : ℕ
  deriving DecidableEq

structure Data where
  blocks : ℕ
  validBlock : ℕ → Bool
  channelBound : ℕ
  dimension : ℕ → ℕ
  channels : ℕ → ℕ
  root : ℕ → ℕ → ℕ
  order : ℕ → ℕ → ℕ
  legal : ℕ → ℕ → Bool
  matching : ℕ → ℕ → Bool

namespace Data
variable (D : Data)

def sortBound : ℕ := D.blocks*3*D.channelBound*7
noncomputable def bound : ℕ := D.sortBound*PrefixAlphabet.vectorCount

def tag (x : Raw) : ℕ := ((x.block*3+x.kind)*D.channelBound+x.channel)*7+x.height
noncomputable def pack (x : Raw) : ℕ := D.tag x*PrefixAlphabet.vectorCount+x.vector
noncomputable def unpack (i : ℕ) : Raw :=
  ⟨i/PrefixAlphabet.vectorCount/7/D.channelBound/3,
    i/PrefixAlphabet.vectorCount/7/D.channelBound%3,
    i/PrefixAlphabet.vectorCount/7%D.channelBound,
    i/PrefixAlphabet.vectorCount%7,i%PrefixAlphabet.vectorCount⟩

theorem join_div (x y m : ℕ) (hm : 0 < m) (hy : y < m) : (x*m+y)/m=x := by
  rw [Nat.mul_comm x m,Nat.mul_add_div hm,Nat.div_eq_of_lt hy,Nat.add_zero]
theorem join_mod (x y m : ℕ) (hy : y < m) : (x*m+y)%m=y := by
  rw [Nat.mul_comm x m,Nat.mul_add_mod,Nat.mod_eq_of_lt hy]

theorem unpack_pack (x : Raw) (hk : x.kind<3) (hc : x.channel<D.channelBound)
    (hh : x.height<7) (hu : x.vector<PrefixAlphabet.vectorCount) : D.unpack (D.pack x)=x := by
  have hC : 0<D.channelBound := by omega
  simp only [unpack,pack,tag,join_div _ _ _ PrefixAlphabet.vectorCount_pos hu,
    join_mod _ _ _ hu,join_div _ _ _ (by omega : 0<7) hh,join_mod _ _ _ hh,
    join_div _ _ _ hC hc,join_mod _ _ _ hc,join_div _ _ _ (by omega : 0<3) hk,join_mod _ _ _ hk]

theorem pack_unpack (i : ℕ) : D.pack (D.unpack i)=i := by
  simp only [pack,tag,unpack]
  rw [Nat.mul_comm (i/PrefixAlphabet.vectorCount/7/D.channelBound/3) 3,Nat.div_add_mod,
    Nat.mul_comm (i/PrefixAlphabet.vectorCount/7/D.channelBound) D.channelBound,Nat.div_add_mod,
    Nat.mul_comm (i/PrefixAlphabet.vectorCount/7) 7,Nat.div_add_mod,
    Nat.mul_comm (i/PrefixAlphabet.vectorCount) PrefixAlphabet.vectorCount,Nat.div_add_mod]

theorem tag_lt (x : Raw) (hb : x.block<D.blocks) (hk : x.kind<3)
    (hc : x.channel<D.channelBound) (hh : x.height<7) : D.tag x<D.sortBound := by
  have h1 : x.block*3+x.kind<D.blocks*3 := by omega
  have h2 : (x.block*3+x.kind)*D.channelBound+x.channel<(D.blocks*3)*D.channelBound :=
    (Nat.add_lt_add_left hc _).trans_le (by rw [←Nat.succ_mul]; exact Nat.mul_le_mul_right _ h1)
  exact (Nat.add_lt_add_left hh _).trans_le (by rw [←Nat.succ_mul]; exact Nat.mul_le_mul_right _ h2)

theorem pack_lt (x : Raw) (hb : x.block<D.blocks) (hk : x.kind<3)
    (hc : x.channel<D.channelBound) (hh : x.height<7) (hu : x.vector<PrefixAlphabet.vectorCount) :
    D.pack x<D.bound :=
  (Nat.add_lt_add_left hu _).trans_le (by
    change D.tag x*PrefixAlphabet.vectorCount+PrefixAlphabet.vectorCount≤D.sortBound*PrefixAlphabet.vectorCount
    rw [←Nat.succ_mul]
    exact Nat.mul_le_mul_right _ (D.tag_lt x hb hk hc hh))

theorem unpack_bounds (hC : 0<D.channelBound) {i : ℕ} (hi : i<D.bound) :
    (D.unpack i).block<D.blocks ∧ (D.unpack i).kind<3 ∧
      (D.unpack i).channel<D.channelBound ∧ (D.unpack i).height<7 ∧
      (D.unpack i).vector<PrefixAlphabet.vectorCount := by
  refine ⟨?_,Nat.mod_lt _ (by omega),Nat.mod_lt _ hC,Nat.mod_lt _ (by omega),
    Nat.mod_lt _ PrefixAlphabet.vectorCount_pos⟩
  have h1 : i/PrefixAlphabet.vectorCount<D.sortBound :=
    (Nat.div_lt_iff_lt_mul PrefixAlphabet.vectorCount_pos).mpr hi
  have h2 : i/PrefixAlphabet.vectorCount/7<D.blocks*3*D.channelBound :=
    (Nat.div_lt_iff_lt_mul (by omega : 0<7)).mpr h1
  have h3 : i/PrefixAlphabet.vectorCount/7/D.channelBound<D.blocks*3 :=
    (Nat.div_lt_iff_lt_mul hC).mpr h2
  exact (Nat.div_lt_iff_lt_mul (by omega : 0<3)).mpr h3

noncomputable def treeValid (x : Raw) : Bool :=
  decide (D.root x.block x.channel≤x.height ∧ x.height≤D.dimension x.block) &&
    (List.range PrefixAlphabet.vectorCount).any (fun j=>D.legal x.block j &&
      decide (PrefixAlphabet.prefixCode (D.order x.block x.channel) x.height j=x.vector))

noncomputable def validRaw (x : Raw) : Bool := D.validBlock x.block &&
  ((decide (x.kind=0 ∧ x.channel=0 ∧ x.height=0 ∧ x.vector=0)) ||
    (decide (x.kind=1 ∧ x.channel<D.channels x.block ∧ x.height=0) && D.legal x.block x.vector) ||
    (decide (x.kind=2 ∧ x.channel<D.channels x.block) && D.treeValid x))
noncomputable def valid (i : ℕ) : Bool := D.validRaw (D.unpack i)

def sortValid (x : Raw) : Bool := D.validBlock x.block &&
  decide ((x.kind=0 ∧ x.channel=0 ∧ x.height=0) ∨
    (x.kind=1 ∧ x.channel<D.channels x.block ∧ x.height=0) ∨
    (x.kind=2 ∧ x.channel<D.channels x.block ∧ D.root x.block x.channel≤x.height ∧
      x.height≤D.dimension x.block))

end Data

variable {B : Type uVariable4} (P : Presentation B) (F : B → PrefixParts.Data)
variable (hDim : ∀b,(F b).dimension≤6) (ε : Bit)

structure Good (D : Data) : Prop where
  blocks : D.blocks=P.bound
  validBlock : D.validBlock=P.valid
  positive : 0<D.channelBound
  channelBound : ∀b,(F b).channels≤D.channelBound
  dimension : ∀b,D.dimension (P.encode b)=(F b).dimension
  channels : ∀b,D.channels (P.encode b)=(F b).channels
  root : ∀b (c : Fin (F b).channels),D.root (P.encode b) c.val=(F b).root c
  order : ∀b (c : Fin (F b).channels),D.order (P.encode b) c.val=PrefixAlphabet.encodeOrder (hDim b) ((F b).order c)
  legal : ∀b i,D.legal (P.encode b) i=true ↔
    ∃z : (F b).Valuation ε,PrefixAlphabet.encode (hDim b) z.val=i

noncomputable def raw (x : PrefixParts.Wiring.Vertex F ε) : Raw :=
  match x.2 with
  | .inl _ => ⟨P.encode x.1,0,0,0,0⟩
  | .inr (.inl (c,z)) => ⟨P.encode x.1,1,c.val,0,PrefixAlphabet.encode (hDim x.1) z.val⟩
  | .inr (.inr t) => ⟨P.encode x.1,2,t.channel.val,t.height,PrefixAlphabet.encode (hDim x.1) t.bits⟩

@[simp] theorem raw_block (x : PrefixParts.Wiring.Vertex F ε) : (raw P F hDim ε x).block=P.encode x.1 := by
  rcases x with ⟨b,x | (x | x)⟩ <;> rfl

theorem raw_bounds {D : Data} (h : Good P F hDim ε D) (x : PrefixParts.Wiring.Vertex F ε) :
    (raw P F hDim ε x).block<D.blocks ∧ (raw P F hDim ε x).kind<3 ∧
      (raw P F hDim ε x).channel<D.channelBound ∧ (raw P F hDim ε x).height<7 ∧
      (raw P F hDim ε x).vector<PrefixAlphabet.vectorCount := by
  have hb := P.encode_lt x.1
  rw [←h.blocks] at hb
  rcases x with ⟨b,x | (⟨c,z⟩ | t)⟩
  · exact ⟨hb,by change 0<3; omega,h.positive,by change 0<7; omega,PrefixAlphabet.vectorCount_pos⟩
  · exact ⟨hb,by change 1<3; omega,c.isLt.trans_le (h.channelBound b),by change 0<7; omega,PrefixAlphabet.encode_lt (hDim b) z.val⟩
  · have ht := t.val.2.1.isLt
    have hd := hDim b
    exact ⟨hb,by change 2<3; omega,t.channel.isLt.trans_le (h.channelBound b),by dsimp [raw,PrefixParts.Data.Tree.height]; omega,
      PrefixAlphabet.encode_lt (hDim b) t.bits⟩

 theorem raw_valid {D : Data} (h : Good P F hDim ε D) (x : PrefixParts.Wiring.Vertex F ε) :
    D.validRaw (raw P F hDim ε x)=true := by
  have hb : D.validBlock (P.encode x.1)=true := h.validBlock ▸ P.encode_valid x.1
  rcases x with ⟨b,x | (⟨c,z⟩ | t)⟩
  · simp only [raw,Data.validRaw,hb,Bool.true_and,and_self,decide_true,Bool.true_or]
  · have hz := (h.legal b (PrefixAlphabet.encode (hDim b) z.val)).mpr ⟨z,rfl⟩
    simp only [raw,Data.validRaw,hb,Bool.true_and,h.channels,one_ne_zero,false_and,
      decide_false,Bool.false_or,true_and,c.isLt,and_true,decide_true,Bool.true_and,hz,Bool.true_or]
  · apply Bool.and_eq_true_iff.mpr ⟨hb,?_⟩
    apply Bool.or_eq_true_iff.mpr
    right
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by simp only [raw,h.channels,t.channel.isLt,and_self,decide_true],?_⟩
    change D.treeValid ⟨P.encode b,2,t.channel.val,t.height,PrefixAlphabet.encode (hDim b) t.bits⟩=true
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by exact decide_eq_true (show D.root (P.encode b) t.channel.val≤t.height ∧
      t.height≤D.dimension (P.encode b) from ⟨(h.root b t.channel) ▸ t.property.1,
        (h.dimension b) ▸ Nat.le_of_lt_succ t.val.2.1.isLt⟩),?_⟩
    obtain ⟨z,hz⟩ := t.property.2
    apply List.any_eq_true.mpr
    refine ⟨PrefixAlphabet.encode (hDim b) z.val,List.mem_range.mpr (PrefixAlphabet.encode_lt _ _),?_⟩
    apply Bool.and_eq_true_iff.mpr
    refine ⟨(h.legal b _).mpr ⟨z,rfl⟩,?_⟩
    rw [h.order,PrefixAlphabet.prefix_encode,hz]
    exact decide_eq_true rfl

end VariableWL.PrefixDescriptor

end OAI
