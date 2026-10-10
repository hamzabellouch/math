import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Basic2
import OAI.Combinatorics.KMedianRecovery.Strictness.IndexedPaymentCoeff

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RatOps
noncomputable def ifNatEq {f g : List Bool → List Bool} {p q : List Bool → ℚ}
    (hf : PolyComputes f) (hg : PolyComputes g)
    (hp : PolyComputes (fun x=>BinaryRational.encode (p x)))
    (hq : PolyComputes (fun x=>BinaryRational.encode (q x))) :
    PolyComputes (fun x=>BinaryRational.encode (if value (f x)=value (g x) then p x else q x)) := by
  have hh := (NatOps.eq hf hg).cond hp hq
  simpa only [decide_eq_true_eq,apply_ite] using hh
end RatOps
namespace BinaryOpeningCoefficient
open WordList RationalLinearFeasibility RationalOpenability

def variableWord {m d : ℕ} {F : Finset (Fin m)} : Variables (Fin d) F → List Bool
  | .inl j=>encode [(0:ℕ).bits,j.val.bits]
  | .inr (f,a,j)=>encode [(1:ℕ).bits,f.val.val.bits,a.val.bits,j.val.bits]
def col (k : ℕ) : List Bool → List Bool := BinaryOpeningPayment.field k ∘ discardPrefix
noncomputable def col_computes (k : ℕ) : PolyComputes (col k) :=
  discardPrefix_computes.comp (BinaryOpeningPayment.field_computes k)
def row (k : ℕ) : List Bool → List Bool := BinaryOpeningConstant.field k ∘ extractPrefix
noncomputable def row_computes (k : ℕ) : PolyComputes (row k) :=
  extractPrefix_computes.comp (BinaryOpeningConstant.field_computes k)
noncomputable def chooseEq {f g : List Bool → ℚ} (k l : ℕ)
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>BinaryRational.encode (if value (col k x)=value (row l x) then f x else g x)) :=
  RatOps.ifNatEq (col_computes k) (row_computes l) hf hg
noncomputable def chooseColTag {f g : List Bool → ℚ} (k : ℕ)
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>BinaryRational.encode (if value (col 0 x)=k then f x else g x)) := by
  have hh := RatOps.ifNatEq (col_computes 0) (const_computes k.bits) hf hg
  convert hh using 1
  funext x
  rw [value_bits]
noncomputable def chooseTag {f g : List Bool → ℚ} (k : ℕ)
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>BinaryRational.encode (if BinaryOpeningConstant.tag (extractPrefix x)=k then f x else g x)) := by
  have hh := (extractPrefix_computes.comp (BinaryOpeningConstant.tag_eq_computes k)).cond hf hg
  simpa only [Function.comp_def,decide_eq_true_eq,apply_ite] using hh
noncomputable def chooseActive {f g : List Bool → ℚ} (k : ℕ)
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>BinaryRational.encode (if BinaryOpeningConstant.active k (extractPrefix x) then f x else g x)) := by
  have hh := (extractPrefix_computes.comp (BinaryOpeningConstant.active_computes k)).cond hf hg
  simpa only [Function.comp_def,apply_ite] using hh
noncomputable def chooseNear {f g : List Bool → ℚ}
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>BinaryRational.encode (if BinaryOpeningConstant.near (extractPrefix x) then f x else g x)) := by
  have hh := (extractPrefix_computes.comp BinaryOpeningConstant.near_computes).cond hf hg
  simpa only [Function.comp_def,decide_eq_true_eq,apply_ite] using hh

def bid (j : ℕ) (x : List Bool) : ℚ :=
  if value (col 0 x)=0 then if value (col 1 x)=value (row j x) then 1 else 0 else 0
noncomputable def bid_computes (j : ℕ) : PolyComputes (fun x=>BinaryRational.encode (bid j x)) :=
  chooseColTag 0 (chooseEq 1 j (RatOps.const 1) (RatOps.const 0)) (RatOps.const 0)
def slack (x : List Bool) : ℚ :=
  if value (col 0 x)=1 then if value (col 1 x)=value (row 2 x) then
    if value (col 2 x)=value (row 3 x) then if value (col 3 x)=value (row 1 x) then 1 else 0 else 0 else 0 else 0
noncomputable def slack_computes : PolyComputes (fun x=>BinaryRational.encode (slack x)) :=
  chooseColTag 1
    (chooseEq 1 2 (chooseEq 2 3 (chooseEq 3 1 (RatOps.const 1) (RatOps.const 0)) (RatOps.const 0)) (RatOps.const 0))
    (RatOps.const 0)
def dual (x : List Bool) : ℚ :=
  if value (col 0 x)=1 then if value (col 1 x)=value (row 2 x) then
    if value (col 2 x)=value (row 1 x) then 1 else 0 else 0 else 0
noncomputable def dual_computes : PolyComputes (fun x=>BinaryRational.encode (dual x)) :=
  chooseColTag 1 (chooseEq 1 2 (chooseEq 2 1 (RatOps.const 1) (RatOps.const 0)) (RatOps.const 0)) (RatOps.const 0)

def paymentQuery (x : List Bool) : List Bool := pairBits (extractPrefix (extractPrefix x),col 1 x)
noncomputable def paymentQuery_computes : PolyComputes paymentQuery :=
  (extractPrefix_computes.comp extractPrefix_computes).pair (col_computes 1)
noncomputable def paymentNear (x : List Bool) : Prop :=
  BinaryOpeningPayment.distance (paymentQuery x)≤
    BinaryOpeningPayment.paramV (paymentQuery x)*BinaryOpeningPayment.paramZ (paymentQuery x)
noncomputable instance paymentNearDecidable (x : List Bool) : Decidable (paymentNear x) := inferInstanceAs (Decidable (_≤_))
noncomputable def paymentNear_computes : PolyComputes (fun x=>[decide (paymentNear x)]) := by
  have distanceComputes : PolyComputes
      (fun input=>BinaryRational.encode (BinaryOpeningPayment.distance (paymentQuery input))) := by
    simpa only [Function.comp_def] using
      (PolyComputes.comp (f:=paymentQuery)
        (g:=fun input=>BinaryRational.encode (BinaryOpeningPayment.distance input))
        paymentQuery_computes BinaryOpeningPayment.distance_computes)
  have paramVComputes : PolyComputes
      (fun input=>BinaryRational.encode (BinaryOpeningPayment.paramV (paymentQuery input))) := by
    simpa only [Function.comp_def] using
      (PolyComputes.comp (f:=paymentQuery)
        (g:=fun input=>BinaryRational.encode (BinaryOpeningPayment.paramV input))
        paymentQuery_computes BinaryOpeningPayment.paramV_computes)
  have paramZComputes : PolyComputes
      (fun input=>BinaryRational.encode (BinaryOpeningPayment.paramZ (paymentQuery input))) := by
    simpa only [Function.comp_def] using
      (PolyComputes.comp (f:=paymentQuery)
        (g:=fun input=>BinaryRational.encode (BinaryOpeningPayment.paramZ input))
        paymentQuery_computes BinaryOpeningPayment.paramZ_computes)
  unfold paymentNear
  exact RatOps.le distanceComputes (RatOps.mul paramVComputes paramZComputes)
noncomputable def payment (x : List Bool) : ℚ :=
  if value (col 0 x)=0 then if BinaryOpeningPayment.active (paymentQuery x) then
    if paymentNear x then 1 else 0 else 0 else 0
noncomputable def payment_computes : PolyComputes (fun x=>BinaryRational.encode (payment x)) := by
  have hn : PolyComputes (fun x=>BinaryRational.encode (if paymentNear x then (1:ℚ) else 0)) := by
    have hh := paymentNear_computes.cond (RatOps.const 1) (RatOps.const 0)
    simpa only [decide_eq_true_eq,apply_ite] using hh
  have ha := (paymentQuery_computes.comp BinaryOpeningPayment.active_computes).cond hn (RatOps.const 0)
  have ha' : PolyComputes (fun x=>BinaryRational.encode (if BinaryOpeningPayment.active (paymentQuery x) then
      if paymentNear x then (1:ℚ) else 0 else 0)) := by
    simpa only [Function.comp_def,apply_ite] using ha
  exact chooseColTag 0 ha' (RatOps.const 0)

noncomputable def coefficient (x : List Bool) : ℚ :=
  if BinaryOpeningConstant.tag (extractPrefix x)=0 then
    if BinaryOpeningConstant.active 1 (extractPrefix x) then -bid 1 x else 0
  else if BinaryOpeningConstant.tag (extractPrefix x)=1 then
    if BinaryOpeningConstant.active 1 (extractPrefix x) then bid 1 x else 0
  else if BinaryOpeningConstant.tag (extractPrefix x)=2 then
    if BinaryOpeningConstant.active 1 (extractPrefix x) then bid 1 x else 0
  else if BinaryOpeningConstant.tag (extractPrefix x)=3 then
    if BinaryOpeningConstant.active 1 (extractPrefix x) then
      if BinaryOpeningConstant.near (extractPrefix x) then 0 else bid 1 x else 0
  else if BinaryOpeningConstant.tag (extractPrefix x)=4 then -payment x
  else if BinaryOpeningConstant.tag (extractPrefix x)=5 then
    if BinaryOpeningConstant.active 3 (extractPrefix x) then -slack x else 0
  else if BinaryOpeningConstant.tag (extractPrefix x)=6 then
    if BinaryOpeningConstant.active 3 (extractPrefix x) then
      (if BinaryOpeningConstant.active 1 (extractPrefix x) then bid 1 x else bid 3 x) - slack x else 0
  else if BinaryOpeningConstant.tag (extractPrefix x)=7 then
    if BinaryOpeningConstant.active 1 (extractPrefix x) then dual x else 0
  else 0
noncomputable def coefficient_computes : PolyComputes (fun x=>BinaryRational.encode (coefficient x)) :=
  chooseTag 0 (chooseActive 1 (RatOps.neg (bid_computes 1)) (RatOps.const 0))
  (chooseTag 1 (chooseActive 1 (bid_computes 1) (RatOps.const 0))
  (chooseTag 2 (chooseActive 1 (bid_computes 1) (RatOps.const 0))
  (chooseTag 3 (chooseActive 1 (chooseNear (RatOps.const 0) (bid_computes 1)) (RatOps.const 0))
  (chooseTag 4 (RatOps.neg payment_computes)
  (chooseTag 5 (chooseActive 3 (RatOps.neg slack_computes) (RatOps.const 0))
  (chooseTag 6 (chooseActive 3 (RatOps.sub (chooseActive 1 (bid_computes 1) (bid_computes 3)) slack_computes) (RatOps.const 0))
  (chooseTag 7 (chooseActive 1 dual_computes (RatOps.const 0)) (RatOps.const 0))))))))

lemma coefficient_indexed {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) (r : Kind (Fin d) W F) (u : Variables (Fin d) F) :
    coefficient (pairBits (pairBits (BinaryOpeningPayment.pack distances F W v z lam eta i,
      BinaryOpeningConstant.kindWord r),variableWord u))=
      EffectiveOpenability.indexedCoeff distances F W v z i r u := by
  have hparam (j : List Bool) : BinaryOpeningPayment.paramV
      (pairBits (BinaryOpeningPayment.pack distances F W v z lam eta i,j))=v ∧
      BinaryOpeningPayment.paramZ (pairBits (BinaryOpeningPayment.pack distances F W v z lam eta i,j))=z := by
    simp only [BinaryOpeningPayment.paramV,BinaryOpeningPayment.paramZ,BinaryOpeningPayment.itemField,
      Function.comp_apply,extractPrefix_pairBits,BinaryOpeningPayment.pack,BinaryOpeningPayment.field_encode,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryRational.decode_encode,and_self]
  rcases u with b|⟨g,b,c⟩ <;> cases r <;>
    simp only [coefficient,extractPrefix_pairBits,BinaryOpeningConstant.tag,
      BinaryOpeningConstant.field,Function.comp_apply,discardPrefix_pairBits,BinaryOpeningConstant.kindWord,
      BinaryOpeningPayment.field_encode,List.getElem?_cons_zero,Option.getD_some,value_bits] <;> norm_num only
  all_goals (try simp only [ite_true,ite_false])
  all_goals (try simp only [BinaryOpeningConstant.near,BinaryOpeningConstant.active,BinaryOpeningConstant.query,
      BinaryOpeningConstant.field,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
      BinaryOpeningPayment.field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
      BinaryOpeningPayment.active_pack,BinaryOpeningPayment.distance_pack,decide_eq_true_eq,(hparam _).1,(hparam _).2])
  all_goals (try simp only [bid,slack,dual,payment,paymentNear,paymentQuery,col,row,variableWord,
      BinaryOpeningConstant.field,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
      BinaryOpeningPayment.field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
      value_bits,BinaryOpeningPayment.active_pack,BinaryOpeningPayment.distance_pack,decide_eq_true_eq,
      (hparam _).1,(hparam _).2])
  all_goals (try simp only [EffectiveOpenability.indexedCoeff,EffectiveOpenability.indexedPaymentCoeff,
      EffectiveOpenability.indexedDualCoeff])
  all_goals simp [Fin.val_inj,Prod.mk.injEq]
  all_goals (try split_ifs)
  all_goals simp_all

lemma coefficient_source {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) (r : Kind (Fin d) W F) (u : Variables (Fin d) F) :
    coefficient (pairBits (pairBits (BinaryOpeningPayment.pack distances F W v z lam eta i,
      BinaryOpeningConstant.kindWord r),variableWord u))=
      (EffectiveOpenability.forms distances F W v z lam eta i r).coeff u := by
  rw [coefficient_indexed,EffectiveOpenability.indexedCoeff_eq]
end BinaryOpeningCoefficient
end MetricKMedianRecovery.BitMachine

end OAI
