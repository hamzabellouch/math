import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Values

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace NatOps
noncomputable def eq {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>[decide (value (f x)=value (g x))]) := by
  have hh := (le hf hg).cond (le hg hf) (const_computes [false])
  convert hh using 1
  funext x
  by_cases h : value (f x)≤value (g x)
  · simp only [decide_eq_true_eq,h,ite_true]
    congr 1
    apply decide_eq_decide.mpr
    omega
  · simp only [decide_eq_true_eq,h,ite_false]
    simp only [List.cons.injEq,and_true,decide_eq_false_iff_not]
    omega
end NatOps
namespace BinaryOpeningConstant
open WordList RationalLinearFeasibility RationalOpenability

def kindWord {m d : ℕ} {F W : Finset (Fin m)} : Kind (Fin d) W F → List Bool
  | .lower j=>encode [(0:ℕ).bits,j.val.bits]
  | .upper j=>encode [(1:ℕ).bits,j.val.bits]
  | .cap j f=>encode [(2:ℕ).bits,j.val.bits,f.val.val.bits]
  | .far j=>encode [(3:ℕ).bits,j.val.bits]
  | .payment=>encode [(4:ℕ).bits]
  | .slackZero f a j=>encode [(5:ℕ).bits,j.val.bits,f.val.val.bits,a.val.bits]
  | .slackTerm f a j=>encode [(6:ℕ).bits,j.val.bits,f.val.val.bits,a.val.bits]
  | .dual f a=>encode [(7:ℕ).bits,a.val.bits,f.val.val.bits]
def field (k : ℕ) : List Bool → List Bool := BinaryOpeningPayment.field k ∘ discardPrefix
noncomputable def field_computes (k : ℕ) : PolyComputes (field k) :=
  discardPrefix_computes.comp (BinaryOpeningPayment.field_computes k)
def query (k : ℕ) (x : List Bool) : List Bool := pairBits (extractPrefix x,field k x)
noncomputable def query_computes (k : ℕ) : PolyComputes (query k) := extractPrefix_computes.pair (field_computes k)
noncomputable def active (k : ℕ) (x : List Bool) : Bool := BinaryOpeningPayment.active (query k x)
noncomputable def active_computes (k : ℕ) : PolyComputes (fun x=>[active k x]) :=
  (query_computes k).comp BinaryOpeningPayment.active_computes
noncomputable def distanceWords (f j : ℕ) (x : List Bool) : List Bool :=
  MetricTable.get (pairBits (pairBits (BinaryOpeningPayment.itemField 0 x,field f x),field j x))
noncomputable def distanceWords_computes (f j : ℕ) : PolyComputes (distanceWords f j) := by
  unfold distanceWords
  simpa only [Function.comp_def] using
    (PolyComputes.comp
      (f:=fun input=>pairBits (pairBits (BinaryOpeningPayment.itemField 0 input,field f input),field j input))
      (g:=MetricTable.get)
      (((BinaryOpeningPayment.itemField_computes 0).pair (field_computes f)).pair (field_computes j))
      MetricTable.get_computes)
noncomputable def distance (f j : ℕ) (x : List Bool) : ℚ := BinaryRational.decode (distanceWords f j x)
noncomputable def distance_computes (f j : ℕ) : PolyComputes (fun x=>BinaryRational.encode (distance f j x)) :=
  RatOps.ofWords (distanceWords_computes f j)
def tag (x : List Bool) : ℕ := value (field 0 x)
noncomputable def tag_eq_computes (k : ℕ) : PolyComputes (fun x=>[decide (tag x=k)]) := by
  have hh := NatOps.eq (field_computes 0) (const_computes k.bits)
  convert hh using 1
  funext x
  congr 1
  apply decide_eq_decide.mpr
  simp only [tag,value_bits]
noncomputable def chooseTag {f g : List Bool → ℚ} (k : ℕ)
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>BinaryRational.encode (if tag x=k then f x else g x)) := by
  have hh := (tag_eq_computes k).cond hf hg
  simpa only [decide_eq_true_eq,apply_ite] using hh
noncomputable def chooseActive {f g : List Bool → ℚ} (k : ℕ)
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>BinaryRational.encode (if active k x then f x else g x)) := by
  have hh := (active_computes k).cond hf hg
  simpa only [apply_ite] using hh
noncomputable def near (x : List Bool) : Prop :=
  BinaryOpeningPayment.distance (query 1 x)≤BinaryOpeningPayment.paramV x*BinaryOpeningPayment.paramZ x
noncomputable instance nearDecidable (x : List Bool) : Decidable (near x) :=
  inferInstanceAs (Decidable (_≤_))
noncomputable def near_computes : PolyComputes (fun x=>[decide (near x)]) := by
  have distanceComputes : PolyComputes
      (fun input=>BinaryRational.encode (BinaryOpeningPayment.distance (query 1 input))) := by
    simpa only [Function.comp_def] using
      (PolyComputes.comp (f:=query 1)
        (g:=fun input=>BinaryRational.encode (BinaryOpeningPayment.distance input))
        (query_computes 1) BinaryOpeningPayment.distance_computes)
  unfold near
  exact RatOps.le distanceComputes
    (RatOps.mul BinaryOpeningPayment.paramV_computes BinaryOpeningPayment.paramZ_computes)
noncomputable def constant (x : List Bool) : ℚ :=
  if tag x=0 then if active 1 x then BinaryOpeningPayment.paramZ x else 0
  else if tag x=1 then if active 1 x then -((1+BinaryOpeningPayment.paramV x*BinaryOpeningPayment.paramV x)*BinaryOpeningPayment.paramZ x) else 0
  else if tag x=2 then if active 1 x then -(BinaryOpeningPayment.scale x*distance 2 1 x) else 0
  else if tag x=3 then if active 1 x then if near x then 0 else -BinaryOpeningPayment.paramZ x else 0
  else if tag x=4 then BinaryRational.decode (BinaryOpeningPayment.run (extractPrefix x))
  else if tag x=6 then if active 3 x then
    if active 1 x then -distance 2 1 x else -(2*distance 2 1 x+distance 2 3 x) else 0
  else if tag x=7 then if active 1 x then -BinaryRational.decode (BinaryOpeningPayment.itemField 4 x) else 0
  else 0
noncomputable def constant_computes : PolyComputes (fun x=>BinaryRational.encode (constant x)) := by
  have hz := BinaryOpeningPayment.paramZ_computes
  have hv := BinaryOpeningPayment.paramV_computes
  have h0 := RatOps.const 0
  have hn : PolyComputes (fun x=>BinaryRational.encode (if near x then 0 else -BinaryOpeningPayment.paramZ x)) := by
    have hh := near_computes.cond h0 (RatOps.neg hz)
    simpa only [decide_eq_true_eq,apply_ite] using hh
  exact chooseTag 0 (chooseActive 1 hz h0)
    (chooseTag 1 (chooseActive 1 (RatOps.neg (RatOps.mul (RatOps.add (RatOps.const 1) (RatOps.mul hv hv)) hz)) h0)
    (chooseTag 2 (chooseActive 1 (RatOps.neg (RatOps.mul BinaryOpeningPayment.scale_computes (distance_computes 2 1))) h0)
    (chooseTag 3 (chooseActive 1 hn h0)
    (chooseTag 4 (RatOps.ofWords (extractPrefix_computes.comp BinaryOpeningPayment.run_computes))
    (chooseTag 6 (chooseActive 3
      (chooseActive 1 (RatOps.neg (distance_computes 2 1))
        (RatOps.neg (RatOps.add (RatOps.mul (RatOps.const 2) (distance_computes 2 1)) (distance_computes 2 3)))) h0)
    (chooseTag 7 (chooseActive 1 (RatOps.neg (RatOps.ofWords (BinaryOpeningPayment.itemField_computes 4))) h0) h0))))))

lemma constant_source {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) (r : Kind (Fin d) W F) :
    constant (pairBits (BinaryOpeningPayment.pack distances F W v z lam eta i,kindWord r))=
      (EffectiveOpenability.forms distances F W v z lam eta i r).constant := by
  have hparam (j : List Bool) : BinaryOpeningPayment.paramV
      (pairBits (BinaryOpeningPayment.pack distances F W v z lam eta i,j))=v ∧
      BinaryOpeningPayment.paramZ (pairBits (BinaryOpeningPayment.pack distances F W v z lam eta i,j))=z ∧
      BinaryRational.decode (BinaryOpeningPayment.itemField 4
        (pairBits (BinaryOpeningPayment.pack distances F W v z lam eta i,j)))=lam := by
    simp only [BinaryOpeningPayment.paramV,BinaryOpeningPayment.paramZ,BinaryOpeningPayment.itemField,
      Function.comp_apply,extractPrefix_pairBits,BinaryOpeningPayment.pack,BinaryOpeningPayment.field_encode,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryRational.decode_encode,and_self]
  cases r <;>
    simp only [kindWord,constant,tag,field,Function.comp_apply,discardPrefix_pairBits,
      BinaryOpeningPayment.field_encode,List.getElem?_cons_zero,
      Option.getD_some,value_bits] <;> norm_num only
  all_goals (try simp only [ite_true,ite_false])
  all_goals (try simp only [near,active,query,field,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
      BinaryOpeningPayment.field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some,BinaryOpeningPayment.active_pack,decide_eq_true_eq])
  all_goals (try simp only [BinaryOpeningPayment.scale,(hparam _).1,(hparam _).2.1,(hparam _).2.2])
  all_goals (try simp only [BinaryOpeningPayment.distance_pack,BinaryOpeningPayment.run_source,BinaryRational.decode_encode])
  all_goals (try simp only [EffectiveOpenability.forms,EffectiveOpenability.dual,Form.const,Form.sub,
      EffectiveOpenability.bid,Form.coord,zero_sub])
  all_goals (try simp only [distance,distanceWords,field,Function.comp_apply,discardPrefix_pairBits,
      BinaryOpeningPayment.itemField,extractPrefix_pairBits,BinaryOpeningPayment.pack,
      BinaryOpeningPayment.field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some,MetricTable.get_pack,BinaryRational.decode_encode,pow_two,Form.sum])
  all_goals (try split_ifs)
  all_goals simp_all [EffectiveOpenability.slack,Form.coord]
  all_goals linarith

end BinaryOpeningConstant
end MetricKMedianRecovery.BitMachine

end OAI
