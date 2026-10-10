import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.ColorLabelMachine

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMenu
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
def code (kind j : ℕ) : List Bool := pairBits (kind.bits,List.replicate j true)
noncomputable def kind (x : List Bool) : ℕ := value (extractPrefix (discardPrefix x))
noncomputable def exponent (x : List Bool) : List Bool := discardPrefix (discardPrefix x)
noncomputable def exponent_computes : PolyComputes exponent := discardPrefix_computes.comp discardPrefix_computes
noncomputable def index (x : List Bool) : List Bool := UnaryResources.lengthBits (exponent x)
noncomputable def index_computes : PolyComputes index := exponent_computes.comp UnaryResources.lengthBits_computes
lemma index_pair (ctx : List Bool) (kind j : ℕ) : index (pairBits (ctx,code kind j))=j.bits := by
  simp only [index,exponent,code,discardPrefix_pairBits,UnaryResources.lengthBits_eq,List.length_replicate]
lemma kind_pair (ctx : List Bool) (k j : ℕ) : kind (pairBits (ctx,code k j))=k := by
  simp only [kind,code,extractPrefix_pairBits,discardPrefix_pairBits,value_bits]
noncomputable def relative (x : List Bool) : Bool := decide (kind x=1)
noncomputable def relative_computes : PolyComputes (fun x=>[relative x]) :=
  NatOps.eq (discardPrefix_computes.comp extractPrefix_computes) (const_computes (1:ℕ).bits)
noncomputable def first (x : List Bool) : Bool := decide (kind x=0)
noncomputable def first_computes : PolyComputes (fun x=>[first x]) :=
  NatOps.eq (discardPrefix_computes.comp extractPrefix_computes) (const_computes (0:ℕ).bits)
def weights (M E J : ℕ) : List Bool := encode [List.replicate M true,List.replicate E true,List.replicate J true]
noncomputable def denominator (i : ℕ) (x : List Bool) : List Bool := UnaryResources.lengthBits (field i (extractPrefix x))
attribute [local irreducible] UnaryResources.lengthBits
noncomputable def denominator_computes (i : ℕ) : PolyComputes (denominator i) := by
  unfold denominator
  exact (extractPrefix_computes.comp (field_computes i)).comp UnaryResources.lengthBits_computes
noncomputable def halfNumerator (x : List Bool) : List Bool := BinaryRationalPower.run
  (pairBits (exponent x++[true],BinaryRational.encode (1/2)))
noncomputable def halfNumerator_computes : PolyComputes halfNumerator :=
  ((exponent_computes.append (const_computes [true])).pair (const_computes (BinaryRational.encode (1/2)))).comp BinaryRationalPower.run_computes
noncomputable def halfNormalizer (x : List Bool) : List Bool := BinaryRationalPower.run
  (pairBits (field 2 (extractPrefix x),BinaryRational.encode (1/2)))
noncomputable def halfNormalizer_computes : PolyComputes halfNormalizer :=
  ((extractPrefix_computes.comp (field_computes 2)).pair (const_computes (BinaryRational.encode (1/2)))).comp BinaryRationalPower.run_computes
noncomputable def weight (x : List Bool) : ℚ :=
  if first x then 1/(3*(value (denominator 0 x):ℚ))
  else if relative x then 1/(3*((value (denominator 1 x):ℚ)+1))
  else (1/3)*(BinaryRational.decode (halfNumerator x)/(1-BinaryRational.decode (halfNormalizer x)))
noncomputable def weight_computes : PolyComputes (fun x=>BinaryRational.encode (weight x)) := by
  have hh := first_computes.cond (RatOps.div (RatOps.const 1) (RatOps.mul (RatOps.const 3) (RatOps.nat (denominator_computes 0))))
    (relative_computes.cond (RatOps.div (RatOps.const 1) (RatOps.mul (RatOps.const 3)
      (RatOps.add (RatOps.nat (denominator_computes 1)) (RatOps.const 1))))
      (RatOps.mul (RatOps.const (1/3)) (RatOps.div (RatOps.ofWords halfNumerator_computes)
        (RatOps.sub (RatOps.const 1) (RatOps.ofWords halfNormalizer_computes)))))
  convert hh using 1
  funext x
  unfold weight
  split_ifs <;> rfl
lemma weight_pair (M E J k j : ℕ) : weight (pairBits (weights M E J,code k j))=
    if k=0 then 1/(3*(M:ℚ)) else if k=1 then 1/(3*((E:ℚ)+1))
    else (1/3)*((1/2:ℚ)^(j+1)/(1-(1/2:ℚ)^J)) := by
  have hp : exponent (pairBits (weights M E J,code k j))++[true]=List.replicate (j+1) true := by
    simp only [exponent,code,discardPrefix_pairBits,List.replicate_succ']
  simp only [weight,first,relative,kind_pair,decide_eq_true_eq,denominator,
    extractPrefix_pairBits,weights,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    UnaryResources.lengthBits_eq,List.length_replicate,value_bits,halfNumerator,halfNormalizer]
  dsimp only [weights] at hp
  rw [hp]
  rw [show pairBits (List.replicate (j+1) true,BinaryRational.encode (1/2))=BinaryRationalPower.pack (1/2) (j+1) from rfl,
    BinaryRationalPower.run_pack]
  rw [show pairBits (List.replicate J true,BinaryRational.encode (1/2))=BinaryRationalPower.pack (1/2) J from rfl,
    BinaryRationalPower.run_pack]
  simp only [BinaryRational.decode_encode]
def optBits (o : Option ℚ) : List Bool := encode (o.toList.map BinaryRational.encode)
def radii (κ pop : ℚ) (near : Option ℚ) : List Bool := encode [BinaryRational.encode κ,BinaryRational.encode pop,optBits near]
noncomputable def denominatorPower (x : List Bool) : List Bool := BinaryRationalPower.run (pairBits (exponent x,
  BinaryRational.encode (1+BinaryRational.decode (field 0 (extractPrefix x)))))
noncomputable def denominatorPower_computes : PolyComputes denominatorPower :=
  (exponent_computes.pair (RatOps.add (RatOps.const 1) (RatOps.ofWords (extractPrefix_computes.comp (field_computes 0))))).comp BinaryRationalPower.run_computes
noncomputable def divide (x : List Bool) : List Bool := BinaryRational.encode
  (BinaryRational.decode (discardPrefix x)/BinaryRational.decode (extractPrefix x))
noncomputable def divide_computes : PolyComputes divide := RatOps.div (RatOps.ofWords discardPrefix_computes) (RatOps.ofWords extractPrefix_computes)
noncomputable def uniformRadius (x : List Bool) : ℚ :=
  (value (index x)+1)*BinaryRational.decode (field 0 (extractPrefix x))*BinaryRational.decode (field 1 (extractPrefix x))
noncomputable def uniformRadius_computes : PolyComputes (fun x=>BinaryRational.encode (uniformRadius x)) :=
  RatOps.mul (RatOps.mul (RatOps.add (RatOps.nat index_computes) (RatOps.const 1))
    (RatOps.ofWords (extractPrefix_computes.comp (field_computes 0))))
    (RatOps.ofWords (extractPrefix_computes.comp (field_computes 1)))
noncomputable def radius (x : List Bool) : List Bool :=
  if relative x then mapWith divide (pairBits (denominatorPower x,field 2 (extractPrefix x)))
  else encode [BinaryRational.encode (uniformRadius x)]
attribute [local irreducible] mapWith
noncomputable def radius_computes : PolyComputes radius := by
  unfold radius
  exact relative_computes.cond
    ((denominatorPower_computes.pair (extractPrefix_computes.comp (field_computes 2))).comp (mapWith_computes divide_computes))
    (cons_computes uniformRadius_computes (const_computes []))
lemma radius_pair (κ pop : ℚ) (near : Option ℚ) (k j : ℕ) :
    radius (pairBits (radii κ pop near,code k j))=
      optBits (if k=1 then near.map (fun r=>r/(1+κ)^j) else some ((j+1)*κ*pop)) := by
  have hd : denominatorPower (pairBits (radii κ pop near,code k j))=BinaryRational.encode ((1+κ)^j) := by
    simp only [denominatorPower,exponent,code,discardPrefix_pairBits,extractPrefix_pairBits,radii,field_encode,
      List.getElem?_cons_zero,Option.getD_some,BinaryRational.decode_encode]
    exact BinaryRationalPower.run_pack (1+κ) j
  simp only [radius,relative,kind_pair,decide_eq_true_eq]
  split_ifs with hk
  · rw [hd]
    simp only [radii,extractPrefix_pairBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
      optBits,mapWith_encode,List.map_map,Function.comp_def,divide,extractPrefix_pairBits,discardPrefix_pairBits,
      BinaryRational.decode_encode,Option.toList_map]
  · simp only [uniformRadius,index_pair,value_bits,radii,extractPrefix_pairBits,field_encode,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some,BinaryRational.decode_encode,optBits,Option.toList_some,List.map_cons,List.map_nil]
end MetricKMedianRecovery.BitMachine.BinaryMenu

end OAI
