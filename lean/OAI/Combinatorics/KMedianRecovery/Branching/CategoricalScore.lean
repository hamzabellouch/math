import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.TableValue
import OAI.Combinatorics.KMedianRecovery.Branching.CategoricalTable

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a T L : ℕ}
def elemBits {q : ℕ} (e : Fin q) : List Bool := e.val.bits
def partBits (part : Fin q→Fin a) : List Bool := encode (List.ofFn (fun e=>(part e).val.bits))
def oracleBits (seed : Categorical.OracleSeed (Fin q) a T L) : List Bool :=
  encode (List.ofFn (fun e=>encode (List.ofFn (fun l=>seedBits (seed e l)))))
def scorePack (ctx : List Bool) (part : Fin q→Fin a) (r : Fin a→Fin T→Option (Fin q))
    (seed : Categorical.OracleSeed (Fin q) a T L) : List Bool :=
  encode [ctx,tableBits elemBits r,oracleBits seed,partBits part]
noncomputable def elementPart (x : List Bool) : List Bool :=
  Lookup.run (pairBits (discardPrefix x,field 3 (extractPrefix x)))
noncomputable def elementPart_computes : PolyComputes elementPart :=
  (discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 3))).comp Lookup.run_computes
noncomputable def elementSamples (x : List Bool) : List Bool :=
  Lookup.run (pairBits (discardPrefix x,field 2 (extractPrefix x)))
noncomputable def elementSamples_computes : PolyComputes elementSamples :=
  (discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 2))).comp Lookup.run_computes
noncomputable def marginalDraw (x : List Bool) : List Bool :=
  draw (encode [field 1 (extractPrefix (extractPrefix x)),discardPrefix x,elementPart (extractPrefix x)])
noncomputable def marginalDraw_computes : PolyComputes marginalDraw :=
  (cons_computes ((extractPrefix_computes.comp extractPrefix_computes).comp (field_computes 1))
    (cons_computes discardPrefix_computes (cons_computes (extractPrefix_computes.comp elementPart_computes)
      (const_computes [])))).comp draw_computes
noncomputable def marginal (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  BinaryRational.encode (BinaryRational.decode (g (pairBits (field 0 (extractPrefix (extractPrefix x)),
      cons (discardPrefix (extractPrefix x)) (marginalDraw x))))-
    BinaryRational.decode (g (pairBits (field 0 (extractPrefix (extractPrefix x)),marginalDraw x))))
noncomputable def marginal_computes {g : List Bool→List Bool} (hg : PolyComputes g) : PolyComputes (marginal g) :=
  RatOps.sub (RatOps.ofWords ((((extractPrefix_computes.comp extractPrefix_computes).comp (field_computes 0)).pair
    (cons_computes (extractPrefix_computes.comp discardPrefix_computes) marginalDraw_computes)).comp hg))
    (RatOps.ofWords ((((extractPrefix_computes.comp extractPrefix_computes).comp (field_computes 0)).pair
      marginalDraw_computes).comp hg))
noncomputable def marginalValues (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  mapWith (marginal g) (pairBits (x,elementSamples x))
attribute [local irreducible] mapWith
noncomputable def marginalValues_computes {g : List Bool→List Bool} (hg : PolyComputes g) : PolyComputes (marginalValues g) := by
  unfold marginalValues
  exact (id_computes.pair elementSamples_computes).comp (mapWith_computes (marginal_computes hg))
noncomputable def score (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  BinaryRational.encode (BinaryRational.decode (RationalArray.sumWords (marginalValues g x)) /
    (value (UnaryResources.lengthBits (Count.run (elementSamples x))):ℚ))
noncomputable def score_computes {g : List Bool→List Bool} (hg : PolyComputes g) : PolyComputes (score g) :=
  RatOps.div (RatOps.ofWords ((marginalValues_computes hg).comp RationalArray.sumWords_computes))
    (RatOps.nat ((elementSamples_computes.comp Count.run_computes).comp UnaryResources.lengthBits_computes))
lemma elementPart_pack (ctx : List Bool) (part : Fin q→Fin a) (r : Fin a→Fin T→Option (Fin q))
    (seed : Categorical.OracleSeed (Fin q) a T L) (e : Fin q) :
    elementPart (pairBits (scorePack ctx part r seed,elemBits e))=(part e).val.bits := by
  simp only [elementPart,scorePack,elemBits,partBits,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,extractPrefix_pairBits,discardPrefix_pairBits,lookup_ofFn]
lemma elementSamples_pack (ctx : List Bool) (part : Fin q→Fin a) (r : Fin a→Fin T→Option (Fin q))
    (seed : Categorical.OracleSeed (Fin q) a T L) (e : Fin q) :
    elementSamples (pairBits (scorePack ctx part r seed,elemBits e))=encode (List.ofFn (fun l=>seedBits (seed e l))) := by
  simp only [elementSamples,scorePack,elemBits,oracleBits,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,extractPrefix_pairBits,discardPrefix_pairBits,lookup_ofFn]
lemma marginalDraw_pack (ctx : List Bool) (part : Fin q→Fin a) (r : Fin a→Fin T→Option (Fin q))
    (seed : Categorical.OracleSeed (Fin q) a T L) (e : Fin q) (s : Fin a→Fin T) :
    marginalDraw (pairBits (pairBits (scorePack ctx part r seed,elemBits e),seedBits s))=
      encode ((drawn (Function.update r (part e) (fun _=>none)) s).map elemBits) := by
  unfold marginalDraw
  rw [extractPrefix_pairBits,elementPart_pack]
  simp only [extractPrefix_pairBits,discardPrefix_pairBits,scorePack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]
  change draw (drawPack elemBits r s (part e).val)=_
  rw [draw_pack,omitted_update]
def rationalMarginal (G : Finset (Fin q)→ℚ) (part : Fin q→Fin a)
    (r : Fin a→Fin T→Option (Fin q)) (e : Fin q) (s : Fin a→Fin T) : ℚ :=
  let S:=Categorical.draw a (Function.update r (part e) (fun _=>none)) s ∅
  G (insert e S)-G S
lemma marginal_pack (g : List Bool→List Bool) (ctx : List Bool) (G : Finset (Fin q)→ℚ)
    (hg : ∀ xs : List (Fin q),g (pairBits (ctx,encode (xs.map elemBits)))=BinaryRational.encode (G xs.toFinset))
    (part : Fin q→Fin a) (r : Fin a→Fin T→Option (Fin q)) (seed : Categorical.OracleSeed (Fin q) a T L)
    (e : Fin q) (s : Fin a→Fin T) :
    marginal g (pairBits (pairBits (scorePack ctx part r seed,elemBits e),seedBits s))=
      BinaryRational.encode (rationalMarginal G part r e s) := by
  unfold marginal
  rw [marginalDraw_pack ctx part r seed e s]
  simp only [extractPrefix_pairBits,discardPrefix_pairBits,scorePack,field_encode,
    List.getElem?_cons_zero,Option.getD_some]
  change BinaryRational.encode (BinaryRational.decode (g (pairBits (ctx,encode ((e::drawn (Function.update r (part e) (fun _=>none)) s).map elemBits))))-
    BinaryRational.decode (g (pairBits (ctx,encode ((drawn (Function.update r (part e) (fun _=>none)) s).map elemBits)))))=_
  rw [hg,hg,BinaryRational.decode_encode,BinaryRational.decode_encode]
  simp only [List.toFinset_cons,drawn_toFinset,rationalMarginal]
def rationalScore (G : Finset (Fin q)→ℚ) (part : Fin q→Fin a)
    (r : Fin a→Fin T→Option (Fin q)) (seed : Categorical.OracleSeed (Fin q) a T L) (e : Fin q) : ℚ :=
  (∑ l,rationalMarginal G part r e (seed e l)) / L
lemma score_pack (g : List Bool→List Bool) (ctx : List Bool) (G : Finset (Fin q)→ℚ)
    (hg : ∀ xs : List (Fin q),g (pairBits (ctx,encode (xs.map elemBits)))=BinaryRational.encode (G xs.toFinset))
    (part : Fin q→Fin a) (r : Fin a→Fin T→Option (Fin q)) (seed : Categorical.OracleSeed (Fin q) a T L) (e : Fin q) :
    score g (pairBits (scorePack ctx part r seed,elemBits e))=BinaryRational.encode (rationalScore G part r seed e) := by
  simp only [score,marginalValues,elementSamples_pack,mapWith_ofFn,marginal_pack g ctx G hg,
    Count.run_encode,List.length_ofFn,UnaryResources.lengthBits_eq,List.length_replicate,value_bits]
  rw [show encode (List.ofFn (fun l=>BinaryRational.encode (rationalMarginal G part r e (seed e l))))=
    RationalArray.encode (List.ofFn (fun l=>rationalMarginal G part r e (seed e l))) by
      simp only [RationalArray.encode,List.map_ofFn,Function.comp_def],RationalArray.sumWords_encode,
    BinaryRational.decode_encode,List.sum_ofFn]
  rfl
lemma rationalScore_cast (G : Finset (Fin q)→ℚ) (part : Fin q→Fin a)
    (r : Fin a→Fin T→Option (Fin q)) (seed : Categorical.OracleSeed (Fin q) a T L) (e : Fin q) :
    (rationalScore G part r seed e:ℝ)=Categorical.scores part (fun S=>(G S:ℝ)) r seed e := by
  simp only [rationalScore,rationalMarginal,Categorical.scores,FiniteSampling.sampleMean,
    Categorical.marginalSample,Categorical.marginal,Rat.cast_div,Rat.cast_sum,Rat.cast_sub,Rat.cast_natCast]
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
