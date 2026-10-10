import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeUnitAssemble
import OAI.Combinatorics.MatchingCount.Sampling.TreeFastUnit

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP Polynomial

def assembleAtFast : Realizer assembleAt := by
  let n : Realizer (fun x : (Frame×Result)×ℕ=>x.1.1.1) := first.fst.fst
  let b : Realizer (fun x : (Frame×Result)×ℕ=>x.1.1.2.1) := first.fst.snd.fst
  let c : Realizer (fun x : (Frame×Result)×ℕ=>x.1.1.2.2) := first.fst.snd.snd
  let i : Realizer (fun x : (Frame×Result)×ℕ=>x.2) := second
  let a := composition n successor
  let j := composition (pair i b) unskipRealizer
  let z := composition (pair first.snd j) (getDFast (0,0))
  let r := pair (composition (pair z.fst b) skipFast) z.snd
  exact (choose (composition (pair i a) natEqual) (pair b c)
    (choose (composition (pair i b) natEqual) (pair a c) r)).congr (by intro x; simp [assembleAt])
lemma polynomial_assembleAtFast : PolynomialTime assembleAtFast := by
  unfold assembleAtFast Realizer.fst Realizer.snd
  dsimp only
  apply polynomial_congr
  have : PolynomialTime unskipRealizer := by
    unfold unskipRealizer
    apply polynomial_congr
    exact polynomial_choose polynomial_less polynomial_first (polynomial_composition polynomial_first polynomial_predecessor)
  have := polynomial_successor
  have := polynomial_getDFast ((0,0) : ℕ×ℕ)
  have := polynomial_skipFast
  tree_poly

def capacity (x : Context) : ℕ := x.1.1.length+x.1.2.length+2
def capacityRealizer : Realizer capacity :=
  (composition (pair (composition (pair (composition first.fst listLength)
    (composition first.snd listLength)) add) (constant 2)) add).congr (fun _=>rfl)
lemma polynomial_capacity : PolynomialTime capacityRealizer := by
  unfold capacityRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  tree_poly

def clippedAt (x : (Context×(Frame×Result))×ℕ) : ℕ×ℕ :=
  let r:=assembleAt (x.1.2,x.2)
  (min r.1 (capacity x.1.1),min r.2 (capacity x.1.1))
def clippedAtRealizer : Realizer clippedAt := by
  let r : Realizer (fun x : (Context×(Frame×Result))×ℕ=>assembleAt (x.1.2,x.2)) := (composition (pair first.snd second) assembleAtFast).congr (fun _=>rfl)
  let cap : Realizer (fun x : (Context×(Frame×Result))×ℕ=>capacity x.1.1) := (composition first.fst capacityRealizer).congr (fun _=>rfl)
  exact (pair (composition (pair r.fst cap) minNat) (composition (pair r.snd cap) minNat)).congr (fun _=>rfl)
lemma polynomial_clippedAt : PolynomialTime clippedAtRealizer := by
  unfold clippedAtRealizer Realizer.fst Realizer.snd
  dsimp only
  apply polynomial_congr
  have := polynomial_assembleAtFast
  have := polynomial_capacity
  have := polynomial_minNat
  tree_poly

def clippedAssemble (x : Context×(Frame×Result)) : Result :=
  (List.range (min (x.2.1.1+2) (x.1.1.1.length+2))).map (fun i=>clippedAt (x,i))
def clippedAssembleRealizer : Realizer clippedAssemble := by
  let n : Realizer (fun x : Context×(Frame×Result)=>x.2.1.1+2) := (composition (pair second.fst.fst (constant 2)) add).congr (fun _=>rfl)
  let m : Realizer (fun x : Context×(Frame×Result)=>x.1.1.1.length+2) := (composition (pair (composition first.fst.fst listLength) (constant 2)) add).congr (fun _=>rfl)
  let rs := composition (composition (pair n m) minNat) range
  exact (composition (pair identity rs) (mapWith clippedAtRealizer)).congr (fun _=>rfl)
lemma polynomial_clippedAssemble : PolynomialTime clippedAssembleRealizer := by
  unfold clippedAssembleRealizer Realizer.fst
  dsimp only
  apply polynomial_congr
  apply polynomial_composition _ (polynomial_mapWith polynomial_clippedAt)
  apply polynomial_pair polynomial_identity
  apply polynomial_boundedRange (by have := polynomial_minNat; tree_poly) (X+2)
  intro x
  simpa only [Function.comp_apply,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat] using
    (min_le_right (x.2.1.1+2) (x.1.1.1.length+2)).trans
    (Nat.add_le_add_right ((list_length_le_weight _).trans ((weight_fst x.1.1).trans ((weight_fst x.1).trans (weight_fst x)))) 2)
lemma clippedAssemble_weight (ctx : Context) (f : Frame) (r : Result) :
    weight (clippedAssemble (ctx,(f,r)))≤64*(weight ctx+1)^2 := by
  have hh :=weight_map_bound (as:=List.range (min (f.1+2) (ctx.1.1.length+2)))
    (f:=fun i=>clippedAt ((ctx,(f,r)),i)) (N:=8*capacity ctx+3) (by
      intro i hi
      let z:=assembleAt ((f,r),i)
      have h1:=weight_nat_numeric (min z.1 (capacity ctx))
      have h2:=weight_nat_numeric (min z.2 (capacity ctx))
      have h3:=min_le_right z.1 (capacity ctx)
      have h4:=min_le_right z.2 (capacity ctx)
      change weight (min z.1 (capacity ctx),min z.2 (capacity ctx))≤_
      rw [weight_prod]
      omega)
  have hn : ctx.1.1.length≤weight ctx := (list_length_le_weight _).trans ((weight_fst ctx.1).trans (weight_fst ctx))
  have hm : ctx.1.2.length≤weight ctx := (list_length_le_weight _).trans ((weight_snd ctx.1).trans (weight_fst ctx))
  have hc : capacity ctx≤2*weight ctx+2 := by unfold capacity; omega
  have hl : min (f.1+2) (ctx.1.1.length+2)≤weight ctx+2 := (min_le_right _ _).trans (by omega)
  simp only [List.length_range] at hh
  have hp :=Nat.mul_le_mul hl (show 8*capacity ctx+3+1≤16*weight ctx+20 by omega)
  change weight (clippedAssemble (ctx,(f,r)))≤_ at hh
  nlinarith

def assemblyFoldStep (x : Frame×(Context×Result)) : Context×Result :=
  (x.2.1,clippedAssemble (x.2.1,(x.1,x.2.2)))
def assemblyFoldStepRealizer : Realizer assemblyFoldStep :=
  (pair second.fst (composition (pair second.fst (pair first second.snd)) clippedAssembleRealizer)).congr (fun _=>rfl)
lemma polynomial_assemblyFoldStep : PolynomialTime assemblyFoldStepRealizer := by
  unfold assemblyFoldStepRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_clippedAssemble
  tree_poly
lemma assemblyFold_fst (pre : List Frame) (ctx : Context) (r : Result) :
    (pre.foldl (fun z f=>assemblyFoldStep (f,z)) (ctx,r)).1=ctx := by
  induction pre generalizing r with
  | nil => rfl
  | cons f pre ih => exact ih _
lemma assemblyFold_weight (pre : List Frame) (ctx : Context) (r : Result) :
    weight (pre.foldl (fun z f=>assemblyFoldStep (f,z)) (ctx,r)).2 ≤
      weight r+pre.length*(64*(weight ctx+1)^2) := by
  induction pre generalizing r with
  | nil => simp
  | cons f pre ih =>
    have hh:=ih (clippedAssemble (ctx,(f,r)))
    have hw:=clippedAssemble_weight ctx f r
    change weight (pre.foldl _ (ctx,clippedAssemble (ctx,(f,r)))).2≤_
    simp only [List.length_cons]
    nlinarith
lemma polynomial_assemblyFold : PolynomialTime (fold assemblyFoldStepRealizer) := by
  apply polynomial_fold polynomial_assemblyFoldStep (70*(X+1)^3)
  rintro fs ⟨ctx,r⟩ pre post he
  let S:=weight (fs,(ctx,r))
  have hp:pre.length≤S := (list_length_le_weight _).trans ((weight_prefix he).trans (weight_fst (fs,(ctx,r))))
  have hc:weight ctx≤S := (weight_fst (ctx,r)).trans (weight_snd (fs,(ctx,r)))
  have hr:weight r≤S := (weight_snd (ctx,r)).trans (weight_snd (fs,(ctx,r)))
  have hh:=assemblyFold_weight pre ctx r
  have hf:=assemblyFold_fst pre ctx r
  rw [←Prod.eta (pre.foldl (fun z f=>assemblyFoldStep (f,z)) (ctx,r)),weight_prod,hf]
  have hm:= Nat.mul_le_mul hp (show 64*(weight ctx+1)^2 ≤64*(S+1)^2 by gcongr)
  simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  change _≤70*(S+1)^3
  nlinarith

lemma resultRep_mem {n m : ℕ} {bags : Fin n → Finset (Fin m)}
    (p : UnitRefresh.ColoredPairing bags) {z : ℕ×ℕ} (hz : z∈resultRep p) : z.1 < n ∧ z.2 < m := by
  simp only [resultRep,List.mem_ofFn] at hz
  obtain ⟨i,rfl⟩:=hz
  exact ⟨(p.pair.mate i).isLt,(p.color i).isLt⟩

lemma clippedAssemble_eq {n m : ℕ} (ctx : Context) (hn : n+2≤ctx.1.1.length) (hm : m≤ctx.1.2.length)
    (bags : Fin (n+2) → Finset (Fin m))
    (c : UnitRefresh.Partner bags (Fin.last (n+1)))
    (p : UnitRefresh.ColoredPairing (fun i=>bags (UnitRefresh.removePairEquiv (Fin.last (n+1)) c.val.1 c.property.1 i).val)) :
    clippedAssemble (ctx,((n,(c.val.1.val,c.val.2.val)),resultRep p))=
      resultRep ((UnitRefresh.ColoredPairing.map (UnitRefresh.residualBags bags (Fin.last (n+1)) c.val.1)
        (UnitRefresh.removePairEquiv (Fin.last (n+1)) c.val.1 c.property.1) p).insert (Fin.last (n+1)) c) := by
  let f : Frame := (n,(c.val.1.val,c.val.2.val))
  have he :=assemble_eq bags c p
  change assemble (f,resultRep p)=_ at he
  unfold clippedAssemble
  dsimp only
  rw [min_eq_left (show n+2 ≤ ctx.1.1.length+2 by omega)]
  trans assemble (f,resultRep p)
  · unfold assemble
    apply List.map_congr_left
    intro i hi
    have hz : assembleAt ((f,resultRep p),i)∈assemble (f,resultRep p) := List.mem_map.mpr ⟨i,hi,rfl⟩
    rw [he] at hz
    obtain ⟨h1,h2⟩:=resultRep_mem _ hz
    have hc1 :(assembleAt ((f,resultRep p),i)).1≤capacity ctx := by unfold capacity; omega
    have hc2 :(assembleAt ((f,resultRep p),i)).2≤capacity ctx := by unfold capacity; omega
    exact Prod.ext (min_eq_left hc1) (min_eq_left hc2)
  · exact he
end MatchingFPRAS.ExecutableUnit

end OAI
