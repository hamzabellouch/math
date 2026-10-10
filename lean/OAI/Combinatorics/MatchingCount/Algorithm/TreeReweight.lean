import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.RationalObservables
import OAI.Combinatorics.MatchingCount.Arithmetic.TreeFractionExtra
import OAI.Combinatorics.MatchingCount.Machines.TreeStateTable
import OAI.Combinatorics.MatchingCount.Graphs.TreeGeometry

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck ExecutableLadder Enlargement RealGeometry

abbrev ReweightData := (Matrix×Matrix)×List Bool

def rawReweight (x : ReweightData×RawReal) : Fraction :=
  if x.2.2=2*x.1.2.length then div (cell (x.1.1.2,x.2.1),cell (x.1.1.1,x.2.1)) else (1,1)
def rawReweightRealizer : Realizer rawReweight :=
  (choose (composition (pair second.snd (composition
      (pair (constant 2) (composition first.snd listLength)) multiply)) natEqual)
    (composition (pair (composition (pair first.fst.snd second.fst) cellRealizer)
      (composition (pair first.fst.fst second.fst) cellRealizer)) divRealizer)
    (constant (1,1))).congr (by intro x; simp only [rawReweight,Function.comp_apply,decide_eq_true_eq])
lemma polynomial_rawReweight : PolynomialTime rawReweightRealizer := by
  unfold rawReweightRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_cell
  have := polynomial_div
  tree_cost
lemma rawReweight_rep {n : ℕ} (w w₁ : Fin n→Fin n→ℚ)
    (hw : ∀ i j,0≤w i j) (hw₁ : ∀ i j,0≤w₁ i j) (K : ℕ)
    (fuel : List Bool) (hf : fuel.length=2*K+2) (e : SourceRealEdge (Fin n) K) :
    rawReweight (((matrixRep w,matrixRep w₁),fuel),(logicalRepr e.1,e.2.val))=
      TreeFraction.repr (RationalSource.rawReweight w w₁ K e) := by
  unfold rawReweight RationalSource.rawReweight
  dsimp only
  rw [hf]
  split_ifs
  · dsimp only [logicalRepr]
    rw [cell_matrixRep,cell_matrixRep,div_repr (hw₁ _ _) (hw _ _)]
    congr 1
    have hp : source e.1<target e.1 := e.1.property
    simp only [BottleneckAlgorithm.edge,ite_eq_left hp]
    rfl
  · rfl

variable {C E : Type} [Codec C] [Codec E] [DecidableEq E] [Inhabited E]
def reweightRow (color : C×RawReal→E) (x : (C×ReweightData)×RawReal) : E×Fraction :=
  (color (x.1.1,x.2),rawReweight (x.1.2,x.2))
def reweightRowRealizer {color : C×RawReal→E} (F : Realizer color) : Realizer (reweightRow color) :=
  (pair (composition (pair first.fst second) F)
    (composition (pair first.snd second) rawReweightRealizer)).congr (fun _=>rfl)
omit [DecidableEq E] [Inhabited E] in
lemma polynomial_reweightRow {color : C×RawReal→E} {F : Realizer color} (hF : PolynomialTime F) :
    PolynomialTime (reweightRowRealizer F) := by
  unfold reweightRowRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_rawReweight
  tree_cost

def reweightTable (color : C×RawReal→E) (x : (C×ReweightData)×List RawReal) : List (E×Fraction) :=
  x.2.map (fun r=>reweightRow color (x.1,r))
def reweightTableRealizer {color : C×RawReal→E} (F : Realizer color) : Realizer (reweightTable color) :=
  mapWith (reweightRowRealizer F)
omit [DecidableEq E] [Inhabited E] in
lemma polynomial_reweightTable {color : C×RawReal→E} {F : Realizer color} (hF : PolynomialTime F) :
    PolynomialTime (reweightTableRealizer F) := polynomial_mapWith (polynomial_reweightRow hF)

def bagReweight (x : List (E×Fraction)×E) : Fraction := lookup (1,1) x
def bagReweightRealizer (Eq : Realizer (fun x : E×E=>decide (x.1=x.2))) : Realizer (bagReweight (E:=E)) :=
  lookupRealizer (1,1) Eq
omit [Codec C] in
lemma polynomial_bagReweight {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    (hE : PolynomialTime Eq) : PolynomialTime (bagReweightRealizer Eq) := polynomial_lookup _ hE
end MatchingFPRAS.ExecutableSource

namespace MatchingFPRAS.ExecutableLadder
lemma lookup_image {I E A : Type} [DecidableEq E] (d : A) (keys : List I)
    (f : I→E) (g : I→A) (hf : Function.Injective f) (i : I) (hi : i∈keys) :
    lookup d (keys.map (fun j=>(f j,g j)),f i)=g i := by
  induction keys with
  | nil=>simp at hi
  | cons j keys ih=>
    by_cases hji : j=i
    · subst j; simp [lookup]
    · have hne : f j≠f i:=fun h=>hji (hf h)
      have hi' : i∈keys:=(List.mem_cons.mp hi).resolve_left (Ne.symm hji)
      simpa [lookup,hne] using ih hi'
lemma lookup_off {I E A : Type} [DecidableEq E] (d : A) (keys : List I)
    (f : I→E) (g : I→A) (e : E) (he : ∀ i∈keys,f i≠e) :
    lookup d (keys.map (fun j=>(f j,g j)),e)=d := by
  induction keys with
  | nil=>simp [lookup]
  | cons i keys ih=>
    have hne:=he i (by simp)
    have ht:=ih (fun j hj=>he j (by simp [hj]))
    simpa [lookup,hne] using ht
end MatchingFPRAS.ExecutableLadder

end OAI
