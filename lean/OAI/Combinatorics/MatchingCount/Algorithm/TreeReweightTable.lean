import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeWeightTable
import OAI.Combinatorics.MatchingCount.Algorithm.TreeNumericStatisticsCorrect

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
lemma lookup_valid {A E B : Type} [DecidableEq E] (d : B) (xs : List A)
    (key : A→E) (value : A→B) (e : E) (b : B)
    (hv : ∀ a∈xs,key a=e→value a=b)
    (hd : (∀ a∈xs,key a≠e)→d=b) :
    lookup d (xs.map (fun a=>(key a,value a)),e)=b := by
  induction xs with
  | nil => simpa [lookup] using hd (by simp)
  | cons a xs ih =>
    by_cases h : key a=e
    · simpa [lookup,h] using hv a (by simp) h
    · have hm:=ih (fun z hz=>hv z (by simp [hz]))
        (fun hh=>hd (by intro z hz; rcases List.mem_cons.mp hz with rfl|hz; exact h; exact hh z hz))
      simpa [lookup,h] using hm
end MatchingFPRAS.ExecutableLadder

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry ExecutableLadder

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
abbrev SourceReweightInput := BagBuildInput×Matrix

def sourceReweightData (x : SourceReweightInput) : ReweightData :=
  ((x.1.1.1.1,x.2),x.1.1.1.2)
def sourceReweightDataRealizer : Realizer sourceReweightData := (pair
  (pair first.fst.fst.fst second) first.fst.fst.snd).congr (fun _=>rfl)
lemma polynomial_sourceReweightData : PolynomialTime sourceReweightDataRealizer := by
  unfold sourceReweightDataRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  tree_cost

def sourceReweightRows (x : SourceReweightInput) : List (Key×Fraction) :=
  reweightTable sourceRealKey ((x.1,sourceReweightData x),realEdges (x.1.1.2,x.1.1.1.2))
def sourceReweightRowsRealizer : Realizer sourceReweightRows := (composition
  (pair (pair first sourceReweightDataRealizer)
    (composition (pair first.fst.snd first.fst.fst.snd) realEdgesRealizer))
  (reweightTableRealizer sourceRealKeyRealizer)).congr (fun _=>rfl)
lemma polynomial_sourceReweightRows : PolynomialTime sourceReweightRowsRealizer := by
  unfold sourceReweightRowsRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_sourceReweightData
  have := polynomial_realEdges
  have := polynomial_reweightTable polynomial_sourceRealKey
  tree_cost

def sourceReweightValue (x : SourceReweightInput×Key) : Fraction :=
  lookup (1,1) (sourceReweightRows x.1,x.2)
def sourceReweightValueRealizer : Realizer sourceReweightValue := (composition
  (pair (composition first sourceReweightRowsRealizer) second)
  (lookupRealizer (1,1) (pairEqual (pairEqual natEqual natEqual) natEqual))).congr (fun _=>rfl)
lemma polynomial_sourceReweightValue : PolynomialTime sourceReweightValueRealizer := by
  unfold sourceReweightValueRealizer
  apply polynomial_congr
  have := polynomial_sourceReweightRows
  have := polynomial_lookup ((1,1) : Fraction)
    (polynomial_pairEqual (polynomial_pairEqual polynomial_natEqual polynomial_natEqual) polynomial_natEqual)
  tree_cost

lemma sourceReweightValue_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w w₁ : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (hw₁ : ∀ a b,0≤w₁ a b)
    (K : ℕ) (e : Transport.BagEdge (RationalSource.bags w K)) :
    sourceReweightValue (((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),matrixRep w₁),sourceKey e)=
      TreeFraction.repr (RationalSource.bagReweight w w₁ K e) := by
  unfold sourceReweightValue sourceReweightRows reweightTable reweightRow sourceReweightData
  dsimp only
  apply lookup_valid
  · intro a ha he
    have hm : a∈(realEdges (List.range n,List.replicate (2*K+2) false)).toFinset:=List.mem_toFinset.mpr ha
    rw [realEdges_finset n K _ (List.length_replicate ..)] at hm
    obtain ⟨q,_,rfl⟩:=Finset.mem_image.mp hm
    rw [sourceRealKey_source hn w hw K] at he
    have hq:=sourceKey_injective he
    change rawReweight (((matrixRep w,matrixRep w₁),List.replicate (2*K+2) false),
      (logicalRepr q.1,q.2.val))=_
    rw [rawReweight_rep w w₁ hw hw₁ K _ (List.length_replicate ..)]
    rw [←hq,RationalSource.bagReweight_on]
  · intro hoff
    have he : ¬∃q,RationalSource.coloredReal w K q=e := by
      rintro ⟨q,hq⟩
      have hm : realRepr q∈realEdges (List.range n,List.replicate (2*K+2) false) := by
        apply List.mem_toFinset.mp
        rw [realEdges_finset n K _ (List.length_replicate ..)]
        exact Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩
      have hh:=hoff (realRepr q) hm
      apply hh
      rw [sourceRealKey_source hn w hw K,hq]
    rw [RationalSource.bagReweight_off w w₁ K e he]
    rfl

def sourceReweightEntry (x : SourceReweightInput×Key) : ℕ×Fraction :=
  ((sourceTables x.1.1).1.idxOf x.2,sourceReweightValue x)
def sourceReweightEntryRealizer : Realizer sourceReweightEntry := (pair
  (keyLookup second (composition first.fst sourceTablesRealizer).fst)
  sourceReweightValueRealizer).congr (fun _=>rfl)
lemma polynomial_sourceReweightEntry : PolynomialTime sourceReweightEntryRealizer := by
  unfold sourceReweightEntryRealizer
  apply polynomial_congr
  exact polynomial_pair (polynomial_keyLookup polynomial_second
    (polynomial_fst (polynomial_composition (polynomial_fst polynomial_first) polynomial_sourceTables)))
    polynomial_sourceReweightValue

def sourceReweights (x : SourceReweightInput) : NumericMarking.Reweights :=
  (sourceTables x.1).1.map (fun key=>sourceReweightEntry (x,key))
def sourceReweightsRealizer : Realizer sourceReweights := rowsWith sourceReweightEntryRealizer
  (composition (first (A:=BagBuildInput) (B:=Matrix)) sourceTablesRealizer).fst
lemma polynomial_sourceReweights : PolynomialTime sourceReweightsRealizer :=
  polynomial_rowsWith polynomial_sourceReweightEntry
    (polynomial_fst (polynomial_composition polynomial_first polynomial_sourceTables))
lemma sourceReweights_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w w₁ : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (hw₁ : ∀ a b,0≤w₁ a b) (K : ℕ) :
    sourceReweights ((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),matrixRep w₁)=
      NumericMarking.reweightsRep (RationalSource.bagReweight w w₁ K) := by
  unfold sourceReweights NumericMarking.reweightsRep
  dsimp only
  rw [sourceTables_catalog hn w hw K]
  unfold sourceCatalog
  rw [List.map_ofFn,List.map_ofFn]
  congr 1
  funext i
  unfold sourceReweightEntry
  dsimp only [Function.comp_apply]
  rw [sourceTables_catalog hn w hw K,sourceCatalog_index,
    sourceReweightValue_source hn w w₁ hw hw₁ K]

open TreePost Turing

theorem sourceReweights_post : ∃ p : Polynomial ℕ,∀ x : SourceReweightInput,∀ t : ℕ,
    p.eval (packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (machine sourceReweightsRealizer.program) (packed x) coins).state=none ∧
      (run (machine sourceReweightsRealizer.program) (packed x) coins).tape.right₀=
        ListBlank.mk (packed (sourceReweights x)) :=
  polynomial_compiles sourceReweightsRealizer polynomial_sourceReweights
end MatchingFPRAS.ExecutableSource

end OAI
