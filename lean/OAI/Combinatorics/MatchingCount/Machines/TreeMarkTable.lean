import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeProbe
import OAI.Combinatorics.MatchingCount.Sampling.TreeNumericMarking

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry ExecutableOptions

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

abbrev MarkRowInput := (BagBuildInput×ℕ)×Key
def phantomPart (x : MarkRowInput) : Fraction :=
  TreeFraction.div (phantomHeight (x.1.1,x.2),(x.1.2,1))
def phantomPartRealizer : Realizer phantomPart := (composition
  (pair (composition (pair first.fst second) phantomHeightRealizer) (pair first.snd (constant 1))) divRealizer).congr (fun _=>rfl)
lemma polynomial_phantomPart : PolynomialTime phantomPartRealizer := by
  unfold phantomPartRealizer
  apply polynomial_congr
  have := polynomial_phantomHeight
  have := polynomial_div
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

def markPortions (x : MarkRowInput) : Fraction×(Fraction×Fraction) :=
  (realPart (x.1.1,x.2),(TreeFraction.sub (phantomPart x,probePart x),probePart x))
def markPortionsRealizer : Realizer markPortions := (pair
  (composition (pair first.fst second) realPartRealizer)
  (pair (composition (pair phantomPartRealizer probePartRealizer) subRealizer) probePartRealizer)).congr (fun _=>rfl)
lemma polynomial_markPortions : PolynomialTime markPortionsRealizer := by
  unfold markPortionsRealizer
  apply polynomial_congr
  have := polynomial_realPart
  have := polynomial_phantomPart
  have := polynomial_probePart
  have := polynomial_sub
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

lemma markPortions_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0<w i j) (K D : ℕ)
    (e : Transport.BagEdge (RationalSource.bags w K)) :
    markPortions (((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),D),sourceKey e)=
      (TreeFraction.repr (RationalSource.portions w K D e 0),
       (TreeFraction.repr (RationalSource.portions w K D e 1),TreeFraction.repr (RationalSource.portions w K D e 2))) := by
  have hnon:=fun a b=>(hw a b).le
  have hheight : 0≤RationalSource.bagHeight w K e.color := by
    unfold RationalSource.bagHeight
    positivity
  have hD : ((D,1) : Fraction)=TreeFraction.repr (D:ℚ) := by simp [TreeFraction.repr]
  have hp : 0≤RationalSource.probePortion w K D e := RationalSource.portions_nonneg w hw K D e 2
  have hsub : RationalSource.probePortion w K D e≤RationalSource.bagHeight w K e.color/D :=
    sub_nonneg.mp (RationalSource.portions_nonneg w hw K D e 1)
  unfold markPortions phantomPart
  dsimp only
  rw [realPart_source hn w hnon K,phantomHeight_source hn w hnon K,
    probePart_source hn w hnon K D,hD,div_repr hheight (Nat.cast_nonneg D),
    sub_repr (div_nonneg hheight (Nat.cast_nonneg D)) hp hsub]
  rfl

def threeOptions (x : Fraction×(Fraction×Fraction)) : Options ℕ :=
  [(0,x.1),(1,x.2.1),(2,x.2.2)]
def threeOptionsRealizer : Realizer threeOptions := (composition
  (pair (pair (constant 0) first)
    (composition (pair (pair (constant 1) second.fst)
      (composition (pair (constant 2) second.snd) listSingleton)) listCons)) listCons).congr (fun _=>rfl)
lemma polynomial_threeOptions : PolynomialTime threeOptionsRealizer := by
  unfold threeOptionsRealizer
  apply polynomial_congr
  have := polynomial_listSingleton (A:=ℕ×Fraction)
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

def sourceMarkRow (x : MarkRowInput) : Options ℕ :=
  (threeOptions (markPortions x)).map (fun a=>(a.1,TreeFraction.div (a.2,sourceBagWeight x)))
def sourceMarkRowRealizer : Realizer sourceMarkRow := (composition
  (pair sourceBagWeightRealizer (composition markPortionsRealizer threeOptionsRealizer))
  (mapWith (pair second.fst (composition (pair second.snd first) divRealizer)))).congr (fun _=>rfl)
lemma polynomial_sourceMarkRow : PolynomialTime sourceMarkRowRealizer := by
  unfold sourceMarkRowRealizer
  apply polynomial_congr
  have := polynomial_sourceBagWeight
  have := polynomial_markPortions
  have := polynomial_threeOptions
  have := polynomial_div
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost
lemma sourceMarkRow_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0<w a b) (K D : ℕ) (hD : 0<D)
    (e : Transport.BagEdge (RationalSource.bags w K)) :
    sourceMarkRow (((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),D),sourceKey e)=
      ExecutableOptions.repr Fin.val (RationalSource.markingTable w hw K D hD e) := by
  unfold sourceMarkRow
  rw [markPortions_source hn w hw K D,sourceBagWeight_source hn w (fun a b=>(hw a b).le) K D]
  have hp:=RationalSource.portions_nonneg w hw K D e
  have hb:=(RationalSource.bagWeight_pos w hw K D hD e).le
  simp only [threeOptions,List.map_cons,List.map_nil,div_repr (hp _) hb]
  simp only [ExecutableOptions.repr,RationalSource.markingTable,List.ofFn_succ,List.ofFn_zero]
  rfl

def sourceMarks (x : BagBuildInput×ℕ) : NumericMarking.Tables :=
  (sourceTables x.1).1.map (fun key=>sourceMarkRow (x,key))
def sourceMarksRealizer : Realizer sourceMarks := rowsWith sourceMarkRowRealizer
  (composition (first (A:=BagBuildInput) (B:=ℕ)) sourceTablesRealizer).fst
lemma polynomial_sourceMarks : PolynomialTime sourceMarksRealizer :=
  polynomial_rowsWith polynomial_sourceMarkRow
    (polynomial_fst (polynomial_composition polynomial_first polynomial_sourceTables))
lemma sourceMarks_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0<w a b) (K D : ℕ) (hD : 0<D) :
    sourceMarks ((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),D)=
      NumericMarking.tableRep (RationalSource.markingTable w hw K D hD) := by
  unfold sourceMarks
  dsimp only
  rw [sourceTables_catalog hn w (fun a b=>(hw a b).le) K]
  unfold sourceCatalog NumericMarking.tableRep
  rw [List.map_ofFn]
  congr 1
  funext i
  exact sourceMarkRow_source hn w hw K D hD _

open TreePost Turing

theorem sourceMarks_post : ∃ p : Polynomial ℕ,∀ x : BagBuildInput×ℕ,∀ t : ℕ,
    p.eval (packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (machine sourceMarksRealizer.program) (packed x) coins).state=none ∧
      (run (machine sourceMarksRealizer.program) (packed x) coins).tape.right₀=
        ListBlank.mk (packed (sourceMarks x)) :=
  polynomial_compiles sourceMarksRealizer polynomial_sourceMarks
end MatchingFPRAS.ExecutableSource

end OAI
