import Mathlib
import OAI.Combinatorics.MatchingCount.Probability.Marking
import OAI.Combinatorics.MatchingCount.Machines.TreeWeightTable

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

def centralKey (x : BagBuildInput×RawLogical) : Key :=
  sourceRealKey (x.1,(x.2,2*x.1.1.1.2.length))
def centralKeyRealizer : Realizer centralKey := (composition
  (pair first (pair second (composition (pair (constant 2) (composition first.fst.fst.snd listLength)) multiply)))
  sourceRealKeyRealizer).congr (fun _=>rfl)
lemma polynomial_centralKey : PolynomialTime centralKeyRealizer := by
  unfold centralKeyRealizer
  apply polynomial_congr
  have := polynomial_sourceRealKey
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost
lemma centralKey_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ)
    (e : LogicalEdge (Fin n)) :
    centralKey ((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),logicalRepr e)=
      sourceKey (RationalSource.centralEdge w K e) := by
  unfold centralKey
  dsimp only
  rw [List.length_replicate]
  exact sourceRealKey_source hn w hw K (e,⟨2*(2*K+2),by omega⟩)

def centralKeys (x : BagBuildInput) : List Key :=
  (logicalEdges x.1.2).map (fun e=>centralKey (x,e))
def centralKeysRealizer : Realizer centralKeys := (rowsWith centralKeyRealizer
  (composition (first (A:=BuildInput) (B:=List Bool)).snd logicalEdgesRealizer)).congr (fun _=>rfl)
lemma polynomial_centralKeys : PolynomialTime centralKeysRealizer :=
  polynomial_congr _ (polynomial_rowsWith polynomial_centralKey
    (polynomial_composition (polynomial_snd polynomial_first) polynomial_logicalEdges))
lemma mem_centralKeys {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ)
    (e : Transport.BagEdge (RationalSource.bags w K)) :
    sourceKey e∈centralKeys (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false) ↔
      ∃ q,RationalSource.centralEdge w K q=e := by
  unfold centralKeys
  rw [List.mem_map]
  constructor
  · rintro ⟨q,hq,he⟩
    obtain ⟨a,rfl⟩:=logicalEdges_complete q hq
    rw [centralKey_source hn w hw K] at he
    exact ⟨a,sourceKey_injective he⟩
  · rintro ⟨q,rfl⟩
    exact ⟨logicalRepr q,logicalRepr_mem q,centralKey_source hn w hw K q⟩

def isCentral (x : BagBuildInput×Key) : Bool := decide (x.2∈centralKeys x.1)
def isCentralRealizer : Realizer isCentral := (composition
  (pair second (composition first centralKeysRealizer))
  (contains (pairEqual (pairEqual natEqual natEqual) natEqual))).congr (by
    intro x; apply Bool.eq_iff_iff.mpr; simp [isCentral])
lemma polynomial_isCentral : PolynomialTime isCentralRealizer :=
  polynomial_congr _ (polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition polynomial_first polynomial_centralKeys))
    (polynomial_contains (polynomial_pairEqual (polynomial_pairEqual polynomial_natEqual polynomial_natEqual) polynomial_natEqual)))

def probePart (x : (BagBuildInput×ℕ)×Key) : Fraction :=
  if isCentral (x.1.1,x.2) then TreeFraction.div ((1,1),(x.1.2,1)) else (0,1)
def probePartRealizer : Realizer probePart := (choose
  (composition (pair first.fst second) isCentralRealizer)
  (composition (pair (constant (1,1)) (pair first.snd (constant 1))) divRealizer)
  (constant (0,1))).congr (fun _=>rfl)
lemma polynomial_probePart : PolynomialTime probePartRealizer := by
  unfold probePartRealizer
  apply polynomial_congr
  have := polynomial_isCentral
  have := polynomial_div
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost
lemma probePart_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K D : ℕ)
    (e : Transport.BagEdge (RationalSource.bags w K)) :
    probePart (((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),D),sourceKey e)=
      TreeFraction.repr (RationalSource.probePortion w K D e) := by
  unfold probePart isCentral
  dsimp only
  simp only [decide_eq_true_eq,RationalSource.probePortion]
  simp only [mem_centralKeys hn w hw K]
  split_ifs
  · have hD : ((D,1) : Fraction)=TreeFraction.repr (D:ℚ) := by simp [TreeFraction.repr]
    rw [hD]
    exact div_repr (by decide : (0:ℚ)≤1) (Nat.cast_nonneg D)
  · rfl
end MatchingFPRAS.ExecutableSource

end OAI
