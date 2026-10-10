import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.RationalEstimator
import OAI.Combinatorics.MatchingCount.Sampling.TreeDPCount
import OAI.Combinatorics.MatchingCount.Algorithm.TreeEstimator
import OAI.Combinatorics.MatchingCount.Algorithm.TreeScalingCorrect
import OAI.Combinatorics.MatchingCount.Algorithm.TreeReweight

namespace OAI

namespace MatchingFPRAS.ExecutableAdaptive
open TreeTyped TreeFraction ExecutableBottleneck ExecutableScaling ExecutableEstimator ExecutableLadder

abbrev ProbeTable := List ((ℕ×ℕ)×Fraction)
abbrev MatrixData := (ℕ×Fraction)×ProbeTable

def orderedPair (x : ℕ×ℕ) : ℕ×ℕ := if x.1<x.2 then x else (x.2,x.1)
def orderedPairRealizer : Realizer orderedPair := (choose less identity (pair second first)).congr (by
  intro x; simp [orderedPair])
lemma polynomial_orderedPair : PolynomialTime orderedPairRealizer := by
  unfold orderedPairRealizer; apply polynomial_congr; tree_cost

def probeValue (x : ProbeTable×(ℕ×ℕ)) : Fraction :=
  if x.2.1=x.2.2 then (0,1) else lookup (0,1) (x.1,orderedPair x.2)
def probeValueRealizer : Realizer probeValue := (choose (composition second natEqual) (constant (0,1))
  (composition (pair first (composition second orderedPairRealizer))
     (lookupRealizer (0,1) (pairEqual natEqual natEqual)))).congr (by intro x; simp [probeValue])
lemma polynomial_probeValue : PolynomialTime probeValueRealizer := by
  unfold probeValueRealizer; apply polynomial_congr
  have := polynomial_orderedPair
  have := polynomial_lookup ((0,1) : Fraction) (polynomial_pairEqual polynomial_natEqual polynomial_natEqual)
  tree_cost

def estimateCell (x : MatrixData×(ℕ×ℕ)) : Fraction :=
  upper (x.1.1.1,(x.1.1.2,probeValue (x.1.2,x.2)))
def estimateCellRealizer : Realizer estimateCell := (composition
  (pair first.fst.fst (pair first.fst.snd (composition (pair first.snd second) probeValueRealizer))) upperRealizer).congr (fun _=>rfl)
lemma polynomial_estimateCell : PolynomialTime estimateCellRealizer := by
  unfold estimateCellRealizer Realizer.fst Realizer.snd; apply polynomial_congr
  have := polynomial_probeValue
  have := polynomial_upper
  tree_cost

def estimateRow (x : (MatrixData×List ℕ)×ℕ) : List Fraction :=
  x.1.2.map (fun j=>estimateCell (x.1.1,(x.2,j)))
def estimateRowRealizer : Realizer estimateRow := (composition
  (pair (pair first.fst second) first.snd)
  (mapWith (composition (pair first.fst (pair first.snd second)) estimateCellRealizer))).congr (fun _=>rfl)
lemma polynomial_estimateRow : PolynomialTime estimateRowRealizer := by
  unfold estimateRowRealizer Realizer.fst Realizer.snd; apply polynomial_congr
  have := polynomial_estimateCell
  tree_cost

def estimateMatrix (x : MatrixData×List ℕ) : Matrix := x.2.map (fun i=>estimateRow (x,i))
def estimateMatrixRealizer : Realizer estimateMatrix := composition (pair identity second) (mapWith estimateRowRealizer)
lemma polynomial_estimateMatrix : PolynomialTime estimateMatrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_second)
    (polynomial_mapWith polynomial_estimateRow)

def multiplyVector (x : Vector×Vector) : Vector :=
  x.1.map (fun z=>(z.1,mul (z.2,lookup (1,1) (x.2,z.1))))
def multiplyVectorRealizer : Realizer multiplyVector := (composition (pair second first)
  (mapWith (pair second.fst (composition (pair second.snd
    (composition (pair first second.fst) (lookupRealizer (1,1) natEqual))) mulRealizer)))).congr (fun _=>rfl)
lemma polynomial_multiplyVector : PolynomialTime multiplyVectorRealizer := by
  unfold multiplyVectorRealizer Realizer.fst Realizer.snd; apply polynomial_congr
  have := polynomial_lookup ((1,1) : Fraction) polynomial_natEqual
  have := polynomial_mul
  tree_cost

def updateVector (x : Matrix×Vector) : Vector := multiplyVector (x.2,scale x.1)
def updateVectorRealizer : Realizer updateVector := (composition
  (pair (second : Realizer (Prod.snd : Matrix×Vector→Vector))
    (composition (first : Realizer (Prod.fst : Matrix×Vector→Matrix)) scaleRealizer)) multiplyVectorRealizer).congr (fun _=>rfl)
lemma polynomial_updateVector : PolynomialTime updateVectorRealizer := by
  unfold updateVectorRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition polynomial_first polynomial_scale)) polynomial_multiplyVector

lemma orderedPair_fin {n : ℕ} (i j : Fin n) (h : i≠j) :
    orderedPair (i.val,j.val)=ExecutableSource.logicalRepr (Enlargement.pairEdge i j h) := by
  unfold orderedPair Enlargement.pairEdge ExecutableSource.logicalRepr
  by_cases hij : i<j
  · simp [show i.val<j.val from hij,min_eq_left hij.le,max_eq_right hij.le]
  · have hji : j ≤ i :=le_of_not_gt hij
    simp [show ¬ i.val<j.val from hij,min_eq_right hji,max_eq_left hji]
lemma probeValue_rep {n : ℕ} (z : Enlargement.LogicalEdge (Fin n)→ℚ) (tab : ProbeTable)
    (ht : ∀ e,lookup (0,1) (tab,ExecutableSource.logicalRepr e)=TreeFraction.repr (z e))
    (i j : Fin n) :
    probeValue (tab,(i.val,j.val))=TreeFraction.repr (FiniteTrial.probeMatrix z i j) := by
  unfold probeValue FiniteTrial.probeMatrix
  by_cases he : i=j
  · subst j; simp; rfl
  · have hv : i.val≠j.val:=fun h=>he (Fin.ext h)
    simp only [ite_eq_right hv,dite_eq_right he]
    rw [orderedPair_fin i j he,ht]

lemma estimateMatrix_rep {n : ℕ} (D : ℕ) (d : ℚ) (hd : 0≤d)
    (z : Enlargement.LogicalEdge (Fin n)→ℚ) (hz : ∀ e,0≤z e) (tab : ProbeTable)
    (ht : ∀ e,lookup (0,1) (tab,ExecutableSource.logicalRepr e)=TreeFraction.repr (z e)) :
    estimateMatrix (((D,TreeFraction.repr d),tab),List.range n)=
      matrixRep (FiniteTrial.estimateMatrix D d z) := by
  unfold estimateMatrix estimateRow matrixRep
  simp only [ExecutableDP.map_range_ofFn]
  congr 1
  funext i
  congr 1
  funext j
  unfold estimateCell
  rw [probeValue_rep z tab ht i j]
  apply upper_rep _ _ _ hd
  unfold FiniteTrial.probeMatrix
  split_ifs
  · exact le_rfl
  · exact hz _

lemma multiplyVector_rep {n : ℕ} (a b : Fin n→ℚ) (ha : ∀ i,0≤a i) (hb : ∀ i,0≤b i) :
    multiplyVector (vectorRep a,vectorRep b)=vectorRep (fun i=>a i*b i) := by
  unfold multiplyVector vectorRep
  rw [List.map_ofFn]
  congr 1
  funext i
  dsimp only [Function.comp_def]
  congr 1
  rw [List.ofFn_eq_map,lookup_image (1,1) (List.finRange n) Fin.val
    (fun j=>TreeFraction.repr (b j)) Fin.val_injective i (by simp),mul_repr (ha i) (hb i)]

lemma updateVector_rep {n : ℕ} (hn : 2≤n) (G : Fin n→Fin n→ℚ)
    (hsym : ∀ i j,G i j=G j i)
    (hG : ∀ i j,i≠j→ Counting.alpha≤G i j ∧ G i j≤3)
    (a : Fin n→ℚ) (ha : ∀ i,0≤a i) :
    updateVector (matrixRep G,vectorRep a)=vectorRep (fun i=>a i*Counting.scalingTrace hn G n i) := by
  unfold updateVector
  rw [scale_rep hn G hsym hG]
  apply multiplyVector_rep a _ ha
  intro i
  exact ((Counting.scalingTrace_invariant hn G hsym hG n).1.pos i).le
end MatchingFPRAS.ExecutableAdaptive

end OAI
