import Mathlib
import OAI.Combinatorics.MatchingCount.Arithmetic.TreeAdaptiveArithmetic

namespace OAI

namespace MatchingFPRAS.ExecutableScaling
open TreeTyped TreeFraction ExecutableLadder

lemma lookup_vectorRep {n : ℕ} (v : Fin n→ℚ) (i : Fin n) (d : Fraction) :
    lookup d (vectorRep v,i.val)=TreeFraction.repr (v i) := by
  unfold vectorRep
  rw [List.ofFn_eq_map]
  exact lookup_image d (List.finRange n) Fin.val (fun j=>TreeFraction.repr (v j))
    Fin.val_injective i (by simp)
end MatchingFPRAS.ExecutableScaling

namespace MatchingFPRAS.ExecutableAdaptive
open TreeTyped TreeFraction ExecutableBottleneck ExecutableScaling ExecutableLadder ExecutableSource

abbrev GraphData := List ℕ×List RawLogical
abbrev ActivityData := (GraphData×List Bool)×Vector
abbrev CellData := (List RawLogical×Fraction)×Vector

def cooling (n : ℕ) : Fraction := div ((1,1),add ((1,1),div ((1,1),(n,1))))
def coolingRealizer : Realizer cooling := (composition (pair (constant (1,1))
  (composition (pair (constant (1,1)) (composition (pair (constant (1,1))
    (pair identity (constant 1))) divRealizer)) addRealizer)) divRealizer).congr (fun _=>rfl)
lemma polynomial_cooling : PolynomialTime coolingRealizer := by
  unfold coolingRealizer; apply polynomial_congr
  have := polynomial_div
  have := TreeFraction.polynomial_add
  tree_cost
lemma cooling_rep (n : ℕ) : cooling n=TreeFraction.repr (FiniteTrial.cooling n) := by
  unfold cooling FiniteTrial.cooling
  rw [←repr_nat n,show ((1,1) : Fraction)=TreeFraction.repr (1:ℚ) from rfl,
    div_repr (by decide) (by positivity),add_repr (by decide) (by positivity),
    div_repr (by decide) (by positivity),one_div]

def cellData (x : ActivityData) : CellData :=
  ((x.1.1.2,fuelPower (cooling x.1.1.1.length,x.1.2)),x.2)
def cellDataRealizer : Realizer cellData := (pair
  (pair first.fst.snd (composition (pair (composition (composition first.fst.fst listLength) coolingRealizer)
    first.snd) fuelPowerRealizer)) second).congr (fun _=>rfl)
lemma polynomial_cellData : PolynomialTime cellDataRealizer := by
  unfold cellDataRealizer; apply polynomial_congr
  have := polynomial_cooling
  have := polynomial_fuelPower
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

def rawCell (x : CellData×RawLogical) : Fraction :=
  if orderedPair x.2∈x.1.1.1 then (1,1) else x.1.1.2
def rawCellRealizer : Realizer rawCell := (choose
  (composition (pair (composition second orderedPairRealizer) first.fst.fst)
    (contains (pairEqual natEqual natEqual))) (constant (1,1)) first.fst.snd).congr (by
      intro x; simp [rawCell])
lemma polynomial_rawCell : PolynomialTime rawCellRealizer := by
  unfold rawCellRealizer; apply polynomial_congr
  have := polynomial_orderedPair
  have := polynomial_contains (polynomial_pairEqual polynomial_natEqual polynomial_natEqual)
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

def stageCell (x : CellData×RawLogical) : Fraction :=
  mul (mul (rawCell x,lookup (1,1) (x.1.2,x.2.1)),lookup (1,1) (x.1.2,x.2.2))
def stageCellRealizer : Realizer stageCell := (composition
  (pair (composition (pair rawCellRealizer (composition (pair first.snd second.fst)
      (lookupRealizer (1,1) natEqual))) mulRealizer)
    (composition (pair first.snd second.snd) (lookupRealizer (1,1) natEqual))) mulRealizer).congr (fun _=>rfl)
lemma polynomial_stageCell : PolynomialTime stageCellRealizer := by
  unfold stageCellRealizer; apply polynomial_congr
  have := polynomial_rawCell
  have := polynomial_lookup ((1,1) : Fraction) polynomial_natEqual
  have := polynomial_mul
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

def stageRow (x : (CellData×List ℕ)×ℕ) : List Fraction :=
  x.1.2.map (fun j=>stageCell (x.1.1,(x.2,j)))
def stageRowRealizer : Realizer stageRow := (composition (pair (pair first.fst second) first.snd)
  (mapWith (composition (pair first.fst (pair first.snd second)) stageCellRealizer))).congr (fun _=>rfl)
lemma polynomial_stageRow : PolynomialTime stageRowRealizer := by
  unfold stageRowRealizer; apply polynomial_congr
  have := polynomial_stageCell
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

def stageMatrix (x : ActivityData) : Matrix :=
  x.1.1.1.map (fun i=>stageRow ((cellData x,x.1.1.1),i))
def stageMatrixRealizer : Realizer stageMatrix := (composition
  (pair (pair cellDataRealizer first.fst.fst) first.fst.fst) (mapWith stageRowRealizer)).congr (fun _=>rfl)
lemma polynomial_stageMatrix : PolynomialTime stageMatrixRealizer := by
  unfold stageMatrixRealizer; apply polynomial_congr
  have := polynomial_cellData
  have := polynomial_stageRow
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

noncomputable def graphRep (G : GraphInput) : GraphData :=
  (List.range G.n,G.edges.toList.map (fun e=>(e.1.val,e.2.val)))
lemma orderedPair_minmax (a b : ℕ) : orderedPair (a,b)=(min a b,max a b) := by
  unfold orderedPair
  by_cases h : a<b
  · simp [h,min_eq_left h.le,max_eq_right h.le]
  · simp [h,min_eq_right (le_of_not_gt h),max_eq_left (le_of_not_gt h)]
lemma edge_mem_graphRep (G : GraphInput) (i j : Fin G.n) :
    orderedPair (i.val,j.val)∈(graphRep G).2 ↔ (min i j,max i j)∈G.edges := by
  rw [orderedPair_minmax]
  simp only [graphRep,List.mem_map,Finset.mem_toList]
  constructor
  · rintro ⟨⟨a,b⟩,hab,he⟩
    have ha : a=min i j := Fin.ext (congrArg Prod.fst he)
    have hb : b=max i j := Fin.ext (congrArg Prod.snd he)
    simpa [ha,hb] using hab
  · intro h
    exact ⟨(min i j,max i j),h,rfl⟩
lemma rawCell_rep (G : GraphInput) (fuel : List Bool) (a : Fin G.n→ℚ) (i j : Fin G.n) :
    rawCell (cellData ((graphRep G,fuel),vectorRep a),(i.val,j.val))=
      TreeFraction.repr (FiniteTrial.raw G fuel.length i j) := by
  unfold rawCell cellData
  dsimp only
  simp only [edge_mem_graphRep]
  unfold FiniteTrial.raw
  split_ifs
  · rfl
  · rw [show (graphRep G).1.length=G.n by simp [graphRep],cooling_rep,
      fuelPower_repr _ (by unfold FiniteTrial.cooling; positivity)]
lemma stageMatrix_rep (G : GraphInput) (fuel : List Bool) (a : Fin G.n→ℚ) (ha : ∀ i,0 ≤ a i) :
    stageMatrix ((graphRep G,fuel),vectorRep a)=
      matrixRep (fun i j=>FiniteTrial.raw G fuel.length i j*a i*a j) := by
  have hr (i j : Fin G.n) : 0 ≤ FiniteTrial.raw G fuel.length i j := by
    unfold FiniteTrial.raw FiniteTrial.cooling
    split_ifs <;> positivity
  unfold stageMatrix stageRow matrixRep
  change (List.range G.n).map _=(List.ofFn _)
  simp only [ExecutableDP.map_range_ofFn]
  congr 1
  funext i
  change (List.range G.n).map _=List.ofFn _
  rw [ExecutableDP.map_range_ofFn]
  congr 1
  funext j
  unfold stageCell
  rw [rawCell_rep,show (cellData ((graphRep G,fuel),vectorRep a)).2=vectorRep a from rfl,
    lookup_vectorRep a i,lookup_vectorRep a j,mul_repr (hr i j) (ha i),
    mul_repr (mul_nonneg (hr i j) (ha i)) (ha j)]
end MatchingFPRAS.ExecutableAdaptive

end OAI
