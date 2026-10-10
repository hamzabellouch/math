import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeDPCount
import OAI.Combinatorics.MatchingCount.Algorithm.TreeScalingCorrect

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck ExecutableHierarchy Polynomial

abbrev ProfileData := List Bool×(Fraction×(Fraction×(Fraction×Fraction)))
def profile (x : ProfileData×ℕ) : Fraction :=
  let p:=x.1.1.length
  let v:=x.1.2
  if x.2<2*p then maximum (v.1,div (v.2.1,threshold (x.1.1++x.1.1,x.2/2)))
  else if x.2=2*p then v.2.2.2
  else maximum (v.1,div (v.2.2.1,threshold (x.1.1++x.1.1,(4*p-x.2)/2)))
def profileRealizer : Realizer profile := by
  let p : Realizer (fun x : ProfileData×ℕ=>x.1.1.length) := composition first.fst listLength
  let twoP := composition (pair (constant 2) p) multiply
  let fourP := composition (pair (constant 4) p) multiply
  let fuel : Realizer (fun x : ProfileData×ℕ=>x.1.1++x.1.1) := composition (pair first.fst first.fst) append
  let lpow := composition (pair fuel (composition (pair second (constant 2)) quotient)) thresholdRealizer
  let rpow := composition (pair fuel (composition (pair (composition (pair fourP second) subtract) (constant 2)) quotient)) thresholdRealizer
  exact (choose (composition (pair second twoP) less)
    (composition (pair first.snd.fst (composition (pair first.snd.snd.fst lpow) divRealizer)) maximumRealizer)
    (choose (composition (pair second twoP) natEqual) first.snd.snd.snd.snd
      (composition (pair first.snd.fst (composition (pair first.snd.snd.snd.fst rpow) divRealizer)) maximumRealizer))).congr (by intro x; simp [profile])
lemma polynomial_profile : PolynomialTime profileRealizer := by
  unfold profileRealizer
  dsimp only
  apply polynomial_congr
  have := polynomial_threshold
  have := polynomial_quotient
  have := polynomial_div
  have := polynomial_maximum
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost
lemma profile_repr (fuel : List Bool) (B Hu Hv lam : ℚ)
    (hB : 0≤B) (hHu : 0≤Hu) (hHv : 0≤Hv) (_hlam : 0≤lam)
    (i : Fin (4*fuel.length+1)) :
    profile ((fuel,(TreeFraction.repr B,(TreeFraction.repr Hu,(TreeFraction.repr Hv,TreeFraction.repr lam)))),i.val)=
      TreeFraction.repr (RationalSource.profile fuel.length B Hu Hv lam i) := by
  unfold profile RationalSource.profile
  dsimp only
  split_ifs with h h'
  · have hi : i.val/2≤(fuel++fuel).length := by simp only [List.length_append]; omega
    rw [threshold_repr _ _ hi,div_repr hHu (by positivity),maximum_repr hB (by positivity)]
  · rfl
  · have hi : (4*fuel.length-i.val)/2≤(fuel++fuel).length := by simp only [List.length_append]; omega
    rw [threshold_repr _ _ hi,div_repr hHv (by positivity),maximum_repr hB (by positivity)]

def height (x : Matrix×ℕ) : Fraction :=
  ExecutableScaling.rowMax ((x.1,(List.range x.1.length).map (fun i=>(i,(1,1)))),x.2)
def heightRealizer : Realizer height :=
  composition (pair (pair first (composition (composition (composition first listLength) range)
      (map (pair identity (constant (1,1)))))) second) ExecutableScaling.rowMaxRealizer
lemma polynomial_height : PolynomialTime heightRealizer := by
  unfold heightRealizer
  have hh : PolynomialTime (composition (composition (first (A:=Matrix) (B:=ℕ)) listLength) range) := by
    apply polynomial_boundedRange (by tree_cost) X
    intro x
    simpa only [eval_X,Function.comp_apply] using (list_length_le_weight x.1).trans (weight_fst x)
  apply polynomial_composition _ ExecutableScaling.polynomial_rowMax
  tree_cost
lemma height_rep {n : ℕ} (hn : 2≤n) (B : Fin n→Fin n→ℚ) (hB : ∀ i j,0≤B i j) (i : Fin n) :
    height (matrixRep B,i.val)=TreeFraction.repr
      ((Finset.univ.erase i).sup' (Counting.others_nonempty hn i) (B i)) := by
  have he : (List.range (matrixRep B).length).map (fun i=>(i,((1,1) : Fraction)))=
      ExecutableScaling.vectorRep (fun _ : Fin n=>(1:ℚ)) := by
    rw [matrixRep_length]
    unfold ExecutableScaling.vectorRep
    rw [ExecutableDP.map_range_ofFn]
    rfl
  unfold height
  dsimp only
  rw [he,ExecutableScaling.rowMax_rep hn B (fun _=>1) (fun i j _=>hB i j) (by intro j; norm_num) i]
  simp only [Counting.rowMaximum,div_one]

def maxHeight (M : Matrix) : Fraction :=
  ((List.range M.length).map (fun i=>height (M,i))).foldl (fun a b=>maximum (b,a)) (0,1)
def maxHeightRealizer : Realizer maxHeight := (composition
  (pair (composition (pair identity (composition listLength range)) (mapWith heightRealizer)) (constant (0,1)))
  (fold maximumRealizer)).congr (fun _=>rfl)
lemma polynomial_maxHeight : PolynomialTime maxHeightRealizer := by
  unfold maxHeightRealizer
  apply polynomial_congr
  have hr:PolynomialTime (composition (listLength (A:=List Fraction)) range) := by
    apply polynomial_boundedRange polynomial_listLength X
    intro M; simpa only [eval_X] using list_length_le_weight M
  have := polynomial_height
  have := polynomial_maximumFold
  tree_cost
end MatchingFPRAS.ExecutableSource

end OAI
