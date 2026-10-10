import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeBuild
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineCoolingSchedule

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped TreeFraction Polynomial ExecutableSource Transport Enlargement

abbrev LadderInput := (ℕ×ℕ)×ℕ

def vertexNumber (x : ℕ×ℕ) : ℕ :=
  (vertices (List.range x.1,List.replicate (2*x.2+2) false)).length
def vertexNumberRealizer : Realizer vertexNumber :=
  composition (composition (pair (composition first range)
    (composition (((constant 2).mulNat second).addNat (constant 2)) fuelRealizer)) verticesRealizer) listLength
lemma vertexNumber_eq (n K : ℕ) : vertexNumber (n,K)=Fintype.card (SourceVertex (Fin n) K) := by
  unfold vertexNumber
  rw [vertices_eq_ofFn_length n _ (4*(2*K+2)) (by simp),List.length_ofFn]
lemma vertexNumber_bound (n K : ℕ) : vertexNumber (n,K)≤n+n^2*(4*(2*K+2)) := by
  have hprod {A B : Type} (a : List A) (b : List B) :
      (a.product b).length=a.length*b.length := List.length_product a b
  unfold vertexNumber vertices internalCount
  simp only [List.length_append,List.length_map,hprod,List.length_range,List.length_replicate]
  have h : (logicalEdges (List.range n)).length≤n*n := by
    simpa only [logicalEdges,hprod,List.length_range] using
      List.length_filter_le (fun e : ℕ×ℕ=>decide (e.1<e.2)) ((List.range n).product (List.range n))
  simpa only [pow_two] using Nat.add_le_add_left (Nat.mul_le_mul_right (4*(2*K+2)) h) n

def distortion (x : ℕ×ℕ) : ℕ := 100*x.2^2*(100000000*(x.1+1)^4)
def distortionRealizer : Realizer distortion :=
  (((constant 100).mulNat (composition second (fixedPower 2))).mulNat
    ((constant 100000000).mulNat (composition (composition first successor) (fixedPower 4)))).congr (fun _=>rfl)
lemma polynomial_distortion : PolynomialTime distortionRealizer := by
  unfold distortionRealizer;apply polynomial_congr
  have := polynomial_fixedPower 2
  have := polynomial_fixedPower 4
  have := polynomial_successor
  simp only [Realizer.mulNat]; tree_cost
lemma distortion_source {G : GraphInput} [Nontrivial (Fin G.n)] (K : ℕ) :
    distortion (G.n,vertexNumber (G.n,K))=FiniteTrial.sourceD (G:=G) K := by
  simp only [distortion,vertexNumber_eq,FiniteTrial.sourceD]

def tierBoundRealizer : Realizer (fun x : LadderInput=>tierBound x.1.1 x.1.2 x.2) :=
  ((composition first.fst (fixedPower 2)).mulNat
    (((composition first.snd clogTwo).addNat ((constant 2).mulNat second)).addNat (constant 2))).congr (fun _=>rfl)
lemma polynomial_tierBound : PolynomialTime tierBoundRealizer := by
  unfold tierBoundRealizer;apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_fixedPower 2
  have := polynomial_clogTwo
  simp only [Realizer.mulNat,Realizer.addNat]; tree_cost

def ladderPowerPlan (x : (ℕ×ℕ)×List Bool) : Fraction×Fraction :=
  (TreeFraction.add ((1,1),TreeFraction.div ((1,1),(x.1.1^2,1))),
    TreeFraction.maximum ((x.1.2,1),TreeFraction.mul ((3,1),fuelPower ((4,1),x.2))))
def ladderPowerPlanRealizer : Realizer ladderPowerPlan :=
  (pair (composition (pair (constant (1,1))
    (composition (pair (constant (1,1)) (pair (composition first.fst (fixedPower 2)) (constant 1))) divRealizer)) addRealizer)
    (composition (pair (pair first.snd (constant 1))
      (composition (pair (constant (3,1)) (composition (pair (constant (4,1)) second) fuelPowerRealizer)) mulRealizer)) maximumRealizer)).congr (fun _=>rfl)
lemma polynomial_ladderPowerPlan : PolynomialTime ladderPowerPlanRealizer := by
  unfold ladderPowerPlanRealizer; apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_div
  have := polynomial_mul
  have := TreeFraction.polynomial_add
  have := TreeFraction.polynomial_maximum
  have := polynomial_fuelPower
  have := polynomial_fixedPower 2
  tree_cost
lemma ladderPowerPlan_repr (N D : ℕ) (fuel : List Bool) :
    ladderPowerPlan ((N,D),fuel)=
      (TreeFraction.repr (rationalBase N),TreeFraction.repr (max (D:ℚ) (3*4^fuel.length))) := by
  unfold ladderPowerPlan
  rw [←repr_nat (N^2),←repr_nat D,
    show ((1,1) : Fraction)=TreeFraction.repr (1:ℚ) from rfl,
    show ((3,1) : Fraction)=TreeFraction.repr (3:ℚ) from rfl,
    show ((4,1) : Fraction)=TreeFraction.repr (4:ℚ) from rfl,
    div_repr (by decide) (by positivity),add_repr (by decide) (by positivity),
    fuelPower_repr _ (by positivity),mul_repr (by decide) (by positivity),
    maximum_repr (by positivity) (by positivity)]
  simp only [rationalBase,Nat.cast_pow,one_div]

def ladderSearchInput (x : LadderInput) : PowerSearchInput :=
  (ladderPowerPlan (x.1,List.replicate x.2 false),List.replicate (tierBound x.1.1 x.1.2 x.2) false)
def ladderSearchInputRealizer : Realizer ladderSearchInput :=
  pair (composition (pair first (composition second fuelRealizer)) ladderPowerPlanRealizer)
    (composition tierBoundRealizer fuelRealizer)
def ladderSchedule (x : LadderInput) : ℕ := findPower (ladderSearchInput x)
def ladderScheduleRealizer : Realizer ladderSchedule := composition ladderSearchInputRealizer findPowerRealizer
lemma ladderSchedule_eq (N D K : ℕ) (hN : 0<N) :
    ladderSchedule ((N,D),K)=endpoint N D K hN := by
  unfold ladderSchedule ladderSearchInput
  rw [ladderPowerPlan_repr,List.length_replicate]
  exact findPower_endpoint N D K hN _ (by simp)
end MatchingFPRAS.OnlineSchedule

end OAI
