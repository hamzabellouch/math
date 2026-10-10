import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.TestRowSize

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory PreparedProjectiveGeometry
open SharpLogRamsey.PointScore SharpLogRamsey.Incidence
open scoped BigOperators Classical NNReal
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedTestRowPencils_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedTestRowPencils_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedTestRowPencils_3 : Fintype (Projectivization K V) := by
  have : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

abbrev pencil (x : Projectivization K V) : Finset (Projectivization K (Module.Dual K V)) :=
  univ.filter (fun H => x.submodule ≤ LinearMap.ker H.rep)

abbrev outsideMass (S O : Finset (Projectivization K V)) (x : Projectivization K V)
    (c : ℝ≥0) (H : Projectivization K (Module.Dual K V)) : ℝ :=
  (c:ℝ)*((S\(O∪{x})).filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card

structure SecondPencil (j R : ℕ) (S O : Finset (Projectivization K V))
    (x : Projectivization K V) (c L : ℝ≥0)
    (A : Finset (Projectivization K (Module.Dual K V))) (f B C : ℝ)
    (T : Finset I) (a : I → ℝ) : Prop where
  low : ∀ H∈A,3/4≤outsideMass S O x c H
  upp : ∀ H∈A,outsideMass S O x c H≤2
  deviation : ∀ H∈A,|outsideMass S O x c H-(1-f)|≤1
  squares : (∑ H∈A,(outsideMass S O x c H-(1-f))^2)≤C*B*Real.exp ((L:ℝ)/100)
  cardinal : ((∑ i∈range j,Nat.card K^i):ℝ)≤C*B^2
  positive : ∀ i∈T,0<a i
  cover : ∀ H∈A,∀ J∈A,H≠J → 0<overlap (S\(O∪{x})) x c H J →
    ∃ i∈T,a i≤overlap (S\(O∪{x})) x c H J ∧ overlap (S\(O∪{x})) x c H J≤2*a i
  pairs : ∀ i∈T,((largePairs (S\(O∪{x})) x c (a i) A).card:ℝ)*a i^200≤B^2*Real.exp (((L:ℝ)*R)/50)
  diagonalBudget : C*2^R≤Real.exp ((L:ℝ)*R/20)
  powerBudget : (2*(L:ℝ)^2)^R≤Real.exp ((L:ℝ)*R/25)
  sumBudget : C^2*Real.exp ((L:ℝ)/50)+(T.card:ℝ)*2^R*Real.exp ((L:ℝ)*R/50)≤Real.exp ((L:ℝ)*R/20)
  twoBudget : 2≤Real.exp ((L:ℝ)*R/20)

structure HighPencil (j R p h : ℕ) (S O : Finset (Projectivization K V))
    (x : Projectivization K V) (c L : ℝ≥0)
    (A : Finset (Projectivization K (Module.Dual K V))) (f B : ℝ)
    (T : Finset I) (a : I → ℝ) : Prop where
  low : ∀ H∈A,3/4≤outsideMass S O x c H
  upp : ∀ H∈A,outsideMass S O x c H≤2
  deviation : ∀ H∈A,|outsideMass S O x c H-(1-f)|≤13/100
  squares : (∑ H∈A,(outsideMass S O x c H-(1-f))^2)≤B*Real.exp (((L:ℝ)*R)/100)
  cardinal : ((∑ i∈range j,Nat.card K^i):ℝ)≤4*B^2
  directions : ((∑ i∈range (j-1),Nat.card K^i):ℝ)≤4*B
  nonnegative : ∀ i∈T,0≤a i
  cover : ∀ H∈A,∀ J∈A,H≠J → 0<overlap (S\(O∪{x})) x c H J →
    ∃ i∈T,a i≤overlap (S\(O∪{x})) x c H J ∧ overlap (S\(O∪{x})) x c H J≤2*a i
  pairs : ∀ i∈T,((largePairs (S\(O∪{x})) x c (a i) A).card:ℝ)*a i^200≤B^2*Real.exp (((L:ℝ)*R)/50)
  neighbors : ∀ H∈A,∀ i∈T,((largeNeighbors (S\(O∪{x})) x c (a i) A H).card:ℝ)*a i^200≤B*Real.exp (((L:ℝ)*R)/50)
  strong : ∀ H∈A,((largeNeighbors (S\(O∪{x})) x c (1/(100*(p:ℝ))) A H).card:ℝ)≤B*Real.exp (-3*((L:ℝ)*R))
  certificateBudget : MomentBudgetBridge.certificateOverhead p T.card ((L:ℝ)*R)≤Real.exp (2*((L:ℝ)*R)/25)
  shiftBudget : MomentBudgetBridge.shiftOverhead p T.card≤Real.exp (2*((L:ℝ)*R)/25)
  pBudget : (p:ℝ)^2≤Real.exp (((L:ℝ)*R)/10)
  pSumBudget : 2*(p:ℝ)+3≤Real.exp (((L:ℝ)*R)/10)
  hPositive : 0<h
  hSize : h≤(R/2)/400
  hError : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2

lemma score_second_tail
    (j R : ℕ) (hdim : Module.finrank K V≤j+1)
    (S O : Finset (Projectivization K V)) (x : Projectivization K V) (c L : ℝ≥0)
    (E : Finset (Projectivization K (Module.Dual K V))) (f B C : ℝ)
    (hf : f≤1/4) (hB : 0≤B) (hC : 0≤C) (hL : 1≤(L:ℝ)) (hR : 200≤R)
    (T : Finset I) (a : I→ℝ) (hc : SecondPencil j R S O x c L (pencil x\E) f B C T a)
    (t : ℝ) (ht : 0<t) :
    (PoissonSchedules.scheduleLaw (fun _ : Fin R×S => L*c)).real
      {ω | x∉sample S ω ∧ t≤|score S O (pencil x\E)
        (fun H y => y.submodule≤LinearMap.ker H.rep) (Real.exp (-(L:ℝ)*(1-f))) ω|}≤
          B^2*Real.exp (-(3/5:ℝ)*((L:ℝ)*R))/t^2 := by
  have hh := actual_point_second_tail j hdim S O x c L (pencil x\E)
    (fun H hH => (mem_filter.mp (mem_sdiff.mp hH).1).2) f B C hf hB hC R hL hR
    hc.low hc.upp hc.deviation hc.squares hc.cardinal T a hc.positive hc.cover hc.pairs
    hc.diagonalBudget hc.powerBudget hc.sumBudget hc.twoBudget t ht
  apply le_trans (measureReal_mono (h₂:=measure_ne_top _ _) ?_) hh
  intro ω hω
  exact ⟨unsampled S ω x hω.1,hω.2⟩

lemma score_high_tail
    (j R p h : ℕ) (hj : 2≤j) (hj3 : j≤3) (hdim : Module.finrank K V≤j+1)
    (S O : Finset (Projectivization K V)) (x : Projectivization K V) (c L : ℝ≥0)
    (E : Finset (Projectivization K (Module.Dual K V))) (f B : ℝ)
    (hf : f≤1/25) (hp : 0<p) (hpe : Even p) (hL : 10000≤(L:ℝ)) (hR : 400≤R)
    (hB : Real.exp (3*((L:ℝ)*R))≤B)
    (T : Finset I) (a : I→ℝ) (hc : HighPencil j R p h S O x c L (pencil x\E) f B T a)
    (t : ℝ) (ht : 0<t) :
    (PoissonSchedules.scheduleLaw (fun _ : Fin R×S => L*c)).real
      {ω | x∉sample S ω ∧ t≤|score S O (pencil x\E)
        (fun H y => y.submodule≤LinearMap.ker H.rep) (Real.exp (-(L:ℝ)*(1-f))) ω|}≤
          B^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R)))/t^p := by
  have hh := actual_point_high_tail j hj hj3 hdim S O x c L (pencil x\E)
    (fun H hH => (mem_filter.mp (mem_sdiff.mp hH).1).2) f B hf hp hpe R hL
    hc.low hc.upp hc.deviation hB hc.cardinal hc.directions T a hc.nonnegative
    hc.cover hc.pairs hc.neighbors hc.strong hc.squares hc.certificateBudget hc.shiftBudget
    hc.pBudget hc.pSumBudget h hc.hPositive hR hc.hSize hc.hError t ht
  apply le_trans (measureReal_mono (h₂:=measure_ne_top _ _) ?_) hh
  intro ω hω
  exact ⟨unsampled S ω x hω.1,hω.2⟩

end
end SharpLogRamsey.PreparedRow

end

end OAI
