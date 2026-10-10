import Mathlib
import OAI.Probability.SKFluctuations.ClockTestAbsLeMul

namespace OAI

/-! Cumulative Increments. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*}

 

def cumulativeIncrements (l : ι → ℝ) (q : ℕ → ι → ℝ) : ℕ → ι → ℝ≥0
  | 0, i => Real.toNNReal (q 0 i-l i)
  | k+1, i => Real.toNNReal (q (k+1) i-q k i)

 theorem cumulativeIncrements_shift (l : ι → ℝ) (q : ℕ → ι → ℝ) :
    (fun k => cumulativeIncrements l q (k+1)) =
      cumulativeIncrements (q 0) (fun k => q (k+1)) := by
  funext k i
  cases k <;> rfl

 theorem clockSteps_cumulative (as : List PositiveMass) (l : ι → ℝ) (q : ℕ → ι → ℝ) :
    clockSteps as (cumulativeIncrements l q) = diagonalBoundarySteps as l q := by
  induction as generalizing l q with
  | nil => rfl
  | cons a as ih =>
    simp only [clockSteps,diagonalBoundarySteps,cumulativeIncrements_shift,ih]
    rfl

 theorem clockSteps_congr (as : List PositiveMass) {q r : ℕ → ι → ℝ≥0}
    (he : ∀ k < as.length, q k = r k) : clockSteps as q = clockSteps as r := by
  induction as generalizing q r with
  | nil => rfl
  | cons a as ih =>
    rw [clockSteps,clockSteps,he 0 (by simp),ih]
    intro k hk
    exact he (k+1) (by simpa using Nat.succ_lt_succ hk)

variable [Fintype ι] [Fintype S]
 theorem ClockTree.weight_congr (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) {q r : ℕ → ι → ℝ≥0}
    (he : ∀ k < as.length, q k = r k) (σ : T.Assignment) (x : ι → ℝ) :
    T.weight w φ q σ x = T.weight w φ r σ x := by
  induction T generalizing q r x with
  | leaf => rfl
  | @step a as T ih =>
    have ht : ∀ k < as.length, q (k+1) = r (k+1) := fun k hk =>
      he (k+1) (by simpa using Nat.succ_lt_succ hk)
    rw [ClockTree.weight_step,ClockTree.weight_step,he 0 (by simp),clockSteps_congr as ht]
    congr 1
    funext y
    exact ih ht σ y
  | fork T U ihT ihU =>
    rw [ClockTree.weight_fork,ClockTree.weight_fork,ihT he,ihU he]

 theorem ClockTree.cumulative_weight_congr (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (l : ι → ℝ) {q r : ℕ → ι → ℝ}
    (he : ∀ k < as.length, q k = r k) (σ : T.Assignment) (x : ι → ℝ) :
    T.weight w φ (cumulativeIncrements l q) σ x = T.weight w φ (cumulativeIncrements l r) σ x := by
  refine T.weight_congr w φ ?_ σ x
  intro k hk
  cases k with
  | zero =>
    funext i
    change Real.toNNReal (q 0 i-l i) = Real.toNNReal (r 0 i-l i)
    rw [he 0 hk]
  | succ k =>
    funext i
    change Real.toNNReal (q (k+1) i-q k i) = Real.toNNReal (r (k+1) i-r k i)
    rw [he (k+1) hk,he k (by omega)]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*}

def previousBoundary (l : ι → ℝ) (q : ℕ → ι → ℝ) : ℕ → ι → ℝ
  | 0 => l
  | k+1 => q k

 theorem cumulativeIncrements_eq (l : ι → ℝ) (q : ℕ → ι → ℝ) (j : ℕ) (i : ι) :
    cumulativeIncrements l q j i = Real.toNNReal (q j i-previousBoundary l q j i) := by
  cases j <;> rfl

 theorem previousBoundary_le {l : ι → ℝ} {q : ℕ → ι → ℝ}
    (hq : ∀ i, Monotone (fun k => q k i)) (hl : ∀ i, l i ≤ q 0 i) (j : ℕ) (i : ι) :
    previousBoundary l q j i ≤ q j i := by
  cases j with
  | zero => exact hl i
  | succ j => exact hq i (Nat.le_succ j)

 theorem cumulativeIncrements_split (l : ι → ℝ) (q : ℕ → ι → ℝ) (j : ℕ)
    {d : ι → ℝ} (hd : ∀ i, previousBoundary l q j i ≤ d i) (hdq : ∀ i, d i ≤ q j i) :
    cumulativeIncrements l q = mixClocks j (cumulativeIncrements l q)
      (prependClock (fun i => Real.toNNReal (d i-previousBoundary l q j i)+Real.toNNReal (q j i-d i))
        (fun k => cumulativeIncrements l q (j+1+k))) := by
  funext k i
  by_cases hk : k < j
  · simp [mixClocks,hk]
  · have hjk : j ≤ k := by omega
    rw [mixClocks,ite_eq_right hk]
    by_cases he : k=j
    · subst k
      simp only [Nat.sub_self,prependClock]
      rw [cumulativeIncrements_eq]
      apply NNReal.coe_injective
      simp only [NNReal.coe_add,Real.coe_toNNReal _ (sub_nonneg.mpr (hd i)),
        Real.coe_toNNReal _ (sub_nonneg.mpr (hdq i)),
        Real.coe_toNNReal _ (sub_nonneg.mpr ((hd i).trans (hdq i)))]
      ring
    · obtain ⟨t,ht⟩ : ∃ t, k-j=t+1 := ⟨k-j-1,by omega⟩
      rw [ht,prependClock]
      have : j+1+t=k := by omega
      rw [this]

 theorem cumulativeIncrements_update (l : ι → ℝ) (q : ℕ → ι → ℝ) (j : ℕ)
    {d : ι → ℝ} (hdq : ∀ i, d i ≤ q j i) (hq : ∀ i, q j i ≤ q (j+1) i) :
    cumulativeIncrements l (Function.update q j d) = mixClocks j (cumulativeIncrements l q)
      (prependClock (fun i => Real.toNNReal (d i-previousBoundary l q j i))
        (addHeadClock (fun k => cumulativeIncrements l q (j+1+k)) (fun i => Real.toNNReal (q j i-d i)))) := by
  funext k i
  by_cases hk : k < j
  · rw [mixClocks,ite_eq_left hk]
    rw [cumulativeIncrements_eq,cumulativeIncrements_eq]
    have hkne : k ≠ j := by omega
    rw [Function.update_of_ne hkne]
    congr 2
    cases k with
    | zero => rfl
    | succ k =>
      change Function.update q j d k i = q k i
      rw [Function.update_of_ne (by omega : k ≠ j)]
  · rw [mixClocks,ite_eq_right hk]
    by_cases he : k=j
    · subst k
      simp only [Nat.sub_self,prependClock,cumulativeIncrements_eq,Function.update_self]
      congr 2
      cases j with
      | zero => rfl
      | succ j =>
        change Function.update q (j+1) d j i = q j i
        rw [Function.update_of_ne (by omega : j ≠ j+1)]
    · by_cases he1 : k=j+1
      · subst k
        rw [show j+1-j=1 by omega]
        simp only [prependClock,addHeadClock,cumulativeIncrements,
          Function.update_of_ne (by omega : j+1 ≠ j),Function.update_self]
        apply NNReal.coe_injective
        simp only [NNReal.coe_add,Real.coe_toNNReal _ (sub_nonneg.mpr (hdq i)),
          Real.coe_toNNReal _ (sub_nonneg.mpr (hq i)),
          Real.coe_toNNReal _ (sub_nonneg.mpr ((hdq i).trans (hq i)))]
        ring
      · obtain ⟨t,ht⟩ : ∃ t, k-j=t+2 := ⟨k-j-2,by omega⟩
        rw [ht]
        change cumulativeIncrements l (Function.update q j d) k i = cumulativeIncrements l q (j+1+(t+1)) i
        rw [show j+1+(t+1)=k by omega,cumulativeIncrements_eq,cumulativeIncrements_eq,
          Function.update_of_ne he]
        congr 2
        cases k with
        | zero => omega
        | succ k =>
          change Function.update q j d k i = q k i
          rw [Function.update_of_ne (by omega : k ≠ j)]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*}

 theorem MassOrdered.pairwise {a : ℝ} {as : List PositiveMass} (ho : MassOrdered a as) :
    as.Pairwise (fun b c => b.val ≤ c.val) := by
  have hall : ∀ a (as : List PositiveMass), MassOrdered a as → ∀ b ∈ as, a ≤ b.val := by
    intro a as
    induction as generalizing a with
    | nil => simp
    | cons b bs ih =>
      intro h c hc
      rcases List.mem_cons.mp hc with rfl|hc
      · exact h.2.1
      · exact h.2.1.trans (ih b.val h.2.2 c hc)
  induction as generalizing a with
  | nil => simp
  | cons b bs ih => exact List.pairwise_cons.mpr ⟨hall b.val bs ho.2.2,ih ho.2.2⟩

 theorem MassOrdered.members_le_one {a : ℝ} {as : List PositiveMass} (ho : MassOrdered a as) :
    ∀ b ∈ as, b.val ≤ 1 := by
  induction as generalizing a with
  | nil => simp
  | cons b bs ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl|hc
    · exact (massOrdered_bounds ho.2.2).2
    · exact ih ho.2.2 c hc

 theorem MassOrdered.of_pairwise {as : List PositiveMass}
    (hp : as.Pairwise (fun b c => b.val ≤ c.val)) (hu : ∀ b ∈ as, b.val ≤ 1)
    {a : ℝ} (ha : 0 ≤ a) (hl : ∀ b ∈ as, a ≤ b.val) (ha1 : a ≤ 1) : MassOrdered a as := by
  induction as generalizing a with
  | nil => exact ⟨ha,ha1⟩
  | cons b bs ih =>
    refine ⟨ha,hl b List.mem_cons_self,?_⟩
    exact ih (List.pairwise_cons.mp hp).2 (fun c hc => hu c (List.mem_cons_of_mem _ hc))
      b.property.le (List.pairwise_cons.mp hp).1 (hu b List.mem_cons_self)

 theorem MassOrdered.tail_at {as : List PositiveMass} (ho : MassOrdered 0 as)
    (j : ℕ) {a b : PositiveMass} {bs : List PositiveMass} (he : as.drop j = a::b::bs) :
    MassOrdered a.val (b::bs) := by
  have hp := (ho.pairwise.sublist (List.drop_sublist j as))
  have hu : ∀ c ∈ as.drop j, c.val ≤ 1 := fun c hc => ho.members_le_one c (List.mem_of_mem_drop hc)
  rw [he] at hp hu
  exact MassOrdered.of_pairwise (List.pairwise_cons.mp hp).2
    (fun c hc => hu c (List.mem_cons_of_mem _ hc)) a.property.le
    (List.pairwise_cons.mp hp).1 (hu a List.mem_cons_self)

 theorem MassOrdered.prefix {a : ℝ} {as : List PositiveMass} (ho : MassOrdered a as)
    (j : ℕ) (q : ℕ → ι → ℝ≥0) : PrefixOrdered a 1 (clockSteps (as.take j) q) := by
  induction as generalizing a j q with
  | nil => simpa [clockSteps,PrefixOrdered] using massOrdered_bounds ho
  | cons b bs ih =>
    cases j with
    | zero => exact massOrdered_bounds ho
    | succ j => exact ⟨ho.1,ho.2.1,b.property,ih ho.2.2 j (fun k => q (k+1))⟩

 
def massGap : List PositiveMass → ℕ → ℝ
  | [],_ => 0
  | [_],_ => 0
  | a::b::_bs,0 => |a.val-b.val|
  | _::b::bs,j+1 => massGap (b::bs) j

 theorem massGap_nonneg (as : List PositiveMass) (j : ℕ) : 0 ≤ massGap as j := by
  induction as generalizing j with
  | nil => rfl
  | cons a bs ih =>
    cases bs with
    | nil => rfl
    | cons b bs => cases j with
      | zero => exact abs_nonneg _
      | succ j => exact ih j

 theorem massGap_drop (as : List PositiveMass) (j : ℕ) : massGap as j = massGap (as.drop j) 0 := by
  induction as generalizing j with
  | nil => simp [massGap]
  | cons a bs ih =>
    cases j with
    | zero => rfl
    | succ j =>
      cases bs with
      | nil => simp [massGap]
      | cons b bs => exact ih j

 theorem massGap_sum (as : List PositiveMass) :
    ∑ j ∈ Finset.range as.length, massGap as j = boundaryCost as (fun _ => 1) (fun _ => 0) := by
  induction as with
  | nil => rfl
  | cons a bs ih =>
    cases bs with
    | nil => simp [massGap,boundaryCost]
    | cons b bs =>
      rw [List.length_cons,Finset.sum_range_succ']
      change (∑ j ∈ Finset.range (b::bs).length, massGap (b::bs) j)+|a.val-b.val| = _
      rw [ih]
      simp only [boundaryCost,sub_zero,abs_one,mul_one]
      ring

 theorem massGap_sum_le_one {as : List PositiveMass} (ho : MassOrdered 0 as) :
    ∑ j ∈ Finset.range as.length, massGap as j ≤ 1 := by
  rw [massGap_sum]
  exact boundaryCost_uniform (by norm_num) ho.pairwise ho.members_le_one (by intro i hi; norm_num)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 

 theorem ClockTree.cumulative_boundary_move {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (j : ℕ) {a b : PositiveMass} {bs : List PositiveMass}
    (he : as.drop j = a::b::bs)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (l : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (d : Fin (n+1) → ℝ)
    (hd : ∀ i, previousBoundary l q j i ≤ d i) (hdq : ∀ i, d i ≤ q j i)
    (hq : ∀ i, q j i ≤ q (j+1) i) (x : Fin (n+1) → ℝ) :
    ∑ σ, |T.weight w φ (cumulativeIncrements l q) σ x-
      T.weight w φ (cumulativeIncrements l (Function.update q j d)) σ x| ≤
      (7*(T.leaves:ℝ)*massGap as j+8*(T.leaves:ℝ)*(T.leaves+1:ℝ)*T.forksAt (j+1))*
        ∑ i, (q j i-d i)*(D i)^2 := by
  let p := cumulativeIncrements l q
  let s := fun k => cumulativeIncrements l q (j+1+k)
  let u := fun i => Real.toNNReal (d i-previousBoundary l q j i)
  let v := fun i => Real.toNNReal (q j i-d i)
  have hh := T.cut_boundary_transfer hw φ j he (ho.tail_at j he) D hD hB p s u v
    (ho.prefix j p) (by norm_num : (1:ℝ) ≤ 1) x
  have hOld := cumulativeIncrements_split l q j hd hdq
  have hNew := cumulativeIncrements_update l q j hdq hq
  dsimp only [p,s,u,v] at hh
  rw [←hNew,←hOld] at hh
  rw [massGap_drop as j,he]
  simp only [massGap]
  simpa only [Real.coe_toNNReal _ (sub_nonneg.mpr (hdq _))] using hh

 

 theorem ClockTree.cumulative_boundary_move_at {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (j : ℕ) (hj : j+1 < as.length)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (l : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (d : Fin (n+1) → ℝ)
    (hd : ∀ i, previousBoundary l q j i ≤ d i) (hdq : ∀ i, d i ≤ q j i)
    (hq : ∀ i, q j i ≤ q (j+1) i) (x : Fin (n+1) → ℝ) :
    ∑ σ, |T.weight w φ (cumulativeIncrements l q) σ x-
      T.weight w φ (cumulativeIncrements l (Function.update q j d)) σ x| ≤
      (7*(T.leaves:ℝ)*massGap as j+8*(T.leaves:ℝ)*(T.leaves+1:ℝ)*T.forksAt (j+1))*
        ∑ i, (q j i-d i)*(D i)^2 := by
  have hl : 2 ≤ (as.drop j).length := by simp only [List.length_drop]; omega
  cases he : as.drop j with
  | nil => simp only [he,List.length_nil] at hl; omega
  | cons a cs =>
    cases cs with
    | nil => simp only [he,List.length_cons,List.length_nil] at hl; omega
    | cons b bs => exact T.cumulative_boundary_move hw φ ho j he D hD hB l q d hd hdq hq x

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*}

 

def loweredBoundary (j : ℕ) (q r : ℕ → ι → ℝ) (k : ℕ) (i : ι) : ℝ :=
  if k<j then min (q k i) (r k i) else q k i

 theorem loweredBoundary_zero (q r : ℕ → ι → ℝ) : loweredBoundary 0 q r = q := by
  funext k i
  simp [loweredBoundary]

 theorem loweredBoundary_mono {q r : ℕ → ι → ℝ}
    (hq : ∀ i, Monotone (fun k => q k i)) (hr : ∀ i, Monotone (fun k => r k i)) (j : ℕ) (i : ι) :
    Monotone (fun k => loweredBoundary j q r k i) := by
  intro k t hkt
  dsimp [loweredBoundary]
  split_ifs with hk ht
  · exact min_le_min (hq i hkt) (hr i hkt)
  · exact (min_le_left _ _).trans (hq i hkt)
  · omega
  · exact hq i hkt

 theorem loweredBoundary_initial {l : ι → ℝ} {q r : ℕ → ι → ℝ}
    (hql : ∀ i, l i ≤ q 0 i) (hrl : ∀ i, l i ≤ r 0 i) (j : ℕ) (i : ι) :
    l i ≤ loweredBoundary j q r 0 i := by
  dsimp [loweredBoundary]
  split_ifs
  · exact le_min (hql i) (hrl i)
  · exact hql i

 theorem loweredBoundary_update (j : ℕ) (q r : ℕ → ι → ℝ) :
    loweredBoundary (j+1) q r = Function.update (loweredBoundary j q r) j
      (fun i => min (q j i) (r j i)) := by
  funext k i
  by_cases hk : k=j
  · subst k
    simp [loweredBoundary]
  · rw [Function.update_of_ne hk]
    have he : k<j+1 ↔ k<j := by omega
    simp [loweredBoundary,he]

 theorem loweredBoundary_previous {l : ι → ℝ} {q r : ℕ → ι → ℝ}
    (hq : ∀ i, Monotone (fun k => q k i)) (hr : ∀ i, Monotone (fun k => r k i))
    (hql : ∀ i, l i ≤ q 0 i) (hrl : ∀ i, l i ≤ r 0 i) (j : ℕ) (i : ι) :
    previousBoundary l (loweredBoundary j q r) j i ≤ min (q j i) (r j i) := by
  cases j with
  | zero => exact le_min (hql i) (hrl i)
  | succ j =>
    change loweredBoundary (j+1) q r j i ≤ _
    simp only [loweredBoundary,Nat.lt_succ_self,ite_eq_left]
    exact min_le_min (hq i (Nat.le_succ j)) (hr i (Nat.le_succ j))

 theorem loweredBoundary_difference {q r : ℕ → ι → ℝ} (j : ℕ) (i : ι) :
    loweredBoundary j q r j i-min (q j i) (r j i) ≤ |q j i-r j i| := by
  simp only [loweredBoundary,lt_self_iff_false,ite_false]
  rcases le_total (q j i) (r j i) with h|h
  · rw [min_eq_left h,sub_self]
    exact abs_nonneg _
  · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem finite_law_triangle_chain {α : Type*} [Fintype α] (p : ℕ → α → ℝ)
    (E : ℕ → ℝ) (N : ℕ) (hE : ∀ j < N, ∑ σ, |p j σ-p (j+1) σ| ≤ E j) :
    ∑ σ, |p 0 σ-p N σ| ≤ ∑ j ∈ Finset.range N, E j := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hh := ih (fun j hj => hE j (Nat.lt_succ_of_lt hj))
    calc
      _ ≤ (∑ σ, |p 0 σ-p N σ|)+∑ σ, |p N σ-p (N+1) σ| := by
        rw [←Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun σ _ => abs_sub_le _ _ _
      _ ≤ _ := by simpa only [Finset.sum_range_succ] using add_le_add hh (hE N (Nat.lt_succ_self _))

variable {S : Type*} {as : List PositiveMass}
 theorem ClockTree.forks_sum_shift_le (T : ClockTree S as) (N : ℕ) (hN : N ≤ as.length) :
    ∑ j ∈ Finset.range N, (T.forksAt (j+1):ℝ) ≤ T.leaves := by
  have hn : ∑ j ∈ Finset.range N, T.forksAt (j+1) ≤ T.leaves := by
    calc
      _ ≤ ∑ j ∈ Finset.range as.length, T.forksAt (j+1) :=
        Finset.sum_le_sum_of_subset (Finset.range_mono hN)
      _ ≤ ∑ j ∈ Finset.range (as.length+1), T.forksAt j := by
        rw [Finset.sum_range_succ']
        omega
      _ ≤ T.leaves := by have := T.forks_total; omega
  exact_mod_cast hn

 theorem massGap_sum_prefix_le_one (ho : MassOrdered 0 as) (N : ℕ) (hN : N ≤ as.length) :
    ∑ j ∈ Finset.range N, massGap as j ≤ 1 := by
  apply le_trans _ (massGap_sum_le_one ho)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN) (fun j _ _ => massGap_nonneg as j)

variable [Fintype S] [Nonempty S] {n : ℕ}

 

 theorem ClockTree.cumulative_lowering {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (T : ClockTree S as)
    (ho : MassOrdered 0 as) (D M : Fin (n+1) → ℝ)
    (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (l : Fin (n+1) → ℝ) (q r : ℕ → Fin (n+1) → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i))
    (hql : ∀ i, l i ≤ q 0 i) (hrl : ∀ i, l i ≤ r 0 i)
    (hM : ∀ i, 0 ≤ M i) (hm : ∀ i j, j < as.length → |q j i-r j i| ≤ M i)
    (x : Fin (n+1) → ℝ) :
    ∑ σ, |T.weight w φ (cumulativeIncrements l q) σ x-
      T.weight w φ (cumulativeIncrements l (loweredBoundary (as.length-1) q r)) σ x| ≤
      (7*(T.leaves:ℝ)+8*(T.leaves:ℝ)^2*(T.leaves+1:ℝ))*∑ i, M i*(D i)^2 := by
  let K : ℝ := ∑ i, M i*(D i)^2
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ => mul_nonneg (hM i) (sq_nonneg _)
  let E := fun j => (7*(T.leaves:ℝ)*massGap as j+8*(T.leaves:ℝ)*(T.leaves+1:ℝ)*T.forksAt (j+1))*K
  have hstep (j : ℕ) (hj : j < as.length-1) :
      ∑ σ, |T.weight w φ (cumulativeIncrements l (loweredBoundary j q r)) σ x-
        T.weight w φ (cumulativeIncrements l (loweredBoundary (j+1) q r)) σ x| ≤ E j := by
    have hh := T.cumulative_boundary_move_at hw φ ho j (by omega) D hD hB l (loweredBoundary j q r)
      (fun i => min (q j i) (r j i)) (loweredBoundary_previous hq hr hql hrl j)
      (fun i => by simp only [loweredBoundary,lt_self_iff_false,ite_false]; exact min_le_left _ _)
      (fun i => loweredBoundary_mono hq hr j i (Nat.le_succ j)) x
    rw [←loweredBoundary_update] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by
      have hg := massGap_nonneg as j
      positivity)
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
      ((loweredBoundary_difference j i).trans (hm i j (by omega))) (sq_nonneg _)
  have hh := finite_law_triangle_chain
    (fun j σ => T.weight w φ (cumulativeIncrements l (loweredBoundary j q r)) σ x)
    E (as.length-1) hstep
  rw [loweredBoundary_zero] at hh
  apply hh.trans
  have hg := massGap_sum_prefix_le_one ho (as.length-1) (by omega)
  have hf := T.forks_sum_shift_le (as.length-1) (by omega)
  have hgm := mul_le_mul_of_nonneg_left hg (show 0 ≤ 7*(T.leaves:ℝ) by positivity)
  have hfm := mul_le_mul_of_nonneg_left hf (show 0 ≤ 8*(T.leaves:ℝ)*(T.leaves+1:ℝ) by positivity)
  dsimp only [E]
  rw [←Finset.sum_mul,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
  apply mul_le_mul_of_nonneg_right _ hK
  nlinarith

 

 theorem ClockTree.cumulative_uniform {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (T : ClockTree S as)
    (ho : MassOrdered 0 as) (D M : Fin (n+1) → ℝ)
    (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (l : Fin (n+1) → ℝ) (q r : ℕ → Fin (n+1) → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i))
    (hql : ∀ i, l i ≤ q 0 i) (hrl : ∀ i, l i ≤ r 0 i)
    (hend : q (as.length-1) = r (as.length-1))
    (hM : ∀ i, 0 ≤ M i) (hm : ∀ i j, j < as.length → |q j i-r j i| ≤ M i)
    (x : Fin (n+1) → ℝ) :
    ∑ σ, |T.weight w φ (cumulativeIncrements l q) σ x-
      T.weight w φ (cumulativeIncrements l r) σ x| ≤
      2*(7*(T.leaves:ℝ)+8*(T.leaves:ℝ)^2*(T.leaves+1:ℝ))*∑ i, M i*(D i)^2 := by
  have hQ := T.cumulative_lowering hw φ ho D M hD hB l q r hq hr hql hrl hM hm x
  have hR := T.cumulative_lowering hw φ ho D M hD hB l r q hr hq hrl hql hM
    (fun i j hj => by rw [abs_sub_comm]; exact hm i j hj) x
  have he (σ : T.Assignment) :
      T.weight w φ (cumulativeIncrements l (loweredBoundary (as.length-1) q r)) σ x =
      T.weight w φ (cumulativeIncrements l (loweredBoundary (as.length-1) r q)) σ x := by
    apply T.cumulative_weight_congr w φ l _ σ x
    intro k hk
    funext i
    by_cases hkl : k < as.length-1
    · simp only [loweredBoundary,hkl,ite_true,min_comm]
    · have hek : k=as.length-1 := by omega
      subst k
      simp only [loweredBoundary,lt_self_iff_false,ite_false]
      exact congrFun hend i
  calc
    _ ≤ (∑ σ, |T.weight w φ (cumulativeIncrements l q) σ x-
          T.weight w φ (cumulativeIncrements l (loweredBoundary (as.length-1) q r)) σ x|)+
        ∑ σ, |T.weight w φ (cumulativeIncrements l r) σ x-
          T.weight w φ (cumulativeIncrements l (loweredBoundary (as.length-1) r q)) σ x| := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro σ _
      rw [he σ,abs_sub_comm (T.weight w φ (cumulativeIncrements l r) σ x)]
      exact abs_sub_le _ _ _
    _ ≤ _ := by convert add_le_add hQ hR using 1; first | rfl | ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 theorem ClockTree.cut_mix_close {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (j : ℕ) (q r s : ℕ → ι → ℝ≥0) (hj : j ≤ as.length)
    {a m K : ℝ} (ha : MassOrdered a (as.drop j)) (hK : 0 ≤ K)
    (hF : ∀ y, |gaussianHierarchy w φ (clockSteps (as.drop j) r) y-
      gaussianHierarchy w φ (clockSteps (as.drop j) s) y| ≤ K)
    (E : ClockTree S (as.drop j) → ℝ)
    (hE : ∀ U σ y, ExpClose (E U) (U.weight w φ r σ y) (U.weight w φ s σ y))
    (hO : PrefixOrdered 0 m (clockSteps (as.take j) q)) (σ : T.Assignment) (x : ι → ℝ) :
    ExpClose ((T.cut j q).budget (fun U => E U+2*m*K))
      (T.weight w φ (mixClocks j q r) σ x) (T.weight w φ (mixClocks j q s) σ x) := by
  rw [T.cut_mix_weight w φ j q r hj σ x,T.cut_mix_weight w φ j q s hj σ x]
  exact (T.cut j q).finite_close
    (gaussianHierarchy_regular hw φ _ (clockSteps_ordered ha s) 0).1.choose_spec
    (gaussianHierarchy_regular hw φ _ (clockSteps_ordered ha r) 0).1.choose_spec hK hF
    (fun U σ => U.weight_smooth hw φ ha s σ 0)
    (fun U σ => U.weight_smooth hw φ ha r σ 0) E hE hO (T.cutAssignmentEquiv j q σ) x

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 

 theorem ClockTree.cut_boundary_close {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (j : ℕ) {a b : PositiveMass} {bs : List PositiveMass} (he : as.drop j = a::b::bs)
    (ho : MassOrdered a.val (b::bs))
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (p q : ℕ → Fin (n+1) → ℝ≥0) (u v : Fin (n+1) → ℝ≥0)
    {c : ℝ} (hO : PrefixOrdered 0 c (clockSteps (as.take j) p)) (hc : c ≤ 1)
    (σ : T.Assignment) (x : Fin (n+1) → ℝ) :
    ExpClose ((7*(T.leaves:ℝ)*|a.val-b.val|+8*(T.leaves:ℝ)*(T.leaves+1:ℝ)*T.forksAt (j+1))*
        ∑ i, (v i:ℝ)*(D i)^2)
      (T.weight w φ (mixClocks j p (prependClock (fun i => u i+v i) q)) σ x)
      (T.weight w φ (mixClocks j p (prependClock u (addHeadClock q v))) σ x) := by
  classical
  have hj : j ≤ as.length := by
    have hl := congrArg List.length he
    simp only [List.length_drop,List.length_cons] at hl
    omega
  have hv : 0 ≤ ∑ i, (v i:ℝ)*(D i)^2 := Finset.sum_nonneg fun i _ => mul_nonneg (v i).coe_nonneg (sq_nonneg _)
  have hc0 : 0 ≤ c := (hO.bounds).2
  have ha : MassOrdered a.val (as.drop j) := he ▸ ⟨a.property.le,le_rfl,ho⟩
  have hP (y : Fin (n+1) → ℝ) :
      |gaussianHierarchy w φ (clockSteps (as.drop j) (prependClock (fun i => u i+v i) q)) y-
        gaussianHierarchy w φ (clockSteps (as.drop j) (prependClock u (addHeadClock q v))) y| ≤
      |a.val-b.val|/2*∑ i, (v i:ℝ)*(D i)^2 := by
    rw [he]
    exact gaussianHierarchy_local_boundary_transfer hw φ ho.2.2 D hB q u v y
  have hh := T.cut_mix_close hw φ j p
    (prependClock (fun i => u i+v i) q) (prependClock u (addHeadClock q v)) hj ha
    (by positivity : 0 ≤ |a.val-b.val|/2*∑ i, (v i:ℝ)*(D i)^2) hP
    (fun U => (6*(U.leaves:ℝ)*|a.val-b.val|+8*(U.leaves:ℝ)*(U.leaves+1:ℝ)*U.forksAt 1)*
      ∑ i, (v i:ℝ)*(D i)^2)
    (fun U τ y => U.local_boundary_close hw φ he ho D hD hB q u v τ y) hO σ x
  apply hh.mono
  let V : ℝ := ∑ i, (v i:ℝ)*(D i)^2
  have heq : (T.cut j p).budget (fun U =>
      (6*(U.leaves:ℝ)*|a.val-b.val|+8*(U.leaves:ℝ)*(U.leaves+1:ℝ)*U.forksAt 1)*V+
        2*c*(|a.val-b.val|/2*V)) =
      (T.cut j p).budget (fun U => (U.leaves:ℝ))*(6*|a.val-b.val| *V)+
      (T.cut j p).budget (fun U => (U.leaves:ℝ)*(U.leaves+1:ℝ)*U.forksAt 1)*(8*V)+
      (T.cut j p).budget (fun _ => (1:ℝ))*(c*|a.val-b.val| *V) := by
    calc
      _ = (T.cut j p).budget (fun U =>
        (U.leaves:ℝ)*(6*|a.val-b.val| *V)+
        ((U.leaves:ℝ)*(U.leaves+1:ℝ)*U.forksAt 1)*(8*V)+(1:ℝ)*(c*|a.val-b.val| *V)) := by
          congr 1
          funext U
          ring
      _ = _ := by rw [BoundaryTree.budget_add,BoundaryTree.budget_add,
        BoundaryTree.budget_mul,BoundaryTree.budget_mul,BoundaryTree.budget_mul]
  change (T.cut j p).budget _ ≤ _
  rw [heq,T.cut_budget_leaves j p hj]
  have hfork := mul_le_mul_of_nonneg_right (T.cut_budget_quadratic_forks j 1 p hj)
    (show 0 ≤ 8*V by positivity)
  have hone := mul_le_mul_of_nonneg_right (T.cut_budget_one j p hj)
    (show 0 ≤ c*|a.val-b.val| *V by positivity)
  have hlast : (T.leaves:ℝ)*(c*|a.val-b.val| *V) ≤ (T.leaves:ℝ)*(|a.val-b.val| *V) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (mul_nonneg (abs_nonneg (a.val-b.val)) hv)]
  dsimp only [V] at hfork hone hlast ⊢
  nlinarith

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 

 theorem ClockTree.cumulative_boundary_close {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (j : ℕ) {a b : PositiveMass} {bs : List PositiveMass}
    (he : as.drop j = a::b::bs)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (l : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (d : Fin (n+1) → ℝ)
    (hd : ∀ i, previousBoundary l q j i ≤ d i) (hdq : ∀ i, d i ≤ q j i)
    (hq : ∀ i, q j i ≤ q (j+1) i) (σ : T.Assignment) (x : Fin (n+1) → ℝ) :
    ExpClose ((7*(T.leaves:ℝ)*massGap as j+8*(T.leaves:ℝ)*(T.leaves+1:ℝ)*T.forksAt (j+1))*
        ∑ i, (q j i-d i)*(D i)^2)
      (T.weight w φ (cumulativeIncrements l q) σ x)
      (T.weight w φ (cumulativeIncrements l (Function.update q j d)) σ x) := by
  let p := cumulativeIncrements l q
  let s := fun k => cumulativeIncrements l q (j+1+k)
  let u := fun i => Real.toNNReal (d i-previousBoundary l q j i)
  let v := fun i => Real.toNNReal (q j i-d i)
  have hh := T.cut_boundary_close hw φ j he (ho.tail_at j he) D hD hB p s u v
    (ho.prefix j p) (by norm_num : (1:ℝ) ≤ 1) σ x
  have hOld := cumulativeIncrements_split l q j hd hdq
  have hNew := cumulativeIncrements_update l q j hdq hq
  dsimp only [p,s,u,v] at hh
  rw [←hNew,←hOld] at hh
  rw [massGap_drop as j,he]
  simp only [massGap]
  simpa only [Real.coe_toNNReal _ (sub_nonneg.mpr (hdq _))] using hh

 

 theorem ClockTree.cumulative_boundary_close_at {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (j : ℕ) (hj : j+1 < as.length)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (l : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (d : Fin (n+1) → ℝ)
    (hd : ∀ i, previousBoundary l q j i ≤ d i) (hdq : ∀ i, d i ≤ q j i)
    (hq : ∀ i, q j i ≤ q (j+1) i) (σ : T.Assignment) (x : Fin (n+1) → ℝ) :
    ExpClose ((7*(T.leaves:ℝ)*massGap as j+8*(T.leaves:ℝ)*(T.leaves+1:ℝ)*T.forksAt (j+1))*
        ∑ i, (q j i-d i)*(D i)^2)
      (T.weight w φ (cumulativeIncrements l q) σ x)
      (T.weight w φ (cumulativeIncrements l (Function.update q j d)) σ x) := by
  have hl : 2 ≤ (as.drop j).length := by simp only [List.length_drop]; omega
  cases he : as.drop j with
  | nil => simp only [he,List.length_nil] at hl; omega
  | cons a cs =>
    cases cs with
    | nil => simp only [he,List.length_cons,List.length_nil] at hl; omega
    | cons b bs => exact T.cumulative_boundary_close hw φ ho j he D hD hB l q d hd hdq hq σ x

end SKFluctuations.Hierarchy

end

end OAI
