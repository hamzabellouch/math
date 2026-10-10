import OAI.NumberTheory.Jacobsthal.Estimates.RegularStripBound
import OAI.NumberTheory.Jacobsthal.Estimates.SortedRealGaps

namespace OAI

namespace Erdos970

section

open Set
namespace ErdosMarkedStrips
open ErdosImplicitCurvature ErdosLocalFiberGraphs ErdosRegularStrip ErdosConvexGraph
attribute [local instance] Classical.propDecidable

noncomputable def polynomialSquarePoints (Q : Bivariate) (S : ℝ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (0 : ℤ) ⌊S⌋).product (Finset.Icc (0 : ℤ) ⌊S⌋)).filter
    (fun p => peval Q p.1 p.2 = 0)

theorem mem_polynomialSquarePoints (Q : Bivariate) (S : ℝ) (p : ℤ × ℤ) :
    p ∈ polynomialSquarePoints Q S ↔ InSquare S p ∧ peval Q p.1 p.2 = 0 := by
  simp only [polynomialSquarePoints,InSquare,Finset.mem_filter,Finset.product_eq_sprod,
    Finset.mem_product,Finset.mem_Icc,Int.le_floor,Int.cast_nonneg_iff]

noncomputable def markedFiberPoints (Q : Bivariate) (t S : ℝ) : Finset (ℤ × ℤ) :=
  (polynomialSquarePoints Q S).filter (fun p => (p.1 : ℝ) = t)

theorem mem_markedFiberPoints (Q : Bivariate) (t S : ℝ) (p : ℤ × ℤ) :
    p ∈ markedFiberPoints Q t S ↔ p ∈ polynomialSquarePoints Q S ∧ (p.1 : ℝ) = t := by
  simp only [markedFiberPoints,Finset.mem_filter]

theorem markedFiber_card_le (Q : Bivariate) (t S : ℝ)
    (hp : verticalPolynomial Q t ≠ 0) : (markedFiberPoints Q t S).card ≤ Q.totalDegree := by
  classical
  obtain ⟨z,hz⟩ : ∃ z : ℝ, peval Q t z ≠ 0 := by
    by_contra! h
    apply hp
    apply Polynomial.funext
    intro z
    rw [verticalPolynomial_eval,h z,Polynomial.eval_zero]
  have hfin := boundedFiber_finite Q t 0 S z hz
  have hmap : ∀ p ∈ (markedFiberPoints Q t S : Set (ℤ × ℤ)),
      (p.2 : ℝ) ∈ boundedFiber Q t 0 S := by
    intro p hp
    have hm := (mem_markedFiberPoints Q t S p).mp hp
    have hs := (mem_polynomialSquarePoints Q S p).mp hm.1
    refine ⟨hs.1.2,?_⟩
    simpa only [hm.2] using hs.2
  have hinj : InjOn (fun p : ℤ × ℤ => (p.2 : ℝ)) (markedFiberPoints Q t S : Set (ℤ × ℤ)) := by
    intro p hp q hq hpq
    have hp1 := ((mem_markedFiberPoints Q t S p).mp hp).2
    have hq1 := ((mem_markedFiberPoints Q t S q).mp hq).2
    apply Prod.ext
    · exact_mod_cast hp1.trans hq1.symm
    · change (p.2 : ℝ) = (q.2 : ℝ) at hpq
      exact_mod_cast hpq
  have hc := ncard_le_ncard_of_injOn (fun p : ℤ × ℤ => (p.2 : ℝ)) hmap hinj hfin
  simp only [ncard_coe_finset] at hc
  exact hc.trans (boundedFiber_card_le_degree Q t 0 S z hz)

theorem square_points_partition (Q : Bivariate) (S : ℝ) (E : Finset ℝ)
    (h0 : 0 ∈ E) (hS : S ∈ E) :
    polynomialSquarePoints Q S =
      E.biUnion (fun t => markedFiberPoints Q t S) ∪
        Finset.univ.biUnion (fun i : Fin (E.card-1) =>
          polynomialStripPoints Q (gapLeft E i) (gapRight E i) S) := by
  classical
  ext p
  constructor
  · intro hp
    have hs := (mem_polynomialSquarePoints Q S p).mp hp
    by_cases hm : (p.1 : ℝ) ∈ E
    · apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr ⟨p.1,hm,(mem_markedFiberPoints Q p.1 S p).mpr ⟨hp,rfl⟩⟩
    · obtain ⟨i,hi⟩ := exists_gap_of_not_mem E h0 hS hs.1.1 hm
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,
        (mem_polynomialStripPoints Q _ _ S p).mpr ⟨hs.1,hi,hs.2⟩⟩
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨t,_,ht⟩ := Finset.mem_biUnion.mp hp
      exact ((mem_markedFiberPoints Q t S p).mp ht).1
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
      have hs := (mem_polynomialStripPoints Q _ _ S p).mp hi
      exact (mem_polynomialSquarePoints Q S p).mpr ⟨hs.1,hs.2.2⟩

end ErdosMarkedStrips

end

section

open Set
namespace ErdosMarkedStrips
open ErdosImplicitCurvature ErdosLocalFiberGraphs ErdosRegularStrip ErdosConvexGraph

def RegularOff (Q : Bivariate) (S : ℝ) (E : Finset ℝ) : Prop :=
  ∀ t ∉ E, (peval Q t 0 ≠ 0 ∧ peval Q t S ≠ 0) ∧
    ∀ y ∈ Icc 0 S, peval Q t y = 0 →
      peval (partialX Q) t y ≠ 0 ∧ peval (partialY Q) t y ≠ 0 ∧
        peval (inflectionPolynomial Q) t y ≠ 0

theorem marked_square_lattice_bound (Q : Bivariate) (S : ℝ) (E : Finset ℝ)
    (hS : 0 ≤ S) (h0 : 0 ∈ E) (hSE : S ∈ E)
    (hfiber : ∀ t ∈ E, verticalPolynomial Q t ≠ 0) (hregular : RegularOff Q S E) :
    ((polynomialSquarePoints Q S).card : ℝ) ≤
      13*(E.card : ℝ)*(Q.totalDegree : ℝ)*(1+S^((2 : ℝ)/3)) := by
  classical
  let B := 1+S^((2 : ℝ)/3)
  have hB : 1 ≤ B := by
    dsimp [B]
    exact le_add_of_nonneg_right (Real.rpow_nonneg hS _)
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hstrip (i : Fin (E.card-1)) :
      ((polynomialStripPoints Q (gapLeft E i) (gapRight E i) S).card : ℝ) ≤
        12*(Q.totalDegree : ℝ)*B := by
    apply regular_strip_lattice_bound Q _ _ S hS
    · exact fun t ht => (hregular t (no_mark_in_gap E i ht)).1
    · exact fun t ht => (hregular t (no_mark_in_gap E i ht)).2
  have hcount : (polynomialSquarePoints Q S).card ≤
      (∑ t ∈ E, (markedFiberPoints Q t S).card) +
      ∑ i : Fin (E.card-1), (polynomialStripPoints Q (gapLeft E i) (gapRight E i) S).card := by
    rw [square_points_partition Q S E h0 hSE]
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le)
  have hm : (∑ t ∈ E, ((markedFiberPoints Q t S).card : ℝ)) ≤
      (E.card : ℝ)*(Q.totalDegree : ℝ) := by
    calc
      _ ≤ ∑ _t ∈ E, (Q.totalDegree : ℝ) := Finset.sum_le_sum (fun t ht => by
        exact_mod_cast markedFiber_card_le Q t S (hfiber t ht))
      _ = _ := by simp
  have hg : (∑ i : Fin (E.card-1),
      ((polynomialStripPoints Q (gapLeft E i) (gapRight E i) S).card : ℝ)) ≤
      (E.card : ℝ)*(12*(Q.totalDegree : ℝ)*B) := by
    calc
      _ ≤ ∑ _i : Fin (E.card-1), 12*(Q.totalDegree : ℝ)*B :=
        Finset.sum_le_sum (fun i _ => hstrip i)
      _ = ((E.card-1 : ℕ) : ℝ)*(12*(Q.totalDegree : ℝ)*B) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le E.card 1) (by positivity)
  have hc : ((polynomialSquarePoints Q S).card : ℝ) ≤
      (∑ t ∈ E, ((markedFiberPoints Q t S).card : ℝ)) +
      ∑ i : Fin (E.card-1), ((polynomialStripPoints Q (gapLeft E i) (gapRight E i) S).card : ℝ) := by
    exact_mod_cast hcount
  calc
    ((polynomialSquarePoints Q S).card : ℝ) ≤
        (E.card : ℝ)*(Q.totalDegree : ℝ) + (E.card : ℝ)*(12*(Q.totalDegree : ℝ)*B) :=
      hc.trans (add_le_add hm hg)
    _ ≤ (E.card : ℝ)*(Q.totalDegree : ℝ)*B + (E.card : ℝ)*(12*(Q.totalDegree : ℝ)*B) := by
      have hscale : (E.card : ℝ)*(Q.totalDegree : ℝ) ≤
          (E.card : ℝ)*(Q.totalDegree : ℝ)*B := by
        calc
          _ = (E.card : ℝ)*(Q.totalDegree : ℝ)*1 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)
      exact add_le_add hscale le_rfl
    _ = 13*(E.card : ℝ)*(Q.totalDegree : ℝ)*(1+S^((2 : ℝ)/3)) := by dsimp [B]; ring

theorem marked_square_cubic_bound (Q : Bivariate) (S : ℝ) (E : Finset ℝ) (C : ℕ)
    (hS : 0 ≤ S) (h0 : 0 ∈ E) (hSE : S ∈ E)
    (hfiber : ∀ t ∈ E, verticalPolynomial Q t ≠ 0) (hregular : RegularOff Q S E)
    (hcard : E.card ≤ C*Q.totalDegree^2) :
    ((polynomialSquarePoints Q S).card : ℝ) ≤
      13*(C : ℝ)*(Q.totalDegree : ℝ)^3*(1+S^((2 : ℝ)/3)) := by
  calc
    ((polynomialSquarePoints Q S).card : ℝ) ≤
        13*(E.card : ℝ)*(Q.totalDegree : ℝ)*(1+S^((2 : ℝ)/3)) :=
      marked_square_lattice_bound Q S E hS h0 hSE hfiber hregular
    _ ≤ 13*((C : ℝ)*(Q.totalDegree : ℝ)^2)*(Q.totalDegree : ℝ)*(1+S^((2 : ℝ)/3)) := by
      gcongr
      exact_mod_cast hcard
    _ = _ := by ring

end ErdosMarkedStrips

end

end Erdos970

end OAI
