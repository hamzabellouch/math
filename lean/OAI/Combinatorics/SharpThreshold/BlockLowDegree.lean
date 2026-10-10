import OAI.Combinatorics.SharpThreshold.Model
import OAI.Combinatorics.SharpThreshold.FourierBasis
import OAI.Combinatorics.SharpThreshold.RestrictionInfluence
import OAI.Combinatorics.SharpThreshold.BlockInfluence
import OAI.Combinatorics.SharpThreshold.GraphRestrictionInfluence
import OAI.Combinatorics.SharpThreshold.RestrictionMassSubtype
import OAI.Combinatorics.SharpThreshold.LowDegree

namespace OAI

universe u

noncomputable section
open scoped BigOperators

namespace Problem313

/-- Averaging the low-degree estimate over exterior configurations preserves its
linear influence bound.  This is the fixed-block averaging step, before averaging
in the choice of the vertex block. -/
theorem average_conditional_low_degree_bound
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P : ι → Prop) [DecidablePred P]
    (p k C : ℝ) (f : (ι → Bool) → Bool)
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hbound : ∀ y : {i // ¬ P i} → Bool,
      (∑ A : Finset {i // P i},
        if A.Nonempty ∧ (A.card : ℝ) ≤ k then
          BiasedFourier.coeff p
            (fun x => boolReal (f (RestrictionInfluence.join P x y))) A ^ 2
        else 0) ≤
      C * ∑ i : {i // P i}, RestrictionInfluence.influence p
        (fun x => f (RestrictionInfluence.join P x y)) i) :
    (∑ y : {i // ¬ P i} → Bool, BiasedFourier.weight p y *
      ∑ A : Finset {i // P i},
        if A.Nonempty ∧ (A.card : ℝ) ≤ k then
          BiasedFourier.coeff p
            (fun x => boolReal (f (RestrictionInfluence.join P x y))) A ^ 2
        else 0) ≤
      C * ∑ i : {i // P i}, RestrictionInfluence.influence p f i.val := by
  classical
  have hw (y : {i // ¬ P i} → Bool) : 0 ≤ BiasedFourier.weight p y := by
    apply Finset.prod_nonneg
    intro i hi
    unfold BiasedFourier.scalarWeight
    split_ifs <;> linarith
  calc
    _ ≤ ∑ y : {i // ¬ P i} → Bool, BiasedFourier.weight p y *
        (C * ∑ i : {i // P i}, RestrictionInfluence.influence p
          (fun x => f (RestrictionInfluence.join P x y)) i) := by
      exact Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hbound y) (hw y))
    _ = C * ∑ y : {i // ¬ P i} → Bool, RestrictionInfluence.weight p y *
        ∑ i : {i // P i}, RestrictionInfluence.influence p
          (fun x => f (RestrictionInfluence.join P x y)) i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      change BiasedFourier.weight p y * (C * _) =
        C * (BiasedFourier.weight p y * _)
      ring
    _ = _ := by rw [RestrictionInfluence.average_totalInfluence]

/-- The same averaging step with the original Fourier mass supplied by the exact
restriction identity. Both premises are equalities/inequalities about the actual
canonical product cube, not an abstract replacement for graph probability. -/
theorem original_mass_bound_of_conditional
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P : ι → Prop) [DecidablePred P]
    (p k C M : ℝ) (f : (ι → Bool) → Bool)
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hmass : M =
      ∑ y : {i // ¬ P i} → Bool, BiasedFourier.weight p y *
        ∑ A : Finset {i // P i},
          if A.Nonempty ∧ (A.card : ℝ) ≤ k then
            BiasedFourier.coeff p
              (fun x => boolReal (f (RestrictionInfluence.join P x y))) A ^ 2
          else 0)
    (hbound : ∀ y : {i // ¬ P i} → Bool,
      (∑ A : Finset {i // P i},
        if A.Nonempty ∧ (A.card : ℝ) ≤ k then
          BiasedFourier.coeff p
            (fun x => boolReal (f (RestrictionInfluence.join P x y))) A ^ 2
        else 0) ≤
      C * ∑ i : {i // P i}, RestrictionInfluence.influence p
        (fun x => f (RestrictionInfluence.join P x y)) i) :
    M ≤ C * ∑ i : {i // P i}, RestrictionInfluence.influence p f i.val := by
  rw [hmass]
  exact average_conditional_low_degree_bound P p k C f hp hp1 hbound

/-- The conditional influence premise for the low-degree theorem follows from
vertex invariance and the low-degree estimate on the restricted cube. -/
theorem block_conditional_low_degree_bound_of_estimate
    {n : ℕ} (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)]
    (hB : 3 ≤ B.card) (f : GraphConfig n → Bool) (hf : VertexInvariant f)
    (p k C : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hestimate : ∀ g : ({e : GraphEdge n // EdgeTouches B e} → Bool) → Bool,
      (∀ e, Reindex.influence p g e ≤
        (∑ d, Reindex.influence p g d) / (B.card : ℝ)) →
      (∑ A : Finset {e : GraphEdge n // EdgeTouches B e},
        if A.Nonempty ∧ (A.card : ℝ) ≤ k then
          BiasedFourier.coeff p (fun x => boolReal (g x)) A ^ 2 else 0) ≤
      C * ∑ e, Reindex.influence p g e) :
    (∑ y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool,
      BiasedFourier.weight p y *
        ∑ A : Finset {e : GraphEdge n // EdgeTouches B e},
          if A.Nonempty ∧ (A.card : ℝ) ≤ k then
            BiasedFourier.coeff p
              (fun x => boolReal (restrictCube (EdgeTouches B) f y x)) A ^ 2
          else 0) ≤
      C * ∑ e : {e : GraphEdge n // EdgeTouches B e}, edgeInfluence p f e.val := by
  have hb (y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool) :=
    hestimate (restrictCube (EdgeTouches B) f y)
      (fun e => block_restricted_influence_le B hB f hf hp hp1 y e)
  calc
    _ ≤ ∑ y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool,
        Reindex.weight p y *
          (C * ∑ e, Reindex.influence p (restrictCube (EdgeTouches B) f y) e) := by
      apply Finset.sum_le_sum
      intro y hy
      exact mul_le_mul_of_nonneg_left (hb y) (Reindex.weight_nonneg hp hp1 y)
    _ = C * ∑ y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool,
        Reindex.weight p y *
          ∑ e, Reindex.influence p (restrictCube (EdgeTouches B) f y) e := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = _ := by rw [block_average_totalInfluence]

/-- Fixed-block Fourier estimate: all exterior Fourier degrees are retained.
The only analytic input is the ordinary low-degree estimate on the free cube. -/
theorem block_low_degree_bound_of_estimate
    {n : ℕ} (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)]
    (hB : 3 ≤ B.card) (f : GraphConfig n → Bool) (hf : VertexInvariant f)
    (p k C : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hestimate : ∀ g : ({e : GraphEdge n // EdgeTouches B e} → Bool) → Bool,
      (∀ e, Reindex.influence p g e ≤
        (∑ d, Reindex.influence p g d) / (B.card : ℝ)) →
      (∑ A : Finset {e : GraphEdge n // EdgeTouches B e},
        if A.Nonempty ∧ (A.card : ℝ) ≤ k then
          BiasedFourier.coeff p (fun x => boolReal (g x)) A ^ 2 else 0) ≤
      C * ∑ e, Reindex.influence p g e) :
    (∑ S : Finset (GraphEdge n),
      if (S.filter (EdgeTouches B)).Nonempty ∧
          ((S.filter (EdgeTouches B)).card : ℝ) ≤ k then
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      C * ∑ e : {e : GraphEdge n // EdgeTouches B e}, edgeInfluence p f e.val := by
  rw [BiasedFourier.restriction_low_degree_mass_subtype (EdgeTouches B) hp hp1]
  exact block_conditional_low_degree_bound_of_estimate B hB f hf p k C
    hp.le hp1.le hestimate

/-- The fixed-block low-degree Fourier bound for invariant graph properties.
All symmetry, restriction and analytic premises are discharged. -/
theorem block_low_degree_bound
    {n : ℕ} (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)]
    (hB : 3 ≤ B.card) (f : GraphConfig n → Bool) (hf : VertexInvariant f)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (∑ S : Finset (GraphEdge n),
      if (S.filter (EdgeTouches B)).Nonempty ∧
          ((S.filter (EdgeTouches B)).card : ℝ) ≤
            Real.sqrt (p * (1 - p)) * Real.log (B.card : ℝ) / 64 then
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      (B.card : ℝ) ^ (-1 / 4 : ℝ) *
        ∑ e : {e : GraphEdge n // EdgeTouches B e}, edgeInfluence p f e.val := by
  have hm : (1 : ℝ) ≤ B.card := by exact_mod_cast (by omega : 1 ≤ B.card)
  exact block_low_degree_bound_of_estimate B hB f hf p
    (Real.sqrt (p * (1 - p)) * Real.log (B.card : ℝ) / 64)
    ((B.card : ℝ) ^ (-1 / 4 : ℝ)) hp hp1
    (fun g hg => BiasedFourier.low_degree_estimate hp hp1 g (B.card : ℝ) hm hg)

/-- Filtered finite-sum version of the fixed-block low-degree bound. -/
theorem block_low_degree_bound_filter
    {n : ℕ} (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)]
    (hB : 3 ≤ B.card) (f : GraphConfig n → Bool) (hf : VertexInvariant f)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (∑ S ∈ Finset.univ.filter (fun S : Finset (GraphEdge n) =>
      1 ≤ (S.filter (EdgeTouches B)).card ∧
        ((S.filter (EdgeTouches B)).card : ℝ) ≤
          Real.sqrt (p * (1 - p)) * Real.log (B.card : ℝ) / 64),
      BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2) ≤
      (B.card : ℝ) ^ (-1 / 4 : ℝ) *
        ∑ e ∈ Finset.univ.filter (EdgeTouches B), edgeInfluence p f e := by
  have h := block_low_degree_bound B hB f hf hp hp1
  have hs : (∑ e : {e : GraphEdge n // EdgeTouches B e}, edgeInfluence p f e.val) =
      ∑ e ∈ Finset.univ.filter (EdgeTouches B), edgeInfluence p f e :=
    (Finset.sum_subtype (Finset.univ.filter (EdgeTouches B))
      (by intro e; simp) (edgeInfluence p f)).symm
  rw [hs] at h
  simpa only [Finset.sum_filter, Finset.one_le_card] using h

end Problem313

end

end OAI
