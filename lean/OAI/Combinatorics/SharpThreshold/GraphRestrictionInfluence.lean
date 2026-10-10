import OAI.Combinatorics.SharpThreshold.RestrictionInfluence
import OAI.Combinatorics.SharpThreshold.InfluenceReindex
import OAI.Combinatorics.SharpThreshold.BlockRestrictionSymmetry
import OAI.Combinatorics.SharpThreshold.BlockSymmetry

namespace OAI

universe u

noncomputable section
open scoped Classical BigOperators

namespace Problem313

/-- The generic restriction weight agrees with the qualified graph weight. -/
theorem restrictionWeight_eq_graphWeight {n : ℕ} (p : ℝ) (x : GraphConfig n) :
    RestrictionInfluence.weight p x = graphWeight p x := rfl

/-- The generic restriction influence agrees with the qualified graph influence. -/
theorem restrictionInfluence_eq_edgeInfluence {n : ℕ} (p : ℝ)
    (f : GraphConfig n → Bool) (e : GraphEdge n) :
    RestrictionInfluence.influence p f e = edgeInfluence p f e := rfl

/-- The two generic influence interfaces have definitionally identical weights. -/
theorem restrictionWeight_eq_reindexWeight {ι : Type u} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (x : ι → Bool) :
    RestrictionInfluence.weight p x = Reindex.weight p x := rfl

/-- The two generic influence interfaces have equal influences after identifying their decidable-equality instances. -/
theorem restrictionInfluence_eq_reindexInfluence {ι : Type u} [Fintype ι] [d : DecidableEq ι]
    (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) :
    RestrictionInfluence.influence p f i = Reindex.influence p f i := by
  cases Subsingleton.elim d (Classical.typeDecidableEq ι)
  rfl

/-- Averaging a conditional free-edge influence recovers its original graph influence. -/
theorem block_average_edgeInfluence {n : ℕ} (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)] (p : ℝ)
    (f : GraphConfig n → Bool) (e : {e : GraphEdge n // EdgeTouches B e}) :
    (∑ y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool,
      Reindex.weight p y * Reindex.influence p (restrictCube (EdgeTouches B) f y) e) =
      edgeInfluence p f e.val := by
  have h := RestrictionInfluence.average_influence (EdgeTouches B) p f e
  unfold RestrictionInfluence.join at h
  unfold restrictCube pasteCube
  simpa only [← restrictionWeight_eq_reindexWeight,
    ← restrictionInfluence_eq_reindexInfluence,
    ← restrictionInfluence_eq_edgeInfluence] using h

/-- Averaging conditional total influence gives precisely the original influences of
edges touching the block; no invariance or monotonicity is needed. -/
theorem block_average_totalInfluence {n : ℕ} (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)] (p : ℝ)
    (f : GraphConfig n → Bool) :
    (∑ y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool,
      Reindex.weight p y * ∑ e : {e : GraphEdge n // EdgeTouches B e},
        Reindex.influence p (restrictCube (EdgeTouches B) f y) e) =
      ∑ e : {e : GraphEdge n // EdgeTouches B e}, edgeInfluence p f e.val := by
  have h := RestrictionInfluence.average_totalInfluence (EdgeTouches B) p f
  unfold RestrictionInfluence.join at h
  unfold restrictCube pasteCube
  simpa only [← restrictionWeight_eq_reindexWeight,
    ← restrictionInfluence_eq_reindexInfluence,
    ← restrictionInfluence_eq_edgeInfluence] using h

/-- The conditional total-influence identity, with a filtered finite edge sum. -/
theorem block_average_totalInfluence_filter {n : ℕ} (B : Finset (Fin n))
    [DecidablePred (EdgeTouches B)] (p : ℝ) (f : GraphConfig n → Bool) :
    (∑ y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool,
      Reindex.weight p y * ∑ e : {e : GraphEdge n // EdgeTouches B e},
        Reindex.influence p (restrictCube (EdgeTouches B) f y) e) =
      ∑ e ∈ Finset.univ.filter (EdgeTouches B), edgeInfluence p f e := by
  rw [block_average_totalInfluence]
  exact (Finset.sum_subtype (Finset.univ.filter (EdgeTouches B))
    (by intro e; simp) (edgeInfluence p f)).symm

end Problem313

end

end OAI
