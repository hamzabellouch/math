import OAI.NumberTheory.TwoPoint.Bounds.ObservedColumnRank
import OAI.NumberTheory.TwoPoint.Walks.TupleColumnCover

namespace OAI

/-! Extract the high-rank witness from failure of the actual forest rank condition. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma ColumnWordPattern.finite_departure {α : Type*} [Fintype α]
    (w : ColumnWordPattern α) (hn : 0 < w.length) (h n : ℕ) (hn' : n ≤ w.length) :
    formalDeparture (columnNatLabel (fun i : Fin w.length => w.label i.val) hn)
        (fun t => (w.coefficient h t : ℝ)) n =
      formalDeparture w.label (fun t => (w.coefficient h t : ℝ)) n := by
  unfold formalDeparture
  apply sum_congr rfl
  intro t ht
  have htl : t < w.length := (mem_range.mp ht).trans_le hn'
  simp only [columnNatLabel, dite_eq_left htl]

/-- Selected equal-label pairs are transported to the observed resampling
coordinates with their same original left and right departure indices. -/
theorem tuple_selected_pairs_observed {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J) (h : ℕ)
    (perfect : Finset (Fin R)) (cut : Fin R)
    (S : Finset (EqualLabelPairs (fun i : perfect.erase cut =>
      (tupleColumnPattern w hR forward padding j).label i.val.val)))
    (hind : LinearIndependent ℝ (pairFamily (labelPairVectors
      (fun i : perfect.erase cut => (tupleColumnPattern w hR forward padding j).label i.val.val)
      (fun i => formalDeparture
        (columnNatLabel (fun i : Fin R => (tupleColumnPattern w hR forward padding j).label i.val) hR)
        (fun t => ((tupleColumnPattern w hR forward padding j).coefficient h t : ℝ)) i.val.val)) S)) :
    LinearIndependent ℝ (Sum.elim
      (fun p : S => formalDeparture (resampledTupleColumnPattern w hR forward padding j).label
          (fun t => ((resampledTupleColumnPattern w hR forward padding j).coefficient h t : ℝ))
          p.val.val.2.1.val.val -
        formalDeparture (resampledTupleColumnPattern w hR forward padding j).label
          (fun t => ((resampledTupleColumnPattern w hR forward padding j).coefficient h t : ℝ))
          p.val.val.2.2.val.val)
      (fun p : S => Pi.basisFun ℝ (patternClasses (w j))
        (patternCoordinate (w j) p.val.val.2.1.val))) := by
  apply (tuple_column_observed_rank_iff w hR forward padding j h
    (fun p : S => p.val.val.2.1.val.val) (fun p : S => p.val.val.2.2.val.val)
    (fun p : S => patternCoordinate (w j) p.val.val.2.1.val)).mpr
  have hs := selected_label_pairs_independent _ _ S hind
  convert hs using 1
  funext z
  rcases z with p | p
  · simp only [Sum.elim_inl]
    exact congrArg₂ (· - ·)
      (ColumnWordPattern.finite_departure (tupleColumnPattern w hR forward padding j)
        hR h _ (Nat.le_of_lt p.val.val.2.1.val.isLt)).symm
      (ColumnWordPattern.finite_departure (tupleColumnPattern w hR forward padding j)
        hR h _ (Nat.le_of_lt p.val.val.2.2.val.isLt)).symm
  · simp only [Sum.elim_inr]
    congr 1
    exact (tupleColumnPattern_label w hR forward padding j p.val.val.2.1.val).symm.trans
      p.val.property.1

/-- Apply the high-rank estimate using only the original perfect-departure
lit conditions. The two divisibility tests per selected pair are derived
here, with no additional resampling premise. -/
theorem tuple_selected_pairs_reciprocal_sum {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J)
    (F : Finset (Fin R → P j))
    (hpattern : ∀ v ∈ F, ∀ a b, v a = v b ↔ w j a = w j b)
    (h Q D B H : ℕ) (hP : ∀ p ∈ P j, p.Prime)
    (hV : 0 < primeHarmonicMass (P j)) (hH : 0 < H)
    (hlo : ∀ p ∈ P j, H ≤ p) (hbound : ∀ p ∈ P j, p ≤ B)
    (hq : ∀ i, padding i ≤ Q)
    (hd : ∀ i, (∏ l ∈ univ.erase j, (w l i).val) ≤ D)
    (perfect : Finset (Fin R)) (cut : Fin R)
    (S : Finset (EqualLabelPairs (fun i : perfect.erase cut =>
      (tupleColumnPattern w hR forward padding j).label i.val.val)))
    (hind : LinearIndependent ℝ (pairFamily (labelPairVectors
      (fun i : perfect.erase cut => (tupleColumnPattern w hR forward padding j).label i.val.val)
      (fun i => formalDeparture
        (columnNatLabel (fun i : Fin R => (tupleColumnPattern w hR forward padding j).label i.val) hR)
        (fun t => ((tupleColumnPattern w hR forward padding j).coefficient h t : ℝ)) i.val.val)) S))
    (base : (patternClasses (w j) → P j) → ℤ)
    (hlit : ∀ x, patternResample (w j) x ∈ F → ∀ i ∈ perfect,
      ((x (patternCoordinate (w j) i)).val : ℤ) ∣ base x + wordDisplacement h
        ((columnTupleWord (Function.update w j (patternResample (w j) x)) forward padding).take i.val)) :
    (∑ v ∈ F, ∏ p ∈ univ.image v, (p.val : ℝ)⁻¹) ≤
      primeHarmonicMass (P j) ^ (univ.image (w j)).card *
        Real.sqrt (((primeHarmonicMass (P j) * H)⁻¹ *
          (1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ))) ^ S.card) := by
  have hs := tuple_selected_pairs_observed w hR forward padding j h perfect cut S hind
  have hb := tuple_column_high_rank_sum (ρ := S) w hR forward padding j F hpattern
    h Q D B H hP hV hH hlo hbound hq hd
    (fun p => p.val.val.2.1.val.val) (fun p => p.val.val.2.2.val.val)
    (fun p => patternCoordinate (w j) p.val.val.2.1.val)
    (fun p => Nat.le_of_lt p.val.val.2.1.val.isLt)
    (fun p => Nat.le_of_lt p.val.val.2.2.val.isLt) hs base
    (fun x hx p => hlit x hx _ (mem_erase.mp p.val.val.2.1.property).2) ?_
  · simpa only [Fintype.card_coe] using hb
  · intro x hx p
    have hew : w j p.val.val.2.1.val = w j p.val.val.2.2.val :=
      (tupleColumnPattern_label w hR forward padding j _).symm.trans
        ((p.val.property.1.trans p.val.property.2.symm).trans
          (tupleColumnPattern_label w hR forward padding j _))
    have hec : patternCoordinate (w j) p.val.val.2.1.val =
        patternCoordinate (w j) p.val.val.2.2.val := Subtype.ext hew
    rw [hec]
    exact hlit x hx _ (mem_erase.mp p.val.val.2.2.property).2

/-- Failure of the forest's low-rank condition supplies the precise
selected-pair witness needed by the reciprocal estimate. -/
theorem tuple_not_low_rank_reciprocal_sum {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J)
    (F : Finset (Fin R → P j))
    (hpattern : ∀ v ∈ F, ∀ a b, v a = v b ↔ w j a = w j b)
    (h Q D B H : ℕ) (hP : ∀ p ∈ P j, p.Prime)
    (hV : 0 < primeHarmonicMass (P j)) (hH : 0 < H)
    (hlo : ∀ p ∈ P j, H ≤ p) (hbound : ∀ p ∈ P j, p ≤ B)
    (hq : ∀ i, padding i ≤ Q)
    (hd : ∀ i, (∏ l ∈ univ.erase j, (w l i).val) ≤ D)
    (perfect : Finset (Fin R)) (cut : Fin R) (r : ℕ)
    (hrank : ¬ColumnLowRank (tupleColumnPattern w hR forward padding j) hR h perfect cut r)
    (base : (patternClasses (w j) → P j) → ℤ)
    (hlit : ∀ x, patternResample (w j) x ∈ F → ∀ i ∈ perfect,
      ((x (patternCoordinate (w j) i)).val : ℤ) ∣ base x + wordDisplacement h
        ((columnTupleWord (Function.update w j (patternResample (w j) x)) forward padding).take i.val)) :
    (∑ v ∈ F, ∏ p ∈ univ.image v, (p.val : ℝ)⁻¹) ≤
      primeHarmonicMass (P j) ^ (univ.image (w j)).card *
        Real.sqrt (((primeHarmonicMass (P j) * H)⁻¹ *
          (1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ))) ^ r) := by
  simp only [ColumnLowRank, not_forall, not_not] at hrank
  obtain ⟨S, hS, hind⟩ := hrank
  have hb := tuple_selected_pairs_reciprocal_sum w hR forward padding j F hpattern
    h Q D B H hP hV hH hlo hbound hq hd perfect cut S hind base hlit
  cases hS
  exact hb

end TwoPointCorrelations

end OAI
