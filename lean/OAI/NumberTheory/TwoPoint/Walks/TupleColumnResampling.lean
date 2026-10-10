import OAI.NumberTheory.TwoPoint.Bounds.PatternResampling
import OAI.NumberTheory.TwoPoint.Walks.TupleColumnWords
import OAI.NumberTheory.TwoPoint.Bounds.ReciprocalColumnRank

namespace OAI

/-! Resampling an observed column preserves the actual numerical tuple word. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

private def wordPosition (R : ℕ) (hR : 0 < R) (t : ℕ) : Fin R :=
  ⟨t % R, Nat.mod_lt _ hR⟩

private lemma wordPosition_val {R : ℕ} (hR : 0 < R) (i : Fin R) :
    wordPosition R hR i.val = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

noncomputable def resampledTupleColumnPattern {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J) :
    ColumnWordPattern (patternClasses (w j)) where
  length := R
  label t := patternCoordinate (w j) (wordPosition R hR t)
  forward t := forward (wordPosition R hR t)
  padding t := padding (wordPosition R hR t)
  otherColumns t := ∏ l ∈ univ.erase j, (w l (wordPosition R hR t)).val

lemma resampledTupleColumnPattern_word {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J)
    (x : patternClasses (w j) → P j) :
    (resampledTupleColumnPattern w hR forward padding j).word (fun c => (x c).val) =
      columnTupleWord (Function.update w j (patternResample (w j) x)) forward padding := by
  change List.ofFn (fun i : Fin R =>
    (resampledTupleColumnPattern w hR forward padding j).step (fun c => (x c).val) i.val) =
      List.ofFn (fun i : Fin R =>
        (⟨forward i, columnTuple (Function.update w j (patternResample (w j) x)) i, padding i⟩ : SignedStep))
  congr 1
  funext i
  simp only [ColumnWordPattern.step, resampledTupleColumnPattern, wordPosition_val]
  congr 1
  rw [← columnTuple_split _ i j]
  congr 1
  · simp [patternResample]
  · apply prod_congr rfl
    intro l hl
    simp only [Function.update_of_ne (mem_erase.mp hl).1]

/-- The reciprocal rank bound for an actual one-column fiber, with the
other columns, signs and padding held fixed. The selected divisibilities
are imposed on the original numerical tuple word after resampling. -/
theorem tuple_column_high_rank_sum {J R : ℕ} {P : Fin J → Finset ℕ}
    {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J)
    (F : Finset (Fin R → P j))
    (hpattern : ∀ v ∈ F, ∀ a b, v a = v b ↔ w j a = w j b)
    (h Q D B H : ℕ) (hP : ∀ p ∈ P j, p.Prime)
    (hV : 0 < primeHarmonicMass (P j)) (hH : 0 < H)
    (hlo : ∀ p ∈ P j, H ≤ p) (hbound : ∀ p ∈ P j, p ≤ B)
    (hq : ∀ i, padding i ≤ Q)
    (hd : ∀ i, (∏ l ∈ univ.erase j, (w l i).val) ≤ D)
    (left right : ρ → ℕ) (control : ρ → patternClasses (w j))
    (hl : ∀ i, left i ≤ R) (hr : ∀ i, right i ≤ R)
    (hind : LinearIndependent ℝ (Sum.elim
      (fun i => formalDeparture (resampledTupleColumnPattern w hR forward padding j).label
          (fun t => ((resampledTupleColumnPattern w hR forward padding j).coefficient h t : ℝ))
          (left i) -
        formalDeparture (resampledTupleColumnPattern w hR forward padding j).label
          (fun t => ((resampledTupleColumnPattern w hR forward padding j).coefficient h t : ℝ))
          (right i))
      (fun i => Pi.basisFun ℝ (patternClasses (w j)) (control i))))
    (base : (patternClasses (w j) → P j) → ℤ)
    (hlit : ∀ x, patternResample (w j) x ∈ F → ∀ i,
      ((x (control i)).val : ℤ) ∣ base x + wordDisplacement h
        ((columnTupleWord (Function.update w j (patternResample (w j) x)) forward padding).take (left i)))
    (hrit : ∀ x, patternResample (w j) x ∈ F → ∀ i,
      ((x (control i)).val : ℤ) ∣ base x + wordDisplacement h
        ((columnTupleWord (Function.update w j (patternResample (w j) x)) forward padding).take (right i))) :
    (∑ v ∈ F, ∏ p ∈ univ.image v, (p.val : ℝ)⁻¹) ≤
      primeHarmonicMass (P j) ^ (univ.image (w j)).card *
        Real.sqrt (((primeHarmonicMass (P j) * H)⁻¹ *
          (1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ))) ^ Fintype.card ρ) := by
  classical
  have hresample := same_pattern_resampled_sum (w j) F
    (fun p : P j => (p.val : ℝ)⁻¹) (fun p => by positivity)
    (fun v => if v ∈ F then 1 else 0) (fun v => by split_ifs <;> positivity) hpattern
  have hrank := (resampledTupleColumnPattern w hR forward padding j).reciprocal_high_rank_bound
    h Q D B H (P j) hP hV hH hlo hbound
    (fun t _ => hq (wordPosition R hR t))
    (fun t _ => hd (wordPosition R hR t)) left right control hl hr hind base
    (fun x => patternResample (w j) x ∈ F)
    (by intro x hx i; rw [resampledTupleColumnPattern_word]; exact hlit x hx i)
    (by intro x hx i; rw [resampledTupleColumnPattern_word]; exact hrit x hx i)
  have hcard : Fintype.card (patternClasses (w j)) = (univ.image (w j)).card :=
    Fintype.card_coe _
  rw [hcard] at hrank
  calc
    _ ≤ ∑ x : patternClasses (w j) → P j,
        if patternResample (w j) x ∈ F then ∏ c, ((x c).val : ℝ)⁻¹ else 0 := by
      simpa [mul_ite] using hresample
    _ ≤ _ := by
      convert hrank using 1
      · apply sum_congr rfl
        intro x _
        split_ifs <;> rfl
      · rfl

end TwoPointCorrelations

end OAI
