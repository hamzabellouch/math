import OAI.GroupTheory.PolycyclicRecognition.Analysis.RemezInput
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Real

namespace OAI

/-! # Keeping compact parameter mass away from a polynomial zero set -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory
open scoped ENNReal

theorem exists_compact_large_polynomial_values
    (rem : RemezPolynomialInput) (n D : ℕ) (hn : 1 ≤ n) (hD : 1 ≤ D) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (p : MvPolynomial (Fin n) ℝ), p.totalDegree ≤ D →
      ∀ (R c : ℝ), 1 ≤ R → 0 < c →
      ∀ x₀ ∈ closedBall 0 R, c ≤ |MvPolynomial.eval x₀ p| →
      ∀ E : Set (Fin n → ℝ), MeasurableSet E → E ⊆ closedBall 0 R →
      0 < (volume E).toReal →
      let η := (c / 2) / (2 * A * (1 + R) ^ n / (volume E).toReal) ^ (n * D)
      ∃ K : Set (Fin n → ℝ), K ⊆ E ∧ IsCompact K ∧
        (volume E).toReal / 4 < (volume K).toReal ∧
        ∀ x ∈ K, η ≤ |MvPolynomial.eval x p| := by
  obtain ⟨A, hA, hrem⟩ := rem n D hn hD
  refine ⟨A, hA, ?_⟩
  intro p hp R c hR hc x₀ hx₀ hx₀c E hE hER hm
  let m := (volume E).toReal
  let a := 2 * A * (1 + R) ^ n / m
  let η := (c / 2) / a ^ (n * D)
  have ha : 0 < a := by dsimp [a, m]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hEfinite : volume E ≠ ∞ :=
    measure_ne_top_of_subset hER (isCompact_closedBall (0 : Fin n → ℝ) R).measure_ne_top
  let B := E ∩ {x | |MvPolynomial.eval x p| < η}
  let G := E ∩ {x | η ≤ |MvPolynomial.eval x p|}
  have hB : MeasurableSet B := hE.inter
    (isOpen_lt p.continuous_eval.abs continuous_const).measurableSet
  have hG : MeasurableSet G := hE.inter
    (isClosed_le continuous_const p.continuous_eval.abs).measurableSet
  have hBfinite : volume B ≠ ∞ := measure_ne_top_of_subset inter_subset_left hEfinite
  have hGfinite : volume G ≠ ∞ := measure_ne_top_of_subset inter_subset_left hEfinite
  have hBmass : (volume B).toReal ≤ m / 2 := by
    by_contra h
    have hlarge : m / 2 < (volume B).toReal := lt_of_not_ge h
    have hBpos : 0 < (volume B).toReal := (by dsimp [m]; positivity : 0 < m / 2).trans hlarge
    have hpoint := hrem p hp R hR B hB (inter_subset_left.trans hER) hBpos
      η hη.le (fun x hx => hx.2.le) x₀ hx₀
    have hquot : A * (1 + R) ^ n / (volume B).toReal ≤ a := by
      dsimp [a]
      apply (div_le_div_iff₀ hBpos hm).mpr
      have hnonneg : 0 ≤ A * (1 + R) ^ n := by positivity
      nlinarith
    have hpow : (A * (1 + R) ^ n / (volume B).toReal) ^ (n * D) ≤ a ^ (n * D) :=
      pow_le_pow_left₀ (by positivity) hquot (n * D)
    have he : a ^ (n * D) * η = c / 2 := by
      dsimp [η]
      field_simp
    have hlast : c ≤ c / 2 := calc
      c ≤ |MvPolynomial.eval x₀ p| := hx₀c
      _ ≤ (A * (1 + R) ^ n / (volume B).toReal) ^ (n * D) * η := hpoint
      _ ≤ a ^ (n * D) * η := mul_le_mul_of_nonneg_right hpow hη.le
      _ = c / 2 := he
    linarith
  have hEG : E = B ∪ G := by
    ext x
    simp only [B, G, mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hx
      rcases lt_or_ge |MvPolynomial.eval x p| η with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hGmass : m / 2 ≤ (volume G).toReal := by
    have hu := measureReal_union_le (μ := volume) B G
    rw [← hEG] at hu
    change m ≤ (volume B).toReal + (volume G).toReal at hu
    linarith
  have hstrict : ENNReal.ofReal (m / 4) < volume G := by
    apply (ENNReal.toReal_lt_toReal (by simp) hGfinite).mp
    rw [ENNReal.toReal_ofReal (by positivity)]
    linarith
  obtain ⟨K, hKG, hK, hKmass⟩ := hG.exists_lt_isCompact hstrict
  refine ⟨K, hKG.trans inter_subset_left, hK, ?_, fun x hx => (hKG hx).2⟩
  have hh := (ENNReal.toReal_lt_toReal (by simp) hK.measure_ne_top).mpr hKmass
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ m / 4)] using hh

end PolycyclicRecognition

end

end OAI
