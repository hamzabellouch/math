import OAI.Probability.InvariantIsing.Fields.CanonicalPairRootLaw
import OAI.Probability.InvariantIsing.Magnetic.ConstrainedBlockMagneticEstimate

namespace OAI

/-! A dimension-free comparison of the actual constrained two-spin mean
with the site-average magnetic field law. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped NNReal BigOperators

namespace InvariantIsing

def restrictedBlockPairMean {N : ℕ} (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty)
    (h : FieldStep) (b : Fin N → ℝ) (i : Fin (h.depth + 1)) : ℝ :=
  (N : ℝ)⁻¹ * ∫ p, ∑ j, spinValue (p.1 j) * spinValue (p.2 j)
    ∂restrictedLevelSpinPair hN S hS h b i

theorem restrictedBlockPairMean_comparison {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (b : Fin N → ℝ)
    (i : Fin (h.depth + 1)) {t : ℝ} (ht : 0 < t) :
    |restrictedBlockPairMean hN S hS h b i -
        (N : ℝ)⁻¹ * ∑ j, magneticLevelAtBias h (b j) i| ≤
      2 * (biasedConstrainedBlockValue Finset.univ h b - biasedConstrainedBlockValue S h b) / t + t / 2 := by
  let P := restrictedLevelSpinPair hN S hS h b i
  let Q := restrictedLevelSpinPair hN Finset.univ Finset.univ_nonempty h b i
  let e := (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool (Fin N)).symm
  let μ := P.map e
  let ν := fun j => biasedFieldLevelSpinPair h (b j) i
  let D := biasedConstrainedBlockValue Finset.univ h b - biasedConstrainedBlockValue S h b
  have hD : 0 ≤ D := (biasedConstrainedBlockValue_gap hN S hS h b).1
  have hQ : Q.map e = Measure.pi ν := canonicalLevelSpinPair_product hN h b i
  have hK : klDiv μ (Measure.pi ν) ≤ 2 * ENNReal.ofReal (N * D) := by
    rw [← hQ]
    exact (klDiv_map_le P Q e.measurable).trans (restrictedLevelSpinPair_entropy hN S hS h b i)
  have hk : klDiv μ (Measure.pi ν) ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hK
  have hkr : (klDiv μ (Measure.pi ν)).toReal ≤ 2 * (N : ℝ) * D := by
    have he := ENNReal.toReal_mono (by finiteness) hK
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg N) hD), mul_assoc] using he
  have he := spinPairSiteSum_entropy_bound μ ν hk ht
  have hmean : (∫ u, spinPairSiteSum u ∂μ) =
      ∫ p, ∑ j, spinValue (p.1 j) * spinValue (p.2 j) ∂P := by
    rw [show μ = P.map e from rfl, integral_map e.measurable.aemeasurable
      (measurable_of_finite spinPairSiteSum).aestronglyMeasurable]
    rfl
  rw [hmean] at he
  simp_rw [show ∀ j, (∫ p, spinPairSiteValue p ∂ν j) = magneticLevelAtBias h (b j) i
    from fun j => biasedFieldLevelSpinPair_mean h (b j) i] at he
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ = (N : ℝ)⁻¹ * |(∫ p, ∑ j, spinValue (p.1 j) * spinValue (p.2 j) ∂P) -
        ∑ j, magneticLevelAtBias h (b j) i| := by
      rw [restrictedBlockPairMean, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hn)]
    _ ≤ (N : ℝ)⁻¹ * ((2 * N * D) / t + N * t / 2) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hn.le)
      exact he.trans (add_le_add_left (div_le_div_of_nonneg_right hkr ht.le) _)
    _ = _ := by
      field_simp
      ring

end InvariantIsing

end

end OAI
