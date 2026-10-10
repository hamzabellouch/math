import OAI.Probability.InvariantIsing.Magnetic.RestrictedPairEntropy
import OAI.Probability.InvariantIsing.Magnetic.ConstrainedBlockBias

namespace OAI

/-! The shared Gaussian root preserves the pair entropy estimate. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped NNReal ENNReal

namespace InvariantIsing

def restrictedLevelSpinPair {N : ℕ} (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty)
    (h : FieldStep) (b : Fin N → ℝ) (i : Fin (h.depth + 1)) : Measure (Spin N × Spin N) :=
  restrictedPairSpinKernel hN S hS h.depth (chainExponent h.cut) (fieldStepVariance h)
    (fun j hj => ((chainExponent_admissible h.ordered_cut h.first h.last).1 j hj).1) i ∘ₘ
      Measure.pi (fun j => gaussianReal (b j) (NNReal.mk (h.height 0) (h.nonneg 0)))

instance restrictedLevelSpinPair_probability {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (b : Fin N → ℝ)
    (i : Fin (h.depth + 1)) : IsProbabilityMeasure (restrictedLevelSpinPair hN S hS h b i) := by
  unfold restrictedLevelSpinPair
  infer_instance

theorem restrictedLevelSpinPair_entropy {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (b : Fin N → ℝ)
    (i : Fin (h.depth + 1)) :
    klDiv (restrictedLevelSpinPair hN S hS h b i)
      (restrictedLevelSpinPair hN Finset.univ Finset.univ_nonempty h b i) ≤
        2 * ENNReal.ofReal ((N : ℝ) *
          (biasedConstrainedBlockValue Finset.univ h b - biasedConstrainedBlockValue S h b)) := by
  let μ := Measure.pi (fun j => gaussianReal (b j) (NNReal.mk (h.height 0) (h.nonneg 0)))
  let B := chainExponent h.cut
  let V := fieldStepVariance h
  have hB : ∀ j < h.depth, 0 < B j :=
    fun j hj => ((chainExponent_admissible h.ordered_cut h.first h.last).1 j hj).1
  have hB1 : ∀ j < h.depth, B j ≤ 1 :=
    fun j hj => ((chainExponent_admissible h.ordered_cut h.first h.last).1 j hj).2.le
  let κ := restrictedPairSpinKernel hN S hS h.depth B V hB i
  let η := restrictedPairSpinKernel hN Finset.univ Finset.univ_nonempty h.depth B V hB i
  let F := restrictedFieldRecursion (Finset.univ : Finset (Spin N)) h.depth B V
  let G := restrictedFieldRecursion S h.depth B V
  have hi (z : Fin N → ℝ) := restrictedPairSpinKernel_entropy hN S hS h.depth B V hB hB1 i z
  have hac (z : Fin N → ℝ) : κ z ≪ η z :=
    (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top (by finiteness) (hi z))).1
  have hκ (z : Fin N → ℝ) : kernelRelativeEntropy κ η z ≤ 2 * ENNReal.ofReal (F z - G z) := by
    rw [kernelRelativeEntropy_eq κ η z (hac z)]
    exact hi z
  have he := entropy_budget_drop μ μ κ η hac (fun z => 2 * ENNReal.ofReal (F z - G z)) hκ
  have hF := restrictedFieldRecursion_biased_root_integrable hN Finset.univ Finset.univ_nonempty h b
  have hG := restrictedFieldRecursion_biased_root_integrable hN S hS h b
  have hDm : Measurable (fun z => ENNReal.ofReal (F z - G z)) :=
    ((restrictedFieldRecursion_regular hN Finset.univ Finset.univ_nonempty h.depth B V hB).1.sub
      (restrictedFieldRecursion_regular hN S hS h.depth B V hB).1).ennreal_ofReal
  have hD0 (z : Fin N → ℝ) : 0 ≤ F z - G z := sub_nonneg.mpr
    (restrictedFieldRecursion_mono hN S Finset.univ hS Finset.univ_nonempty
      (Finset.subset_univ S) h.depth B V hB z)
  rw [klDiv_self, zero_add, lintegral_const_mul 2 hDm,
    ← ofReal_integral_eq_lintegral_ofReal (f := fun z => F z - G z) (μ := μ)
      (hF.sub hG) (Filter.Eventually.of_forall hD0)] at he
  have hval : (∫ z, F z - G z ∂μ) = (N : ℝ) *
      (biasedConstrainedBlockValue Finset.univ h b - biasedConstrainedBlockValue S h b) := by
    rw [integral_sub (f := F) (g := G) hF hG]
    unfold biasedConstrainedBlockValue
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    dsimp only [μ, F, G, B, V]
    field_simp
    ring
  rw [hval] at he
  exact he

end InvariantIsing

end

end OAI
