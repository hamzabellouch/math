import OAI.Probability.InvariantIsing.Magnetic.RestrictedFieldTerminal
import OAI.Probability.InvariantIsing.Fields.FieldPublishedPairInput
import OAI.Probability.InvariantIsing.Arrays.NSpinFactorization

namespace OAI

/-! The actual vector Gaussian recursion for a constrained cavity block.
Regularity follows from the terminal's finite-spin estimates, with no
assumption on the number of cascade levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def restrictedFieldRecursion {N : ℕ} (S : Finset (Spin N)) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) : (Fin N → ℝ) → ℝ :=
  cascadeRecursion n b (fun i => vectorGaussianLaw N (v i))
    (fun _ p => p.1 + p.2) (restrictedFieldTerminal S)

lemma restrictedFieldRecursion_regular {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) :
    Measurable (restrictedFieldRecursion S n b v) ∧
      HasLinearGrowth (restrictedFieldRecursion S n b v) := by
  have hm := (continuous_restrictedFieldTerminal S hS).measurable
  exact ⟨measurable_cascadeRecursion n b _ (fun _ => measurable_fst.add measurable_snd) hm,
    cascadeRecursion_linearGrowth n b _ (fun i _ => vectorGaussianLaw_moments hN (v i))
      hm (restrictedFieldTerminal_linearGrowth S hS) hb⟩

lemma restrictedFieldRecursion_lipschitz {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (z y : Fin N → ℝ) :
    |restrictedFieldRecursion S n b v z - restrictedFieldRecursion S n b v y| ≤ N * ‖z - y‖ :=
  cascadeRecursion_lipschitz n b _ (fun i _ => vectorGaussianLaw_moments hN (v i))
    (continuous_restrictedFieldTerminal S hS).measurable
    (restrictedFieldTerminal_linearGrowth S hS)
    (restrictedFieldTerminal_norm_difference S hS) hb z y

lemma integrable_exp_restrictedFieldRecursion {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (root : ℝ≥0) (t : ℝ) (z : Fin N → ℝ) :
    Integrable (fun w => Real.exp (t * restrictedFieldRecursion S n b v (z + w)))
      (vectorGaussianLaw N root : Measure (Fin N → ℝ)) := by
  obtain ⟨hm, hg⟩ := restrictedFieldRecursion_regular hN S hS n b v hb
  exact integrable_exp_of_linearGrowth _ (vectorGaussianLaw_moments hN root)
    (hm.comp (measurable_const.add measurable_id)) (hg.add_left z) t

lemma restrictedFieldRecursion_root_integrable {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (root : ℝ≥0) :
    Integrable (restrictedFieldRecursion S n b v)
      (vectorGaussianLaw N root : Measure (Fin N → ℝ)) := by
  obtain ⟨hm, C, L, _, hL, hbound⟩ := restrictedFieldRecursion_regular hN S hS n b v hb
  apply ((integrable_const C).add (((vectorGaussianLaw_moments hN root) 1).const_mul L)).mono'
    hm.aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs]
  calc
    _ ≤ C + L * ‖z‖ := hbound z
    _ ≤ C + L * Real.exp (1 * ‖z‖) := by
      gcongr
      simpa only [one_mul] using (le_add_of_nonneg_right zero_le_one).trans
        (Real.add_one_le_exp ‖z‖)

def constrainedBlockValue {N : ℕ} (S : Finset (Spin N)) (h : FieldStep) : ℝ :=
  (N : ℝ)⁻¹ * (∫ z, restrictedFieldRecursion S h.depth (chainExponent h.cut)
    (fieldStepVariance h) z
    ∂(vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ))) -
      h.height (Fin.last h.depth) / 2

lemma constrainedBlockValue_root_integrable {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) :
    Integrable (restrictedFieldRecursion S h.depth (chainExponent h.cut) (fieldStepVariance h))
      (vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ)) :=
  restrictedFieldRecursion_root_integrable hN S hS _ _ _
    (fun i hi => ((chainExponent_admissible h.ordered_cut h.first h.last).1 i hi).1) _

end InvariantIsing

end

end OAI
