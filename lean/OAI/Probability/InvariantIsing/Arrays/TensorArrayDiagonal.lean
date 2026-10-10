import OAI.Probability.InvariantIsing.Arrays.TensorArrayLaw
import OAI.Probability.InvariantIsing.Arrays.TensorDiagonalError

namespace OAI

/-! Actual array self-overlap deviations, with compact deterministic centers. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology

namespace InvariantIsing

lemma tensorNamespacedObservableAverage_mono {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D E : SpecialOrthogonal N → (Spin N × LabeledLeaf n) → ℝ)
    (hD : Measurable (Function.uncurry D)) (hE : Measurable (Function.uncurry E))
    {B C : ℝ} (hDb : ∀ U x, |D U x| ≤ B) (hEb : ∀ U x, |E U x| ≤ C)
    (hDE : ∀ U x, D U x ≤ E U x) :
    tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h D ≤
      tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h E := by
  apply integral_mono
    (tensorNamespacedObservableAverage_integrable μ eig c I degree amplitude n b r h D hD hDb)
    (tensorNamespacedObservableAverage_integrable μ eig c I degree amplitude n b r h E hE hEb)
  intro p
  apply integral_mono
    (Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable B
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hDb p.1.1 x))
    (Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable C
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hEb p.1.1 x))
  exact hDE p.1.1

lemma tensorSpectralDiagonal_clipping {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (a : Fin m) (center : ℝ) :
    tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h
      (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - spectralDiagonalCenter center|) ≤
      tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h
      (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center|) := by
  exact tensorNamespacedObservableAverage_mono μ eig c I degree amplitude n b r h _ _
    (measurable_spectralDiagonalDeviation (I a) n _) (measurable_spectralDiagonalDeviation (I a) n _)
    (fun U x => spectralDiagonalDeviation_abs_le (specialRotation U) (I a) _ x.1)
    (fun U x => spectralDiagonalDeviation_abs_le (specialRotation U) (I a) _ x.1)
    (fun U x => abs_sub_spectralDiagonalCenter_le
      ⟨projectedOverlap_self_nonneg _ _ _, projectedOverlap_self_le_one _ _ _⟩ center)

theorem tensorNamespacedArrayLaw_observable_test {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (F : SpectralArray (m + 1) → ℝ) (hF : Continuous F)
    (D : SpecialOrthogonal N → (Spin N × LabeledLeaf n) → ℝ) (i : ℕ)
    (he : ∀ (U : SpecialOrthogonal N) (σ : ℕ → Spin N × LabeledLeaf n),
      F (fun ij : ℕ × ℕ => spectralJointEntry (specialRotation U) I n (σ ij.1) (σ ij.2)) = D U (σ i)) :
    (∫ x, F x ∂(tensorNamespacedArrayLaw μ eig c I degree amplitude n b r h :
      Measure (SpectralArray (m + 1)))) =
      tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h D := by
  rw [tensorNamespacedArrayLaw, spectralArrayLaw_integral _ _ _ _ _ _ _ F hF]
  unfold tensorNamespacedObservableAverage
  apply integral_congr_ae
  filter_upwards [] with p
  let ν := tensorNamespacedReference eig c I degree amplitude n r h p
  have ht := integral_map (measurable_pi_apply i).aemeasurable
    (μ := Measure.infinitePi (fun _ : ℕ => ν)) (measurable_of_countable (D p.1.1)).aestronglyMeasurable
  rw [Measure.infinitePi_map_eval] at ht
  change (∫ σ, F (fun ij : ℕ × ℕ =>
    spectralJointEntry (specialRotation p.1.1) I n (σ ij.1) (σ ij.2))
    ∂Measure.infinitePi (fun _ : ℕ => ν)) = ∫ x, D p.1.1 x ∂ν
  simp_rw [he]
  exact ht.symm

theorem tensorNamespacedArrayLaw_spectralDiagonal {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (i : ℕ) (a : Fin m) (center : ℝ) :
    (∫ x, |(x (i, i) a.castSucc : ℝ) - center|
      ∂(tensorNamespacedArrayLaw μ eig c I degree amplitude n b r h : Measure (SpectralArray (m + 1)))) =
      tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h
        (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center|) := by
  apply tensorNamespacedArrayLaw_observable_test μ eig c I degree amplitude n b r h _
    (by fun_prop) _ i
  intro U σ
  rw [spectralJointEntry_spectral]

lemma tensorNamespacedArrayLaw_treeDiagonal {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (i : ℕ) :
    (∫ x, |(x (i, i) (Fin.last m) : ℝ) - (n : ℝ) / (n + 1 : ℕ)|
      ∂(tensorNamespacedArrayLaw μ eig c I degree amplitude n b r h : Measure (SpectralArray (m + 1)))) = 0 := by
  calc
    _ = tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h (fun _ _ => 0) := by
      apply tensorNamespacedArrayLaw_observable_test μ eig c I degree amplitude n b r h _
        (by fun_prop) _ i
      intro U σ
      rw [spectralJointEntry_tree, treeOverlap_self, sub_self, abs_zero]
    _ = 0 := by unfold tensorNamespacedObservableAverage; simp

end InvariantIsing

end

end OAI
