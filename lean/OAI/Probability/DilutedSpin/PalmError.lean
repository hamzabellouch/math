import OAI.Probability.DilutedSpin.FullRootPalm
import OAI.Probability.DilutedSpin.FullTreeScore

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma fullSelectedTreeScore_one (z : FullRootState Y X I M) :
    fullSelectedTreeScore S a T Q m base sel fixed D E t u (fun _ => 1) z =
      fullSelectedRawScore T Q m base sel fixed D E t z u := by
  exact selectedTreeScore_one S a T Q m (base z.1 z.2.1.1 z.2.1.2)
    (rootArray z.2.2.1 z.2.2.2) sel fixed D E t u

/-- The Palm covariance bound under the same complete original reservoir.
Normalization by a type mass `c` can be done after this identity; no root
Poisson families have been deleted or resampled. -/
theorem fullRoot_palm_error
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4)
    (hA : ∀ i x y, 1/2 ≤ selectedFactor sel fixed D E t u i x y) (hs : 0 < s) :
    |(∫ z, fullInsertedTreeScore ν S a T Q m base
        (selectedFactor sel fixed D E t u) (selectedNumerator sel E) f z ∂fullRootLaw ξ μ ν r s) -
      (∫ z, fullSelectedTreeMean S T Q m base sel fixed D E t u f z ∂fullRootLaw ξ μ ν r s) *
      (∫ z, fullInsertedTreeScore ν S a T Q m base
        (selectedFactor sel fixed D E t u) (selectedNumerator sel E) (fun _ => 1) z ∂fullRootLaw ξ μ ν r s)| ≤
      B * fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u / (s:ℝ) := by
  have hh := fullTree_score_error ξ μ ν r s S a T Q m base sel fixed D E t u f hb hB hf hD hE ht hu
  rw [fullRoot_selected_palm ν ξ μ r s S a T Q m base sel fixed D E t u f hb hB hf hD hE ht hu hA] at hh
  have hone := fullRoot_selected_palm ν ξ μ r s S a T Q m base sel fixed D E t u (fun _ => 1)
    hb (by norm_num : (0:ℝ) ≤ 1) (by intro x; norm_num : ∀ x, |(1:ℝ)| ≤ 1) hD hE ht hu hA
  simp_rw [fullSelectedTreeScore_one] at hone
  rw [hone] at hh
  have hsr : (0:ℝ) < s := by exact_mod_cast hs
  rw [mul_left_comm _ (s:ℝ), ← mul_sub,abs_mul,abs_of_pos hsr] at hh
  exact (le_div_iff₀ hsr).mpr (by nlinarith)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
