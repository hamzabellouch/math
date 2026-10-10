import OAI.Probability.InvariantIsing.Cavity.CavityTreeCutoffMeasurability
import OAI.Probability.InvariantIsing.Cavity.CavityOriginalRadialCutoff

namespace OAI

/-! The original geometric cutoff average is bounded and measurable in
the labeled tree, so its comparison may be averaged over that tree. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem cavity_original_tree_regular {N n m d depth : ℕ}
    (μ : Measure (Orthogonal (N+n))) [IsProbabilityMeasure μ] (hN : 0 < N+n)
    (g : Fin (N+n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hB : Measurable B) (eig : Fin (N+n) → ℝ) (u : ℕ → ℝ)
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ)
    (hF : ∀ σ, |F σ| ≤ M) :
    Measurable (fun T : LabeledTree depth => ∫ U,
      cavityOriginalGeometricMean g B T eig u (1+R^2) F (cavityOrientationLift hN U) ∂μ) ∧
    ∀ T : LabeledTree depth, |∫ U,
      cavityOriginalGeometricMean g B T eig u (1+R^2) F (cavityOrientationLift hN U) ∂μ| ≤ M := by
  constructor
  · have he := funext fun T : LabeledTree depth =>
      cavity_original_radial_cutoff μ hN g B hB T eig u hR F
    rw [he]
    have hmB : Measurable (fun U : SpecialOrthogonal (N+n) =>
        B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) :=
      hB.comp ((measurable_cavityCompressionGrams g).comp
        (measurable_subtype_coe.subtype_mk))
    exact measurable_cavityFullCutoffDisorderTest_tree _ eig (cavitySpectralGroup g) u _
      (measurableSet_cavitySpecialCutoff g _ hmB R) _
      ((measurable_of_countable (fun σ : Fin 2 → Spin (N+n) × LabeledLeaf depth =>
        F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2)))).comp measurable_snd)
  · intro T
    have hh := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun U => cavityOriginalGeometricMean g B T eig u (1+R^2) F (cavityOrientationLift hN U))
      (C := M) (ae_of_all _ fun U => cavityOriginalGeometricMean_bound g B T eig u (1+R^2) F hM hF _)
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

end InvariantIsing

end

end OAI
