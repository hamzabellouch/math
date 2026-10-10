import OAI.Probability.InvariantIsing.Cavity.CavityProjectionGeometry
import OAI.Probability.InvariantIsing.Cavity.CavityFullTail

namespace OAI

/-! The full-model cutoff estimate for the actual normalized spectral
image construction, with no inverse-Gram estimate on the bad event. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma measurable_cavityFullSpecialCoordinates {N n m d : ℕ}
    (g : Fin (N + n) → Fin m)
    (B : SpecialOrthogonal (N + n) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : Measurable B) (σ : Spin (N + n)) :
    Measurable (fun U => cavityFullSpecialCoordinates g (B U) U σ) := by
  have hO : Measurable (cavitySpecialOrthogonal (N := N + n)) :=
    measurable_subtype_coe.subtype_mk
  have hA : Measurable (fun U : SpecialOrthogonal (N + n) =>
      cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U))) :=
    measurable_pi_iff.mpr fun a => ((measurable_cavitySpectralImage g a).comp
      (measurable_cavityColumns N n)).comp hO
  have hW := (measurable_cavityEigenspaceFrame (N + n) m n).comp hA
  have hmul : Continuous (fun p : Matrix (Fin (N + n)) (Fin (m * n)) ℝ ×
      Matrix (Fin (m * n)) (Fin d) ℝ => p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  have hV := hmul.measurable.comp (hW.prodMk hB)
  have hz : Measurable (fun U : SpecialOrthogonal (N + n) =>
      ((cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U))) *
        B U).transpose *ᵥ (specialRotation U (spinVector σ)).ofLp)) := by
    apply measurable_pi_iff.mpr
    intro j
    change Measurable (fun U : SpecialOrthogonal (N + n) => ∑ i : Fin (N + n),
      (cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U))) *
        B U) i j * specialRotation U (spinVector σ) i)
    apply Finset.measurable_sum
    intro i _
    exact hV.eval_matrix.mul (measurable_specialRotation_eval (spinVector σ) i)
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.continuous.measurable).comp hz

theorem cavity_full_geometric_tail {N n m d depth : ℕ} (hN : 0 < N + n)
    (μ : Measure (SpecialOrthogonal (N + n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin (N + n) → ℝ) (g : Fin (N + n) → Fin m)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (B : SpecialOrthogonal (N + n) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hmB : Measurable B) (hB : ∀ U, (B U).transpose * B U = 1)
    (good : Set (SpecialOrthogonal (N + n))) (hgood : MeasurableSet good)
    {L R : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hbound : ∀ U ∈ good, ∀ a,
      ‖(CFC.sqrt (cavityCompressionGrams g (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L) :
    cavityFullDisorderTest μ T eig (cavitySpectralGroup g) u
      (fun U σ => if R < ‖cavityFullSpecialCoordinates g (B U) U (σ 0).1‖ then 1 else 0) ≤
    μ.real goodᶜ + L ^ 2 * ((m : ℝ) * n) / R ^ 2 := by
  let y := fun (U : SpecialOrthogonal (N + n))
    (σ : Fin 2 → Spin (N + n) × LabeledLeaf depth) =>
      cavityFullSpecialCoordinates g (B U) U (σ 0).1
  have hmy : Measurable (Function.uncurry y) := by
    apply measurable_from_prod_countable_left
    intro σ
    exact measurable_cavityFullSpecialCoordinates g B hmB (σ 0).1
  have hgeom : ∀ U ∈ good, ∀ σ,
      (L ^ 2)⁻¹ * ‖y U σ‖ ^ 2 ≤
        cavityProjectionAxesTest (cavitySpectralGroup g) (Fin.natAdd N) U σ := by
    intro U hU σ
    have h := cavity_full_special_coordinates_control g (B U) (hB U) U (σ 0).1 hL.le (hbound U hU)
    have he : (∑ a, ∑ j : Fin n,
        (cavitySpectralProjection (specialRotation U) (cavitySpectralGroup g a)
          (spinVector (σ 0).1) (Fin.natAdd N j)) ^ 2) =
        cavityProjectionAxesTest (cavitySpectralGroup g) (Fin.natAdd N) U σ := by
      exact (Fintype.sum_prod_type (fun t : Fin m × Fin n =>
        (cavitySpectralProjection (specialRotation U) (cavitySpectralGroup g t.1)
          (spinVector (σ 0).1) (Fin.natAdd N t.2)) ^ 2)).symm
    rw [he] at h
    exact (inv_mul_le_iff₀ (sq_pos_of_pos hL)).mpr h
  have ht := cavity_full_tail_probability hN μ T eig (cavitySpectralGroup g) u hu
    (Fin.natAdd N) good hgood y hmy (inv_pos.mpr (sq_pos_of_pos hL)) hR hgeom
  have hid : ((m : ℝ) * n) / ((L ^ 2)⁻¹ * R ^ 2) =
      L ^ 2 * ((m : ℝ) * n) / R ^ 2 := by
    field_simp
  simpa only [hid, y] using ht

end InvariantIsing

end

end OAI
