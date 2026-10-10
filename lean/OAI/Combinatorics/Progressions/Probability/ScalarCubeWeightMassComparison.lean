import OAI.Combinatorics.Progressions.Estimates.ProgressionCubeEmbedding

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal Classical

theorem scalarCube_weight_mass_comparison (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (w : (Option I → ℝ) → ℝ) {B T η : ℝ≥0} (hη : 0 < η)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (h : scalarCubeNormalizationThreshold I M (B / η) (T / η) ≤ L) :
    let hs := scalarCubeNormalizationThreshold_spec I h
    |(scalarCubeResidueWeights I L M hs.1 m r hm hmM hs.2.1).mean
      (fun z => w (fun i => (z i : ℝ) / L)) - ∫ x, w x ∂scalarCubeMeasure I| ≤ (η : ℝ) / 2 := by
  have hη' : (0 : ℝ) < η := hη
  have hs := scalarCubeNormalizationThreshold_spec I h
  apply scalarCubeResidueWeights_riemann_of_length I L M hs.1 m r hm hmM hs.2.1 w
    hLip B.coe_nonneg (fun x => by rw [Real.norm_of_nonneg (hw x).1]; exact (hw x).2)
    (half_pos hη') hs.2.2.1
  have he : M * scalarCubeRiemannAllowance I B T / ((η : ℝ) / 2) =
      2 * M * scalarCubeRiemannAllowance I (B / η : ℝ≥0) (T / η : ℝ≥0) := by
    simp only [scalarCubeRiemannAllowance, NNReal.coe_div]
    field_simp [hη'.ne']
  rw [he]
  exact hs.2.2.2

theorem scalarCube_continuous_mass_of_discrete (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (w : (Option I → ℝ) → ℝ) {B T η : ℝ≥0} (hη : 0 < η)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (h : scalarCubeNormalizationThreshold I M (B / η) (T / η) ≤ L)
    (hretained : (η : ℝ) ≤ (scalarCubeResidueWeights I L M
      (scalarCubeNormalizationThreshold_spec I h).1 m r hm hmM
      (scalarCubeNormalizationThreshold_spec I h).2.1).mean (fun z => w (fun i => (z i : ℝ) / L))) :
    (η : ℝ) / 2 ≤ ∫ x, w x ∂scalarCubeMeasure I := by
  have he := scalarCube_weight_mass_comparison I L M m r hm hmM w hη hw hLip h
  have hh := (abs_le.mp he).2
  linarith

theorem scalarCube_translated_weight_mean (q L M : ℕ) (root : ℤ) (hL : 0 < L)
    (m : Option (Fin q) → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card (Fin q) + 1) * M ≤ L) (w : (Option (Fin q) → ℝ) → ℝ) :
    (scalarCubeResidueWeights (Fin q) L M hL m r hm hmM hsize).mean
      (fun z => w (fun i => (z i : ℝ) / L)) =
      𝔼 x : TranslatedResidueSupportedCube q L root m (shiftScalarCubeResidues (-root) m r),
        translatedCubeWeight L root w (supportedCubeCoordinates x.val.val) := by
  have he := scalarCubeResidueWeights_translated_mean q L M root hL m
    (shiftScalarCubeResidues (-root) m r) hm hmM hsize (translatedCubeWeight L root w)
  simpa only [shiftScalarCubeResidues_neg_cancel, translatedCubeWeight, shiftScalarCube_neg_shift] using he

theorem scalarCube_coefficient_weight_mean (L M : ℕ) (hL : 0 < L)
    (m : ℕ) (r : ZMod m) (hm : 0 < m) (hmM : m ≤ M) (hsize : M ≤ L)
    (w : (Option Empty → ℝ) → ℝ) :
    (scalarCubeResidueWeights Empty L M hL (fun _ => m) (fun _ => r)
      (fun _ => hm) (fun _ => hmM) (by simpa using hsize)).mean
      (fun z => w (fun i => (z i : ℝ) / L)) =
      𝔼 x : ↥(coefficientResidueSet L m r), w (fun _ => (x.val : ℝ) / L) := by
  rw [scalarCubeResidueWeights_mean]
  apply Fintype.expect_equiv (emptyScalarCubeResidueEquiv L (fun _ => m) (fun _ => r))
  intro x
  congr 1
  funext i
  cases i with
  | none => rfl
  | some a => exact a.elim

end Erdos3

end

end OAI
