import OAI.Combinatorics.Progressions.Estimates.RelativeRetainedCubeSource

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def retainedCubeResidueModel {q M : ℕ} (s : FiniteCubeSlice q) [Nonempty s.Domain]
    (n : Option (Fin q) → ℕ) (hdvd : ∀ i, s.modulus i ∣ n i) (r : s.ResidueLabel n)
    (hn : ∀ i, 0 < n i) (hnM : ∀ i, n i ≤ M) (w : (Option (Fin q) → ℝ) → ℝ)
    (B T η : ℝ≥0) (hη : 0 < η) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hcut : scalarCubeNormalizationThreshold (Fin q) M (B / η) (T / η) ≤ s.length)
    (hr : r ∉ (FiniteProbabilityWeights.uniform s.Domain).lowWeightFibers (s.residueLabelMap n)
      (fun x => translatedCubeWeight s.length s.root w (s.coordinates x)) η) :
    SmoothCubeSlice q M (B / (η / 2)) (T / (η / 2)) := by
  apply retainedSmoothCubeSlice s.length s.root n (shiftScalarCubeResidues s.root n r.val)
    hn hnM w B T η hη hw hLip hcut
  have hres := shiftScalarCubeResidues_neg_cancel (-s.root) n r.val
  simp only [neg_neg] at hres
  rw [hres]
  exact s.retained_refineResidues_mean_ge n hdvd r (translatedCubeWeight s.length s.root w) η hr

theorem retainedCubeResidueModel_finiteSlice {q M : ℕ} (s : FiniteCubeSlice q) [Nonempty s.Domain]
    (n : Option (Fin q) → ℕ) (hdvd : ∀ i, s.modulus i ∣ n i) (r : s.ResidueLabel n)
    (hn : ∀ i, 0 < n i) (hnM : ∀ i, n i ≤ M) (w : (Option (Fin q) → ℝ) → ℝ)
    (B T η : ℝ≥0) (hη : 0 < η) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hcut : scalarCubeNormalizationThreshold (Fin q) M (B / η) (T / η) ≤ s.length)
    (hr : r ∉ (FiniteProbabilityWeights.uniform s.Domain).lowWeightFibers (s.residueLabelMap n)
      (fun x => translatedCubeWeight s.length s.root w (s.coordinates x)) η) :
    (retainedCubeResidueModel s n hdvd r hn hnM w B T η hη hw hLip hcut hr).finiteSlice =
      s.refineResidues n r := by
  change (⟨s.length, s.root, n,
    shiftScalarCubeResidues (-s.root) n (shiftScalarCubeResidues s.root n r.val)⟩ : FiniteCubeSlice q) = _
  have hres := shiftScalarCubeResidues_neg_cancel (-s.root) n r.val
  simp only [neg_neg] at hres
  rw [hres]
  rfl

noncomputable def retainedCoefficientResidueModel {M : ℕ} (s : FiniteCoefficientSlice)
    [Nonempty s.Domain] (n : ℕ) (hdvd : s.modulus ∣ n) (r : s.ResidueLabel n)
    (hn : 0 < n) (hnM : n ≤ M) (w : (Option Empty → ℝ) → ℝ)
    (B T η : ℝ≥0) (hη : 0 < η) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hcut : scalarCubeNormalizationThreshold Empty M (B / η) (T / η) ≤ s.length)
    (hr : r ∉ (FiniteProbabilityWeights.uniform s.Domain).lowWeightFibers (s.residueLabelMap n)
      (fun x => w (fun _ => (x.val : ℝ) / s.length)) η) :
    SmoothCoefficientSlice M (B / (η / 2)) (T / (η / 2)) := by
  apply retainedSmoothCoefficientSlice s.length n r.val hn hnM w B T η hη hw hLip hcut
  refine FiniteProbabilityWeights.retained_embedding_mean_ge
    (s.residueLabelMap n) (fun x => w (fun _ => (x.val : ℝ) / s.length)) η r
    (s.refineResiduesEmbedding n hdvd r) hr ?_ (s.refineResidues_mass_pos n hdvd r)
  apply (s.refineResiduesEmbedding_range n hdvd r).trans
  ext x
  simp only [Finset.mem_filter]

theorem retainedCoefficientResidueModel_finiteSlice {M : ℕ} (s : FiniteCoefficientSlice)
    [Nonempty s.Domain] (n : ℕ) (hdvd : s.modulus ∣ n) (r : s.ResidueLabel n)
    (hn : 0 < n) (hnM : n ≤ M) (w : (Option Empty → ℝ) → ℝ)
    (B T η : ℝ≥0) (hη : 0 < η) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hcut : scalarCubeNormalizationThreshold Empty M (B / η) (T / η) ≤ s.length)
    (hr : r ∉ (FiniteProbabilityWeights.uniform s.Domain).lowWeightFibers (s.residueLabelMap n)
      (fun x => w (fun _ => (x.val : ℝ) / s.length)) η) :
    (retainedCoefficientResidueModel s n hdvd r hn hnM w B T η hη hw hLip hcut hr).finiteSlice
      s.offset s.stride = s.refineResidues n r := rfl

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal Classical

theorem integral_pos_of_normalized_div {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hnorm : (∫ x, w x / ∫ y, w y ∂μ ∂μ) = 1) : 0 < ∫ x, w x ∂μ := by
  apply lt_of_le_of_ne (integral_nonneg hw)
  intro hz
  rw [← hz] at hnorm
  simp at hnorm

theorem retainedCubeResidueModel_law {q M : ℕ} (s : FiniteCubeSlice q) [Nonempty s.Domain]
    (n : Option (Fin q) → ℕ) (hdvd : ∀ i, s.modulus i ∣ n i) (r : s.ResidueLabel n)
    (hn : ∀ i, 0 < n i) (hnM : ∀ i, n i ≤ M) (w : (Option (Fin q) → ℝ) → ℝ)
    (B T η : ℝ≥0) (hη : 0 < η) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hcut : scalarCubeNormalizationThreshold (Fin q) M (B / η) (T / η) ≤ s.length)
    (hr : r ∉ (FiniteProbabilityWeights.uniform s.Domain).lowWeightFibers (s.residueLabelMap n)
      (fun x => translatedCubeWeight s.length s.root w (s.coordinates x)) η) :
    let t := retainedCubeResidueModel s n hdvd r hn hnM w B T η hη hw hLip hcut hr
    let v : t.Domain → ℝ := fun x => translatedCubeWeight s.length s.root w (t.finiteSlice.coordinates x)
    ∀ hv : 0 < ∑ x, v x, ∃ ht : 0 < ∑ x, t.sliceWeight x,
      t.law ht = FiniteProbabilityWeights.ofPositiveWeights v (fun _ => (hw _).1) hv := by
  dsimp only
  intro hv
  let t := retainedCubeResidueModel s n hdvd r hn hnM w B T η hη hw hLip hcut hr
  have hI : 0 < ∫ x, w x ∂scalarCubeMeasure (Fin q) :=
    integral_pos_of_normalized_div _ w (fun x => (hw x).1) t.weight_integral
  have ht : 0 < ∑ x, t.sliceWeight x := by
    change 0 < ∑ x : t.Domain,
      translatedCubeWeight s.length s.root w (t.finiteSlice.coordinates x) /
        ∫ y, w y ∂scalarCubeMeasure (Fin q)
    rw [← Finset.sum_div]
    exact div_pos hv hI
  refine ⟨ht, ?_⟩
  exact FiniteProbabilityWeights.ofPositiveWeights_div _ _ hv hI

theorem retainedCoefficientResidueModel_law {M : ℕ} (s : FiniteCoefficientSlice)
    [Nonempty s.Domain] (n : ℕ) (hdvd : s.modulus ∣ n) (r : s.ResidueLabel n)
    (hn : 0 < n) (hnM : n ≤ M) (w : (Option Empty → ℝ) → ℝ)
    (B T η : ℝ≥0) (hη : 0 < η) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hcut : scalarCubeNormalizationThreshold Empty M (B / η) (T / η) ≤ s.length)
    (hr : r ∉ (FiniteProbabilityWeights.uniform s.Domain).lowWeightFibers (s.residueLabelMap n)
      (fun x => w (fun _ => (x.val : ℝ) / s.length)) η) :
    let t := retainedCoefficientResidueModel s n hdvd r hn hnM w B T η hη hw hLip hcut hr
    let v : t.Domain → ℝ := fun x => w (fun _ => (x.val : ℝ) / s.length)
    ∀ hv : 0 < ∑ x, v x, ∃ ht : 0 < ∑ x, t.sliceWeight x,
      t.law ht = FiniteProbabilityWeights.ofPositiveWeights v (fun _ => (hw _).1) hv := by
  dsimp only
  intro hv
  let t := retainedCoefficientResidueModel s n hdvd r hn hnM w B T η hη hw hLip hcut hr
  have hI : 0 < ∫ x, w x ∂scalarCubeMeasure Empty :=
    integral_pos_of_normalized_div _ w (fun x => (hw x).1) t.weight_integral
  have ht : 0 < ∑ x, t.sliceWeight x := by
    change 0 < ∑ x : t.Domain,
      w (fun _ => (x.val : ℝ) / s.length) / ∫ y, w y ∂scalarCubeMeasure Empty
    rw [← Finset.sum_div]
    exact div_pos hv hI
  refine ⟨ht, ?_⟩
  exact FiniteProbabilityWeights.ofPositiveWeights_div _ _ hv hI

end Erdos3

end

end OAI
