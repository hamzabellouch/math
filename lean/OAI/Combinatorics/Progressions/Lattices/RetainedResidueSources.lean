import OAI.Combinatorics.Progressions.Estimates.RetainedCoefficientSlice
import OAI.Combinatorics.Progressions.Probability.RefinedSliceLaws

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def retainedCubeSliceOfFinite {q M : ℕ} (s : FiniteCubeSlice q)
    (hm : ∀ i, 0 < s.modulus i) (hmM : ∀ i, s.modulus i ≤ M)
    (w : (Option (Fin q) → ℝ) → ℝ) (B T η : ℝ≥0)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hmean : (η : ℝ) ≤ 𝔼 x : s.Domain, translatedCubeWeight s.length s.root w (s.coordinates x)) :
    RetainedCubeSlice q M B T η := by
  refine {
    length := s.length, root := s.root, modulus := s.modulus
    residue := shiftScalarCubeResidues s.root s.modulus s.residue
    modulus_pos := hm, modulus_le := hmM
    weight := w, weight_range := hw, weight_lipschitz := hLip, mean_lower := ?_ }
  have hres := shiftScalarCubeResidues_neg_cancel (-s.root) s.modulus s.residue
  simp only [neg_neg] at hres
  rw [hres]
  exact hmean

theorem retainedCubeSliceOfFinite_finiteSlice {q M : ℕ} (s : FiniteCubeSlice q)
    (hm : ∀ i, 0 < s.modulus i) (hmM : ∀ i, s.modulus i ≤ M)
    (w : (Option (Fin q) → ℝ) → ℝ) (B T η : ℝ≥0)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hmean : (η : ℝ) ≤ 𝔼 x : s.Domain, translatedCubeWeight s.length s.root w (s.coordinates x)) :
    (retainedCubeSliceOfFinite s hm hmM w B T η hw hLip hmean).finiteSlice = s := by
  change (⟨s.length, s.root, s.modulus,
    shiftScalarCubeResidues (-s.root) s.modulus
      (shiftScalarCubeResidues s.root s.modulus s.residue)⟩ : FiniteCubeSlice q) = s
  have hres := shiftScalarCubeResidues_neg_cancel (-s.root) s.modulus s.residue
  simp only [neg_neg] at hres
  rw [hres]

noncomputable def retainedCubeSliceOfResidue {q M : ℕ} (s : FiniteCubeSlice q) [Nonempty s.Domain]
    (n : Option (Fin q) → ℕ) (hdvd : ∀ i, s.modulus i ∣ n i) (r : s.ResidueLabel n)
    (hn : ∀ i, 0 < n i) (hnM : ∀ i, n i ≤ M) (w : (Option (Fin q) → ℝ) → ℝ)
    (B T η : ℝ≥0) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hr : r ∉ (FiniteProbabilityWeights.uniform s.Domain).lowWeightFibers (s.residueLabelMap n)
      (fun x => translatedCubeWeight s.length s.root w (s.coordinates x)) η) :
    RetainedCubeSlice q M B T η :=
  retainedCubeSliceOfFinite (s.refineResidues n r) hn hnM w B T η hw hLip
    (s.retained_refineResidues_mean_ge n hdvd r (translatedCubeWeight s.length s.root w) η hr)

theorem retainedCubeSliceOfResidue_finiteSlice {q M : ℕ} (s : FiniteCubeSlice q) [Nonempty s.Domain]
    (n : Option (Fin q) → ℕ) (hdvd : ∀ i, s.modulus i ∣ n i) (r : s.ResidueLabel n)
    (hn : ∀ i, 0 < n i) (hnM : ∀ i, n i ≤ M) (w : (Option (Fin q) → ℝ) → ℝ)
    (B T η : ℝ≥0) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hr : r ∉ (FiniteProbabilityWeights.uniform s.Domain).lowWeightFibers (s.residueLabelMap n)
      (fun x => translatedCubeWeight s.length s.root w (s.coordinates x)) η) :
    (retainedCubeSliceOfResidue s n hdvd r hn hnM w B T η hw hLip hr).finiteSlice =
      s.refineResidues n r :=
  retainedCubeSliceOfFinite_finiteSlice _ _ _ _ _ _ _ _ _ _

noncomputable def retainedCoefficientSliceOfFinite {M : ℕ} (s : FiniteCoefficientSlice)
    (hm : 0 < s.modulus) (hmM : s.modulus ≤ M) (w : (Option Empty → ℝ) → ℝ) (B T η : ℝ≥0)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hmean : (η : ℝ) ≤ 𝔼 x : s.Domain, w (fun _ => (x.val : ℝ) / s.length)) :
    RetainedCoefficientSlice M B T η where
  length := s.length
  modulus := s.modulus
  residue := s.residue
  modulus_pos := hm
  modulus_le := hmM
  weight := w
  weight_range := hw
  weight_lipschitz := hLip
  mean_lower := hmean

theorem retainedCoefficientSliceOfFinite_finiteSlice {M : ℕ} (s : FiniteCoefficientSlice)
    (hm : 0 < s.modulus) (hmM : s.modulus ≤ M) (w : (Option Empty → ℝ) → ℝ) (B T η : ℝ≥0)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hmean : (η : ℝ) ≤ 𝔼 x : s.Domain, w (fun _ => (x.val : ℝ) / s.length)) :
    (retainedCoefficientSliceOfFinite s hm hmM w B T η hw hLip hmean).finiteSlice s.offset s.stride = s := rfl

noncomputable def retainedCoefficientSliceOfResidue {M : ℕ} (s : FiniteCoefficientSlice) [Nonempty s.Domain]
    (n : ℕ) (hdvd : s.modulus ∣ n) (r : s.ResidueLabel n) (hn : 0 < n) (hnM : n ≤ M)
    (w : (Option Empty → ℝ) → ℝ) (B T η : ℝ≥0)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hr : r ∉ (FiniteProbabilityWeights.uniform s.Domain).lowWeightFibers (s.residueLabelMap n)
      (fun x => w (fun _ => (x.val : ℝ) / s.length)) η) : RetainedCoefficientSlice M B T η := by
  apply retainedCoefficientSliceOfFinite (s.refineResidues n r) hn hnM w B T η hw hLip
  refine FiniteProbabilityWeights.retained_embedding_mean_ge
    (s.residueLabelMap n) (fun x => w (fun _ => (x.val : ℝ) / s.length)) η r
    (s.refineResiduesEmbedding n hdvd r) hr ?_ (s.refineResidues_mass_pos n hdvd r)
  apply (s.refineResiduesEmbedding_range n hdvd r).trans
  ext x
  simp only [Finset.mem_filter]

theorem retainedCoefficientSliceOfResidue_finiteSlice {M : ℕ} (s : FiniteCoefficientSlice) [Nonempty s.Domain]
    (n : ℕ) (hdvd : s.modulus ∣ n) (r : s.ResidueLabel n) (hn : 0 < n) (hnM : n ≤ M)
    (w : (Option Empty → ℝ) → ℝ) (B T η : ℝ≥0)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hr : r ∉ (FiniteProbabilityWeights.uniform s.Domain).lowWeightFibers (s.residueLabelMap n)
      (fun x => w (fun _ => (x.val : ℝ) / s.length)) η) :
    (retainedCoefficientSliceOfResidue s n hdvd r hn hnM w B T η hw hLip hr).finiteSlice s.offset s.stride =
      s.refineResidues n r := rfl

end Erdos3

end

end OAI
