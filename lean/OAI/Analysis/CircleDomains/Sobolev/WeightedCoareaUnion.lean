import OAI.Analysis.CircleDomains.Sobolev.CoareaInput

namespace OAI

/-! Countable measurable disjoint assembly of the weighted coarea identity. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma measurableSet_restricted_scalar_level {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) {A : Set ℂ} (hA : MeasurableSet A)
    (hAD : A ⊆ D) (t : ℝ) : MeasurableSet (A ∩ {z | f z = t}) := by
  have he : A ∩ {z | f z = t} = A ∩ (D ∩ {z | f z = t}) := by
    ext z
    constructor
    · exact fun hz => ⟨hz.1, hAD hz.1, hz.2⟩
    · exact fun hz => ⟨hz.1, hz.2.2⟩
  rw [he]
  exact hA.inter (measurableSet_scalar_level hD hf t)

lemma weightedScalarLevelLength_iUnion {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) (A : ℕ → Set ℂ)
    (hA : ∀ n, MeasurableSet (A n)) (hdj : Pairwise (Disjoint on A))
    (hAD : ∀ n, A n ⊆ D) (q : ℂ → ℝ≥0∞) (t : ℝ) :
    weightedScalarLevelLength (⋃ n, A n) f q t = ∑' n, weightedScalarLevelLength (A n) f q t := by
  simp only [weightedScalarLevelLength, iUnion_inter]
  apply lintegral_iUnion (fun n => measurableSet_restricted_scalar_level hD hf (hA n) (hAD n) t)
  exact fun i j hij => (hdj hij).mono inter_subset_left inter_subset_left

lemma weighted_coarea_iUnion {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) (A : ℕ → Set ℂ)
    (hA : ∀ n, MeasurableSet (A n)) (hdj : Pairwise (Disjoint on A))
    (hAD : ∀ n, A n ⊆ D) (q : ℂ → ℝ≥0∞)
    (hlocal : ∀ n, WeightedScalarCoareaIdentity (A n) f q) :
    WeightedScalarCoareaIdentity (⋃ n, A n) f q := by
  have heq : weightedScalarLevelLength (⋃ n, A n) f q =
      fun t => ∑' n, weightedScalarLevelLength (A n) f q t :=
    funext (weightedScalarLevelLength_iUnion hD hf A hA hdj hAD q)
  refine ⟨by rw [heq]; exact AEMeasurable.tsum (fun n => (hlocal n).1), ?_⟩
  rw [heq, lintegral_tsum (fun n => (hlocal n).1)]
  calc
    (∑' n, ∫⁻ t, weightedScalarLevelLength (A n) f q t) =
        ∑' n, ∫⁻ z in A n, q z * ENNReal.ofReal ‖fderiv ℝ f z‖ :=
      tsum_congr (fun n => (hlocal n).2)
    _ = _ := (lintegral_iUnion hA hdj (fun z => q z * ENNReal.ofReal ‖fderiv ℝ f z‖)).symm

end CircleDomainRigidity

end

end OAI
