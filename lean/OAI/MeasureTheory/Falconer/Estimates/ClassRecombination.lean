import OAI.MeasureTheory.Falconer.Measures.ClassSupport
import OAI.MeasureTheory.Falconer.Fourier.ProductFilterIntegral

namespace OAI

/-! # Exact recombination with the original class masses -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

 theorem classMeasure_eq_mass_smul (Q : DyadicCube d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (L : Finset (CellPath d)) (f : CellPath d → List ℕ) (T : List ℕ)
    (hT : classMeasure Q μ L f T univ ≠ 0) :
    classMeasure Q μ L f T =
      classMeasure Q μ L f T univ • normalizedClass Q μ L f T := by
  let : IsFiniteMeasure (classMeasure Q μ L f T) := by unfold classMeasure; infer_instance
  rw [normalizedClass,smul_smul,ENNReal.mul_inv_cancel hT (measure_ne_top _ _),one_smul]

 theorem retained_class_mass_sum_le_one (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (f : CellPath d → List ℕ) (F : Finset (List ℕ)) (hF : F ⊆ L.image f) :
    (∑ T ∈ F, classMeasure Q μ L f T univ) ≤ 1 := by
  apply (Finset.sum_le_sum_of_subset hF).trans
  rw [class_mass_sum Q hQ μ hL f]
  exact prob_le_one

 theorem retained_class_recombination (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (f : CellPath d → List ℕ) (F : Finset (List ℕ))
    (hF : ∀ T ∈ F, classMeasure Q μ L f T univ ≠ 0) :
    μ.restrict (⋃ T ∈ F, leafUnion Q (classLeaves L f T)) =
      ∑ T ∈ F, classMeasure Q μ L f T univ • normalizedClass Q μ L f T := by
  rw [Measure.restrict_biUnion_finset]
  · change (Measure.sum fun i : F => classMeasure Q μ L f i) = _
    rw [Measure.sum_coe_finset F (fun T => classMeasure Q μ L f T)]
    apply Finset.sum_congr rfl
    intro T hT
    exact classMeasure_eq_mass_smul Q μ L f T (hF T hT)
  · intro T _ U _ hne
    exact leafUnion_disjoint Q hQ
      (fun _ hp => hL (Finset.mem_filter.mp hp).1)
      (fun _ hp => hL (Finset.mem_filter.mp hp).1) (classLeaves_disjoint L f hne)
  · intro T
    exact leafUnion_measurable Q _

 theorem class_original_pair_bad_mass (Q : DyadicCube d) (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [SFinite ν] (L : Finset (CellPath d)) (f : CellPath d → List ℕ)
    (T : List ℕ) (hT : classMeasure Q μ L f T univ ≠ 0)
    (B : Set (Space d × Space d)) (hB : MeasurableSet B) {ε : ℝ≥0∞}
    (hsmall : ((normalizedClass Q μ L f T).prod ν) B ≤ ε) :
    (μ.prod ν) ((leafUnion Q (classLeaves L f T) ×ˢ univ) ∩ B) ≤
      classMeasure Q μ L f T univ*ε := by
  have he : (μ.prod ν) ((leafUnion Q (classLeaves L f T) ×ˢ univ) ∩ B) =
      ((classMeasure Q μ L f T).prod ν) B := by
    change _ = ((μ.restrict (leafUnion Q (classLeaves L f T))).prod ν) B
    conv_rhs => rw [← Measure.restrict_univ (μ := ν)]
    rw [Measure.prod_restrict,Measure.restrict_apply hB,inter_comm]
  have hp : (classMeasure Q μ L f T).prod ν =
      classMeasure Q μ L f T univ • ((normalizedClass Q μ L f T).prod ν) := by
    conv_lhs => rw [classMeasure_eq_mass_smul Q μ L f T hT]
    rw [Measure.prod_smul_left]
  rw [he,hp,Measure.smul_apply,smul_eq_mul]
  exact mul_le_mul' le_rfl hsmall

end Falconer.Regularization

end OAI
