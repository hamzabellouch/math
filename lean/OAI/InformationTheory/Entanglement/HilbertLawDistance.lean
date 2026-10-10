import OAI.InformationTheory.Entanglement.HilbertMeasureEmbedding
import OAI.InformationTheory.Entanglement.CQVariation

namespace OAI

noncomputable section
open scoped BigOperators ENNReal MeasureTheory InnerProductSpace ComplexOrder MatrixOrder
open MeasureTheory Matrix ContinuousLinearMap
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {T : Type*} [MeasurableSpace T]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} {n : Type} [Fintype n] [DecidableEq n]

def hilbertVariation (b : HilbertBasis ι ℂ H) (F : Set T → H →L[ℂ] H) : ℝ≥0∞ :=
  ⨆ (P : Finset (Set T)) (_ : ∀ s∈P, MeasurableSet s)
    (_ : (P : Set (Set T)).PairwiseDisjoint id), ∑ s∈P, hilbertENorm b (F s)
lemma variation_le_hilbertVariation (b : HilbertBasis ι ℂ H) (F : Set T → H →L[ℂ] H)
    (M : VectorMeasure T (TraceMatrix n))
    (hc : ∀ s, MeasurableSet s → ‖M s‖ₑ≤hilbertENorm b (F s)) :
    M.variation Set.univ≤hilbertVariation b F := by
  by_contra h
  obtain ⟨P,_,hpd,hpm,hP⟩ := M.exists_lt_sum_of_lt_variation MeasurableSet.univ (lt_of_not_ge h)
  have hs : (∑ s∈P, ‖M s‖ₑ)≤∑ s∈P, hilbertENorm b (F s) :=
    Finset.sum_le_sum (fun s hs => hc s (hpm s hs))
  have hv : (∑ s∈P, hilbertENorm b (F s))≤hilbertVariation b F :=
    le_iSup_of_le P (le_iSup_of_le hpm (le_iSup_of_le hpd le_rfl))
  exact (not_lt_of_ge (hs.trans hv)) hP

def hilbertIdeal (σ : Set T → H →L[ℂ] H) (i j : Fin 2) (s : Set T) : H →L[ℂ] H :=
  if i=j then (((1/2 : ℝ) : ℂ) • σ s) else 0
lemma hilbertIdeal_positive (b : HilbertBasis ι ℂ H)
    (σ : PositiveHilbertMeasure T H b) (i j : Fin 2) {s : Set T} (hs : MeasurableSet s) :
    HasFinitePositiveTrace b (hilbertIdeal σ.value i j s) := by
  unfold hilbertIdeal
  split_ifs
  · exact finitePositiveTrace_real_smul b _ (by norm_num) (σ.positive s hs)
  · exact ⟨le_rfl,by simp⟩
omit [MeasurableSpace T] [CompleteSpace H] in
lemma hilbertErase_ideal (b : HilbertBasis ι ℂ H) (v : n → H) (i₀ : n)
    (σ : Set T → H →L[ℂ] H) (i j : Fin 2) (s : Set T) :
    hilbertErase b v i₀ (hilbertIdeal σ i j s)=
      (if i=j then halfDensity (hilbertErase b v i₀ (σ s)) else 0) := by
  unfold hilbertIdeal
  split_ifs
  · rw [hilbertErase_real_smul]
    norm_num [halfDensity]
  · ext a b
    simp [hilbertErase,hilbertCompress,hilbertTrace,Matrix.trace,Matrix.diag]

def hilbertCQDistance (b : HilbertBasis ι ℂ H)
    (W : Fin 2 → Fin 2 → PositiveHilbertMeasure T H b) (σ : PositiveHilbertMeasure T H b) : ℝ≥0∞ :=
  ∑ i, ∑ j, hilbertVariation b (fun s => (W i j).value s-hilbertIdeal σ.value i j s)

theorem hilbertCQDistance_recovery (b : HilbertBasis ι ℂ H) (v : n → H)
    (hv : Orthonormal ℂ v) (i₀ : n)
    (W : Fin 2 → Fin 2 → PositiveHilbertMeasure T H b) (σ : PositiveHilbertMeasure T H b) :
    ENNReal.ofReal (cqBitDistance (fun i j => (W i j).erase v hv i₀) (σ.erase v hv i₀))≤
      hilbertCQDistance b W σ := by
  rw [cqBitDistance_variation]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply variation_le_hilbertVariation
  intro s hs
  rw [← ofReal_norm,TraceMatrix.norm_eq,cqDifferenceMeasure_value _ _ _ _ hs,
    PositiveHilbertMeasure.erase_value _ v hv i₀ hs,
    PositiveHilbertMeasure.erase_value _ v hv i₀ hs,← hilbertErase_ideal]
  exact hilbertErase_positive_difference_econtract b v hv i₀
    ((W i j).positive s hs) (hilbertIdeal_positive b σ i j hs)

end SecretKey

end

end OAI
