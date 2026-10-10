import OAI.Analysis.FiniteFactor.OrbitSampling.SecondMarginal

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal
noncomputable section

def sourceSamplingRectangle (E G : SourceCoordinate → Set ℝ) :
    Set ((SourceCoordinate → ℝ) × (SourceCoordinate → ℝ)) :=
  {p | ∀ i, p.1 i ∈ E i ∧ p.2 i ∈ G i}

theorem sourceSamplingRectangle_measurable (E G : SourceCoordinate → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    MeasurableSet (sourceSamplingRectangle E G) := by
  simp only [sourceSamplingRectangle,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact ((hE i).preimage ((measurable_pi_apply i).comp measurable_fst)).inter
    ((hG i).preimage ((measurable_pi_apply i).comp measurable_snd))

theorem sourceSamplingProduct_first_indicator (I : Finset SourceCoordinate) (stage : ℕ)
    (E G : SourceCoordinate → Set ℝ)
    (houtside : ∀ i ∉ sourceSamplingPrefix stage,
      Set.Ico (0 : ℝ) 1 ⊆ E i ∧ Set.Ico (0 : ℝ) 1 ⊆ G i)
    (θ x : SourceCoordinate → ℝ) (n : ℤ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1) :
    sourceSamplingProduct stage false (fun i => decide (i ∈ I)) E G n θ x =
      if (x,coordinateRotate θ n x) ∈ sourceSamplingRectangle E G
      then sourceSamplingWeight I stage θ n x else 0 := by
  have hy (i) : coordinateRotate θ n x i ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
  have he : (∀ i ∈ sourceSamplingPrefix stage, x i ∈ E i ∧ coordinateRotate θ n x i ∈ G i) ↔
      (x,coordinateRotate θ n x) ∈ sourceSamplingRectangle E G := by
    constructor
    · intro h i
      by_cases hi : i ∈ sourceSamplingPrefix stage
      · exact h i hi
      · exact ⟨(houtside i hi).1 (hx i),(houtside i hi).2 (hy i)⟩
    · intro h i _
      exact h i
  unfold sourceSamplingProduct samplingOrientedWeight samplingTestedFirstWeight
  simp only [Bool.false_eq_true,ite_false,← coordinateRotate_phase]
  simp only [Finset.prod_ite_zero,he]
  rfl

/-- Inverse rotation exchanges the two actual tested product orientations. -/
theorem sourceSamplingProduct_second_inverse (I : Finset SourceCoordinate) (stage : ℕ)
    (E G : SourceCoordinate → Set ℝ) (θ y : SourceCoordinate → ℝ) (n : ℤ)
    (hy : ∀ i, y i ∈ Set.Ico (0 : ℝ) 1) :
    sourceSamplingProduct stage false (fun i => decide (i ∈ I)) E G n θ
      (coordinateRotate θ (-n) y) =
    sourceSamplingProduct stage true (fun i => decide (i ∈ I)) E G n θ y := by
  have hinv : coordinateRotate θ n (coordinateRotate θ (-n) y) = y := by
    simpa only [neg_neg] using coordinateRotate_neg_cube θ y (-n) hy
  apply Finset.prod_congr rfl
  intro i _
  have hi := congrFun hinv i
  rw [coordinateRotate_phase] at hi
  simp only [samplingOrientedWeight,Bool.false_eq_true,ite_false,ite_true,samplingTestedFirstWeight,hi]
  rw [coordinateRotate_neg_phase]

/-- The restricted orbit-pair summand is exactly the pushforward of its
first tested product, with no assumed marginal law. -/
theorem sourceSamplingSummand_restrict_rectangle (I : Finset SourceCoordinate) (stage : ℕ)
    (E G : SourceCoordinate → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (houtside : ∀ i ∉ sourceSamplingPrefix stage,
      Set.Ico (0 : ℝ) 1 ⊆ E i ∧ Set.Ico (0 : ℝ) 1 ⊆ G i)
    (θ : SourceCoordinate → ℝ) (n : ℤ) :
    (sourceSamplingSummand I stage θ n).restrict (sourceSamplingRectangle E G) =
      (sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal
        (sourceSamplingProduct stage false (fun i => decide (i ∈ I)) E G n θ x))).map
          (fun x => (x,coordinateRotate θ n x)) := by
  have hp : Measurable (fun x : SourceCoordinate → ℝ => (x,coordinateRotate θ n x)) :=
    measurable_id.prodMk (coordinateRotate_preserving θ n).measurable
  have hR := sourceSamplingRectangle_measurable E G hE hG
  unfold sourceSamplingSummand sourceSamplingWeightedMeasure
  rw [Measure.restrict_map hp hR,restrict_withDensity (hp hR),← withDensity_indicator (hp hR)]
  congr 1
  apply withDensity_congr_ae
  filter_upwards [sourceSamplingHaar_cube] with x hx
  rw [sourceSamplingProduct_first_indicator I stage E G houtside θ x n hx]
  change (if (x,coordinateRotate θ n x) ∈ sourceSamplingRectangle E G
    then ENNReal.ofReal (sourceSamplingWeight I stage θ n x) else 0) = _
  split_ifs <;> simp

end
end FiniteFactor

end OAI
