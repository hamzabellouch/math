import OAI.Probability.DilutedSpin.RootOverlapVariance

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PrescribedTree
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {B : I → Type} [∀ i, Fintype (B i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {n r M N : ℕ}

variable (A : PrescribedTree n)
    (T : KernelTower Ω (n+1+r)) (Q : (i : I) → Fin (n+1+r) → FiniteLaw (B i))
    (m : Fin (n+1+r) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (n+1+r) → ℝ)
    (old : (i : I) → FinitePath Ω (n+1+r) → FinitePath (B i) (n+1+r) → ℝ)
    (V : FinitePath Ω (n+1+r) → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    (hV : ∀ y i, |V y i| ≤ 1)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma root_unarySquareMean_eq (z : FullRootState Y X I M) :
    unarySquareMean A r (rootTower T Q m base old z) (rootVector V z) =
      rootTreeMean (stem (unary A) r) T Q m base old
        (fun x => (spatialProduct (fun _ : (stem (unary A) r).Leaf => V) x)^2) z := by
  unfold unarySquareMean rootTreeMean packRoot
  apply FiniteLaw.expect_congr
  intro w
  rw [treeOverlap_eq_spatialProduct]
  rfl

include hb hV in
lemma integrable_rootUnarySquareMean : Integrable (fun z : FullRootState Y X I M =>
    unarySquareMean A r (rootTower T Q m base old z) (rootVector V z)) μ := by
  simp_rw [root_unarySquareMean_eq]
  apply integrable_rootTreeMean T Q m base old hb _ _ μ (B := 1)
  intro x
  rw [abs_sq]
  exact (sq_le_one_iff_abs_le_one _).mpr (spatialProduct_bound _ (fun _ => hV) x)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma root_forkPairMean_eq (z : FullRootState Y X I M) :
    forkPairMean A r (rootTower T Q m base old z) (rootVector V z) =
      rootTreeMean (stem (doubled A) r) T Q m base old
        (fun x => spatialProduct (fun _ : A.Leaf => V)
          (fun a => x (stemLeaf (doubled A) r ⟨0,a⟩)) *
        spatialProduct (fun _ : A.Leaf => V)
          (fun a => x (stemLeaf (doubled A) r ⟨1,a⟩))) z := by
  unfold forkPairMean rootTreeMean packRoot
  apply FiniteLaw.expect_congr
  intro w
  simp only [forkOverlap_paths]
  rfl

include hb hV in
lemma integrable_rootForkPairMean : Integrable (fun z : FullRootState Y X I M =>
    forkPairMean A r (rootTower T Q m base old z) (rootVector V z)) μ := by
  simp_rw [root_forkPairMean_eq]
  apply integrable_rootTreeMean T Q m base old hb _ _ μ (B := 1)
  intro x
  rw [abs_mul]
  exact (mul_le_mul (spatialProduct_bound _ (fun _ => hV) _)
    (spatialProduct_bound _ (fun _ => hV) _) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)

include hb hV in
lemma integrable_rootSqrtShapeEnergy : Integrable (fun z : FullRootState Y X I M =>
    Real.sqrt (shapeEnergyAt A r (rootTower T Q m base old z) (rootVector V z))) μ := by
  apply Integrable.of_bound (measurable_rootShapeEnergy A r T Q m base old V hb).sqrt.aestronglyMeasurable 2
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (Real.sqrt_le_sqrt (shapeEnergyAt_le_four A r _ _ (fun y i => hV _ i))).trans_eq (by norm_num)

include hb hV in
 
theorem root_overlapVariance_le_marker [IsProbabilityMeasure μ] :
    overlapVariance μ (rootAlphabet (Ω := Ω) (A := B)) (stem (unary A) r)
      (rootTower T Q m base old) (rootVector V) ≤
      Real.sqrt (∫ z, shapeEnergyAt A r (rootTower T Q m base old z) (rootVector V z) ∂μ) +
      |markerDefect μ (rootAlphabet (Ω := Ω) (A := B)) A r
        (rootTower T Q m base old) (rootVector V)| := by
  exact overlapVariance_le_marker μ _ A r _ _
    (integrable_rootUnarySquareMean A T Q m base old V hb μ hV)
    (integrable_rootForkPairMean A T Q m base old V hb μ hV)
    (integrable_rootShapeEnergy A r T Q m base old V hb μ hV)
    (integrable_rootSqrtShapeEnergy A T Q m base old V hb μ hV)

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
