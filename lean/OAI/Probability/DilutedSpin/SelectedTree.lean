import OAI.Probability.DilutedSpin.GlobalSelectedError
import OAI.Probability.DilutedSpin.TreeMeasurable

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

noncomputable def selectedTreeMean (S : PrescribedTree L)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) {n : ℕ} (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ) : ℝ :=
  (S.sampleLaw (KernelTower.tilt L (tower roots L T Q) m
    (logWeight base roots (selectedFactor sel fixed D E t u)))).expect
    (fun x => f (fun b => physical roots L (S.pathAt b x)))

noncomputable def selectedTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) {n : ℕ} (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ) : ℝ :=
  (S.sampleLaw (KernelTower.tilt L (tower roots L T Q) m
    (logWeight base roots (selectedFactor sel fixed D E t u)))).expect
    (fun x => f (fun b => physical roots L (S.pathAt b x)) *
      KernelTower.perturbScore (selectedCoefficient roots sel D)
        (selectedCoefficient roots sel E) t u (S.pathAt a x))

variable (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)

noncomputable def fullSelectedTreeMean (z : FullRootState Y X I M) : ℝ :=
  packRoot (fun h k x n y => selectedTreeMean S T Q m (base h k x) (rootArray n y) sel fixed D E t u f) z

noncomputable def fullSelectedTreeScore (z : FullRootState Y X I M) : ℝ :=
  packRoot (fun h k x n y => selectedTreeScore S a T Q m (base h k x) (rootArray n y) sel fixed D E t u f) z

lemma measurable_fullSelectedTreeMean
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fullSelectedTreeMean S T Q m base sel fixed D E t u f) := by
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only [selectedTreeMean]
  refine PrescribedTree.measurable_tilt_sample_expect S (tower (rootArray n y) L T Q) m ?_ ?_
  · intro w
    exact (hb k _).add measurable_const
  · exact fun _ => measurable_const

lemma measurable_fullSelectedTreeScore
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fullSelectedTreeScore S a T Q m base sel fixed D E t u f) := by
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only [selectedTreeScore]
  refine PrescribedTree.measurable_tilt_sample_expect S (tower (rootArray n y) L T Q) m ?_ ?_
  · intro w
    exact (hb k _).add measurable_const
  · exact fun _ => measurable_const

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
lemma fullSelectedTreeMean_bound {B : ℝ} (hf : ∀ x, |f x| ≤ B) (z : FullRootState Y X I M) :
    |fullSelectedTreeMean S T Q m base sel fixed D E t u f z| ≤ B :=
  FiniteLaw.abs_expect_le _ (fun _ => hf _)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
lemma fullSelectedTreeScore_bound {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (z : FullRootState Y X I M) :
    |fullSelectedTreeScore S a T Q m base sel fixed D E t u f z| ≤ 2*B*(z.2.2.1:ℝ) := by
  apply FiniteLaw.abs_expect_le
  intro x
  rw [abs_mul]
  have hscore := KernelTower.perturbScore_bound _ _
    (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht hu (S.pathAt a x)
  have hb := mul_le_mul (hf (fun b => physical (rootArray z.2.2.1 z.2.2.2) L (S.pathAt b x))) hscore (abs_nonneg _) hB
  exact hb.trans_eq (by ring)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
/-- Exact old-tree/one-path estimate at every disorder realization, with the
identical selected tower used in the globally centered score error. -/
lemma fullSelectedTree_centered_bound {B center : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (z : FullRootState Y X I M) :
    |fullSelectedTreeScore S a T Q m base sel fixed D E t u f z -
      fullSelectedTreeMean S T Q m base sel fixed D E t u f z * center| ≤
      B * fullSelectedDeviation T Q m base sel fixed D E t z u center := by
  dsimp only [fullSelectedDeviation]
  rw [selected_perturbLog_eq]
  exact PrescribedTree.anchor_centered_bound S a _ _ _ hB (fun x => hf _)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
