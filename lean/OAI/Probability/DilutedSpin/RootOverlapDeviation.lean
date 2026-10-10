import OAI.Probability.DilutedSpin.MixedDeviation
import OAI.Probability.DilutedSpin.QSubtreePotential
import OAI.Probability.DilutedSpin.RootOverlapBounds

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
variable {Z : Type} [MeasurableSpace Z] {n N : ℕ}

noncomputable def overlapDeviation (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (S : PrescribedTree n) (K : (z : Z) → KernelTower (Ω z) n)
    (V : (z : Z) → FinitePath (Ω z) n → Fin N → ℝ) : ℝ :=
  FiniteLaw.mixedDeviation μ (fun z => Sample (Ω z) S)
    (fun z => S.sampleLaw (K z)) (fun z => treeOverlap S (V z))

noncomputable def subsetDeviation (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (S : PrescribedTree n) (A : Finset S.Leaf) (K : (z : Z) → KernelTower (Ω z) n)
    (V : (z : Z) → FinitePath (Ω z) n → Fin N → ℝ) : ℝ :=
  FiniteLaw.mixedDeviation μ (fun z => Sample (Ω z) S)
    (fun z => S.sampleLaw (K z)) (fun z => subsetOverlap S A (V z))

lemma SplitMap.subsetDeviation_eq (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    {U T : PrescribedTree n} (f : SplitMap U T)
    (A : Finset T.Leaf) (hA : ∀ b, (∃ a, f.leaf a=b) ↔ b∈A)
    (K : (z : Z) → KernelTower (Ω z) n)
    (V : (z : Z) → FinitePath (Ω z) n → Fin N → ℝ) :
    subsetDeviation μ Ω T A K V=overlapDeviation μ Ω U K V := by
  unfold subsetDeviation overlapDeviation FiniteLaw.mixedDeviation
  have hm (z : Z) := f.expect_subsetOverlap A hA (K z) (V z) id
  simp only [id_eq] at hm
  simp_rw [hm]
  apply integral_congr_ae
  exact ae_of_all μ (fun z => f.expect_subsetOverlap A hA (K z) (V z)
    (fun x => |x-(∫ y, (U.sampleLaw (K y)).expect (treeOverlap U (V y)) ∂μ)|))

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PrescribedTree
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {B : I → Type} [∀ i, Fintype (B i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

variable (S : PrescribedTree L)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (B i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (B i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]
    (hV : ∀ y i, |V y i| ≤ 1)

include hb hV in
lemma integrable_rootOverlapCenteredAbs (c : ℝ) : Integrable (fun z : FullRootState Y X I M =>
    (S.sampleLaw (rootTower T Q m base old z)).expect
      (fun w => |treeOverlap S (rootVector V z) w-c|)) μ := by
  have he (z : FullRootState Y X I M) :
      (S.sampleLaw (rootTower T Q m base old z)).expect
        (fun w => |treeOverlap S (rootVector V z) w-c|)=
      rootTreeMean S T Q m base old (fun x => |spatialProduct (fun _ : S.Leaf => V) x-c|) z := by
    unfold rootTreeMean packRoot
    apply FiniteLaw.expect_congr
    intro w
    rw [treeOverlap_eq_spatialProduct]
    rfl
  simp_rw [he]
  apply integrable_rootTreeMean T Q m base old hb _ _ μ (B := 1+|c|)
  intro x
  rw [abs_abs]
  exact (abs_sub _ _).trans (add_le_add (spatialProduct_bound _ (fun _ => hV) x) le_rfl)

include hb hV in
lemma root_overlapDeviation_le_variance {t : ℝ} (ht : 0<t) :
    overlapDeviation μ (rootAlphabet (Ω := Ω) (A := B)) S (rootTower T Q m base old) (rootVector V) ≤
      overlapVariance μ (rootAlphabet (Ω := Ω) (A := B)) S (rootTower T Q m base old) (rootVector V)/(2*t)+t/2 := by
  apply FiniteLaw.mixedDeviation_le_variance
  · simpa using integrable_rootOverlapMoment S T Q m base old V hb μ hV 1
  · exact integrable_rootOverlapMoment S T Q m base old V hb μ hV 2
  · exact integrable_rootOverlapCenteredAbs S T Q m base old V hb μ hV _
  · exact ht

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
