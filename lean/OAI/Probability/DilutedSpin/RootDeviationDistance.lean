import OAI.Probability.DilutedSpin.RootOverlapBounds
import OAI.Probability.DilutedSpin.RootPatternComparison

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory PrescribedTree
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable {μ ν : Measure (FullRootState Y X I M)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {d : ℝ} (hd : BoundedDistance μ ν d)
    (S : PrescribedTree L) (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hV : ∀ y i, |V y i| ≤ 1)

include hd hb hV in
lemma root_subsetDeviation_distance (B : Finset S.Leaf) :
    |subsetDeviation μ (rootAlphabet (Ω := Ω) (A := A)) S B
      (rootTower T Q m base old) (rootVector V) -
     subsetDeviation ν (rootAlphabet (Ω := Ω) (A := A)) S B
      (rootTower T Q m base old) (rootVector V)| ≤ 3*d := by
  apply FiniteLaw.mixedDeviation_distance hd
  · intro z w
    exact subsetOverlap_bound S B _ (fun y i => hV _ i) w
  · exact measurable_rootTreeMean S T Q m base old
      (fun x => (∑ i, ∏ a∈B, V (x a) i)/(N:ℝ)) hb
  · intro c
    exact measurable_rootTreeMean S T Q m base old
      (fun x => |(∑ i, ∏ a∈B, V (x a) i)/(N:ℝ)-c|) hb

include hd hb hV in
lemma root_shapeDeviation_distance (hd0 : 0 ≤ d) :
    |shapeDeviation μ (rootAlphabet (Ω := Ω) (A := A)) S
      (rootTower T Q m base old) (rootVector V) -
     shapeDeviation ν (rootAlphabet (Ω := Ω) (A := A)) S
      (rootTower T Q m base old) (rootVector V)| ≤ (2:ℝ)^S.leaves*(3*d) := by
  classical
  unfold shapeDeviation
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _B : Finset S.Leaf, 3*d := by
      apply Finset.sum_le_sum
      intro B _
      by_cases hB : B.Nonempty
      · simp only [ite_eq_left hB]
        exact root_subsetDeviation_distance hd S T Q m base old V hb hV B
      · simp only [ite_eq_right hB,sub_self,abs_zero]
        positivity
    _ = _ := by simp [card_leaf]

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
