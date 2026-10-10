import OAI.Probability.DilutedSpin.FullTreeScore
import OAI.Probability.DilutedSpin.GeneralRootArrayLaw

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {L n : ℕ}

noncomputable def selectedNumerator (sel : I → Bool)
    (E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (i : I) (x : FinitePath Ω L) (y : FinitePath (A i) L) : ℝ :=
  if sel i then E i x y else 0

omit [Fintype Ω] [∀ i, Fintype (A i)] in
lemma selectedNumerator_bound (sel : I → Bool)
    (E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hE : ∀ i x y, |E i x y| ≤ 1) (i : I) (x : FinitePath Ω L) (y : FinitePath (A i) L) :
    |selectedNumerator sel E i x y| ≤ 1 := by
  unfold selectedNumerator
  split <;> simp_all

lemma selectedTreeScore_sum (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ) :
    selectedTreeScore S a T Q m base roots sel fixed D E t u f =
      ∑ q, treeScore S a T Q m base roots (selectedFactor sel fixed D E t u)
        (selectedNumerator sel E) f q := by
  simp only [selectedTreeScore,KernelTower.perturbScore,Finset.mul_sum,treeScore,
    ← FiniteLaw.expect_sum]
  apply FiniteLaw.expect_congr
  intro x
  apply Finset.sum_congr rfl
  intro q _
  cases h : sel (roots q) <;> simp [selectedCoefficient,selectedFactor,selectedNumerator,h]

lemma selectedTreeScore_one (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) :
    selectedTreeScore S a T Q m base roots sel fixed D E t u (fun _ => 1) =
      selectedScore T Q m base roots sel fixed D E t u := by
  simp only [selectedTreeScore,one_mul,selectedScore]
  exact PrescribedTree.pathAt_expect S a _ _

variable [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure I) [IsProbabilityMeasure ν]

/-- Selected score Palm at a fixed physical realization. The whole original
root-label reservoir is retained; only one independent label/mark is inserted. -/
theorem selected_palm (S : PrescribedTree L) (a : S.Leaf)
    (s : ℝ≥0) (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (sel : I → Bool)
    (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (hE : ∀ i x y, |E i x y| ≤ 1)
    (hA : ∀ i x y, 1/2 ≤ selectedFactor sel fixed D E t u i x y) :
    (∫ n : ℕ, ∫ y, selectedTreeScore S a T Q m base (rootArray n y) sel fixed D E t u f
      ∂rootLaw n (fun _ => ν) ∂poissonMeasure s) =
      (s:ℝ) * ∫ n : ℕ, ∫ i, ∫ y,
        insertedTreeScore S a T Q m base (rootArray n y) i
          (selectedFactor sel fixed D E t u) (selectedNumerator sel E) f
        ∂rootLaw n (fun _ => ν) ∂ν ∂poissonMeasure s := by
  have heL (n : ℕ) := integral_rootArray_eq_pi ν n
    (fun roots => selectedTreeScore S a T Q m base roots sel fixed D E t u f)
  have heR (n : ℕ) (i : I) := integral_rootArray_eq_pi ν n
    (fun roots => insertedTreeScore S a T Q m base roots i
      (selectedFactor sel fixed D E t u) (selectedNumerator sel E) f)
  simp_rw [heL,heR,selectedTreeScore_sum]
  exact full_reservoir_palm ν S a s T Q m base _ _ f hf (selectedNumerator_bound sel E hE) hA

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
