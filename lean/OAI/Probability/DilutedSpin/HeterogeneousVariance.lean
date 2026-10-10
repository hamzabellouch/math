import OAI.Probability.DilutedSpin.Core

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] {L : ℕ}

/-- The random-count convex correction has its own addition/deletion cost.
Replacement of an existing root point is unaffected. -/
theorem correctedRoot_family_variance
    (μ : Measure I) [IsProbabilityMeasure μ] (r : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ i x y, |Real.log (factor i x y)| ≤ C) (c : ℝ) :
    variance (fun z : Sigma (RootPath I) =>
      root T Q m base (rootArray z.1 z.2) factor+c*z.1)
      (familyLaw (poissonMeasure r) (fun n => rootLaw n (fun _ => μ))) ≤
        (2*C^2+(C+|c|)^2)*(r : ℝ) := by
  let F := fun n (x : RootPath I n) => root T Q m base (rootArray n x) factor+c*n
  have hF (n : ℕ) : Measurable (F n) :=
    measurable_of_countable _
  have hbound (n : ℕ) (x : RootPath I n) : |F n x| ≤ |KernelTower.backwardLog L T m base|+(C+|c|)*n := by
    dsimp only [F]
    have h := abs_root_le T Q m hm base (rootArray n x) factor hf
    calc
      _ ≤ |root T Q m base (rootArray n x) factor|+|c*(n:ℝ)| := abs_add_le _ _
      _ ≤ |KernelTower.backwardLog L T m base|+C*n+|c| * n := by rw [abs_mul,abs_of_nonneg (show (0:ℝ) ≤ n from Nat.cast_nonneg n)]; linarith
      _ = |KernelTower.backwardLog L T m base|+(C+|c|)*n := by ring
  have hrep (n : ℕ) (i : Fin n) (x : RootPath I n) (y : I) :
      |F n x-F n (replaceRoot n x i y)| ≤ 2*C := by
    dsimp only [F]
    rw [add_sub_add_right_eq_sub,rootArray_replace,abs_sub_comm]
    exact root_update_bound T Q m hm base (rootArray n x) i y factor hf
  have hadd (n : ℕ) (x : I) (y : RootPath I n) : |F (n+1) (x,y)-F n y| ≤ C+|c| := by
    change |root T Q m base (Fin.cons x (rootArray n y)) factor+c*(n+1:ℕ)-
      (root T Q m base (rootArray n y) factor+c*n)| ≤ _
    rw [Nat.cast_add,Nat.cast_one]
    have h := root_cons_bound T Q m hm base (rootArray n y) x factor (hf x)
    calc
      _ = |root T Q m base (Fin.cons x (rootArray n y)) factor-
        root T Q m base (rootArray n y) factor+c| := by congr 1; ring
      _ ≤ |root T Q m base (Fin.cons x (rootArray n y)) factor-
        root T Q m base (rootArray n y) factor|+|c| := abs_add_le _ _
      _ ≤ C+|c| := add_le_add h le_rfl

  have h := familyPoisson_variance_le μ r hF hbound (add_nonneg hC (abs_nonneg c)) hrep hadd
  convert h using 1; ring

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
