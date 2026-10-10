import OAI.Probability.DilutedSpin.RegularDepth

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

/-- The concentration estimate under one genuine product probability measure,
with independent physical fields and both Poisson reservoirs. -/
theorem variance_actual_root
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (hbmeas : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    {B C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ h k x y, |base h k x y| ≤ B+C*k)
    (hf : ∀ i x y, |Real.log (factor i x y)| ≤ D)
    (hrep : ∀ h k (j : Fin k) x z y,
      |base h k x y-base h k (replaceRoot k x j z) y| ≤ 2*C)
    (hadd : ∀ h k z x y, |base h (k+1) (z,x) y-base h k x y| ≤ C)
    (E : Fin M → ℝ)
    (hfield : ∀ j h z k x y, |base h k x y-base (replaceRoot M h j z) k x y| ≤ E j)
    (c : ℝ) :
    variance (packRoot (fun h k x n y => root T Q m (base h k x) (rootArray n y) factor+c*n))
      (fullRootLaw ξ μ ν r s) ≤
      3*C^2*(r : ℝ)+3*(D+|c|)^2*(s : ℝ)+∑ j, (E j)^2/2 := by
  have hF (k n : ℕ) : Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n =>
      root T Q m (base z.1.1 k z.1.2) (rootArray n z.2) factor+c*n) :=
    (measurable_root_base T Q m (fun z : RootPath Y M × RootPath X k => base z.1 k z.2) (hbmeas k) factor n).add measurable_const
  have hB (h : RootPath Y M) (k : ℕ) (x : RootPath X k) (n : ℕ) (y : RootPath I n) :
      |root T Q m (base h k x) (rootArray n y) factor+c*n| ≤ B+C*k+(D+|c|)*n := by
    have hh := root_uniform_bound T Q m hm (base h k x) (rootArray n y) factor (hb h k x) hf
    calc
      _ ≤ |root T Q m (base h k x) (rootArray n y) factor|+|c*(n:ℝ)| := abs_add_le _ _
      _ ≤ B+C*k+D*n+|c| *n := by
        rw [abs_mul,abs_of_nonneg (show (0:ℝ) ≤ n from Nat.cast_nonneg n)]
        exact add_le_add hh le_rfl
      _ = _ := by ring
  rw [fullRoot_variance_eq ξ μ ν r s hF hC (add_nonneg hD (abs_nonneg c)) hB]
  exact full_root_variance μ ν ξ r s T Q m hm base hbmeas factor hC hD hb hf hrep hadd E hfield c

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
