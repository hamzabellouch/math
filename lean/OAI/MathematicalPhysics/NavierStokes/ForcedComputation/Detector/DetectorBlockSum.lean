import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusScalarInput

namespace OAI

/-! A detector's countably many bursts form a smooth field: only finitely
many bursts have begun in a neighborhood of any physical time. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set Filter
open scoped ContDiff Topology

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def detectorBlockSum (F : ℕ → ℝ × Plane → E) (y : ℝ × Plane) : E := ∑' n, F n y

omit [NormedSpace ℝ E] in
theorem detectorBlockSum_local_of_time_bound (F : ℕ → ℝ × Plane → E)
    (hbefore : ∀ (n : ℕ) y, y.1 < 2 * ((n : ℝ) + 1) → F n y = 0)
    (y : ℝ × Plane) (N : ℕ) (hN : y.1 + 1 ≤ (N : ℝ)) :
    detectorBlockSum F =ᶠ[𝓝 y] fun z => ∑ n ∈ Finset.range N, F n z := by
  have hn : ∀ᶠ z : ℝ × Plane in 𝓝 y, z.1 < y.1 + 1 :=
    (continuous_fst.tendsto y).eventually (eventually_lt_nhds (by linarith))
  filter_upwards [hn] with z hz
  apply tsum_eq_sum
  intro n hnot
  have hnN : N ≤ n := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hnot)
  have hc : (N : ℝ) ≤ n := by exact_mod_cast hnN
  have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact hbefore n z (by linarith)

omit [NormedSpace ℝ E] in
theorem detectorBlockSum_local (F : ℕ → ℝ × Plane → E)
    (hbefore : ∀ (n : ℕ) y, y.1 < 2 * ((n : ℝ) + 1) → F n y = 0) (y : ℝ × Plane) :
    ∃ N : ℕ, detectorBlockSum F =ᶠ[𝓝 y] fun z => ∑ n ∈ Finset.range N, F n z := by
  let N := ⌈y.1 + 1⌉₊
  have hN : y.1 + 1 ≤ (N : ℝ) := Nat.le_ceil _
  exact ⟨N, detectorBlockSum_local_of_time_bound F hbefore y N hN⟩

omit [NormedSpace ℝ E] in
/-- A coarse rational approximation to physical time gives a finite prefix
valid throughout a neighborhood, hence for every derivative there as well. -/
theorem detectorBlockSum_local_of_approximation (F : ℕ → ℝ × Plane → E)
    (hbefore : ∀ (n : ℕ) y, y.1 < 2 * ((n : ℝ) + 1) → F n y = 0)
    (y : ℝ × Plane) (q : ℚ) (hq : |y.1 - (q : ℝ)| ≤ 1) :
    detectorBlockSum F =ᶠ[𝓝 y]
      fun z => ∑ n ∈ Finset.range ⌈q + 2⌉₊, F n z := by
  apply detectorBlockSum_local_of_time_bound F hbefore y
  have hc : (q : ℝ) + 2 ≤ (⌈q + 2⌉₊ : ℝ) := by
    exact_mod_cast (Nat.le_ceil (q + 2))
  have hy := (abs_le.mp hq).2
  linarith

theorem detectorBlockSum_smooth (F : ℕ → ℝ × Plane → E)
    (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (hbefore : ∀ (n : ℕ) y, y.1 < 2 * ((n : ℝ) + 1) → F n y = 0) :
    ContDiff ℝ ∞ (detectorBlockSum F) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  obtain ⟨N, hN⟩ := detectorBlockSum_local F hbefore y
  have hs : ContDiff ℝ ∞ (fun z => ∑ n ∈ Finset.range N, F n z) := by
    apply ContDiff.sum
    intro n _
    exact hF n
  exact hs.contDiffAt.congr_of_eventuallyEq hN

end
end ForcedComputation.VelocityDetector

end

end OAI
