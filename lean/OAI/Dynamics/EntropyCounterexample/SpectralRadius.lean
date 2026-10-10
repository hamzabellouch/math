import OAI.Dynamics.EntropyCounterexample.Definitions
import OAI.Dynamics.EntropyCounterexample.FiniteSpectrumBound

namespace OAI

noncomputable section

namespace Problem340

def homologyEigenvalueRadii {X : Type} [TopologicalSpace X]
    (f : X → X) (hf : Continuous f) : Set ℝ :=
  {r : ℝ | ∃ n : ℕ, ∃ a b : ℝ, ∃ u v : RealSingularHomology n X,
    (u ≠ 0 ∨ v ≠ 0) ∧
    realHomologyMap n f hf u = a • u - b • v ∧
    realHomologyMap n f hf v = b • u + a • v ∧
    r = Real.sqrt (a ^ 2 + b ^ 2)}

theorem abs_eigenvalue_mem_homologyEigenvalueRadii
    {X : Type} [TopologicalSpace X] {f : X → X} (hf : Continuous f)
    {n : ℕ} {μ : ℝ} {v : RealSingularHomology n X}
    (hv : v ≠ 0) (heigen : realHomologyMap n f hf v = μ • v) :
    |μ| ∈ homologyEigenvalueRadii f hf := by
  refine ⟨n, μ, 0, v, 0, Or.inl hv, ?_, ?_, ?_⟩
  · simpa using heigen
  · simp
  · simp [Real.sqrt_sq_eq_abs]

theorem eigenvalue_le_totalRealHomologySpectralRadius
    {X : Type} [TopologicalSpace X] {f : X → X} (hf : Continuous f)
    (hbounded : BddAbove (homologyEigenvalueRadii f hf))
    {n : ℕ} {μ : ℝ} {v : RealSingularHomology n X}
    (hv : v ≠ 0) (heigen : realHomologyMap n f hf v = μ • v) :
    |μ| ≤ totalRealHomologySpectralRadius f hf := by
  exact le_csSup hbounded (abs_eigenvalue_mem_homologyEigenvalueRadii hf hv heigen)

theorem bddAbove_homologyEigenvalueRadii_of_finiteDimensional
    {X : Type} [TopologicalSpace X]
    [∀ n, FiniteDimensional ℝ (RealSingularHomology n X)]
    (f : X → X) (hf : Continuous f) (N : ℕ)
    (hvanish : ∀ n, N < n → Subsingleton (RealSingularHomology n X)) :
    BddAbove (homologyEigenvalueRadii f hf) :=
  bddAbove_total_pairedEigenvalue_moduli (fun n => realHomologyMap n f hf) N hvanish

theorem log_two_le_log_totalRealHomologySpectralRadius
    {X : Type} [TopologicalSpace X] {f : X → X} (hf : Continuous f)
    (hbounded : BddAbove (homologyEigenvalueRadii f hf))
    {n : ℕ} {v : RealSingularHomology n X}
    (hv : v ≠ 0) (heigen : realHomologyMap n f hf v = (2 : ℝ) • v) :
    Real.log (2 : ℝ) ≤ Real.log (totalRealHomologySpectralRadius f hf) := by
  have htwo : (2 : ℝ) ≤ totalRealHomologySpectralRadius f hf := by
    simpa using eigenvalue_le_totalRealHomologySpectralRadius hf hbounded hv heigen
  exact Real.log_le_log (by norm_num) htwo

end Problem340

end

end OAI
