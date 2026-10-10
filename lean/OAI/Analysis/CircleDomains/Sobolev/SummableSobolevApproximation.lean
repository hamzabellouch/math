import OAI.Analysis.CircleDomains.Sobolev.UniformSobolevApproximation
import OAI.Analysis.CircleDomains.Probability.SummableErrorExtraction

namespace OAI

/-! Uniform smooth approximation with summable errors in both actual
weak partial derivatives on a compact set. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_summable_sobolev_approximation
    {Ω K : Set EuclideanPlane} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Ω) (hc : Continuous u) :
    ∃ φ : ℕ → EuclideanPlane → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n) ∧ HasCompactSupport (φ n)) ∧
      TendstoUniformlyOn φ u atTop K ∧
      (∀ i : Fin 2, Summable (fun n => (eLpNorm (fun p =>
        fderiv ℝ (φ n) p (EuclideanSpace.single i 1)-hu.weakGrad p i)
        2 (volume.restrict K)).toReal)) := by
  obtain ⟨φ, hφ, hU, hG⟩ := exists_uniform_sobolev_approximation hΩ hK hKΩ hu hc
  let a (i : Fin 2) (n : ℕ) := (eLpNorm (fun p =>
    fderiv ℝ (φ n) p (EuclideanSpace.single i 1)-hu.weakGrad p i)
    2 (volume.restrict K)).toReal
  have ht (i : Fin 2) : Tendsto (a i) atTop (𝓝 0) := by
    simpa only [a, Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp)).comp (hG i)
  obtain ⟨s, hs, hsum⟩ := exists_summable_error_extraction
    (b := fun n => a 0 n+a 1 n) (fun n => add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (by simpa using (ht 0).add (ht 1))
  refine ⟨φ ∘ s, fun n => hφ (s n), ?_, ?_⟩
  · intro U hU'
    exact hs.eventually (hU U hU')
  · intro i
    change Summable (fun n => a i (s n))
    apply Summable.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg) _ hsum
    intro n
    fin_cases i
    · exact le_add_of_nonneg_right ENNReal.toReal_nonneg
    · exact le_add_of_nonneg_left ENNReal.toReal_nonneg

end CircleDomainRigidity

end

end OAI
