import OAI.Analysis.Mahler.HolomorphicLogC2
import OAI.Analysis.Mahler.SourceRescaling

namespace OAI

open Set Filter Metric
open scoped Topology
namespace MahlerRescaling
noncomputable section
variable {n N m : ℕ} {U : Set (Mahler.ComplexEuclidean n)}
  {f : Fin N → Mahler.ComplexEuclidean n → ℂ}
  {G : Fin N → MvPolynomial (Fin n) ℂ}

/-- The exact logarithm in the rescaled mass argument. -/
def rescaledLogEnergy (f : Fin N → Mahler.ComplexEuclidean n → ℂ) (m : ℕ)
    (ε : ℝ) (z : Mahler.ComplexEuclidean n) : ℝ :=
  Real.log (∑ j, Complex.normSq (rescale (f j) m ε z))

def leadingLogEnergy (G : Fin N → MvPolynomial (Fin n) ℂ)
    (z : Mahler.ComplexEuclidean n) : ℝ :=
  Real.log (∑ j, Complex.normSq (leadingComponent G j z))

/-- The norm sum is the rescaled tau, with no
normalization factor omitted. This identity also holds at epsilon=0. -/
lemma rescaled_sumNormSq_eq_tau (ε : ℝ) (z : Mahler.ComplexEuclidean n) :
    (∑ j, Complex.normSq (rescale (f j) m ε z)) =
      (ε^(2*m))⁻¹ * Mahler.tau f (ε • z) := by
  simp only [rescale, Complex.real_smul, Complex.normSq_mul, Complex.normSq_ofReal,
    ← pow_two, ← inv_pow, ← pow_mul, Nat.mul_comm m 2, Mahler.tau, Finset.mul_sum]

lemma rescaledLogEnergy_eq_log_tau (ε : ℝ) (z : Mahler.ComplexEuclidean n) :
    rescaledLogEnergy f m ε z = Real.log ((ε^(2*m))⁻¹ * Mahler.tau f (ε • z)) := by
  rw [rescaledLogEnergy, rescaled_sumNormSq_eq_tau]

theorem source_rescaling_log_uniform_C2 (h : Mahler.MassHypotheses n N m U f G) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ z ∈ SymmetricMahler.logCompactAnnulus n,
        c ≤ ∑ j, Complex.normSq (rescale (f j) m ε z)) ∧
    TendstoUniformlyOn (rescaledLogEnergy f m) (leadingLogEnergy G)
      (𝓝[>] 0) (SymmetricMahler.logCompactAnnulus n) ∧
    TendstoUniformlyOn (fun ε => fderiv ℝ (rescaledLogEnergy f m ε))
      (fderiv ℝ (leadingLogEnergy G)) (𝓝[>] 0) (SymmetricMahler.logCompactAnnulus n) ∧
    TendstoUniformlyOn (fun ε => fderiv ℝ (fderiv ℝ (rescaledLogEnergy f m ε)))
      (fderiv ℝ (fderiv ℝ (leadingLogEnergy G)))
      (𝓝[>] 0) (SymmetricMahler.logCompactAnnulus n) := by
  have he : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j,
      DifferentiableOn ℂ (rescale (f j) m ε) (ball 0 4) := by
    apply Filter.eventually_all.mpr
    intro j
    obtain ⟨C, hC, δ, hδ, hb⟩ := source_rescaling_C2_bound h j
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with ε hε hεδ
    exact (hb ε hε hεδ).1
  have hp : ∀ z ∈ SymmetricMahler.logCompactAnnulus n,
      0 < ∑ j, Complex.normSq (leadingComponent G j z) := by
    intro z hz
    obtain ⟨j, hj⟩ := h.leading_nonzero z (SymmetricMahler.logCompactAnnulus_ne_zero hz)
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨j, Finset.mem_univ j, Complex.normSq_pos.mpr hj⟩
  have hk : SymmetricMahler.logCompactAnnulus n ⊆
      closedBall (0 : Mahler.ComplexEuclidean n) 2 := sdiff_subset
  exact SymmetricMahler.uniform_C2_log_sumNormSq_of_holomorphic
    (SymmetricMahler.isCompact_logCompactAnnulus n) isOpen_ball
    (SymmetricMahler.logCompactAnnulus_subset_ball n)
    (fun j => (leadingComponent_differentiable G j).differentiableOn) he hp
    (fun j => ((source_rescaling_uniform_C2 h j).1).mono hk)
    (fun j => ((source_rescaling_uniform_C2 h j).2.1).mono hk)
    (fun j => ((source_rescaling_uniform_C2 h j).2.2).mono hk)

/-- The logarithmic jet limit expressed through the rescaled tau. -/
theorem source_rescaling_log_tau_uniform_C2 (h : Mahler.MassHypotheses n N m U f G) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ z ∈ SymmetricMahler.logCompactAnnulus n,
        c ≤ (ε^(2*m))⁻¹ * Mahler.tau f (ε • z)) ∧
    TendstoUniformlyOn (fun ε z => Real.log ((ε^(2*m))⁻¹ * Mahler.tau f (ε • z)))
      (fun z => Real.log (Mahler.tau (leadingComponent G) z))
      (𝓝[>] 0) (SymmetricMahler.logCompactAnnulus n) ∧
    TendstoUniformlyOn (fun ε => fderiv ℝ (fun z => Real.log ((ε^(2*m))⁻¹ * Mahler.tau f (ε • z))))
      (fderiv ℝ (fun z => Real.log (Mahler.tau (leadingComponent G) z)))
      (𝓝[>] 0) (SymmetricMahler.logCompactAnnulus n) ∧
    TendstoUniformlyOn
      (fun ε => fderiv ℝ (fderiv ℝ (fun z => Real.log ((ε^(2*m))⁻¹ * Mahler.tau f (ε • z)))))
      (fderiv ℝ (fderiv ℝ (fun z => Real.log (Mahler.tau (leadingComponent G) z))))
      (𝓝[>] 0) (SymmetricMahler.logCompactAnnulus n) := by
  have he : rescaledLogEnergy f m =
      fun ε z => Real.log ((ε^(2*m))⁻¹ * Mahler.tau f (ε • z)) :=
    funext (fun ε => funext (rescaledLogEnergy_eq_log_tau ε))
  have hg : leadingLogEnergy G = fun z => Real.log (Mahler.tau (leadingComponent G) z) := rfl
  simpa only [he, hg, rescaled_sumNormSq_eq_tau]
    using source_rescaling_log_uniform_C2 h

end
end MahlerRescaling

end OAI
