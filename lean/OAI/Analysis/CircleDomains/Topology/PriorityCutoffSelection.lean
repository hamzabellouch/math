import OAI.Analysis.CircleDomains.Sobolev.CountableEnergyNeighborhoods
import OAI.Analysis.CircleDomains.Sobolev.L2SummableMajorant

namespace OAI

/-! Simultaneous source selection: shrinking supports have small total
weighted mass, while their smooth cutoff gradients have a prescribed
summable budget. Overlap of the supports is allowed. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_priority_cutoffs
    {E : Set ℂ} {g : ℂ → ℝ} (hg : MemLp g 2 (volume.restrict E))
    (c : ℕ → ℂ) (O : ℕ → Set ℂ) (hO : ∀ n, O n ∈ 𝓝 (c n))
    {δ : ℝ≥0∞} (hδ : 0 < δ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hsum : Summable ε) :
    ∃ (r : ℕ → ℝ) (χ : ℕ → ℂ → ℝ),
      (∀ n, 0 < r n) ∧ Tendsto r atTop (𝓝 0) ∧
      (∀ n, ball (c n) (r n) ⊆ O n) ∧
      (∫⁻ z in ⋃ n, ball (c n) (r n), ENNReal.ofReal (g z^2) ∂volume.restrict E) < δ ∧
      (∀ n, ContDiff ℝ (↑(⊤ : ℕ∞)) (χ n) ∧ HasCompactSupport (χ n) ∧
        tsupport (χ n) ⊆ ball (c n) (r n) ∧ (∀ z, χ n z ∈ Icc (0 : ℝ) 1) ∧
        (∀ᶠ z in 𝓝 (c n), χ n z = 1)) ∧
      MemLp (fun z => ∑' n, ‖fderiv ℝ (χ n) z‖) 2 volume ∧
      (eLpNorm (fun z => ∑' n, ‖fderiv ℝ (χ n) z‖) 2 volume).toReal ≤ ∑' n, ε n := by
  let μ := (volume.restrict E).withDensity (fun z => ENNReal.ofReal (g z^2))
  have hfin : (∫⁻ z, ENNReal.ofReal (g z^2) ∂volume.restrict E) < ∞ := by
    simpa only [hasFiniteIntegral_iff_enorm, Real.enorm_eq_ofReal_abs, abs_sq] using
      hg.integrable_sq.hasFiniteIntegral
  let : IsFiniteMeasure μ := isFiniteMeasure_withDensity hfin.ne
  obtain ⟨r, hr, hrt, hsub, hmass⟩ := exists_shrinking_energy_balls μ c O hO hδ
  obtain ⟨χ, hχ, hnorm, hnormsum, _⟩ := exists_summable_energy_cutoffs c r hr ε hε hsum
  have hM (n : ℕ) := (hχ n).2.2.2.2.2.1
  have hnorm' : Summable (fun n => (eLpNorm (fun z => ‖fderiv ℝ (χ n) z‖) 2 volume).toReal) := by
    simpa only [eLpNorm_norm _ (hM _).aestronglyMeasurable] using hnorm
  obtain ⟨hmajorant, hmajorantNorm⟩ := l2_tsum_of_summable_norms
    (fun n z => ‖fderiv ℝ (χ n) z‖) (fun n => (hM n).norm) hnorm'
  refine ⟨r, χ, hr, hrt, hsub, ?_, ?_, hmajorant, ?_⟩
  · dsimp only [μ] at hmass
    rwa [withDensity_apply _ (isOpen_iUnion (fun _ => isOpen_ball)).measurableSet] at hmass
  · intro n
    exact ⟨(hχ n).1, (hχ n).2.1, (hχ n).2.2.1, (hχ n).2.2.2.1, (hχ n).2.2.2.2.1⟩
  · apply hmajorantNorm.trans
    simpa only [eLpNorm_norm _ (hM _).aestronglyMeasurable] using hnormsum

end CircleDomainRigidity

end

end OAI
