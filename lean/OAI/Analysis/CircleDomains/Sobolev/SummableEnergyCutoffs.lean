import OAI.Analysis.CircleDomains.Topology.CenteredSmallCutoffs
import OAI.Analysis.CircleDomains.Sobolev.SphericalGradientEnergyNorm
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

namespace OAI

/-! A prescribed positive summable budget gives actual smooth source
cutoffs with summable L2 differential norms and an almost everywhere
summable pointwise differential majorant. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem smooth_cutoff_gradient_memLp {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    MemLp (fderiv ℝ f) 2 volume :=
  (hf.continuous_fderiv (by simp)).memLp_of_hasCompactSupport (hs.fderiv (𝕜 := ℝ))

 theorem smooth_cutoff_energy_eq_norm_sq {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    (∫ z, ‖fderiv ℝ f z‖^2) = (eLpNorm (fderiv ℝ f) 2 volume).toReal^2 := by
  have hm := smooth_cutoff_gradient_memLp hf hs
  simpa only [eLpNorm_norm _ hm.aestronglyMeasurable] using integral_sq_eq_eLpNorm_toReal_sq hm.norm

 theorem exists_summable_energy_cutoffs
    (c : ℕ → ℂ) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hsum : Summable ε) :
    ∃ χ : ℕ → ℂ → ℝ,
      (∀ n, ContDiff ℝ ∞ (χ n) ∧ HasCompactSupport (χ n) ∧
        tsupport (χ n) ⊆ ball (c n) (r n) ∧ (∀ z, χ n z ∈ Icc (0 : ℝ) 1) ∧
        (∀ᶠ z in 𝓝 (c n), χ n z = 1) ∧ MemLp (fderiv ℝ (χ n)) 2 volume ∧
        (eLpNorm (fderiv ℝ (χ n)) 2 volume).toReal < ε n) ∧
      Summable (fun n => (eLpNorm (fderiv ℝ (χ n)) 2 volume).toReal) ∧
      (∑' n, (eLpNorm (fderiv ℝ (χ n)) 2 volume).toReal) ≤ ∑' n, ε n ∧
      (∀ᵐ z ∂volume, Summable (fun n => ‖fderiv ℝ (χ n) z‖)) := by
  choose χ hχ using fun n => exists_small_energy_cutoff (c n) (hr n) (sq_pos_of_pos (hε n))
  have hdata (n : ℕ) : ContDiff ℝ ∞ (χ n) ∧ HasCompactSupport (χ n) ∧
      tsupport (χ n) ⊆ ball (c n) (r n) ∧ (∀ z, χ n z ∈ Icc (0 : ℝ) 1) ∧
      (∀ᶠ z in 𝓝 (c n), χ n z = 1) ∧ MemLp (fderiv ℝ (χ n)) 2 volume ∧
      (eLpNorm (fderiv ℝ (χ n)) 2 volume).toReal < ε n := by
    obtain ⟨hf, hs, hsup, hu, ho, he⟩ := hχ n
    refine ⟨hf, hs, hsup, hu, ho, smooth_cutoff_gradient_memLp hf hs, ?_⟩
    rw [smooth_cutoff_energy_eq_norm_sq hf hs] at he
    nlinarith [hε n, ENNReal.toReal_nonneg (a := eLpNorm (fderiv ℝ (χ n)) 2 volume)]
  have hbound (n : ℕ) : (eLpNorm (fderiv ℝ (χ n)) 2 volume).toReal ≤ ε n := (hdata n).2.2.2.2.2.2.le
  have hsm : Summable (fun n => (eLpNorm (fderiv ℝ (χ n)) 2 volume).toReal) :=
    Summable.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg) hbound hsum
  refine ⟨χ, hdata, hsm, hsm.tsum_le_tsum hbound hsum, ?_⟩
  have hfin : (∑' n, eLpNorm (fderiv ℝ (χ n)) 2 volume) < (⊤ : ℝ≥0∞) := by
    apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n => ?_)) hsum.tsum_ofReal_lt_top
    rw [← ENNReal.ofReal_toReal (hdata n).2.2.2.2.2.1.ne_top]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  exact summable_norm_of_tsum_eLpNorm_ne_top (p := 2) (μ := volume)
    (f := fun n => fderiv ℝ (χ n)) (by norm_num) hfin.ne

end CircleDomainRigidity

end

end OAI
