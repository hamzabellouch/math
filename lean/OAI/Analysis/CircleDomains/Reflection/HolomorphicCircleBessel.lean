import OAI.Analysis.CircleDomains.Reflection.HolomorphicCircleCoefficients

namespace OAI

/-! The finite square-sum bound for the actual holomorphic Taylor
coefficients, with the unnormalized Euclidean angular integral. -/
open Set Filter Function Metric Real MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma holomorphic_circle_memLp {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (sphere 0 r)) :
    MemLp (fun θ => f (circleMap 0 r θ)) 2 (volume.restrict (Ioc 0 (2*Real.pi))) := by
  have hc : Continuous (fun θ => f (circleMap 0 r θ)) := by
    apply hf.comp_continuous (continuous_circleMap 0 r)
    intro θ
    simpa only [abs_of_pos hr] using circleMap_mem_sphere' (0 : ℂ) r θ
  obtain ⟨C, hC⟩ := (isCompact_Icc.image hc).isBounded.exists_norm_le
  apply MemLp.of_bound hc.aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  exact hC _ (mem_image_of_mem _ ⟨hθ.1.le, hθ.2⟩)

lemma holomorphic_circle_bessel {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (closedBall 0 r)) (S : Finset ℕ) :
    ∑ n ∈ S, ‖diskTaylorCoefficient f n‖^2 * r^(2*n) ≤
      circleAverage (fun z => ‖f z‖^2) 0 r := by
  have hc : ContinuousOn f (sphere 0 r) := hf.continuousOn.mono sphere_subset_closedBall
  have hs := hasSum_sq_fourierCoeffOn (show (0 : ℝ) < 2*Real.pi by positivity)
    (holomorphic_circle_memLp hr hc)
  have hle := hs.summable.sum_le_tsum (s := S.image (fun n : ℕ => (n : ℤ)))
    (fun n _ => sq_nonneg ‖fourierCoeffOn (show (0 : ℝ) < 2*Real.pi by positivity)
      (fun θ => f (circleMap 0 r θ)) n‖)
  rw [hs.tsum_eq, Finset.sum_image (by intro a _ b _ hab; exact Int.ofNat_inj.mp hab)] at hle
  have he (n : ℕ) :
      ‖fourierCoeffOn (show (0 : ℝ) < 2*Real.pi by positivity)
        (fun θ => f (circleMap 0 r θ)) (n : ℤ)‖^2 =
        ‖diskTaylorCoefficient f n‖^2*r^(2*n) := by
    rw [holomorphic_circle_fourierCoefficient hr hf n, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    ring
  simp_rw [he] at hle
  simpa only [sub_zero, smul_eq_mul, circleAverage] using hle

end CircleDomainRigidity

end

end OAI
