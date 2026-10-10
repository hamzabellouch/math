import OAI.Analysis.CircleDomains.Sobolev.PrioritySmooth
import OAI.Analysis.CircleDomains.Sobolev.L2AdditiveMajorant

namespace OAI

/-! The source L2 error of priority interpolation is bounded by the
summable cutoff gradient and the original gradient on the changed set. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem cutoff_gradient_summable_of_local_tail
    {χ : ℕ → ℂ → ℝ} {p : ℂ}
    (hz : ∃ N : ℕ, ∀ᶠ q in 𝓝 p, ∀ n, N ≤ n → χ n q = 0) :
    Summable (fun n => ‖fderiv ℝ (χ n) p‖) := by
  obtain ⟨N, hN⟩ := hz
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro n hn
  have he : χ n =ᶠ[𝓝 p] (fun _ => 0) :=
    hN.mono (fun q hq => hq n (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hn)))
  rw [he.fderiv_eq]
  simp

 theorem priority_source_L2_error
    {B U : Set ℂ} (hB : IsClosed B) (hU : IsOpen U) (hUB : U ⊆ Bᶜ)
    (b : ℕ → ℂ) (hb : ∀ n, b n ∈ B) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (χ : ℕ → ℂ → ℝ) (hχ : ∀ n, ContDiff ℝ ∞ (χ n))
    (hunit : ∀ n z, χ n z ∈ Icc (0 : ℝ) 1)
    (hs : ∀ n, support (χ n) ⊆ ball (b n) (r n))
    (c : ℕ → ℝ) (X : ℂ → ℝ) (hX : ContDiffOn ℝ ∞ X Bᶜ)
    {K : ℝ} (hK : 0 ≤ K) (hc : ∀ n, ‖c n‖ ≤ K) (hXb : ∀ z ∈ U, ‖X z‖ ≤ K)
    (hDX : MemLp (fderiv ℝ X) 2 (volume.restrict U))
    (hA : MemLp (fun z => ∑' n, ‖fderiv ℝ (χ n) z‖) 2 volume) :
    let P := fun z => priorityInfiniteValue (fun n => χ n z) c (X z)
    let S := ⋃ n, support (χ n)
    MemLp (fun z => fderiv ℝ P z-fderiv ℝ X z) 2 (volume.restrict U) ∧
      (eLpNorm (fun z => fderiv ℝ P z-fderiv ℝ X z) 2 (volume.restrict U)).toReal ≤
        2*K*(eLpNorm (fun z => ∑' n, ‖fderiv ℝ (χ n) z‖) 2 (volume.restrict U)).toReal +
          (eLpNorm (S.indicator (fun z => ‖fderiv ℝ X z‖)) 2 (volume.restrict U)).toReal := by
  let P := fun z => priorityInfiniteValue (fun n => χ n z) c (X z)
  let S := ⋃ n, support (χ n)
  have hPs : ContDiffOn ℝ ∞ P U :=
    (priorityInfiniteValue_smooth_off_dust hB b hb r hr χ hχ hs c X hX).mono hUB
  have hXs := hX.mono hUB
  have hD : AEStronglyMeasurable (fun z => fderiv ℝ P z-fderiv ℝ X z) (volume.restrict U) :=
    ((hPs.continuousOn_fderiv_of_isOpen hU (by simp)).sub
      (hXs.continuousOn_fderiv_of_isOpen hU (by simp))).aestronglyMeasurable hU.measurableSet
  have hS : MeasurableSet S :=
    MeasurableSet.iUnion (fun n => ((hχ n).continuous.isOpen_preimage _ isOpen_ne).measurableSet)
  apply l2_norm_le_of_additive_majorant (by positivity) hD (hA.restrict U) (hDX.norm.indicator hS)
  · exact Eventually.of_forall (fun z => tsum_nonneg (fun n => norm_nonneg _))
  · exact Eventually.of_forall (fun z => indicator_nonneg (fun _ _ => norm_nonneg _) z)
  · filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    obtain ⟨V, hV, hzV, N, hN⟩ := concentrated_cutoffs_eventually_zero hB b hb r hr χ hs (hUB hz)
    have htail : ∃ N : ℕ, ∀ᶠ q in 𝓝 z, ∀ n, N ≤ n → χ n q = 0 :=
      ⟨N, Filter.mem_of_superset (hV.mem_nhds hzV) (fun q hq n hn => hN n hn q hq)⟩
    exact priorityInfiniteValue_derivative_error χ c X
      ((hXs.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)) (hXb z hz)
      (fun n => ⟨(hχ n).differentiable (by simp) z, hunit n z⟩) hc
      (cutoff_gradient_summable_of_local_tail htail) htail

end CircleDomainRigidity

end

end OAI
