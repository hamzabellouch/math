import OAI.Analysis.CircleDomains.Sobolev.LocalSobolevSmoothing
import OAI.Analysis.CircleDomains.Sobolev.UniformLocalMollification

namespace OAI

/-! Simultaneous uniform and gradient approximation on a compact planar
set. The approximants are the actual positive convolutions of a cutoff. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_uniform_sobolev_approximation
    {Ω K : Set EuclideanPlane} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Ω) (hc : Continuous u) :
    ∃ φ : ℕ → EuclideanPlane → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n) ∧ HasCompactSupport (φ n)) ∧
      TendstoUniformlyOn φ u atTop K ∧
      (∀ i : Fin 2, Tendsto (fun n => eLpNorm (fun p =>
        fderiv ℝ (φ n) p (EuclideanSpace.single i 1)-hu.weakGrad p i)
        2 (volume.restrict K)) atTop (𝓝 0)) := by
  obtain ⟨η, V, hη, hsη, _, hsub, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK hΩ hKΩ
  have hVΩ : V ⊆ Ω := by
    intro p hp
    apply hsub
    apply subset_tsupport η
    change η p ≠ 0
    rw [hone p hp]
    exact one_ne_zero
  let w : EuclideanPlane → ℝ := fun p => η p*u p
  obtain ⟨hw⟩ := exists_global_compact_cutoff_witness hΩ hu.memW1p hη hsη hsub
  have hwL : MemLp w 2 volume := by simpa only [Measure.restrict_univ] using hw.memLp
  have heq : EqOn w u V := fun p hp => by dsimp only [w]; rw [hone p hp, one_mul]
  refine ⟨planarMollification w, fun n =>
    ⟨planarMollification_smooth (hwL.locallyIntegrable (by norm_num)) n,
      planarMollification_hasCompactSupport hsη.mul_right n⟩, ?_, ?_⟩
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have ht := planarMollification_uniform_on_compact hwL.aestronglyMeasurable hK
      hV hKV (hη.continuous.mul hc).continuousOn hε
    filter_upwards [ht] with n hn p hp
    rw [Real.dist_eq, abs_sub_comm, ← heq (hKV hp)]
    exact hn p hp
  · intro i
    have hg := weakGrad_eq_on_cutoff_plateau hV hVΩ hu hw hone i
    have hl := tendsto_eLpNorm_restrict_zero (V := K)
      (planarMollification_tendsto_gradient_L2 hw i)
    convert hl using 1
    funext n
    apply eLpNorm_congr_ae
    have hgK := hg.filter_mono
      (ae_mono (Measure.restrict_mono hKV le_rfl))
    filter_upwards [hgK] with p hp
    rw [hp]

end CircleDomainRigidity

end

end OAI
