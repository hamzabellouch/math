import OAI.Analysis.CircleDomains.Sobolev.LocalSobolevSmoothing
import OAI.Analysis.CircleDomains.Sobolev.UniformLocalMollification

namespace OAI

/-! Positive local smoothing of real branches, without imposing a global
unit-interval range on the branches of a circle-valued coordinate. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem exists_local_lift_sobolev_smoothing
    {Ω K : Set EuclideanPlane} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Ω) :
    ∃ (V : Set EuclideanPlane) (φ : ℕ → EuclideanPlane → ℝ),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧
      (∀n, ContDiff ℝ (⊤ : ℕ∞) (φ n) ∧ HasCompactSupport (φ n)) ∧
      (∀ᶠ n in atTop, tsupport (φ n) ⊆ Ω) ∧
      Tendsto (fun n => eLpNorm (fun x => φ n x - u x) 2 (volume.restrict V))
        atTop (𝓝 0) ∧
      (∀i : Fin 2, Tendsto (fun n => eLpNorm (fun x =>
        (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hu.weakGrad x i)
        2 (volume.restrict V)) atTop (𝓝 0)) ∧
      (∀W : Set EuclideanPlane, IsOpen W → K ⊆ W → ∀c : ℝ,
        (∀x ∈ W, u x = c) → ∀ᶠ n in atTop, ∀x ∈ K, φ n x = c) ∧
      (∀ᶠ n in atTop, ∀a b : ℝ, (∀x ∈ Ω, u x ∈ Icc a b) →
        ∀x ∈ K, φ n x ∈ Icc a b) ∧
      (ContinuousOn u Ω → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ x ∈ K, |φ n x - u x| < ε) := by
  obtain ⟨η, V, hη, hsη, _, hsub, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK hΩ hKΩ
  have hVΩ : V ⊆ Ω := by
    intro x hx
    apply hsub
    apply subset_tsupport η
    change η x ≠ 0
    rw [hone x hx]
    exact one_ne_zero
  let w : EuclideanPlane → ℝ := fun x => η x * u x
  obtain ⟨hw⟩ := exists_global_compact_cutoff_witness hΩ hu.memW1p hη hsη hsub
  have hwLp : MemLp w 2 volume := by simpa only [Measure.restrict_univ] using hw.memLp
  have hw_eq : EqOn w u V := fun x hx => by dsimp [w]; rw [hone x hx, one_mul]
  refine ⟨V, planarMollification w, hV, hKV, hVΩ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ⟨planarMollification_smooth (hwLp.locallyIntegrable (by norm_num)) n,
      planarMollification_hasCompactSupport hsη.mul_right n⟩
  · exact planarMollification_support_eventually hsη.mul_right hΩ
      (tsupport_mul_subset_left.trans hsub)
  · have hl := tendsto_eLpNorm_restrict_zero (V := V) (planarMollification_tendsto_L2 hwLp)
    convert hl using 1
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    rw [hw_eq hx]
  · intro i
    have hgi := weakGrad_eq_on_cutoff_plateau hV hVΩ hu hw hone i
    have hl := tendsto_eLpNorm_restrict_zero (V := V)
      (planarMollification_tendsto_gradient_L2 hw i)
    convert hl using 1
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [hgi] with x hx
    rw [hx]
  · intro W hW hKW c hc
    apply planarMollification_eq_on_compact_eventually hK (hV.inter hW)
      (subset_inter hKV hKW)
    intro x hx
    rw [hw_eq hx.1, hc x hx.2]
  · filter_upwards [planarMollifier_samples_eventually hK hV hKV] with n hn a b hab x hx
    apply normed_convolution_mem_Icc volume (DeGiorgi.shrinkingBump n) hwLp.aestronglyMeasurable
    intro y hy
    have hyV := hn x hx hy
    rw [hw_eq hyV]
    exact hab y (hVΩ hyV)

  · intro hc ε hε
    have hwc : ContinuousOn w V := (hη.continuous.continuousOn).mul (hc.mono hVΩ)
    filter_upwards [planarMollification_uniform_on_compact hwLp.aestronglyMeasurable
      hK hV hKV hwc hε] with n hn x hx
    simpa only [hw_eq (hKV hx)] using hn x hx

end CircleDomainRigidity

end

end OAI
