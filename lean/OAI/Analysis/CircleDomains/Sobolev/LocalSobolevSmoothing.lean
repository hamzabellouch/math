import OAI.Analysis.CircleDomains.Sobolev.CompactSobolevCutoff
import OAI.Analysis.CircleDomains.Sobolev.CompactMollifierSampling

namespace OAI

/-! Local positive smoothing with errors relative to the original weak
gradient. Compact cutoffs are removed on a neighborhood of the core. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem weakPartial_congrOn {V : Set EuclideanPlane} (hV : IsOpen V)
    {f g G : EuclideanPlane → ℝ} {i : Fin 2}
    (hG : DeGiorgi.HasWeakPartialDeriv i G f V) (hfg : EqOn f g V) :
    DeGiorgi.HasWeakPartialDeriv i G g V := by
  intro φ hφ hsφ hsubφ
  calc
    _ = ∫x in V, f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) :=
      setIntegral_congr_fun hV.measurableSet (fun x hx => by rw [hfg hx])
    _ = _ := hG φ hφ hsφ hsubφ

theorem weakGrad_eq_on_cutoff_plateau
    {Ω V : Set EuclideanPlane} (hV : IsOpen V) (hVΩ : V ⊆ Ω)
    {u η : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Ω)
    (hw : DeGiorgi.MemW1pWitness 2 (fun x => η x * u x) univ)
    (hone : ∀x ∈ V, η x = 1) (i : Fin 2) :
    (fun x => hw.weakGrad x i) =ᵐ[volume.restrict V] fun x => hu.weakGrad x i := by
  let hwV := hw.restrict hV (subset_univ V)
  let huV := hu.restrict hV hVΩ
  have hG := weakPartial_congrOn hV (hwV.isWeakGrad i)
    (fun x hx => by rw [hone x hx, one_mul])
  simpa only [hwV, huV, DeGiorgi.MemW1pWitness.restrict] using
    hG.ae_eq hV (huV.isWeakGrad i)
    ((hwV.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
    ((huV.weakGrad_component_memLp i).locallyIntegrable (by norm_num))

theorem tendsto_eLpNorm_restrict_zero
    {f : ℕ → EuclideanPlane → ℝ} {V : Set EuclideanPlane}
    (hf : Tendsto (fun n => eLpNorm (f n) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 (volume.restrict V)) atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hf
    (fun _ => bot_le) (fun n => eLpNorm_mono_measure (f n) Measure.restrict_le_self)

theorem exists_local_positive_sobolev_smoothing
    {Ω K : Set EuclideanPlane} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Ω)
    (hunit : ∀x ∈ Ω, u x ∈ Icc 0 1) :
    ∃ (V : Set EuclideanPlane) (φ : ℕ → EuclideanPlane → ℝ),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧
      (∀n, ContDiff ℝ (⊤ : ℕ∞) (φ n) ∧ HasCompactSupport (φ n) ∧
        ∀x, φ n x ∈ Icc 0 1) ∧
      (∀ᶠ n in atTop, tsupport (φ n) ⊆ Ω) ∧
      Tendsto (fun n => eLpNorm (fun x => φ n x - u x) 2 (volume.restrict V))
        atTop (𝓝 0) ∧
      (∀i : Fin 2, Tendsto (fun n => eLpNorm (fun x =>
        (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hu.weakGrad x i)
        2 (volume.restrict V)) atTop (𝓝 0)) ∧
      (∀W : Set EuclideanPlane, IsOpen W → K ⊆ W → ∀c : ℝ,
        (∀x ∈ W, u x = c) → ∀ᶠ n in atTop, ∀x ∈ K, φ n x = c) ∧
      (∀ᶠ n in atTop, ∀a b : ℝ, (∀x ∈ Ω, u x ∈ Icc a b) →
        ∀x ∈ K, φ n x ∈ Icc a b) := by
  obtain ⟨η, V, hη, hsη, hηunit, hsub, hV, hKV, hone⟩ :=
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
  have hwunit : ∀x, w x ∈ Icc 0 1 := compact_cutoff_mem_Icc hunit hηunit hsub
  have hwLp : MemLp w 2 volume := by simpa only [Measure.restrict_univ] using hw.memLp
  have hw_eq : EqOn w u V := fun x hx => by dsimp [w]; rw [hone x hx, one_mul]
  refine ⟨V, planarMollification w, hV, hKV, hVΩ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ⟨planarMollification_smooth (hwLp.locallyIntegrable (by norm_num)) n,
      planarMollification_hasCompactSupport hsη.mul_right n,
      planarMollification_mem_Icc hwLp.aestronglyMeasurable hwunit n⟩
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

end CircleDomainRigidity

end

end OAI
