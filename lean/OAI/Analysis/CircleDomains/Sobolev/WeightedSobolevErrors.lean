import OAI.Analysis.CircleDomains.Sobolev.LocalSobolevSmoothing

namespace OAI

/-! Quantitative error estimates for multiplying local Sobolev
approximations by smooth partition functions. -/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem aestronglyMeasurable_mul_of_support
    {V : Set EuclideanPlane} (hV : MeasurableSet V)
    {f ψ : EuclideanPlane → ℝ} (hf : AEStronglyMeasurable f (volume.restrict V))
    (hψ : Continuous ψ) (hs : Function.support ψ ⊆ V) :
    AEStronglyMeasurable (fun x => ψ x * f x) volume := by
  have hi : V.indicator (fun x => ψ x * f x) = fun x => ψ x * f x := by
    funext x
    by_cases hx : x ∈ V
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx, Function.notMem_support.mp (fun h => hx (hs h)), zero_mul]
  rw [← hi]
  exact (aestronglyMeasurable_indicator_iff hV).2 (hψ.aestronglyMeasurable.restrict.mul hf)

theorem eLpNorm_mul_le_of_support
    {V : Set EuclideanPlane} (hV : MeasurableSet V)
    {f ψ : EuclideanPlane → ℝ} (hf : AEStronglyMeasurable f (volume.restrict V))
    (hψ : Continuous ψ) {C : ℝ≥0} (hC : ∀x, ‖ψ x‖ ≤ C)
    (hs : Function.support ψ ⊆ V) :
    eLpNorm (fun x => ψ x * f x) 2 volume ≤ C * eLpNorm f 2 (volume.restrict V) := by
  have hi : V.indicator (fun x => ψ x * f x) = fun x => ψ x * f x := by
    funext x
    by_cases hx : x ∈ V
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx, Function.notMem_support.mp (fun h => hx (hs h)), zero_mul]
  rw [← hi, eLpNorm_indicator_eq_eLpNorm_restrict hV]
  apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (hψ.aestronglyMeasurable.restrict.mul hf)
  exact Eventually.of_forall fun x => by
    have hnn : ‖ψ x‖₊ ≤ C := by exact_mod_cast hC x
    simpa only [Pi.mul_apply, nnnorm_mul] using mul_le_mul' hnn (le_refl ‖f x‖₊)

theorem tendsto_eLpNorm_mul_zero_of_support
    {V : Set EuclideanPlane} (hV : MeasurableSet V)
    {f : ℕ → EuclideanPlane → ℝ} (hf : ∀n, AEStronglyMeasurable (f n) (volume.restrict V))
    {ψ : EuclideanPlane → ℝ} (hψ : Continuous ψ) (hsψ : HasCompactSupport ψ)
    (hs : Function.support ψ ⊆ V)
    (hlim : Tendsto (fun n => eLpNorm (f n) 2 (volume.restrict V)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => ψ x * f n x) 2 volume) atTop (𝓝 0) := by
  obtain ⟨A, hA⟩ := hψ.bounded_above_of_compact_support hsψ
  let C : ℝ≥0 := ⟨max A 0, le_max_right _ _⟩
  have hC : ∀x, ‖ψ x‖ ≤ C := fun x => (hA x).trans (le_max_left _ _)
  have hl : Tendsto (fun n => (C : ℝ≥0∞) * eLpNorm (f n) 2 (volume.restrict V))
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.coe_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
    (fun _ => bot_le) (fun n => eLpNorm_mul_le_of_support hV (hf n) hψ hC hs)

theorem tendsto_partition_derivative_error
    {V : Set EuclideanPlane} (hV : IsOpen V)
    {u : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u V)
    {φ : ℕ → EuclideanPlane → ℝ} (hφ : ∀n, ContDiff ℝ (⊤ : ℕ∞) (φ n))
    (hv : Tendsto (fun n => eLpNorm (fun x => φ n x - u x) 2 (volume.restrict V))
      atTop (𝓝 0))
    (hg : ∀i : Fin 2, Tendsto (fun n => eLpNorm (fun x =>
      (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hu.weakGrad x i)
      2 (volume.restrict V)) atTop (𝓝 0))
    {ψ : EuclideanPlane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hsψ : HasCompactSupport ψ) (hsub : tsupport ψ ⊆ V) (i : Fin 2) :
    Tendsto (fun n => eLpNorm (fun x =>
      ψ x * ((fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hu.weakGrad x i) +
      (fderiv ℝ ψ x) (EuclideanSpace.single i 1) * (φ n x - u x)) 2 volume)
      atTop (𝓝 0) := by
  let dψ : EuclideanPlane → ℝ := fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)
  have hdψ : Continuous dψ := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsdψ : HasCompactSupport dψ := hsψ.fderiv_apply (𝕜 := ℝ) _
  have hsubdψ : Function.support dψ ⊆ V :=
    (subset_tsupport dψ).trans ((tsupport_fderiv_apply_subset ℝ _).trans hsub)
  have hv' := tendsto_eLpNorm_mul_zero_of_support hV.measurableSet
    (fun n => (hφ n).continuous.aestronglyMeasurable.restrict.sub hu.memLp.aestronglyMeasurable)
    hdψ hsdψ hsubdψ hv
  have hg' := tendsto_eLpNorm_mul_zero_of_support hV.measurableSet
    (fun n => ((hφ n).continuous_fderiv (by simp)).clm_apply continuous_const
      |>.aestronglyMeasurable.restrict.sub (hu.weakGrad_component_memLp i).aestronglyMeasurable)
    hψ.continuous hsψ ((subset_tsupport ψ).trans hsub) (hg i)
  have hl := hg'.add hv'
  simp only [zero_add] at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
    (fun _ => bot_le)
  intro n
  exact eLpNorm_add_le (by norm_num)

theorem aestronglyMeasurable_partition_derivative_error
    {V : Set EuclideanPlane} (hV : IsOpen V)
    {u : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u V)
    {v ψ : EuclideanPlane → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hsub : tsupport ψ ⊆ V) (i : Fin 2) :
    AEStronglyMeasurable (fun x =>
      ψ x * ((fderiv ℝ v x) (EuclideanSpace.single i 1) - hu.weakGrad x i) +
      (fderiv ℝ ψ x) (EuclideanSpace.single i 1) * (v x - u x)) volume := by
  have hdv : Continuous (fun x => (fderiv ℝ v x) (EuclideanSpace.single i 1)) :=
    (hv.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψ : Continuous (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  exact (aestronglyMeasurable_mul_of_support hV.measurableSet
    (hdv.aestronglyMeasurable.restrict.sub (hu.weakGrad_component_memLp i).aestronglyMeasurable)
    hψ.continuous ((subset_tsupport ψ).trans hsub)).add
      (aestronglyMeasurable_mul_of_support hV.measurableSet
        (hv.continuous.aestronglyMeasurable.restrict.sub hu.memLp.aestronglyMeasurable)
        hdψ ((subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ _).trans hsub)))

end CircleDomainRigidity

end

end OAI
