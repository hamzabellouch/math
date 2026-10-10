import OAI.Analysis.CircleDomains.Rigidity.TraceTruncationWeak
import OAI.Analysis.CircleDomains.Rigidity.TraceTruncationLimits

namespace OAI

/-! A continuous, compactly supported, nonnegative Sobolev function with
zero trace extends through the excluded set with zero weak gradient there.
Smooth value truncations give the extension without a geometric assumption
on that closed set. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem zero_trace_global_weak
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u) (hb : ∀ x, u x ∈ Icc 0 1)
    (hz : ∀ x ∉ U, u x = 0) (hw : DeGiorgi.MemW1pWitness 2 u U) (i : Fin 2) :
    DeGiorgi.HasWeakPartialDeriv i
      ({x | u x ≠ 0}.indicator (U.indicator (fun x => hw.weakGrad x i))) u univ := by
  classical
  let δ : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hδ : ∀ n, 0 < δ n := fun n => inv_pos.mpr (by positivity)
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let G : EuclideanPlane → ℝ := U.indicator (fun x => hw.weakGrad x i)
  have hG : MemLp G 2 volume :=
    (memLp_indicator_iff_restrict hU.measurableSet).mpr (hw.weakGrad_component_memLp i)
  obtain ⟨C, hC, hbound⟩ := smoothTraceTruncation_uniform_deriv_bound
  intro φ hφ hsφ hsub
  let v : EuclideanPlane := EuclideanSpace.single i 1
  have hD : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsD : HasCompactSupport (fun x => fderiv ℝ φ x v) := hsφ.fderiv_apply (𝕜 := ℝ) v
  have hleft := tendsto_integral_of_dominated_convergence (μ := volume)
    (F := fun n x => smoothTraceTruncation (δ n) (u x) * fderiv ℝ φ x v)
    (f := fun x => u x * fderiv ℝ φ x v)
    (fun x => ‖fderiv ℝ φ x v‖)
    (fun n => (((smoothTraceTruncation_contDiff (δ n)).continuous.comp hu).aestronglyMeasurable).mul
      hD.aestronglyMeasurable)
    (hD.integrable_of_hasCompactSupport hsD).norm
    (fun n => Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_eq_abs (smoothTraceTruncation (δ n) (u x)),
        abs_of_nonneg (smoothTraceTruncation_mem (hb x).1).1]
      exact (mul_le_mul_of_nonneg_right
        ((smoothTraceTruncation_mem (hb x).1).2.trans (hb x).2) (norm_nonneg _)).trans_eq (one_mul _))
    (Eventually.of_forall fun x =>
      (smoothTraceTruncation_tendsto hδ hδlim (hb x).1).mul_const _)
  have hright := tendsto_integral_bounded_mul_L2
    (g := fun _ : ℕ => G) (G := G)
    (h := fun n x => deriv (smoothTraceTruncation (δ n)) (u x))
    (H := fun x => if u x = 0 then 0 else 1) (φ := φ)
    (fun _ => hG) hG (hφ.continuous.memLp_of_hasCompactSupport hsφ)
    (by
      simp only [sub_self]
      change Tendsto (fun _ : ℕ => eLpNorm (0 : EuclideanPlane → ℝ) 2 volume) atTop (𝓝 0)
      simp only [eLpNorm_zero]
      exact tendsto_const_nhds)
    (fun n => (((smoothTraceTruncation_contDiff (δ n)).of_le (by simp) :
      ContDiff ℝ 1 (smoothTraceTruncation (δ n))).continuous_deriv le_rfl).comp hu
      |>.aestronglyMeasurable)
    hC (fun n => Eventually.of_forall fun x => hbound (δ n) (hδ n) (u x))
    (Eventually.of_forall fun x => smoothTraceTruncation_deriv_tendsto hδ hδlim (hb x).1)
  have heq (n : ℕ) :
      (∫ x, smoothTraceTruncation (δ n) (u x) * fderiv ℝ φ x v) =
        -(∫ x, deriv (smoothTraceTruncation (δ n)) (u x) * G x * φ x) := by
    simpa only [Measure.restrict_univ, comp_apply] using
      smooth_trace_truncation_weak hU hu hs hb hz hw (hδ n) i φ hφ hsφ hsub
  have he := tendsto_nhds_unique hleft (by simpa only [heq] using hright.neg)
  simp only [Measure.restrict_univ]
  convert he using 1
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : u x = 0 <;> simp [hx, G]

 def nonnegativeZeroTraceWitness
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u) (hb : ∀ x, u x ∈ Icc 0 1)
    (hz : ∀ x ∉ U, u x = 0) (hw : DeGiorgi.MemW1pWitness 2 u U) :
    DeGiorgi.MemW1pWitness 2 u univ where
  memLp := by simpa only [Measure.restrict_univ] using hu.memLp_of_hasCompactSupport hs
  weakGrad := fun x => WithLp.toLp 2 (fun i =>
    {x | u x ≠ 0}.indicator (U.indicator (fun x => hw.weakGrad x i)) x)
  weakGrad_component_memLp i := by
    simp only [Measure.restrict_univ]
    exact ((memLp_indicator_iff_restrict hU.measurableSet).mpr
      (hw.weakGrad_component_memLp i)).indicator (isOpen_ne_fun hu continuous_const).measurableSet
  isWeakGrad := zero_trace_global_weak hU hu hs hb hz hw

 theorem nonnegativeZeroTraceWitness_zero
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u) (hb : ∀ x, u x ∈ Icc 0 1)
    (hz : ∀ x ∉ U, u x = 0) (hw : DeGiorgi.MemW1pWitness 2 u U)
    (i : Fin 2) {x : EuclideanPlane} (hx : x ∉ U) :
    (nonnegativeZeroTraceWitness hU hu hs hb hz hw).weakGrad x i = 0 := by
  change {y | u y ≠ 0}.indicator (U.indicator (fun y => hw.weakGrad y i)) x = 0
  apply indicator_of_notMem
  change ¬ u x ≠ 0
  simp only [hz x hx, ne_eq, not_true_eq_false, not_false_eq_true]

end CircleDomainRigidity

end

end OAI
