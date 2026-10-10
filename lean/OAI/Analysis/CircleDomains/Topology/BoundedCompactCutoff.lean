import OAI.Analysis.CircleDomains.Sobolev.CompactSobolevCutoff

namespace OAI

/-! A compact smooth cutoff of a bounded weakly differentiable scalar,
with its actual product-rule gradient retained. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem locallyIntegrable_of_unit_bound {f : EuclideanPlane → ℝ}
    (hm : AEStronglyMeasurable f volume) (hf : ∀ x, f x ∈ Icc 0 1) :
    LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  apply (MemLp.of_bound (p := (2 : ℝ≥0∞)) hm.restrict 1 ?_).integrable (by norm_num)
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hf x).1]
    exact (hf x).2

 def boundedCompactCutoffWitness
    {f : EuclideanPlane → ℝ} {G : EuclideanPlane → EuclideanPlane}
    (hm : AEStronglyMeasurable f volume) (hf : ∀ x, f x ∈ Icc 0 1)
    (hG : ∀ i : Fin 2, MemLp (fun x => G x i) 2 volume)
    (hw : DeGiorgi.HasWeakGrad G f univ)
    {η : EuclideanPlane → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hs : HasCompactSupport η) :
    DeGiorgi.MemW1pWitness 2 (fun x => η x * f x) univ where
  memLp := by
    simp only [Measure.restrict_univ]
    apply (hη.continuous.memLp_of_hasCompactSupport hs : MemLp η 2 volume).of_le
      (hη.continuous.aestronglyMeasurable.mul hm)
    exact Eventually.of_forall fun x => by
      simp only [Pi.mul_apply]
      rw [norm_mul, Real.norm_eq_abs (f x), abs_of_nonneg (hf x).1]
      exact (mul_le_mul_of_nonneg_left (hf x).2 (norm_nonneg _)).trans_eq (mul_one _)
  weakGrad := fun x => WithLp.toLp 2 (fun i =>
    η x * G x i + fderiv ℝ η x (EuclideanSpace.single i 1) * f x)
  weakGrad_component_memLp := by
    intro i
    simp only [Measure.restrict_univ]
    obtain ⟨B, hB⟩ := hη.continuous.bounded_above_of_compact_support hs
    have hfirst : MemLp (fun x => η x * G x i) 2 volume := by
      apply (hG i).of_le_mul (c := B)
        (hη.continuous.aestronglyMeasurable.mul (hG i).aestronglyMeasurable)
      exact Eventually.of_forall fun x => by
        simp only [Pi.mul_apply]
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)
    have hc : Continuous (fun x => fderiv ℝ η x (EuclideanSpace.single i 1)) :=
      (hη.continuous_fderiv (by simp)).clm_apply continuous_const
    have hsecond : MemLp (fun x => fderiv ℝ η x (EuclideanSpace.single i 1) * f x) 2 volume := by
      apply (hc.memLp_of_hasCompactSupport (hs.fderiv_apply (𝕜 := ℝ) _)
        : MemLp (fun x => fderiv ℝ η x (EuclideanSpace.single i 1)) 2 volume).of_le
          (hc.aestronglyMeasurable.mul hm)
      exact Eventually.of_forall fun x => by
        simp only [Pi.mul_apply]
        rw [norm_mul, Real.norm_eq_abs (f x), abs_of_nonneg (hf x).1]
        exact (mul_le_mul_of_nonneg_left (hf x).2 (norm_nonneg _)).trans_eq (mul_one _)
    exact hfirst.add hsecond
  isWeakGrad := by
    intro i
    simpa only [PiLp.toLp_apply] using
      DeGiorgi.HasWeakPartialDeriv.mul_smooth isOpen_univ (hw i) hη
        (by simpa only [Measure.restrict_univ] using locallyIntegrable_of_unit_bound hm hf)
        (by simpa only [Measure.restrict_univ] using (hG i).locallyIntegrable (by norm_num))

end CircleDomainRigidity

end

end OAI
