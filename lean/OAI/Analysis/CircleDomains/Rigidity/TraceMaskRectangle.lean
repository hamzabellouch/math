import OAI.Analysis.CircleDomains.Modulus.NormedAffineLinePayment
import OAI.Analysis.CircleDomains.Rigidity.TracePrimitiveMeasurability
import OAI.Analysis.CircleDomains.Selection.RectangleSliceData
import OAI.Analysis.CircleDomains.Sobolev.WeightedSobolevTransport

namespace OAI

/-! The actual infinite mask is locally Sobolev wherever its raw scalar
is smooth. The gradient is constructed from line payments and Fubini;
only the square-integrable sum of the actual cutoff gradients is used. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem continuous_memLp_rectangle {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (a b c d : ℝ) : MemLp f 2 (volume.restrict (Icc a b ×ˢ Icc c d)) := by
  let : IsFiniteMeasure (volume.restrict (Icc a b ×ˢ Icc c d) : Measure (ℝ × ℝ)) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable.restrict C
    ((ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)).mono fun p hp => hC p hp)

 theorem smooth_masked_scalar_rectangle_sobolev
    {cutoff : ℕ → (ℝ × ℝ) → ℝ} (hs : ∀ j, ContDiff ℝ 1 (cutoff j))
    (hc : ∀ j p, cutoff j p ∈ Icc (0:ℝ) 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {b : ℝ × ℝ → ℝ} (hb : ContDiff ℝ 1 b)
    {P : ℝ × ℝ → ℝ} (hPm : Measurable P) (hP0 : ∀ p, 0 ≤ P p)
    {a₁ a₂ b₁ b₂ : ℝ} (ha : a₁ ≤ a₂) (hb' : b₁ ≤ b₂)
    (hP2 : MemLp P 2 (volume.restrict (Icc a₁ a₂ ×ˢ Icc b₁ b₂)))
    (hdom : ∀ n, ∀ᵐ p ∂volume.restrict (Icc a₁ a₂ ×ˢ Icc b₁ b₂),
      ∑ j ∈ Finset.range n, volume.real (I j)*‖fderiv ℝ (cutoff j) p‖ ≤ P p)
    (a : ℝ) :
    ∃ W : DeGiorgi.MemW1pWitness 2
      ((fun p => infiniteTracePrimitive cutoff I a p (b p)) ∘ euclideanPlaneCoordinates)
      (euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂)),
      ∀ i : Fin 2, ∀ᵐ z ∂volume.restrict
        (euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂)),
        |W.weakGrad z i| ≤ ‖fderiv ℝ b (euclideanPlaneCoordinates z)‖+P (euclideanPlaneCoordinates z) := by
  let U : ℝ × ℝ → ℝ := fun p => infiniteTracePrimitive cutoff I a p (b p)
  let Q : ℝ × ℝ → ℝ := fun p => ‖fderiv ℝ b p‖
  let ρ : ℝ × ℝ → ℝ := fun p => Q p+P p
  have hQc : Continuous Q := (hb.continuous_fderiv (by norm_num)).norm
  have hgc (j : ℕ) : Continuous (fun p => ‖fderiv ℝ (cutoff j) p‖) :=
    ((hs j).continuous_fderiv (by norm_num)).norm
  have hρm : Measurable ρ := hQc.measurable.add hPm
  have hρ2 : MemLp ρ 2 (volume.restrict (Icc a₁ a₂ ×ˢ Icc b₁ b₂)) :=
    (continuous_memLp_rectangle hQc _ _ _ _).add hP2
  let : IsFiniteMeasure (volume.restrict (Icc a₁ a₂ ×ˢ Icc b₁ b₂) : Measure (ℝ × ℝ)) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hU2 : MemLp U 2 (volume.restrict (Icc a₁ a₂ ×ˢ Icc b₁ b₂)) :=
    infinite_masked_scalar_memLp hc (fun j => (hs j).continuous) hI hIf hb.continuous.measurable
      (continuous_memLp_rectangle hb.continuous _ _ _ _) a
  have hPi := rectangle_L2_line_integrable ha hb' hP2
  have hD (n : ℕ) := rectangle_ae_slices
    (measurableSet_le (Finset.measurable_sum _ (fun j _ =>
      measurable_const.mul (hgc j).measurable)) hPm) (hdom n)
  have hDx : ∀ᵐ y ∂volume.restrict (Icc b₁ b₂), ∀ n,
      ∀ᵐ x ∂volume.restrict (Icc a₁ a₂),
        ∑ j ∈ Finset.range n, volume.real (I j)*‖fderiv ℝ (cutoff j) (x,y)‖ ≤ P (x,y) :=
    ae_all_iff.mpr (fun n => (hD n).1)
  have hDy : ∀ᵐ x ∂volume.restrict (Icc a₁ a₂), ∀ n,
      ∀ᵐ y ∂volume.restrict (Icc b₁ b₂),
        ∑ j ∈ Finset.range n, volume.real (I j)*‖fderiv ℝ (cutoff j) (x,y)‖ ≤ P (x,y) :=
    ae_all_iff.mpr (fun n => (hD n).2)
  have hx : ∀ᵐ y ∂volume.restrict (Icc b₁ b₂),
      AbsolutelyContinuousOnInterval (fun x => U (x,y)) a₁ a₂ ∧
      ∀ᵐ x ∂volume.restrict (Icc a₁ a₂), |deriv (fun t => U (t,y)) x| ≤ ρ (x,y) := by
    filter_upwards [hPi.1,hDx] with y hiy hdy
    have hg (j : ℕ) : IntervalIntegrable (fun x => ‖fderiv ℝ (cutoff j) (x,y)‖) volume a₁ a₂ :=
      ((hgc j).comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    have hq : IntervalIntegrable (fun x => Q (x,y)) volume a₁ a₂ :=
      (hQc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    have hd (n : ℕ) : ∀ᵐ x ∂volume.restrict (uIoc a₁ a₂),
        ∑ j ∈ Finset.range n, volume.real (I j)*‖fderiv ℝ (cutoff j) (x,y)‖ ≤ P (x,y) :=
      ae_restrict_of_ae_restrict_of_subset (by simpa only [uIoc_of_le ha] using Ioc_subset_Icc_self) (hdy n)
    have hcut : ∀ j, ∀ x ∈ uIcc a₁ a₂, ∀ z ∈ uIcc a₁ a₂,
        |cutoff j (x,y)-cutoff j (z,y)| ≤ ∫ t in uIoc x z, ‖fderiv ℝ (cutoff j) (t,y)‖ :=
      fun j x _ z _ => smooth_horizontal_increment (hs j) y x z
    have hraw : ∀ x ∈ uIcc a₁ a₂, ∀ z ∈ uIcc a₁ a₂,
        |b (x,y)-b (z,y)| ≤ ∫ t in uIoc x z, Q (t,y) :=
      fun x _ z _ => smooth_horizontal_increment hb y x z
    constructor
    · simpa only [U,infiniteTracePrimitive_comp] using
        masked_scalar_ACL_of_line_payment_ae (fun j x => hc j (x,y)) hI hIf hg hiy hq
          hcut hd hraw a
    · simpa only [U,ρ,Q,infiniteTracePrimitive_comp] using
        masked_scalar_derivative_of_line_payment_ae (fun j x => hc j (x,y)) hI hIf ha hg hiy hq
          (Eventually.of_forall fun x => add_nonneg (norm_nonneg _) (hP0 _)) hcut hd hraw a
  have hy : ∀ᵐ x ∂volume.restrict (Icc a₁ a₂),
      AbsolutelyContinuousOnInterval (fun y => U (x,y)) b₁ b₂ ∧
      ∀ᵐ y ∂volume.restrict (Icc b₁ b₂), |deriv (fun t => U (x,t)) y| ≤ ρ (x,y) := by
    filter_upwards [hPi.2,hDy] with x hix hdx
    have hg (j : ℕ) : IntervalIntegrable (fun y => ‖fderiv ℝ (cutoff j) (x,y)‖) volume b₁ b₂ :=
      ((hgc j).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    have hq : IntervalIntegrable (fun y => Q (x,y)) volume b₁ b₂ :=
      (hQc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    have hd (n : ℕ) : ∀ᵐ y ∂volume.restrict (uIoc b₁ b₂),
        ∑ j ∈ Finset.range n, volume.real (I j)*‖fderiv ℝ (cutoff j) (x,y)‖ ≤ P (x,y) :=
      ae_restrict_of_ae_restrict_of_subset (by simpa only [uIoc_of_le hb'] using Ioc_subset_Icc_self) (hdx n)
    have hcut : ∀ j, ∀ y ∈ uIcc b₁ b₂, ∀ z ∈ uIcc b₁ b₂,
        |cutoff j (x,y)-cutoff j (x,z)| ≤ ∫ t in uIoc y z, ‖fderiv ℝ (cutoff j) (x,t)‖ :=
      fun j y _ z _ => smooth_vertical_increment (hs j) x y z
    have hraw : ∀ y ∈ uIcc b₁ b₂, ∀ z ∈ uIcc b₁ b₂,
        |b (x,y)-b (x,z)| ≤ ∫ t in uIoc y z, Q (x,t) :=
      fun y _ z _ => smooth_vertical_increment hb x y z
    constructor
    · simpa only [U,infiniteTracePrimitive_comp] using
        masked_scalar_ACL_of_line_payment_ae (fun j y => hc j (x,y)) hI hIf hg hix hq
          hcut hd hraw a
    · simpa only [U,ρ,Q,infiniteTracePrimitive_comp] using
        masked_scalar_derivative_of_line_payment_ae (fun j y => hc j (x,y)) hI hIf hb' hg hix hq
          (Eventually.of_forall fun y => add_nonneg (norm_nonneg _) (hP0 _)) hcut hd hraw a
  obtain ⟨Gx,Gy,_,_,hGx,hGy,hbound,hweak⟩ := exists_rectangle_weak_gradient ha hb' hU2 hρm hρ2
    (hx.mono fun _ h => h.1) (hy.mono fun _ h => h.1)
    (hx.mono fun _ h => h.2) (hy.mono fun _ h => h.2)
  exact exists_bounded_rectangle_sobolev_witness hU2 hGx hGy hbound hweak

end CircleDomainRigidity

end

end OAI
