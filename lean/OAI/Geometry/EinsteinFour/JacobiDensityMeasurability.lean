import OAI.Geometry.EinsteinFour.JacobiODEPositivity
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI

/-! Measurability of the first-conjugate-point truncation. The apparently
uncountable condition is a countable intersection of open conditions on
compact time intervals. No stability theorem for conjugate points is used. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix MeasureTheory Set
open scoped Topology Matrix.Norms.L2Operator

noncomputable section

private theorem isOpen_forall_isUnit {K X : Type*} [TopologicalSpace K]
    [CompactSpace K] [TopologicalSpace X] (f : K × X → NormalMatrix)
    (hf : Continuous f) : IsOpen {x | ∀ k, IsUnit (f (k, x))} := by
  have hz : IsClosed {p : K × X | (f p).det = 0} :=
    isClosed_eq hf.matrix_det continuous_const
  have hc := isClosedMap_snd_of_compactSpace _ hz
  have heq : {x | ∀ k, IsUnit (f (k, x))} =
      (Prod.snd '' {p : K × X | (f p).det = 0})ᶜ := by
    ext x
    simp only [mem_ofPred_eq, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
      mem_compl_iff, mem_image, Prod.exists]
    aesop
  rw [heq]
  exact hc.isOpen_compl

def preconjugateSet {X : Type*} (J : ℝ × X → NormalMatrix) : Set (ℝ × X) :=
  {p | ∀ s, 0 < s → s ≤ p.1 → IsUnit (J (s, p.2))}

private def compactPreconjugateSet {X : Type*} (J : ℝ × X → NormalMatrix)
    (n : ℕ) : Set (ℝ × X) :=
  {p | ∀ r : Icc (1 / ((n : ℝ) + 1)) 1, IsUnit (J (p.1 * r.val, p.2))}

theorem measurableSet_preconjugate {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (J : ℝ × X → NormalMatrix)
    (hJ : Continuous J) : MeasurableSet (preconjugateSet J) := by
  have hopen (n : ℕ) : IsOpen (compactPreconjugateSet J n) := by
    apply isOpen_forall_isUnit
      (fun p : Icc (1 / ((n : ℝ) + 1)) 1 × (ℝ × X) =>
        J (p.2.1 * p.1.val, p.2.2))
    exact hJ.comp (((continuous_fst.comp continuous_snd).mul
      (continuous_subtype_val.comp continuous_fst)).prodMk
        (continuous_snd.comp continuous_snd))
  have heq : preconjugateSet J = {p : ℝ × X | p.1 ≤ 0} ∪
      ({p : ℝ × X | 0 < p.1} ∩ ⋂ n, compactPreconjugateSet J n) := by
    ext p
    constructor
    · intro hp
      by_cases ht : p.1 ≤ 0
      · exact Or.inl ht
      · refine Or.inr ⟨lt_of_not_ge ht, mem_iInter.mpr (fun n r => ?_)⟩
        have hr : 0 < r.val := lt_of_lt_of_le (by positivity) r.property.1
        exact hp _ (mul_pos (lt_of_not_ge ht) hr)
          (by nlinarith [r.property.2])
    · rintro (ht | ⟨ht, hp⟩) s hs hst
      · exact False.elim (not_lt_of_ge (hst.trans ht) hs)
      · change 0 < p.1 at ht
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hs ht)
        let r : Icc (1 / ((n : ℝ) + 1)) 1 :=
          ⟨s / p.1, hn.le, (div_le_one ht).mpr hst⟩
        have h := mem_iInter.mp hp n r
        have he : p.1 * r.val = s := by dsimp [r]; field_simp [ne_of_gt ht]
        simpa only [he] using h
  rw [heq]
  exact (isClosed_le continuous_fst continuous_const).measurableSet.union
    ((isOpen_lt continuous_const continuous_fst).measurableSet.inter
      (MeasurableSet.iInter (fun n => (hopen n).measurableSet)))

def truncatedJacobiDensity {X : Type*} (J : ℝ × X → NormalMatrix) (p : ℝ × X) : ℝ :=
  open Classical in if p ∈ preconjugateSet J then (J p).det else 0

theorem truncatedJacobiDensity_rescale {X : Type*} (J : ℝ × X → NormalMatrix)
    (c : ℝ) (hc : 0 < c) (t : ℝ) (x : X) :
    truncatedJacobiDensity (fun p => J (c * p.1, p.2)) (t, x) =
      truncatedJacobiDensity J (c * t, x) := by
  classical
  have hp : (t, x) ∈ preconjugateSet (fun p => J (c * p.1, p.2)) ↔
      (c * t, x) ∈ preconjugateSet J := by
    constructor
    · intro h s hs hst
      have h' := h (s / c) (div_pos hs hc) ((div_le_iff₀ hc).mpr (by nlinarith))
      simpa only [mul_div_cancel₀ _ hc.ne'] using h'
    · intro h s hs hst
      exact h (c * s) (mul_pos hc hs) (mul_le_mul_of_nonneg_left hst hc.le)
  simp only [truncatedJacobiDensity, hp]

theorem measurable_truncatedJacobiDensity {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (J : ℝ × X → NormalMatrix)
    (hJ : Continuous J) : Measurable (truncatedJacobiDensity J) := by
  classical
  exact Measurable.ite (measurableSet_preconjugate J hJ) hJ.matrix_det.measurable
    measurable_const

theorem norm_truncatedJacobiDensity_le {X : Type*} (J : ℝ × X → NormalMatrix)
    (p : ℝ × X) : ‖truncatedJacobiDensity J p‖ ≤ |(J p).det| := by
  classical
  unfold truncatedJacobiDensity
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using abs_nonneg (J p).det

/-- Each fixed-radius density is integrable on a compact parameter space.
Only joint continuity of the actual Jacobi matrix is needed. -/
theorem integrable_truncatedJacobiDensity_slice {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (J : ℝ × X → NormalMatrix) (hJ : Continuous J) (t : ℝ) :
    Integrable (fun x => truncatedJacobiDensity J (t, x)) μ := by
  have hd : Continuous (fun x => |(J (t, x)).det|) :=
    (hJ.comp (continuous_const.prodMk continuous_id)).matrix_det.abs
  have hi : Integrable (fun x => |(J (t, x)).det|) μ :=
    hd.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply hi.mono'
    ((measurable_truncatedJacobiDensity J hJ).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => norm_truncatedJacobiDensity_le J (t, x))

theorem integrable_truncatedJacobiDensity_product {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (J : ℝ × X → NormalMatrix) (hJ : Continuous J) (a b : ℝ) :
    Integrable (truncatedJacobiDensity J) ((volume.restrict (Icc a b)).prod μ) := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set X))).exists_bound_of_continuousOn
      hJ.matrix_det.continuousOn
  have hs : ∀ᵐ p : ℝ × X ∂(volume.restrict (Icc a b)).prod μ, p.1 ∈ Icc a b := by
    apply (Measure.ae_prod_iff_ae_ae (measurable_fst measurableSet_Icc)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact Filter.Eventually.of_forall (fun _ => ht)
  apply (integrable_const (max 0 C : ℝ)).mono'
    (measurable_truncatedJacobiDensity J hJ).aestronglyMeasurable
  filter_upwards [hs] with p hp
  exact (norm_truncatedJacobiDensity_le J p).trans
    ((hC p ⟨hp, mem_univ _⟩).trans (le_max_right _ _))

/-- The averaged radial density is integrable on every bounded time interval. -/
theorem intervalIntegrable_truncatedJacobiDensity_average {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (J : ℝ × X → NormalMatrix) (hJ : Continuous J) (a b : ℝ)
    (hab : a ≤ b) :
    IntervalIntegrable (fun t => ∫ x, truncatedJacobiDensity J (t, x) ∂μ) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  exact (integrable_truncatedJacobiDensity_product μ J hJ a b).integral_prod_left

end
end PositiveEinsteinFour.Jacobi

end OAI
