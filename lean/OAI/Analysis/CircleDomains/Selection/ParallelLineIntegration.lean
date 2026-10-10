import OAI.Analysis.CircleDomains.Topology.ParallelDiskTolls
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-!
# Integration of the parallel-line payments

The linewise variation and hole costs are integrated without a measurable
choice of crossing segments. Cauchy–Schwarz is applied only to the density
in the chosen bounded region. This is the integration step of the
parallel-line lemma in Section 5 of the Koebe manuscript.
-/

open Set Function Metric MeasureTheory

namespace CircleDomainRigidity

theorem integral_le_sqrt_measure_mul_L2
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {g : X → ℝ} (hg : MemLp g 2 μ) (hpos : 0 ≤ᵐ[μ] g) :
    (∫ x, g x ∂μ) ≤ Real.sqrt (μ.real univ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (f := fun _ : X => (1 : ℝ)) (g := g)
    (Filter.Eventually.of_forall (fun _ => zero_le_one)) hpos
    (memLp_const 1) (by simpa using hg)
  simpa only [one_mul, Real.rpow_two, one_pow, integral_const, smul_eq_mul, mul_one,
    Real.sqrt_eq_rpow] using h

theorem integral_le_disk_L2 {ρ : ℂ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hρ : MemLp ρ 2 volume) (hpos : ∀ z, 0 ≤ ρ z)
    (hsupport : support ρ ⊆ closedBall 0 L) :
    Integrable ρ ∧ (∫ z, ρ z) ≤
      Real.sqrt Real.pi * L * Real.sqrt (∫ z, ρ z ^ 2) := by
  let : IsFiniteMeasure (volume.restrict (closedBall (0 : ℂ) L)) :=
    isFiniteMeasure_restrict.mpr measure_closedBall_lt_top.ne
  have hi : IntegrableOn ρ (closedBall 0 L) :=
    (hρ.mono_measure Measure.restrict_le_self).integrable (by norm_num)
  have heq : (closedBall (0 : ℂ) L).indicator ρ = ρ := indicator_eq_self.mpr hsupport
  have heq2 : (closedBall (0 : ℂ) L).indicator (fun z => ρ z ^ 2) = (fun z => ρ z ^ 2) := by
    apply indicator_eq_self.mpr
    intro z hz
    exact hsupport (by simpa only [mem_support, ne_eq, pow_eq_zero_iff (by norm_num : 2 ≠ 0)] using hz)
  refine ⟨(integrableOn_iff_integrable_of_support_subset hsupport).mp hi, ?_⟩
  have h := integral_le_sqrt_measure_mul_L2 (μ := volume.restrict (closedBall (0 : ℂ) L))
    (hρ.mono_measure Measure.restrict_le_self)
    (Filter.Eventually.of_forall hpos)
  rw [Measure.real, Measure.restrict_apply_univ, real_volume_closedBall 0 hL,
    Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hL] at h
  rw [← integral_indicator measurableSet_closedBall, heq,
    ← integral_indicator measurableSet_closedBall, heq2] at h
  exact h

theorem integral_horizontal_slices {ρ : ℂ → ℝ} (hρ : Integrable ρ) :
    Integrable (fun y : ℝ => ∫ x : ℝ, ρ ⟨x, y⟩) ∧
      (∫ y : ℝ, ∫ x : ℝ, ρ ⟨x, y⟩) = ∫ z : ℂ, ρ z := by
  have he := (Complex.volume_preserving_equiv_real_prod.symm
    Complex.measurableEquivRealProd).integrable_comp hρ.aestronglyMeasurable
  have hp : Integrable (fun p : ℝ × ℝ => ρ ⟨p.1, p.2⟩) := he.mpr hρ
  refine ⟨hp.integral_prod_right, ?_⟩
  calc
    _ = ∫ p : ℝ × ℝ, ρ ⟨p.1, p.2⟩ := (integral_prod_symm _ hp).symm
    _ = _ := (Complex.volume_preserving_equiv_real_prod.symm
      Complex.measurableEquivRealProd).integral_comp' ρ

theorem integrated_parallel_line_payment
    {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ)
    {ρ : ℂ → ℝ} {J : Set ℝ} {L : ℝ}
    (hJfinite : volume J ≠ ⊤)
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i) (hL : 0 ≤ L)
    (hρ : MemLp ρ 2 volume) (hpos : ∀ z, 0 ≤ ρ z)
    (hsupport : support ρ ⊆ closedBall 0 L)
    (hpay : ∀ᵐ y ∂volume.restrict J, 1 ≤ (∫ x : ℝ, ρ ⟨x, y⟩) +
      ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt (∫ z, ρ z ^ 2) +
      ∑ i, 2 * r i * A i := by
  let : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.mpr hJfinite
  have hiρ := integral_le_disk_L2 hL hρ hpos hsupport
  have hslices := integral_horizontal_slices hiρ.1
  let toll : ℝ → ℝ := fun y =>
    ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y
  have hitoll : Integrable toll := by
    apply integrable_finsetSum
    intro i _
    exact (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  have hsumpos : ∀ y, 0 ≤ (∫ x : ℝ, ρ ⟨x, y⟩) + toll y := by
    intro y
    exact add_nonneg (integral_nonneg (fun _ => hpos _))
      (Finset.sum_nonneg (fun i _ => indicator_nonneg (fun _ _ => hA i) y))
  calc
    (volume J).toReal = ∫ _y in J, (1 : ℝ) := by simp [measureReal_def]
    _ ≤ ∫ y in J, (∫ x : ℝ, ρ ⟨x, y⟩) + toll y :=
      integral_mono_ae (integrable_const _) (hslices.1.add hitoll).integrableOn hpay
    _ ≤ ∫ y : ℝ, (∫ x : ℝ, ρ ⟨x, y⟩) + toll y :=
      setIntegral_le_integral (hslices.1.add hitoll) (Filter.Eventually.of_forall hsumpos)
    _ = (∫ z, ρ z) + ∑ i, 2 * r i * A i := by
      rw [integral_add hslices.1 hitoll, hslices.2]
      exact congrArg _ (integral_parallel_disk_tolls c r A hr)
    _ ≤ _ := add_le_add hiρ.2 le_rfl

theorem integrated_parallel_line_payment_square_norm
    {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ)
    {ρ : ℂ → ℝ} {J : Set ℝ} {L : ℝ}
    (hJfinite : volume J ≠ ⊤)
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i) (hL : 0 ≤ L)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hsub : ∀ i, closedBall (c i) (r i) ⊆ closedBall 0 L)
    (hρ : MemLp ρ 2 volume) (hpos : ∀ z, 0 ≤ ρ z)
    (hsupport : support ρ ⊆ closedBall 0 L)
    (hpay : ∀ᵐ y ∂volume.restrict J, 1 ≤ (∫ x : ℝ, ρ ⟨x, y⟩) +
      ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt (∫ z, ρ z ^ 2) +
      2 * L * Real.sqrt (∑ i, A i ^ 2) := by
  have h := integrated_parallel_line_payment c r A hJfinite hr hA hL hρ hpos hsupport hpay
  have ht := parallel_disk_tolls_le_square_norm c r A hr hL hdisj hsub
  rw [integral_parallel_disk_tolls c r A hr] at ht
  exact h.trans (add_le_add le_rfl ht)

end CircleDomainRigidity

end OAI
