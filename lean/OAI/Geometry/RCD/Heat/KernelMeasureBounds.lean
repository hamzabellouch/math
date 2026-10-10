import OAI.Geometry.RCD.Heat.ActualHeatMass
import OAI.Geometry.RCD.Coordinates.SymmetricDomination
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-!
# Continuous kernel bounds at every source pole

Bounds initially valid almost everywhere in the reference measure extend
to every pole by continuity and full support. The resulting pointwise
bounds may then be integrated against a singular local mass measure.
-/

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) [μ.Regular]
  {p : ℝ → X → X → ℝ} (hp : IsContinuousHeatKernel μ hQ p)

/-- An actual average over the testing set, in the first kernel variable. -/
def kernelAverage (p : ℝ → X → X → ℝ) (t : ℝ) (s : Set X) (z : X) : ℝ :=
  (μ.real s)⁻¹ * ∫ a in s, p t a z ∂μ

include hp in
theorem kernelAverage_continuous [IsLocallyFiniteMeasure μ]
    {t : ℝ} (ht : 0 < t) {s : Set X} (hs : MeasurableSet s)
    (hbounded : Bornology.IsBounded s) : Continuous (kernelAverage μ p t s) := by
  apply Continuous.const_mul
  rw [continuous_iff_continuousAt]
  intro z
  let U := Metric.closedBall z 1
  have hU : IsCompact U := isCompact_closedBall z 1
  have hUn : U ∈ 𝓝 z := Metric.closedBall_mem_nhds z (by norm_num)
  have hS : IsCompact (closure s) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hbounded.closure
  have hjoint : Continuous (fun za : X × X => p t za.2 za.1) :=
    (hp.continuous_joint t ht).comp continuous_swap
  obtain ⟨C, hC⟩ := (hU.prod hS).bddAbove_image hjoint.norm.continuousOn
  apply continuousAt_of_dominated (bound := fun _ => C)
  · filter_upwards with x
    exact ((hp.continuous_joint t ht).comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · filter_upwards [hUn] with x hx
    filter_upwards [ae_restrict_mem hs] with a ha
    exact hC ⟨(x, a), ⟨hx, subset_closure ha⟩, rfl⟩
  · exact integrableOn_const hbounded.measure_lt_top.ne
  · filter_upwards with a
    exact (hp.continuous_right t ht a).continuousAt

omit [BorelSpace X] [ProperSpace X] [μ.Regular] in
/-- Full support turns a continuous almost-everywhere inequality into an
everywhere inequality. The measure used for this extension is the reference
measure, not the possibly singular measure used afterwards. -/
theorem continuous_bound_everywhere [μ.IsOpenPosMeasure]
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ᵐ z ∂μ, f z ≤ g z) : ∀ z, f z ≤ g z := by
  have hd := μ.dense_of_ae h
  have hc : IsClosed {z | f z ≤ g z} := isClosed_le hf hg
  have he : {z | f z ≤ g z} = univ := by
    rw [← hc.closure_eq, hd.closure_eq]
  intro z
  change z ∈ {z | f z ≤ g z}
  rw [he]
  trivial

include hp in
/-- The averaged kernel difference estimate extends to every pole before
it is paired with the full Bochner measure. -/
theorem kernelAverage_difference_everywhere [IsLocallyFiniteMeasure μ]
    [μ.IsOpenPosMeasure] {t : ℝ} (ht : 0 < t) {s : Set X}
    (hs : MeasurableSet s) (hbounded : Bornology.IsBounded s) (x : X)
    (B : X → ℝ) (hB : Continuous B)
    (h : ∀ᵐ z ∂μ, |kernelAverage μ p t s z - p t x z| ≤ B z) :
    ∀ z, |kernelAverage μ p t s z - p t x z| ≤ B z :=
  continuous_bound_everywhere μ
    (((kernelAverage_continuous μ hQ hp ht hs hbounded).sub
      (hp.continuous_right t ht x)).abs) hB h

omit [MeasurableSpace X] [BorelSpace X] [ProperSpace X] [μ.Regular] in
private theorem compact_weight_bound {f : X → ℝ} (hf : Continuous f)
    (hs : HasCompactSupport f) : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hs.isCompact_range hf).isBounded.exists_norm_le
  exact ⟨C, fun x => hC _ (mem_range_self x)⟩

private def compactWeight {f : X → ℝ} (hf : Continuous f)
    (hs : HasCompactSupport f) : X →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup f hf
    (compact_weight_bound hf hs).choose (compact_weight_bound hf hs).choose_spec

variable [IsLocallyFiniteMeasure μ]
  {χ : X → ℝ} (hχ : Continuous χ) (hsχ : HasCompactSupport χ)

/-- Average the kernel first, then integrate the cutoff average against
the full mass measure. -/
def cutoffAverageHeatMass {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (M : PositiveBilinearMeasure X E) {t : ℝ} (ht : 0 < t)
    (s : Set X) (hs : MeasurableSet s) (hbounded : Bornology.IsBounded s) : E →L[ℝ] E :=
  M.weightedOperator (compactWeight
    (hχ.mul (kernelAverage_continuous μ hQ hp ht hs hbounded)) hsχ.mul_right)

/-- Fubini identifies integration of the averaged kernel with the average
of the actual heat mass matrices. Compact cutoffs control the integrand
even when the mass is singular. -/
theorem cutoffAverageHeatMass_energy {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (M : PositiveBilinearMeasure X E) {t : ℝ} (ht : 0 < t)
    (s : Set X) (hs : MeasurableSet s) (hbounded : Bornology.IsBounded s) (v : E) :
    ⟪v, cutoffAverageHeatMass μ hQ hp hχ hsχ M ht s hs hbounded v⟫_ℝ =
      (μ.real s)⁻¹ * ∫ a in s, ⟪v, cutoffHeatMass μ hQ hp hχ hsχ M ht a v⟫_ℝ ∂μ := by
  let : IsFiniteMeasure (μ.restrict s) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hbounded.measure_lt_top⟩
  let F : X × X → ℝ := fun az => χ az.2 * p t az.1 az.2
  have hF : Continuous F := (hχ.comp continuous_snd).mul (hp.continuous_joint t ht)
  have hcompact : IsCompact (closure s ×ˢ tsupport χ) :=
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure hbounded.closure).prod
      hsχ.isCompact
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image hF.norm.continuousOn
  have hbound : ∀ᵐ az ∂(μ.restrict s).prod (M.measure v), ‖F az‖ ≤ max C 0 := by
    apply (Measure.ae_prod_iff_ae_ae (isClosed_le hF.norm continuous_const).measurableSet).mpr
    filter_upwards [ae_restrict_mem hs] with a ha
    exact Filter.Eventually.of_forall fun z => by
      by_cases hz : z ∈ tsupport χ
      · exact (hC ⟨(a, z), ⟨subset_closure ha, hz⟩, rfl⟩).trans (le_max_left _ _)
      · simp only [F, image_eq_zero_of_notMem_tsupport hz, zero_mul, norm_zero]
        exact le_max_right _ _
  have hint : Integrable F ((μ.restrict s).prod (M.measure v)) :=
    Integrable.of_bound hF.aestronglyMeasurable (max C 0) hbound
  have hswap := integral_integral_swap (f := fun a z => χ z * p t a z) hint
  rw [cutoffAverageHeatMass, M.weightedOperator_energy]
  change (∫ z, χ z * ((μ.real s)⁻¹ * ∫ a in s, p t a z ∂μ) ∂(M.measure v)) = _
  calc
    _ = (μ.real s)⁻¹ * ∫ z, ∫ a in s, χ z * p t a z ∂μ ∂(M.measure v) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        dsimp only
        rw [integral_const_mul]
        ring
    _ = (μ.real s)⁻¹ * ∫ a in s, ∫ z, χ z * p t a z ∂(M.measure v) ∂μ := by
      exact congrArg (fun q : ℝ => (μ.real s)⁻¹ * q) hswap.symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun a => (cutoffHeatMass_energy μ hQ hp hχ hsχ M ht a v).symm

/-- The continuous all-pole extension permits the kernel difference to
be integrated against singular mass, with its full quantitative bound. -/
theorem cutoffAverageHeatMass_difference_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [μ.IsOpenPosMeasure] (M : PositiveBilinearMeasure X E)
    (hχpos : ∀ z, 0 ≤ χ z) {t : ℝ} (ht : 0 < t)
    (s : Set X) (hs : MeasurableSet s) (hbounded : Bornology.IsBounded s) (x : X)
    (B : X → ℝ) (hB : Continuous B)
    (hbound : ∀ᵐ z ∂μ, |kernelAverage μ p t s z - p t x z| ≤ B z) (v : E) :
    |⟪v, (cutoffAverageHeatMass μ hQ hp hχ hsχ M ht s hs hbounded -
      cutoffHeatMass μ hQ hp hχ hsχ M ht x) v⟫_ℝ| ≤
      ∫ z, χ z * B z ∂(M.measure v) := by
  let w := compactWeight
    (hχ.mul (kernelAverage_continuous μ hQ hp ht hs hbounded)) hsχ.mul_right
  let b := compactWeight (hχ.mul hB) hsχ.mul_right
  have hevery := kernelAverage_difference_everywhere μ hQ hp ht hs hbounded x B hB hbound
  have hdiff : ∀ z, |w z - cutoffHeatWeight μ hQ hp hχ hsχ ht x z| ≤ b z := by
    intro z
    change |χ z * kernelAverage μ p t s z - χ z * p t x z| ≤ χ z * B z
    rw [← mul_sub, abs_mul, abs_of_nonneg (hχpos z)]
    exact mul_le_mul_of_nonneg_left (hevery z) (hχpos z)
  have hh := M.weightedOperator_energy_difference_le w
    (cutoffHeatWeight μ hQ hp hχ hsχ ht x) b hdiff v
  rw [M.weightedOperator_energy b v] at hh
  exact hh

/-- The actual averaged-minus-pointwise heat mass satisfies the bilinear
bound in the same full Bochner measure, including its singular part. -/
theorem cutoffAverageHeatMass_difference_bilinear_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [μ.IsOpenPosMeasure] (M : PositiveBilinearMeasure X E)
    (hχpos : ∀ z, 0 ≤ χ z) {t : ℝ} (ht : 0 < t)
    (s : Set X) (hs : MeasurableSet s) (hbounded : Bornology.IsBounded s) (x : X)
    (B : X → ℝ) (hB : Continuous B)
    (hbound : ∀ᵐ z ∂μ, |kernelAverage μ p t s z - p t x z| ≤ B z) (v w : E) :
    ⟪v, (cutoffAverageHeatMass μ hQ hp hχ hsχ M ht s hs hbounded -
      cutoffHeatMass μ hQ hp hχ hsχ M ht x) w⟫_ℝ ^ 2 ≤
      (∫ z, χ z * B z ∂(M.measure v)) * (∫ z, χ z * B z ∂(M.measure w)) := by
  let D := cutoffAverageHeatMass μ hQ hp hχ hsχ M ht s hs hbounded -
    cutoffHeatMass μ hQ hp hχ hsχ M ht x
  let b := compactWeight (hχ.mul hB) hsχ.mul_right
  let P := M.weightedOperator b
  have hsym : D.IsSymmetric :=
    (M.weightedOperator_isSymmetric _).sub (M.weightedOperator_isSymmetric _)
  have hdom (u : E) : |⟪u, D u⟫_ℝ| ≤ ⟪u, P u⟫_ℝ := by
    rw [show ⟪u, P u⟫_ℝ = ∫ z, χ z * B z ∂(M.measure u) from
      M.weightedOperator_energy b u]
    exact cutoffAverageHeatMass_difference_le μ hQ hp hχ hsχ M hχpos ht
      s hs hbounded x B hB hbound u
  have h := symmetric_domination_cauchy_schwarz D P hsym hdom v w
  have hv : ⟪v, P v⟫_ℝ = ∫ z, χ z * B z ∂(M.measure v) := M.weightedOperator_energy b v
  have hw : ⟪w, P w⟫_ℝ = ∫ z, χ z * B z ∂(M.measure w) := M.weightedOperator_energy b w
  rw [hv, hw] at h
  exact h

end RegularPointCoordinates

end

end OAI
