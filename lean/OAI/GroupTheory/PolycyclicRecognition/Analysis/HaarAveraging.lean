import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Analysis.Normed.Group.Seminorm
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Order.Compact

namespace OAI

/-!
# Averaging translated masses

The boundary argument averages a Radon measure over Haar translates.  The
identities below use genuine measures and measurable multiplication, including
the Tonelli step.  Invariance is required only of Haar measure, not of the
measure whose translated masses are being compared.
-/

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

variable {G : Type*} [Group G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]

/-- A left translate, expressed as a measurable preimage. -/
def leftTranslate (E : Set G) (z : G) : Set G := {y | z⁻¹ * y ∈ E}

omit [MeasurableInv G] in
theorem measurableSet_leftTranslate {E : Set G} (hE : MeasurableSet E) (z : G) :
    MeasurableSet (leftTranslate E z) := hE.preimage (measurable_const.mul measurable_id)

/-- Tonelli's identity for the average mass of translates. -/
theorem average_translate_eq (μ ρ : Measure G) [SFinite μ] [SFinite ρ]
    {E S : Set G} (hE : MeasurableSet E) :
    (∫⁻ z in S, ρ (leftTranslate E z) ∂μ) =
      ∫⁻ y, μ (S ∩ {z | z⁻¹ * y ∈ E}) ∂ρ := by
  have hm : Measurable (fun p : G × G => p.1⁻¹ * p.2) :=
    measurable_fst.inv.mul measurable_snd
  calc
    (∫⁻ z in S, ρ (leftTranslate E z) ∂μ) =
        ∫⁻ z in S, ∫⁻ y, E.indicator (fun _ => (1 : ℝ≥0∞)) (z⁻¹ * y) ∂ρ ∂μ := by
      congr 1
      funext z
      symm
      have hf : Measurable (fun y : G => z⁻¹ * y) :=
        measurable_const.mul measurable_id
      calc
        _ = 1 * ρ ((fun y : G => z⁻¹ * y) ⁻¹' E) :=
          lintegral_indicator_const_comp hf hE 1
        _ = ρ (leftTranslate E z) := by
          rw [one_mul]
          congr 1
    _ = ∫⁻ y, ∫⁻ z in S, E.indicator (fun _ => (1 : ℝ≥0∞)) (z⁻¹ * y) ∂μ ∂ρ :=
      lintegral_lintegral_swap ((measurable_const.indicator hE).comp hm).aemeasurable
    _ = ∫⁻ y, μ (S ∩ {z | z⁻¹ * y ∈ E}) ∂ρ := by
      congr 1
      funext y
      rw [lintegral_indicator_const_comp (f := fun z : G => z⁻¹ * y)
        (measurable_id.inv.mul measurable_const) hE 1]
      simp only [one_mul]
      have hs : MeasurableSet ((fun z : G => z⁻¹ * y) ⁻¹' E) :=
        hE.preimage (measurable_id.inv.mul measurable_const)
      rw [Measure.restrict_apply hs]
      congr 1
      ext z
      exact and_comm

/-- Unimodularity identifies the total mass of the averaging kernel. -/
theorem translate_kernel_mass (μ : Measure G) [IsInvInvariant μ] [IsMulRightInvariant μ]
    (E : Set G) (y : G) : μ {z | z⁻¹ * y ∈ E} = μ E := by
  change μ (Inv.inv ⁻¹' ((fun z => z * y) ⁻¹' E)) = μ E
  rw [measure_preimage_inv, measure_preimage_mul_right]

/-- The set-theoretic sandwich underlying the Haar averaging estimate.
`inner` consists of points whose entire averaging kernel lies in `S`, while
outside `outer` the kernel misses `S`. -/
theorem average_translate_sandwich
    (μ ρ : Measure G) [SFinite μ] [SFinite ρ]
    [IsInvInvariant μ] [IsMulRightInvariant μ]
    {E S inner outer : Set G} (hE : MeasurableSet E)
    (hi : MeasurableSet inner) (ho : MeasurableSet outer)
    (hin : ∀ y ∈ inner, ∀ z, z⁻¹ * y ∈ E → z ∈ S)
    (hout : ∀ y, ∀ z ∈ S, z⁻¹ * y ∈ E → y ∈ outer) :
    μ E * ρ inner ≤ (∫⁻ z in S, ρ (leftTranslate E z) ∂μ) ∧
      (∫⁻ z in S, ρ (leftTranslate E z) ∂μ) ≤ μ E * ρ outer := by
  rw [average_translate_eq μ ρ hE]
  constructor
  · calc
      μ E * ρ inner = ∫⁻ y, inner.indicator (fun _ => μ E) y ∂ρ := by
        rw [lintegral_indicator_const hi]
      _ ≤ _ := lintegral_mono fun y => by
        by_cases hy : y ∈ inner
        · rw [indicator_of_mem hy]
          have heq : S ∩ {z | z⁻¹ * y ∈ E} = {z | z⁻¹ * y ∈ E} :=
            inter_eq_right.mpr (fun z hz => hin y hy z hz)
          rw [heq, translate_kernel_mass]
        · rw [indicator_of_notMem hy]
          exact bot_le
  · calc
      _ ≤ ∫⁻ y, outer.indicator (fun _ => μ E) y ∂ρ := lintegral_mono fun y => by
        by_cases hy : y ∈ outer
        · rw [indicator_of_mem hy, ← translate_kernel_mass μ E y]
          exact measure_mono inter_subset_right
        · rw [indicator_of_notMem hy]
          have heq : S ∩ {z | z⁻¹ * y ∈ E} = ∅ := by
            apply eq_empty_iff_forall_notMem.mpr
            rintro z ⟨hz, he⟩
            exact hy (hout y z hz he)
          rw [heq, measure_empty]
      _ = μ E * ρ outer := lintegral_indicator_const ho _

/-- Balls for a left-invariant length function. -/
def lengthBall (ℓ : GroupSeminorm G) (r : ℝ) : Set G := {x | ℓ x < r}

/-- The group length associated to the left-invariant metric used in the
Lie-group application. -/
def distanceLength [PseudoMetricSpace G] [IsIsometricSMul G G] : GroupSeminorm G where
  toFun g := dist 1 g
  map_one' := dist_self _
  mul_le' x y := by
    calc
      dist 1 (x * y) ≤ dist 1 x + dist x (x * y) := dist_triangle _ _ _
      _ = dist 1 x + dist 1 y := by
        congr 1
        simpa only [mul_one] using dist_mul_left x 1 y
  inv' x := by
    calc
      dist 1 x⁻¹ = dist x 1 := by
        simpa only [mul_one, mul_inv_cancel] using (dist_mul_left x 1 x⁻¹).symm
      _ = dist 1 x := dist_comm _ _

/-- The metric version of the Tonelli sandwich. It uses the triangle
inequality for group length; commutativity is not required. -/
theorem ball_average_sandwich
    (μ ρ : Measure G) [SFinite μ] [SFinite ρ]
    [IsInvInvariant μ] [IsMulRightInvariant μ]
    (ℓ : GroupSeminorm G) (hℓ : Measurable ℓ)
    {E : Set G} (hE : MeasurableSet E) {R T : ℝ} (hR : ∀ e ∈ E, ℓ e ≤ R) :
    μ E * ρ (lengthBall ℓ (T - R)) ≤
        (∫⁻ z in lengthBall ℓ T, ρ (leftTranslate E z) ∂μ) ∧
      (∫⁻ z in lengthBall ℓ T, ρ (leftTranslate E z) ∂μ) ≤
        μ E * ρ (lengthBall ℓ (T + R)) := by
  apply average_translate_sandwich μ ρ hE
    (hℓ measurableSet_Iio) (hℓ measurableSet_Iio)
  · intro y hy z hz
    have he := hR (z⁻¹ * y) hz
    have hh := map_mul_le_add ℓ y (z⁻¹ * y)⁻¹
    rw [map_inv_eq_map] at hh
    simp only [mul_inv_rev, inv_inv, mul_inv_cancel_left] at hh
    change ℓ y < T - R at hy
    change ℓ z < T
    linarith
  · intro y z hz he
    have hh := map_mul_le_add ℓ z (z⁻¹ * y)
    rw [mul_inv_cancel_left] at hh
    have he' := hR (z⁻¹ * y) he
    change ℓ z < T at hz
    change ℓ y < T + R
    linarith

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Integrating a uniform upper bound on all translated masses. -/
theorem average_translate_le (μ ρ : Measure G) {E S : Set G}
    {a K : ℝ≥0∞} (h : ∀ z, ρ (leftTranslate E z) ≤ K * a) :
    (∫⁻ z in S, ρ (leftTranslate E z) ∂μ) ≤ K * a * μ S := by
  calc
    _ ≤ ∫⁻ _ in S, K * a ∂μ := lintegral_mono h
    _ = _ := by rw [setLIntegral_const]

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Integrating a uniform lower bound on all translated masses. -/
theorem le_mul_average_translate (μ ρ : Measure G) {E S : Set G}
    {a K : ℝ≥0∞} (hK : K ≠ ∞) (h : ∀ z, a ≤ K * ρ (leftTranslate E z)) :
    a * μ S ≤ K * (∫⁻ z in S, ρ (leftTranslate E z) ∂μ) := by
  calc
    _ = ∫⁻ _ in S, a ∂μ := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ z in S, K * ρ (leftTranslate E z) ∂μ := lintegral_mono h
    _ = _ := lintegral_const_mul' K _ hK

/-- Comparing two compact shapes needs only one finite ball of positive
measure and its volume growth bound. The radius may depend on both shapes. -/
theorem translated_mass_comparison_at_radius
    (μ ρ : Measure G) [SFinite μ] [SFinite ρ]
    [IsInvInvariant μ] [IsMulRightInvariant μ]
    (ℓ : GroupSeminorm G) (hℓ : Measurable ℓ)
    {E F : Set G} (hE : MeasurableSet E) (hF : MeasurableSet F)
    {T : ℝ} (hET : ∀ e ∈ E, ℓ e ≤ T) (hFT : ∀ f ∈ F, ℓ f ≤ T)
    {a b K D : ℝ≥0∞} (hK : K ≠ ∞)
    (ha : ∀ z, a ≤ K * ρ (leftTranslate E z))
    (hb : ∀ z, ρ (leftTranslate F z) ≤ K * b)
    (hvol0 : μ (lengthBall ℓ T) ≠ 0) (hvoltop : μ (lengthBall ℓ T) ≠ ∞)
    (hgrowth : μ (lengthBall ℓ (3 * T)) ≤ D * μ (lengthBall ℓ T)) :
    a * μ F ≤ (K * K * D) * b * μ E := by
  have h₁ := le_mul_average_translate (S := lengthBall ℓ T) μ ρ hK ha
  have h₂ := (ball_average_sandwich (T := T) μ ρ ℓ hℓ hE hET).2
  have h₃ := (ball_average_sandwich (T := 3 * T) μ ρ ℓ hℓ hF hFT).1
  have ht : 3 * T - T = T + T := by ring
  rw [ht] at h₃
  have h₄ := average_translate_le (S := lengthBall ℓ (3 * T)) μ ρ hb
  apply (ENNReal.mul_le_mul_iff_right hvol0 hvoltop).mp
  calc
    μ (lengthBall ℓ T) * (a * μ F) = μ F * (a * μ (lengthBall ℓ T)) := by ac_rfl
    _ ≤ μ F * (K * (∫⁻ z in lengthBall ℓ T, ρ (leftTranslate E z) ∂μ)) :=
      mul_le_mul_right h₁ _
    _ ≤ μ F * (K * (μ E * ρ (lengthBall ℓ (T + T)))) :=
      mul_le_mul_right (mul_le_mul_right h₂ K) _
    _ = K * μ E * (μ F * ρ (lengthBall ℓ (T + T))) := by ac_rfl
    _ ≤ K * μ E * (∫⁻ z in lengthBall ℓ (3 * T), ρ (leftTranslate F z) ∂μ) :=
      mul_le_mul_right h₃ _
    _ ≤ K * μ E * (K * b * μ (lengthBall ℓ (3 * T))) := mul_le_mul_right h₄ _
    _ = (K * K * b * μ E) * μ (lengthBall ℓ (3 * T)) := by ac_rfl
    _ ≤ (K * K * b * μ E) * (D * μ (lengthBall ℓ T)) := mul_le_mul_right hgrowth _
    _ = μ (lengthBall ℓ T) * ((K * K * D) * b * μ E) := by ac_rfl

/-- The Haar-averaging comparison, uniformly over all bounded measurable
shapes. No absolute continuity of `ρ` is assumed. The growth hypothesis is the
large-scale ball-volume bound, independent of the shapes. -/
theorem haar_averaging_comparison
    (μ ρ : Measure G) [SFinite μ] [SFinite ρ]
    [IsInvInvariant μ] [IsMulRightInvariant μ]
    (ℓ : GroupSeminorm G) (hℓ : Measurable ℓ)
    {J : Type*} (E : J → Set G) (a : J → ℝ≥0∞)
    (hE : ∀ j, MeasurableSet (E j))
    (hbounded : ∀ j, ∃ R : ℝ, ∀ e ∈ E j, ℓ e ≤ R)
    {K D : ℝ≥0∞} (hK : K ≠ ∞)
    (hlower : ∀ j z, a j ≤ K * ρ (leftTranslate (E j) z))
    (hupper : ∀ j z, ρ (leftTranslate (E j) z) ≤ K * a j)
    (hballs : ∃ T₀ : ℝ, ∀ T, T₀ ≤ T →
      μ (lengthBall ℓ T) ≠ 0 ∧ μ (lengthBall ℓ T) ≠ ∞ ∧
      μ (lengthBall ℓ (3 * T)) ≤ D * μ (lengthBall ℓ T)) :
    ∀ j k, a j * μ (E k) ≤ (K * K * D) * a k * μ (E j) := by
  intro j k
  obtain ⟨Rj, hj⟩ := hbounded j
  obtain ⟨Rk, hk⟩ := hbounded k
  obtain ⟨T₀, hT₀⟩ := hballs
  let T := max (max Rj Rk) T₀
  have hT := hT₀ T (le_max_right _ _)
  exact translated_mass_comparison_at_radius μ ρ ℓ hℓ (hE j) (hE k)
    (fun e he => (hj e he).trans ((le_max_left _ _).trans (le_max_left _ _)))
    (fun e he => (hk e he).trans ((le_max_right _ _).trans (le_max_left _ _)))
    hK (hlower j) (hupper k) hT.1 hT.2.1 hT.2.2

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- A doubling estimate gives the tripling bound used above, with the square
of the doubling constant. -/
theorem tripling_of_doubling (μ : Measure G) (ℓ : GroupSeminorm G)
    {T₀ : ℝ} (hT₀ : 0 ≤ T₀) {D : ℝ≥0∞}
    (hd : ∀ T, T₀ ≤ T → μ (lengthBall ℓ (2 * T)) ≤ D * μ (lengthBall ℓ T))
    {T : ℝ} (hT : T₀ ≤ T) :
    μ (lengthBall ℓ (3 * T)) ≤ (D * D) * μ (lengthBall ℓ T) := by
  have ht0 : 0 ≤ T := hT₀.trans hT
  have hm : lengthBall ℓ (3 * T) ⊆ lengthBall ℓ (2 * (2 * T)) := by
    intro x hx
    change ℓ x < 2 * (2 * T)
    change ℓ x < 3 * T at hx
    linarith
  calc
    _ ≤ μ (lengthBall ℓ (2 * (2 * T))) := measure_mono hm
    _ ≤ D * μ (lengthBall ℓ (2 * T)) := hd _ (by linarith)
    _ ≤ D * (D * μ (lengthBall ℓ T)) := mul_le_mul_right (hd T hT) D
    _ = _ := by rw [mul_assoc]

/-- The compact-set version used for boundary images. All geometric inputs
are explicit: a left-invariant metric and eventual Haar-volume doubling.
The measure `ρ` can be singular. -/
theorem haar_averaging_compact
    [MetricSpace G] [BorelSpace G] [IsIsometricSMul G G]
    (μ ρ : Measure G) [SFinite μ] [SFinite ρ]
    [IsInvInvariant μ] [IsMulRightInvariant μ]
    {J : Type*} (E : J → Set G) (a : J → ℝ≥0∞)
    (hE : ∀ j, IsCompact (E j)) {K D : ℝ≥0∞} (hK : K ≠ ∞)
    (hlower : ∀ j z, a j ≤ K * ρ (leftTranslate (E j) z))
    (hupper : ∀ j z, ρ (leftTranslate (E j) z) ≤ K * a j)
    (hballs : ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ T, T₀ ≤ T →
      μ (Metric.ball 1 T) ≠ 0 ∧ μ (Metric.ball 1 T) ≠ ∞ ∧
      μ (Metric.ball 1 (2 * T)) ≤ D * μ (Metric.ball 1 T)) :
    ∀ j k, a j * μ (E k) ≤ (K * K * (D * D)) * a k * μ (E j) := by
  let ℓ : GroupSeminorm G := distanceLength
  have hℓ : Continuous ℓ := continuous_const.dist continuous_id
  have hb (r : ℝ) : lengthBall ℓ r = Metric.ball 1 r := by
    ext x
    change dist 1 x < r ↔ dist x 1 < r
    rw [dist_comm]
  have hbounded : ∀ j, ∃ R : ℝ, ∀ e ∈ E j, ℓ e ≤ R := by
    intro j
    obtain ⟨R, hR⟩ := (hE j).bddAbove_image hℓ.continuousOn
    exact ⟨R, fun e he => hR (mem_image_of_mem ℓ he)⟩
  apply haar_averaging_comparison μ ρ ℓ hℓ.measurable E a
    (fun j => (hE j).measurableSet) hbounded hK hlower hupper
  obtain ⟨T₀, hT₀, hT⟩ := hballs
  refine ⟨T₀, fun T ht => ⟨?_, ?_, ?_⟩⟩
  · simpa only [hb] using (hT T ht).1
  · simpa only [hb] using (hT T ht).2.1
  · apply tripling_of_doubling μ ℓ hT₀ _ ht
    intro t ht
    simpa only [hb] using (hT t ht).2.2

end PolycyclicRecognition

end OAI
