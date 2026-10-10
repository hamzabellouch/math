import OAI.Combinatorics.BalancedRyser.Probability.PatternMarginals
import OAI.Combinatorics.BalancedRyser.Probability.PatternMomentsLemmas

namespace OAI

open MeasureTheory
open scoped BigOperators ENNReal

namespace Balanced.PatternModel
open scoped _root_.Balanced

theorem measurable_fixCoordinates_map (P : PatternModel) (K : Finset P.Color)
    (x : P.Sample) : Measurable (P.fixCoordinates K x) := by
  classical
  apply measurable_pi_iff.mpr
  intro c
  by_cases hc : c ∈ K
  · simp [fixCoordinates, hc]
  · simpa [fixCoordinates, hc] using
      (measurable_pi_apply c : Measurable (fun ω : P.Sample => ω c))

theorem lintegral_fixCoordinates_eq_lmarginal (P : PatternModel)
    (K : Finset P.Color) (x : P.Sample) (f : P.Sample → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ ω, f (P.fixCoordinates K x ω) ∂P.measure) =
      lmarginal P.law (Finset.univ \ K) f x := by
  classical
  let L := lmarginal P.law (Finset.univ \ K) f x
  have hcomp (y : P.Sample) (z : (c : ↥(Finset.univ \ K)) → P.Value c) :
      P.fixCoordinates K x (Function.updateFinset y (Finset.univ \ K) z) =
        Function.updateFinset x (Finset.univ \ K) z := by
    funext c
    by_cases hc : c ∈ K <;> simp [fixCoordinates, Function.updateFinset_def, hc]
  have hinner : lmarginal P.law (Finset.univ \ K)
      (fun ω => f (P.fixCoordinates K x ω)) = fun _ => L := by
    funext y
    simp only [lmarginal, hcomp, L]
  have hconst : lmarginal P.law (Finset.univ \ K) (fun _ : P.Sample => L) =
      fun _ => L := by
    funext y
    simp [lmarginal]
  have h := lintegral_eq_of_lmarginal_eq (Finset.univ \ K)
    (hf.comp (P.measurable_fixCoordinates_map K x)) measurable_const (hinner.trans hconst.symm)
  simpa only [measure, Function.comp_apply, lintegral_const, measure_univ, mul_one, L] using h

theorem fixCoordinates_comp (P : PatternModel) (K₀ K : Finset P.Color)
    (x y ω : P.Sample) :
    P.fixCoordinates K₀ x (P.fixCoordinates K y ω) =
      P.fixCoordinates (K₀ ∪ K) (P.fixCoordinates K₀ x y) ω := by
  classical
  funext c
  by_cases hc₀ : c ∈ K₀ <;> by_cases hc : c ∈ K <;>
    simp [fixCoordinates, hc₀, hc]

theorem fixed_moment_le_pow (P : PatternModel)
    (K₀ : Finset P.Color) (x : P.Sample) (r s : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hsupport : ∀ a, (P.support a).card ≤ r)
    (hbound : ∀ K : Finset P.Color, K.card ≤ (s - 1) * r → ∀ y,
      P.fixedExpectation (K₀ ∪ K) y P.count ≤ C) :
    P.fixedExpectation K₀ x (fun ω => P.count ω ^ s) ≤ C ^ s := by
  classical
  have hi_meas (a : P.Label) : Measurable (P.indicator a) :=
    measurable_const.indicator (P.eventMeasurable a)
  have hi_nonneg (a : P.Label) (ω : P.Sample) : 0 ≤ P.indicator a ω :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have hi_le (a : P.Label) (ω : P.Sample) : P.indicator a ω ≤ 1 := by
    simp only [indicator, Set.indicator_apply]
    split_ifs <;> norm_num
  have hc_meas : Measurable P.count :=
    Finset.measurable_sum _ (fun a _ => hi_meas a)
  have hc_nonneg (ω : P.Sample) : 0 ≤ P.count ω :=
    Finset.sum_nonneg (fun a _ => hi_nonneg a ω)
  have hc_le (ω : P.Sample) : P.count ω ≤ (Fintype.card P.Label : ℝ) := by
    calc
      P.count ω ≤ ∑ _a : P.Label, (1 : ℝ) :=
        Finset.sum_le_sum (fun a _ => hi_le a ω)
      _ = _ := by simp
  have hfixed_integrable (J : Finset P.Color) (y : P.Sample) :
      Integrable (fun ω => P.count (P.fixCoordinates J y ω)) P.measure := by
    change Integrable _ (Measure.pi P.law)
    apply Integrable.of_bound
      (hc_meas.comp (P.measurable_fixCoordinates_map J y)).aestronglyMeasurable
      (Fintype.card P.Label : ℝ)
    exact Filter.Eventually.of_forall (fun ω => by
      change ‖P.count (P.fixCoordinates J y ω)‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (hc_nonneg _)]
      exact hc_le _)
  have hresult := PatternMarginals.integral_moment_le_pow_of_marginal_bound P.law
    (fun a ω => P.indicator a (P.fixCoordinates K₀ x ω))
    (fun a => P.support a \ K₀) r s C hC
    (fun a => (hi_meas a).comp (P.measurable_fixCoordinates_map K₀ x))
    (fun a ω => hi_nonneg a _) (fun a => (Finset.card_le_card Finset.sdiff_subset).trans (hsupport a))
    (by
      intro a ω ω' hω
      have hevent := P.dependsOn a (P.fixCoordinates K₀ x ω)
        (P.fixCoordinates K₀ x ω') (by
          intro c hc
          by_cases hc₀ : c ∈ K₀
          · simp [fixCoordinates, hc₀]
          · simpa [fixCoordinates, hc₀] using
              hω c (Finset.mem_sdiff.mpr ⟨hc, hc₀⟩))
      simp only [indicator, Set.indicator_apply, hevent])
    (by
      intro K hK y
      change lmarginal P.law (Finset.univ \ K)
        (fun ω => ENNReal.ofReal (P.count (P.fixCoordinates K₀ x ω))) y ≤
          ENNReal.ofReal C
      have hFc : Measurable (fun ω => ENNReal.ofReal
          (P.count (P.fixCoordinates K₀ x ω))) :=
        (hc_meas.comp (P.measurable_fixCoordinates_map K₀ x)).ennreal_ofReal
      rw [← P.lintegral_fixCoordinates_eq_lmarginal K y _ hFc]
      simp_rw [P.fixCoordinates_comp K₀ K x y]
      rw [← ofReal_integral_eq_lintegral_ofReal
        (hfixed_integrable (K₀ ∪ K) (P.fixCoordinates K₀ x y))
        (Filter.Eventually.of_forall (fun ω => hc_nonneg _))]
      exact ENNReal.ofReal_le_ofReal (hbound K hK (P.fixCoordinates K₀ x y)))
  simpa only [fixedExpectation, measure, count] using hresult

theorem fixedExpectation_mul_le_of_fixedBounds (P : PatternModel)
    (K₀ K : Finset P.Color) (x : P.Sample)
    (F Z : P.Sample → ℝ) (C BF BZ : ℝ) (hC : 0 ≤ C)
    (hF : Measurable F) (hZ : Measurable Z)
    (hFn : ∀ ω, 0 ≤ F ω) (hZn : ∀ ω, 0 ≤ Z ω)
    (hFB : ∀ ω, F ω ≤ BF) (hZB : ∀ ω, Z ω ≤ BZ)
    (hdepends : ∀ ω ω', (∀ c ∈ K₀ ∪ K, ω c = ω' c) → F ω = F ω')
    (hbound : ∀ y, P.fixedExpectation (K₀ ∪ K) y Z ≤ C) :
    P.fixedExpectation K₀ x (fun ω => F ω * Z ω) ≤
      C * P.fixedExpectation K₀ x F := by
  have hfixed_integrable (J : Finset P.Color) (y : P.Sample)
      (G : P.Sample → ℝ) (BG : ℝ) (hG : Measurable G)
      (hGn : ∀ ω, 0 ≤ G ω) (hGB : ∀ ω, G ω ≤ BG) :
      Integrable (fun ω => G (P.fixCoordinates J y ω)) (Measure.pi P.law) := by
    apply Integrable.of_bound
      (hG.comp (P.measurable_fixCoordinates_map J y)).aestronglyMeasurable BG
    exact Filter.Eventually.of_forall (fun ω => by
      change ‖G (P.fixCoordinates J y ω)‖ ≤ BG
      rw [Real.norm_eq_abs, abs_of_nonneg (hGn _)]
      exact hGB _)
  change (∫ ω, F (P.fixCoordinates K₀ x ω) * Z (P.fixCoordinates K₀ x ω)
      ∂Measure.pi P.law) ≤ C * ∫ ω, F (P.fixCoordinates K₀ x ω) ∂Measure.pi P.law
  apply PatternMarginals.weighted_integral_le_of_marginal_bound P.law K
    (fun ω => F (P.fixCoordinates K₀ x ω))
    (fun ω => Z (P.fixCoordinates K₀ x ω)) C hC
    (hF.comp (P.measurable_fixCoordinates_map K₀ x))
    (hZ.comp (P.measurable_fixCoordinates_map K₀ x))
    (fun ω => hFn _) (fun ω => hZn _)
    (hfixed_integrable K₀ x F BF hF hFn hFB)
  · intro ω ω' hω
    apply hdepends
    intro c hc
    by_cases hc₀ : c ∈ K₀
    · simp [fixCoordinates, hc₀]
    · have hcK : c ∈ K := (Finset.mem_union.mp hc).resolve_left hc₀
      simpa [fixCoordinates, hc₀] using hω c hcK
  · intro y
    have hZc : Measurable (fun ω => ENNReal.ofReal (Z (P.fixCoordinates K₀ x ω))) :=
      (hZ.comp (P.measurable_fixCoordinates_map K₀ x)).ennreal_ofReal
    rw [← P.lintegral_fixCoordinates_eq_lmarginal K y _ hZc]
    simp_rw [P.fixCoordinates_comp K₀ K x y]
    simp only [measure]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (hfixed_integrable (K₀ ∪ K) (P.fixCoordinates K₀ x y) Z BZ hZ hZn hZB)
      (Filter.Eventually.of_forall (fun ω => hZn _))]
    exact ENNReal.ofReal_le_ofReal (hbound (P.fixCoordinates K₀ x y))

theorem fixedExpectation_positive_extension_le (P : PatternModel)
    (K₀ K : Finset P.Color) (x : P.Sample)
    (F Z : P.Sample → ℝ) (C BF BZ : ℝ) (hC : 0 ≤ C)
    (hF : Measurable F) (hZ : Measurable Z)
    (hFn : ∀ ω, 0 ≤ F ω) (hZn : ∀ ω, 0 ≤ Z ω)
    (hFB : ∀ ω, F ω ≤ BF) (hZB : ∀ ω, Z ω ≤ BZ)
    (hdepends : ∀ ω ω', (∀ c ∈ K₀ ∪ K, ω c = ω' c) → F ω = F ω')
    (hbound : ∀ y, P.fixedExpectation (K₀ ∪ K) y Z ≤ C) :
    P.fixedExpectation K₀ x
        (fun ω => F ω * (Z ω + P.fixedExpectation K₀ x Z)) ≤
      (2 * C) * P.fixedExpectation K₀ x F := by
  have hmean : P.fixedExpectation K₀ x Z ≤ C := by
    have h := P.fixedExpectation_mul_le_of_fixedBounds K₀ K x
      (fun _ => 1) Z C 1 BZ hC measurable_const hZ
      (fun _ => zero_le_one) hZn (fun _ => le_rfl) hZB
      (by intros; rfl) hbound
    simpa [fixedExpectation, measure] using h
  have hmean_nonneg : 0 ≤ P.fixedExpectation K₀ x Z :=
    integral_nonneg (fun ω => hZn _)
  have hZi (J : Finset P.Color) (y : P.Sample) :
      Integrable (fun ω => Z (P.fixCoordinates J y ω)) (Measure.pi P.law) := by
    apply Integrable.of_bound
      (hZ.comp (P.measurable_fixCoordinates_map J y)).aestronglyMeasurable BZ
    exact Filter.Eventually.of_forall (fun ω => by
      change ‖Z (P.fixCoordinates J y ω)‖ ≤ BZ
      rw [Real.norm_eq_abs, abs_of_nonneg (hZn _)]
      exact hZB _)
  apply P.fixedExpectation_mul_le_of_fixedBounds K₀ K x F
    (fun ω => Z ω + P.fixedExpectation K₀ x Z)
    (2 * C) BF (BZ + P.fixedExpectation K₀ x Z) (mul_nonneg (by norm_num) hC)
    hF (hZ.add measurable_const) hFn
    (fun ω => add_nonneg (hZn ω) hmean_nonneg) hFB
    (fun ω => add_le_add (hZB ω) le_rfl) hdepends
  intro y
  have hadd : P.fixedExpectation (K₀ ∪ K) y
        (fun ω => Z ω + P.fixedExpectation K₀ x Z) =
      P.fixedExpectation (K₀ ∪ K) y Z + P.fixedExpectation K₀ x Z := by
    unfold fixedExpectation
    simp only [measure]
    rw [integral_add (hZi (K₀ ∪ K) y) (integrable_const _)]
    simp
  rw [hadd]
  linarith [hbound y]

end Balanced.PatternModel

namespace Balanced
open scoped _root_.Balanced

theorem uniformPatternMoments_of_totalBound
    (P : ℕ → PatternModel) (K₀ : ∀ q, Finset (P q).Color)
    (hsupport : UniformPatternSupports P)
    (hbound : UniformPatternTotalBound P K₀ (fun _ => 1)) :
    UniformPatternMoments P K₀ := by
  obtain ⟨r, hr⟩ := hsupport
  intro s _hs
  obtain ⟨C, hC, q₀, hq₀⟩ := hbound ((s - 1) * r)
  refine ⟨C ^ s, pow_pos hC s, q₀, ?_⟩
  intro q hq x
  apply (P q).fixed_moment_le_pow (K₀ q) x r s C hC.le (hr q)
  intro K hK y
  simpa only [mul_one] using hq₀ q hq K hK y

end Balanced

end OAI
