import OAI.MeasureTheory.Falconer.Angular.AngularProductEnergyIntegral

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem product_moment_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (U V : ℝ × UnitCircle → ℂ) (hU : Measurable U) (hV : Measurable V)
    {C D : ℝ} (_hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hbU : ∀ x, ‖U x‖ ≤ C) (hbV : ∀ x, ‖V x‖ ≤ D) :
    Integrable (fun r => sourceRealAngularMoment U r * sourceRealAngularMoment V r) μ := by
  apply Integrable.of_bound
    ((sourceRealAngularMoment_measurable U hU).mul (sourceRealAngularMoment_measurable V hV)).aestronglyMeasurable
    ((C^2*sourceArcLength.real univ)*(D^2*sourceArcLength.real univ))
  filter_upwards with r
  change ‖sourceRealAngularMoment U r * sourceRealAngularMoment V r‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sourceRealAngularMoment_nonneg U r)
    (sourceRealAngularMoment_nonneg V r))]
  exact mul_le_mul (sourceRealAngularMoment_bound U hbU r) (sourceRealAngularMoment_bound V hbV r)
    (sourceRealAngularMoment_nonneg V r) (by positivity)

theorem circle_pair_schur_bound {ι : Type*} (S : Finset ι)
    (U V : ι → ℝ × UnitCircle → ℂ)
    (hU : ∀ i ∈ S, Measurable (U i)) (hV : ∀ i ∈ S, Measurable (V i))
    (C D : ι → ℝ) (hC : ∀ i ∈ S, 0 ≤ C i) (hD : ∀ i ∈ S, 0 ≤ D i)
    (hbU : ∀ i ∈ S, ∀ x, ‖U i x‖ ≤ C i) (hbV : ∀ i ∈ S, ∀ x, ‖V i x‖ ≤ D i)
    (F : ℝ × (UnitCircle × UnitCircle) → ℂ) {d : ℝ} (_hd : 0 ≤ d)
    (hb : ∀ r u w, ‖F (r,(u,w))‖ ≤ d * ∑ i ∈ S, ‖U i (r,u)‖^2*‖V i (r,w)‖^2)
    (r : ℝ) :
    ‖∫ u, ∫ w, F (r,(u,w)) ∂sourceArcLength ∂sourceArcLength‖ ≤
      d * ∑ i ∈ S, sourceRealAngularMoment (U i) r * sourceRealAngularMoment (V i) r := by
  have hiU (i : ι) (hi : i ∈ S) := integrable_circle_norm_square (fun u => U i (r,u))
    ((hU i hi).comp (measurable_const.prodMk measurable_id)) (hC i hi) (fun u => hbU i hi (r,u))
  have hiV (i : ι) (hi : i ∈ S) := integrable_circle_norm_square (fun w => V i (r,w))
    ((hV i hi).comp (measurable_const.prodMk measurable_id)) (hD i hi) (fun w => hbV i hi (r,w))
  have inner (u : UnitCircle) :
      ‖∫ w, F (r,(u,w)) ∂sourceArcLength‖ ≤
        d * ∑ i ∈ S, ‖U i (r,u)‖^2 * sourceRealAngularMoment (V i) r := by
    have hi : Integrable (fun w => d * ∑ i ∈ S, ‖U i (r,u)‖^2*‖V i (r,w)‖^2) sourceArcLength :=
      (integrable_finsetSum S (fun i hi => (hiV i hi).const_mul _)).const_mul d
    have he := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall (hb r u))
    simpa only [integral_const_mul,integral_finsetSum S (fun i hi => (hiV i hi).const_mul _),
      sourceRealAngularMoment] using he
  have hi : Integrable (fun u => d * ∑ i ∈ S, ‖U i (r,u)‖^2*sourceRealAngularMoment (V i) r) sourceArcLength :=
    (integrable_finsetSum S (fun i hi => (hiU i hi).mul_const _)).const_mul d
  have he := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall inner)
  simpa only [integral_const_mul,integral_finsetSum S (fun i hi => (hiU i hi).mul_const _),
    integral_mul_const,sourceRealAngularMoment] using he

theorem original_product_schur_integral {ι : Type*} (S : Finset ι)
    (U V : ι → ℝ × UnitCircle → ℂ)
    (hU : ∀ i ∈ S, Measurable (U i)) (hV : ∀ i ∈ S, Measurable (V i))
    (C D : ι → ℝ) (hC : ∀ i ∈ S, 0 ≤ C i) (hD : ∀ i ∈ S, 0 ≤ D i)
    (hbU : ∀ i ∈ S, ∀ x, ‖U i x‖ ≤ C i) (hbV : ∀ i ∈ S, ∀ x, ‖V i x‖ ≤ D i)
    (F : ℝ × (UnitCircle × UnitCircle) → ℂ) {d : ℝ} (hd : 0 ≤ d)
    (hb : ∀ r u w, ‖F (r,(u,w))‖ ≤ d * ∑ i ∈ S, ‖U i (r,u)‖^2*‖V i (r,w)‖^2)
    (p v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    ‖((2:ℝ)^(2*(v-p))) • (((2:ℝ)^v)⁻¹ •
      ∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) • F (r,(u,w)) ∂sourceArcLength ∂sourceArcLength)‖ ≤
      d * ∑ i ∈ S, (sourceAngularH p v Ψ (U i) (V i)).toReal := by
  let := sourceAngularShellMeasure_finite v Ψ hW hw (fun t ht => by
    by_contra hn
    have := (hs t hn).2
    linarith)
  have hzero : ∀ t ≤ 0, Ψ t = 0 := by
    intro t ht
    by_contra hn
    have := (hs t hn).1
    linarith
  have hi (i : ι) (hi : i ∈ S) := product_moment_integrable (sourceAngularShellMeasure v Ψ)
    (U i) (V i) (hU i hi) (hV i hi) (hC i hi) (hD i hi) (hbU i hi) (hbV i hi)
  have hh := norm_integral_le_of_norm_le
    ((integrable_finsetSum S hi).const_mul d)
    (Filter.Eventually.of_forall (circle_pair_schur_bound S U V hU hV C D hC hD hbU hbV F hd hb))
  have he (i : ι) (hi : i ∈ S) := (sourceAngularH_finite_integral p v Ψ
    (U i) (V i) (hU i hi) (hV i hi) (hC i hi) (hD i hi) (hbU i hi) (hbV i hi)).2
  simp_rw [integral_smul]
  rw [← sourceAngularShellMeasure_integral v hΨ hpos hzero]
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (2:ℝ)^(2*(v-p)))]
  calc
    _ ≤ (2:ℝ)^(2*(v-p)) * (∫ r, d * ∑ i ∈ S,
        sourceRealAngularMoment (U i) r * sourceRealAngularMoment (V i) r ∂sourceAngularShellMeasure v Ψ) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum S hi]
      simp_rw [Finset.sum_congr rfl he]
      rw [← Finset.mul_sum]
      ring

end PlanarFalconer

end OAI
