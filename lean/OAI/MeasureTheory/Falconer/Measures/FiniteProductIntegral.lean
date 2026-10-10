import OAI.MeasureTheory.Falconer.Angular.FiniteAngularSquare

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem bounded_circle_pair_integral_measurable
    (F : ℝ × (UnitCircle × UnitCircle) → ℂ) (hF : Measurable F) :
    Measurable (fun r => ∫ u, ∫ w, F (r,(u,w)) ∂sourceArcLength ∂sourceArcLength) := by
  have h : Measurable (fun p : (ℝ × UnitCircle) × UnitCircle => F (p.1.1,(p.1.2,p.2))) :=
    hF.comp (by fun_prop)
  exact h.stronglyMeasurable.integral_prod_right'.measurable.stronglyMeasurable.integral_prod_right'.measurable

theorem bounded_circle_pair_integral_norm
    (F : ℝ × (UnitCircle × UnitCircle) → ℂ) {C : ℝ}
    (hb : ∀ p, ‖F p‖ ≤ C) (r : ℝ) :
    ‖∫ u, ∫ w, F (r,(u,w)) ∂sourceArcLength ∂sourceArcLength‖ ≤
      (C*sourceArcLength.real univ)*sourceArcLength.real univ := by
  apply norm_integral_le_of_norm_le_const
  filter_upwards with u
  exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall (fun w => hb (r,(u,w))))

theorem bounded_original_integral_sum {ι : Type*} (S : Finset ι)
    (F : ι → ℝ × (UnitCircle × UnitCircle) → ℂ)
    (hF : ∀ i ∈ S, Measurable (F i)) (C : ι → ℝ)
    (hC : ∀ i ∈ S, 0 ≤ C i) (hb : ∀ i ∈ S, ∀ p, ‖F i p‖ ≤ C i)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, |Ψ t| ≤ W) {R : ℝ} (hR : 0 < R) :
    (∫ r : ℝ, ∫ u, ∫ w, Ψ (r/R) • (∑ i ∈ S, F i (r,(u,w)))
      ∂sourceArcLength ∂sourceArcLength) =
    ∑ i ∈ S, ∫ r : ℝ, ∫ u, ∫ w, Ψ (r/R) • F i (r,(u,w))
      ∂sourceArcLength ∂sourceArcLength := by
  have hi (i : ι) (hi : i ∈ S) (r : ℝ) (u : UnitCircle) :
      Integrable (fun w => F i (r,(u,w))) sourceArcLength :=
    Integrable.of_bound ((hF i hi).comp (by fun_prop)).aestronglyMeasurable (C i)
      (Filter.Eventually.of_forall (fun w => hb i hi (r,(u,w))))
  have hj (i : ι) (hi : i ∈ S) (r : ℝ) :
      Integrable (fun u => ∫ w, F i (r,(u,w)) ∂sourceArcLength) sourceArcLength := by
    have hm : Measurable (fun p : UnitCircle × UnitCircle => F i (r,p)) :=
      (hF i hi).comp (by fun_prop)
    apply Integrable.of_bound hm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      (C i*sourceArcLength.real univ)
    filter_upwards with u
    exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall (fun w => hb i hi (r,(u,w))))
  have hk (i : ι) (hi : i ∈ S) :
      Integrable (fun r => Ψ (r/R) • (∫ u, ∫ w, F i (r,(u,w)) ∂sourceArcLength ∂sourceArcLength)) :=
    bounded_shell_integrable hΨ hs hW hw hR _
      (bounded_circle_pair_integral_measurable (F i) (hF i hi)).aestronglyMeasurable
      (mul_nonneg (mul_nonneg (hC i hi) measureReal_nonneg) measureReal_nonneg)
      (bounded_circle_pair_integral_norm (F i) (hb i hi))
  simp_rw [integral_smul]
  have he (r : ℝ) :
      (∫ u, ∫ w, ∑ i ∈ S, F i (r,(u,w)) ∂sourceArcLength ∂sourceArcLength) =
      ∑ i ∈ S, ∫ u, ∫ w, F i (r,(u,w)) ∂sourceArcLength ∂sourceArcLength := by
    simp_rw [integral_finsetSum S (fun i hi' => hi i hi' r _)]
    exact integral_finsetSum S (fun i hi' => hj i hi' r)
  simp_rw [he,Finset.smul_sum]
  exact integral_finsetSum S hk

end PlanarFalconer

end OAI
