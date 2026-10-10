import OAI.MeasureTheory.Falconer.Graphs.GraphSpatialFubini

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def graphOriginalKernel (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ) (Ψ : ℝ → ℝ) (R : ℝ)
    (p : ℝ × (UnitCircle × UnitCircle)) (x : Fin 4 → Plane) : ℂ :=
  Ψ (p.1/R) • graphFourKernel b W x p.1 p.2.1 p.2.2

theorem graphOriginalKernel_measurable
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2)) (hW : Measurable W)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (R : ℝ) :
    Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      graphOriginalKernel b W Ψ R p.1 p.2) := by
  unfold graphOriginalKernel
  simp only [Complex.real_smul]
  apply Measurable.mul
  · fun_prop
  · exact graphFourKernel_measurable b W hb hW

theorem graphOriginalKernel_norm_le
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (hw : ∀ p, ‖W p‖ ≤ 1) {Ψ : ℝ → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) (R : ℝ)
    (p : ℝ × (UnitCircle × UnitCircle)) (x : Fin 4 → Plane) :
    ‖graphOriginalKernel b W Ψ R p x‖ ≤ C*((B 0*B 1)*(B 2*B 3)) := by
  simp only [graphOriginalKernel, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (hc _) (graphFourKernel_norm_le b W B hB hbound hw x _ _ _)
    (norm_nonneg _) hC

theorem graphOriginalKernel_integrable
    (μ : Measure (Fin 4 → Plane)) [IsFiniteMeasure μ]
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2)) (hW : Measurable W)
    (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (hw : ∀ p, ‖W p‖ ≤ 1) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) {R : ℝ} (hR : 0 < R) :
    Integrable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      graphOriginalKernel b W Ψ R p.1 p.2)
      ((volume.prod (sourceArcLength.prod sourceArcLength)).prod μ) := by
  have hK : IsCompact (Icc (R/4) (4*R) ×ˢ (univ : Set (UnitCircle × UnitCircle))) :=
    isCompact_Icc.prod isCompact_univ
  apply compact_finite_spatial_integrable _ μ hK.measurableSet hK.measure_lt_top
    (graphOriginalKernel_measurable b W hb hW hΨ R)
    (mul_nonneg hC (mul_nonneg (mul_nonneg (hB 0) (hB 1)) (mul_nonneg (hB 2) (hB 3))))
  · intro p
    exact graphOriginalKernel_norm_le b W B hB hbound hw hC hc R p.1 p.2
  · intro p hp
    have hn : Ψ (p.1.1/R) ≠ 0 := by
      intro hz; exact hp (by simp [graphOriginalKernel, hz])
    have hh := hsupp _ hn
    refine ⟨⟨?_,?_⟩,mem_univ _⟩
    · have := (lt_div_iff₀ hR).mp hh.1; linarith
    · have := (div_lt_iff₀ hR).mp hh.2; linarith

theorem circle_pair_integral (F : UnitCircle × UnitCircle → ℂ)
    (hF : Measurable F) {C : ℝ} (hb : ∀ p, ‖F p‖ ≤ C) :
    (∫ p, F p ∂sourceArcLength.prod sourceArcLength) =
      ∫ u, ∫ v, F (u,v) ∂sourceArcLength ∂sourceArcLength :=
  integral_prod _ (Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall hb))

theorem graphOriginalKernel_spatial_swap
    (μ : Measure (Fin 4 → Plane)) [IsFiniteMeasure μ]
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2)) (hW : Measurable W)
    (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (hw : ∀ p, ‖W p‖ ≤ 1) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) {R : ℝ} (hR : 0 < R) :
    (∫ r : ℝ, ∫ u, ∫ v, ∫ x, graphOriginalKernel b W Ψ R (r,(u,v)) x ∂μ
      ∂sourceArcLength ∂sourceArcLength) =
      ∫ x, ∫ r : ℝ, ∫ u, ∫ v, graphOriginalKernel b W Ψ R (r,(u,v)) x
        ∂sourceArcLength ∂sourceArcLength ∂volume ∂μ := by
  let G := graphOriginalKernel b W Ψ R
  have hg := graphOriginalKernel_measurable b W hb hW hΨ R
  have hd := graphOriginalKernel_norm_le b W B hB hbound hw hC hc R
  have hi := graphOriginalKernel_integrable μ b W hb hW B hB hbound hw hΨ hsupp hC hc hR
  have hslice (x : Fin 4 → Plane) : Integrable (fun p => G p x)
      (volume.prod (sourceArcLength.prod sourceArcLength)) := by
    have hh := graphOriginalKernel_integrable (Measure.dirac x) b W hb hW B hB hbound hw
      hΨ hsupp hC hc hR
    have he := hh.integral_prod_left
    simpa only [integral_dirac] using he
  have hcircle (r : ℝ) :
      (∫ p, ∫ x, G (r,p) x ∂μ ∂sourceArcLength.prod sourceArcLength) =
        ∫ u, ∫ v, ∫ x, G (r,(u,v)) x ∂μ ∂sourceArcLength ∂sourceArcLength := by
    have hm : Measurable (fun p : (UnitCircle × UnitCircle) × (Fin 4 → Plane) => G (r,p.1) p.2) :=
      hg.comp (show Measurable (fun p : (UnitCircle × UnitCircle) × (Fin 4 → Plane) =>
        ((r,p.1),p.2)) from by fun_prop)
    exact circle_pair_integral _ hm.stronglyMeasurable.integral_prod_right'.measurable
      (fun p => norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall (hd (r,p))))
  calc
    _ = ∫ r : ℝ, ∫ p, ∫ x, G (r,p) x ∂μ ∂sourceArcLength.prod sourceArcLength := by
      simp_rw [hcircle]
      rfl
    _ = ∫ p, ∫ x, G p x ∂μ ∂volume.prod (sourceArcLength.prod sourceArcLength) :=
      (integral_prod _ hi.integral_prod_left).symm
    _ = ∫ x, ∫ p, G p x ∂volume.prod (sourceArcLength.prod sourceArcLength) ∂μ :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [integral_prod _ (hslice x)]
      apply integral_congr_ae
      filter_upwards with r
      exact circle_pair_integral _
        (hg.comp (show Measurable (fun p : UnitCircle × UnitCircle => ((r,p),x)) from by fun_prop))
        (fun p => hd (r,p) x)

end PlanarFalconer

end OAI
