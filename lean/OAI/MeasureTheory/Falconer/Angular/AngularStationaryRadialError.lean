import OAI.MeasureTheory.Falconer.Angular.AngularOriginalIntegrability
import OAI.MeasureTheory.Falconer.Graphs.ParentRetainedEnergy

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem angularPairCircleIntegral_norm_le (β : Plane → UnitCircle → ℂ)
    (x y : Plane) {C : ℝ} (hC : 0 ≤ C)
    (hx : ∀ u, ‖β x u‖ ≤ C) (hy : ∀ u, ‖β y u‖ ≤ C) (r : ℝ) :
    ‖angularPairCircleIntegral β x y r‖ ≤ sourceArcLength.real univ*C^2 := by
  rw [mul_comm]
  apply norm_integral_le_of_norm_le_const
  filter_upwards with u
  simp only [norm_mul,sourcePlaneWave_norm,one_mul,Complex.norm_conj]
  simpa only [pow_two] using mul_le_mul (hx u) (hy u) (norm_nonneg _) hC

theorem angularPairCircleIntegral_measurable (β : Plane → UnitCircle → ℂ)
    (hβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2)) (x y : Plane) :
    Measurable (angularPairCircleIntegral β x y) := by
  have hm : Measurable (fun p : ℝ × UnitCircle =>
      sourcePlaneWave p.1 p.2 (x-y)*(β x p.2*conj (β y p.2))) := by
    apply (sourcePlaneWave_continuous (x-y)).measurable.mul
    apply Measurable.mul
    · exact hβ.comp (measurable_const.prodMk measurable_snd)
    · exact Complex.continuous_conj.measurable.comp
        (hβ.comp (measurable_const.prodMk measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem fullCircleStationaryExpansion_measurable (f : ℝ → ℂ) (n : ℕ) :
    Measurable (fun Λ => fullCircleStationaryExpansion Λ f n) := by
  unfold fullCircleStationaryExpansion fresnelCoefficient stationaryDerivativeExpansion
  fun_prop

theorem complex_product_replacement_bound (A B E F : ℂ) {C ε : ℝ}
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C)
    (hE : ‖A-E‖ ≤ ε) (hF : ‖B-F‖ ≤ ε) :
    ‖A*B-E*F‖ ≤ ε*(2*C+ε) := by
  have he : ‖E‖ ≤ C+ε := by
    have ht := norm_add_le A (E-A)
    rw [add_sub_cancel,norm_sub_rev E A] at ht
    exact ht.trans (add_le_add hA hE)
  calc
    _ = ‖(A-E)*B+E*(B-F)‖ := by congr 1; ring
    _ ≤ ‖A-E‖*‖B‖+‖E‖*‖B-F‖ := by simpa only [norm_mul] using norm_add_le ((A-E)*B) (E*(B-F))
    _ ≤ ε*C+(C+ε)*ε := by gcongr
    _ = _ := by ring

theorem angular_radial_product_replacement (v : ℝ) {Ψ : ℝ → ℝ}
    (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W)
    (A B E F : ℝ → ℂ) (hmA : Measurable A) (hmB : Measurable B)
    (hmE : Measurable E) (hmF : Measurable F)
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hA : ∀ r, ‖A r‖ ≤ C) (hB : ∀ r, ‖B r‖ ≤ C)
    (hE : ∀ r, Ψ (r/(2:ℝ)^v) ≠ 0 → ‖A r-E r‖ ≤ ε)
    (hF : ∀ r, Ψ (r/(2:ℝ)^v) ≠ 0 → ‖B r-F r‖ ≤ ε) :
    ‖((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) • (A r*B r)) -
      ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) • (E r*F r))‖ ≤
      4*W*(ε*(2*C+ε)) := by
  have hz : ∀ t ≤ 0, Ψ t = 0 := by
    intro t ht
    by_contra hn
    have := (hs t hn).1
    linarith
  have hupper : ∀ t, 4 < t → Ψ t = 0 := by
    intro t ht
    by_contra hn
    exact (not_lt_of_ge (hs t hn).2.le) ht
  let μ := sourceAngularShellMeasure v Ψ
  let : IsFiniteMeasure μ := sourceAngularShellMeasure_finite v Ψ hW hw hupper
  have hae := sourceAngularShellMeasure_ae_nonzero v Ψ hΨ
  have he : ∀ᵐ r ∂μ, ‖E r‖ ≤ C+ε := by
    filter_upwards [hae] with r hr
    have ht := norm_add_le (A r) (E r-A r)
    rw [add_sub_cancel,norm_sub_rev (E r) (A r)] at ht
    exact ht.trans (add_le_add (hA r) (hE r hr))
  have hf : ∀ᵐ r ∂μ, ‖F r‖ ≤ C+ε := by
    filter_upwards [hae] with r hr
    have ht := norm_add_le (B r) (F r-B r)
    rw [add_sub_cancel,norm_sub_rev (F r) (B r)] at ht
    exact ht.trans (add_le_add (hB r) (hF r hr))
  have hiAB : Integrable (fun r => A r*B r) μ :=
    Integrable.of_bound (hmA.mul hmB).aestronglyMeasurable (C*C)
      (Filter.Eventually.of_forall (fun r => by rw [norm_mul]; exact mul_le_mul (hA r) (hB r) (norm_nonneg _) hC))
  have hiEF : Integrable (fun r => E r*F r) μ := by
    apply Integrable.of_bound (hmE.mul hmF).aestronglyMeasurable ((C+ε)*(C+ε))
    filter_upwards [he,hf] with r her hfr
    change ‖E r*F r‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul her hfr (norm_nonneg _) (add_nonneg hC hε)
  rw [← sourceAngularShellMeasure_integral v hΨ hpos hz,
    ← sourceAngularShellMeasure_integral v hΨ hpos hz,← integral_sub hiAB hiEF]
  apply (norm_integral_le_of_norm_le_const (show ∀ᵐ r ∂μ,
    ‖A r*B r-E r*F r‖ ≤ ε*(2*C+ε) from by
      filter_upwards [hae] with r hr
      exact complex_product_replacement_bound _ _ _ _ hC hε (hA r) (hB r) (hE r hr) (hF r hr))).trans
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right
    (sourceAngularShellMeasure_real_mass_le v Ψ hW hw hupper)
    (show 0 ≤ ε*(2*C+ε) by positivity)

end PlanarFalconer

end OAI
