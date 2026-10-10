import OAI.MeasureTheory.Falconer.Estimates.SpatialSharedBound
import OAI.MeasureTheory.Falconer.Fourier.AllDimensionalSpatialFourierSeparation

namespace OAI

/-! # Uniform independent-angle control removes the spatial Fourier variable

The spatial coefficient pays its squared L1 norm. All exchanges of the
radial and spatial integrations follow from bounded measurable endpoint
families and the finite original shell measure.
-/

namespace Falconer
open Set MeasureTheory
open scoped ComplexConjugate

noncomputable def spatialSharedAmplitude {d : ℕ} (c : Space d → ℂ)
    (U V : Space d × (ℝ × Sphere d) → ℂ) (r : ℝ) : ℂ :=
  ∫ w : Sphere d, (∫ ξ : Space d, c ξ*(U (ξ,(r,w))*star (V (ξ,(r,w)))))
    ∂sphereMeasure d

theorem spatialSharedAmplitude_measurable {d : ℕ} (c : Space d → ℂ)
    (hcm : Measurable c) (U V : Space d × (ℝ × Sphere d) → ℂ)
    (hU : Measurable U) (hV : Measurable V) :
    Measurable (spatialSharedAmplitude c U V) := by
  have hUV : Measurable (fun p : (ℝ × Sphere d) × Space d =>
      c p.2*(U (p.2,p.1)*star (V (p.2,p.1)))) :=
    (hcm.comp measurable_snd).mul ((hU.comp measurable_swap).mul
      (continuous_star.measurable.comp (hV.comp measurable_swap)))
  exact hUV.stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable

theorem spatial_shared_shell_le {d : ℕ} (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (c : Space d → ℂ) (hcm : Measurable c) (hc : Integrable c)
    (U V : Space d × (ℝ × Sphere d) → ℂ) (hU : Measurable U) (hV : Measurable V)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbU : ∀ z, ‖U z‖ ≤ B) (hbV : ∀ z, ‖V z‖ ≤ C)
    (E : ℝ) (hE : ∀ ξ : Space d, independentAngularEnergy a v Ψ
      (fun p => U (ξ,p)) (fun p => V (ξ,p)) ≤ E) :
    (2 : ℝ)^((d : ℝ)*(v-a)) *
      (∫ r : ℝ, ‖spatialSharedAmplitude c U V r‖^2
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤
      (∫ ξ : Space d, ‖c ξ‖)^2*E := by
  let μ := PlanarFalconer.sourceAngularShellMeasure v Ψ
  let ℓ := ∫ ξ : Space d, ‖c ξ‖
  let N := (2 : ℝ)^((d : ℝ)*(v-a))
  let G : Space d × ℝ → ℝ := fun p =>
    sphereMoment (fun z => U (p.1,z)) p.2 * sphereMoment (fun z => V (p.1,z)) p.2
  let I : ℝ → ℝ := fun r => ∫ ξ : Space d, ‖c ξ‖*G (ξ,r)
  have hℓ : 0 ≤ ℓ := integral_nonneg (fun _ => norm_nonneg _)
  have hN : 0 ≤ N := Real.rpow_nonneg (by norm_num) _
  have hU' : Measurable (fun p : (Space d × ℝ) × Sphere d => U (p.1.1,(p.1.2,p.2))) :=
    hU.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hV' : Measurable (fun p : (Space d × ℝ) × Sphere d => V (p.1.1,(p.1.2,p.2))) :=
    hV.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hGm : Measurable G :=
    (hU'.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable.mul
      (hV'.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  have hG0 : ∀ p, 0 ≤ G p := fun p => mul_nonneg
    (sphereMoment_nonneg _ _) (sphereMoment_nonneg _ _)
  let K := (B^2*(sphereMeasure d).real univ)*(C^2*(sphereMeasure d).real univ)
  have hGb (p : Space d × ℝ) : G p ≤ K :=
    mul_le_mul (sphereMoment_le (fun z => U (p.1,z)) hB (fun z => hbU (p.1,z)) p.2)
      (sphereMoment_le (fun z => V (p.1,z)) hC (fun z => hbV (p.1,z)) p.2)
      (sphereMoment_nonneg _ _) (by positivity)
  have hi : Integrable (fun p : Space d × ℝ => ‖c p.1‖*G p) (volume.prod μ) := by
    apply ((hc.norm.comp_fst μ).mul_const K).mono'
      ((hcm.norm.comp measurable_fst).mul hGm).aestronglyMeasurable
    filter_upwards with p
    change ‖‖c p.1‖*G p‖ ≤ ‖c p.1‖*K
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (hG0 p))]
    exact mul_le_mul_of_nonneg_left (hGb p) (norm_nonneg _)
  have hIi : Integrable I μ := hi.integral_prod_right
  have hpoint (r : ℝ) : ‖spatialSharedAmplitude c U V r‖^2 ≤ ℓ*I r := by
    exact spatial_shared_integral_sq_le c hcm hc
      (fun p => U (p.1,(r,p.2))) (fun p => V (p.1,(r,p.2)))
      (hU.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
      (hV.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
      hB hC (fun p => hbU (p.1,(r,p.2))) (fun p => hbV (p.1,(r,p.2)))
  have hFi : Integrable (fun r => ‖spatialSharedAmplitude c U V r‖^2) μ := by
    apply (hIi.const_mul ℓ).mono'
      ((spatialSharedAmplitude_measurable c hcm U V hU hV).norm.pow_const 2).aestronglyMeasurable
    filter_upwards with r
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact hpoint r
  have hswap : (∫ r, I r ∂μ) = ∫ ξ : Space d, ‖c ξ‖*(∫ r, G (ξ,r) ∂μ) := by
    simpa only [I,integral_const_mul] using
      (integral_integral_swap (f := fun ξ r => ‖c ξ‖*G (ξ,r)) hi).symm
  have hQi : Integrable (fun ξ : Space d => ‖c ξ‖*(∫ r, G (ξ,r) ∂μ)) := by
    simpa only [integral_const_mul] using hi.integral_prod_left
  have hbound : N*(∫ r, I r ∂μ) ≤ ℓ*E := by
    rw [hswap,← integral_const_mul]
    calc
      _ ≤ ∫ ξ : Space d, ‖c ξ‖*E :=
        integral_mono (hQi.const_mul N) (hc.norm.mul_const E) (fun ξ => by
          have he := mul_le_mul_of_nonneg_left (hE ξ) (norm_nonneg (c ξ))
          change N*(‖c ξ‖*(∫ r, G (ξ,r) ∂μ)) ≤ ‖c ξ‖*E
          have hid : N*(‖c ξ‖*(∫ r, G (ξ,r) ∂μ)) =
              ‖c ξ‖*independentAngularEnergy a v Ψ (fun p => U (ξ,p)) (fun p => V (ξ,p)) := by
            dsimp only [independentAngularEnergy,N,G,μ]
            ring
          rw [hid]
          exact he)
      _ = ℓ*E := integral_mul_const E _
  change N*(∫ r, ‖spatialSharedAmplitude c U V r‖^2 ∂μ) ≤ ℓ^2*E
  calc
    _ ≤ N*(∫ r, ℓ*I r ∂μ) := mul_le_mul_of_nonneg_left
      (integral_mono hFi (hIi.const_mul ℓ) hpoint) hN
    _ = ℓ*(N*(∫ r, I r ∂μ)) := by rw [integral_const_mul]; ring
    _ ≤ ℓ*(ℓ*E) := mul_le_mul_of_nonneg_left hbound hℓ
    _ = _ := by ring

theorem spatial_fourier_shared_shell_le {d : ℕ} (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ℕ)
    (U V : Space d × (ℝ × Sphere d) → ℂ) (hU : Measurable U) (hV : Measurable V)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbU : ∀ z, ‖U z‖ ≤ B) (hbV : ∀ z, ‖V z‖ ≤ C)
    (E : ℝ) (hE : ∀ ξ : Space d, independentAngularEnergy a v Ψ
      (fun p => U (ξ,p)) (fun p => V (ξ,p)) ≤ E) :
    (2 : ℝ)^((d : ℝ)*(v-a)) *
      (∫ r : ℝ, ‖spatialSharedAmplitude (spatialFourierCoeff δ L hδ hL j) U V r‖^2
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤
      (spatialFourierCost (d := d) δ L hδ hL j)^2*E :=
  spatial_shared_shell_le a v Ψ (spatialFourierCoeff δ L hδ hL j)
    (spatialFourierCoeff (d := d) δ L hδ hL j).continuous.measurable
    (spatialFourierCoeff_integrable δ L hδ hL j) U V hU hV hB hC hbU hbV E hE

end Falconer

end OAI
