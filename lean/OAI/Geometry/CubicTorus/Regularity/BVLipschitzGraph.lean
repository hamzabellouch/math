import Mathlib
import OAI.Geometry.CubicTorus.Reflection.BVScaledFlux

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma trapped_characteristic {U : Set Torus} {c : Torus} {n x : Cover}
    {r ε : ℝ} (hr : 0 < r) (hrsmall : r < 1 / 2) (_hε : 0 ≤ ε)
    (htrap : normalCap c n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap c (-n) r (ε * r) ⊆ U)
    (hx : ‖x‖ < 1) (hstrip : ε < |⟪n, x⟫|) :
    characteristic U (quotientMap (r • x) + c) = halfspaceIndicator n x := by
  have hnorm : ‖r • x‖ < r := by
    rw [norm_smul, Real.norm_of_nonneg hr.le]
    nlinarith
  have hsl : shortestLift ((quotientMap (r • x) + c) - c) = r • x := by
    rw [add_sub_cancel_right]
    exact shortestLift_quotientMap (hnorm.trans hrsmall)
  have hd : dist (quotientMap (r • x) + c) c < r := by
    rw [dist_eq_norm, ← norm_shortestLift, hsl]
    exact hnorm
  by_cases hneg : ⟪n, x⟫ < 0
  · have hm : quotientMap (r • x) + c ∈ U := by
      apply htrap.2
      refine ⟨hd, ?_⟩
      rw [hsl, inner_neg_left, inner_smul_right]
      rw [abs_of_neg hneg] at hstrip
      nlinarith [mul_lt_mul_of_pos_right hstrip hr]
    simp [characteristic, halfspaceIndicator, hm, hneg]
  · have hm : quotientMap (r • x) + c ∉ U := by
      have hh : quotientMap (r • x) + c ∈ (closure U)ᶜ := by
        apply htrap.1
        refine ⟨hd, ?_⟩
        rw [hsl, inner_smul_right]
        rw [abs_of_nonneg (le_of_not_gt hneg)] at hstrip
        nlinarith [mul_lt_mul_of_pos_right hstrip hr]
      exact fun h ↦ hh (subset_closure h)
    simp [characteristic, halfspaceIndicator, hm, hneg]

theorem normalMeasure_trapped_projection {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {a n : Cover} (hn : ‖n‖ = 1) {r ε : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : 0 ≤ ε)
    (hc : Metric.closedBall a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    (htrap : normalCap (quotientMap a) n r (ε * r) ⊆ (closure E)ᶜ ∧
      normalCap (quotientMap a) (-n) r (ε * r) ⊆ E)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ ⊆ Metric.ball (0 : Cover) 1)
    (hstrip : ∀ x, |⟪n, x⟫| ≤ ε → fderiv ℝ ψ x n = 0) :
    (∫ z, ψ (r⁻¹ • ((z.1 : Cover) - a)) * ⟪(z.2 : Cover), n⟫
      ∂(μ : Measure NormalBundle)) / r ^ 2 =
      ∫ y : Plane, ψ (normalPlaneEmbedding n y) := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ ψ x • n) := hψ.smul_const n
  have hsF : tsupport (fun x ↦ ψ x • n) ⊆ Metric.ball (0 : Cover) 1 :=
    (tsupport_smul_subset_left (f := ψ) (g := fun _ ↦ n)).trans hs
  have hf := normalMeasure_scaled_flux hE hμ hF
    (hsF.trans Metric.ball_subset_closedBall) a hr hc
  simp only [inner_smul_right] at hf
  rw [hf, ← integral_plane_coordinates,
    ← integral_halfspace_flux hn hψ (hs.trans Metric.ball_subset_closedBall)]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ tsupport (fun x ↦ ψ x • n)
  · by_cases hm : |⟪n, x⟫| ≤ ε
    · rw [divergence_smul_const (hψ.differentiable (by simp)).differentiableAt, hstrip x hm]
      simp
    · have he := trapped_characteristic hr hrsmall hε htrap
        (show ‖x‖ < 1 by simpa using hsF hx) (lt_of_not_ge hm)
      rw [quotientMap_add]
      exact congrArg (fun t : ℝ ↦ t * divergence (fun x ↦ ψ x • n) x) he
  · rw [divergence_of_notMem_tsupport hx]
    simp

lemma unit_normal_sq_distance {ν n : Cover} (hν : ‖ν‖ = 1) (hn : ‖n‖ = 1) :
    ‖ν - n‖ ^ 2 = 2 * (1 - ⟪ν, n⟫) := by
  rw [norm_sub_sq_real, hν, hn]
  ring

theorem normalMeasure_trapped_excess {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {a n : Cover} (hn : ‖n‖ = 1) {r ε : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : 0 ≤ ε)
    (hc : Metric.closedBall a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    (htrap : normalCap (quotientMap a) n r (ε * r) ⊆ (closure E)ᶜ ∧
      normalCap (quotientMap a) (-n) r (ε * r) ⊆ E)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ ⊆ Metric.ball (0 : Cover) 1)
    (hstrip : ∀ x, |⟪n, x⟫| ≤ ε → fderiv ℝ ψ x n = 0) :
    (∫ z, ψ (r⁻¹ • ((z.1 : Cover) - a)) ∂(μ : Measure NormalBundle)) / r ^ 2 -
      (∫ y : Plane, ψ (normalPlaneEmbedding n y)) =
      (∫ z, ψ (r⁻¹ • ((z.1 : Cover) - a)) * ‖(z.2 : Cover) - n‖ ^ 2
        ∂(μ : Measure NormalBundle)) / (2 * r ^ 2) := by
  have hp := normalMeasure_trapped_projection hE hμ hn hr hrsmall hε hc htrap hψ hs hstrip
  let f : NormalBundle → ℝ := fun z ↦ ψ (r⁻¹ • ((z.1 : Cover) - a))
  have hf : Continuous f := hψ.continuous.comp
    ((continuous_subtype_val.comp continuous_fst).sub continuous_const |>.const_smul r⁻¹)
  have hfi : Integrable f (μ : Measure NormalBundle) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hν : Continuous (fun z : NormalBundle ↦ ⟪(z.2 : Cover), n⟫) :=
    (continuous_subtype_val.comp continuous_snd).inner continuous_const
  have hgi : Integrable (fun z : NormalBundle ↦ f z * ⟪(z.2 : Cover), n⟫)
      (μ : Measure NormalBundle) :=
    (hf.mul hν).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (z : NormalBundle) :
      f z * ‖(z.2 : Cover) - n‖ ^ 2 = 2 * (f z - f z * ⟪(z.2 : Cover), n⟫) := by
    rw [unit_normal_sq_distance (by simpa using z.2.property) hn]
    ring
  change _ - _ = (∫ z, f z * ‖(z.2 : Cover) - n‖ ^ 2 ∂(μ : Measure NormalBundle)) / _
  simp_rw [he]
  rw [integral_const_mul, integral_sub hfi hgi, ← hp]
  dsimp [f]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma gradient_of_notMem_tsupport {ψ : Cover → ℝ} {x : Cover}
    (hx : x ∉ tsupport ψ) : gradient ψ x = 0 := by
  simp [gradient, fderiv_of_notMem_tsupport ℝ hx]

lemma gradient_tsupport_subset (ψ : Cover → ℝ) :
    tsupport (gradient ψ) ⊆ tsupport ψ := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hh
  exact hx (gradient_of_notMem_tsupport hh)

theorem normalMeasure_local_laplacian {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    (∫ x : Cover, characteristic E (quotientMap x) * divergence (gradient ψ) x) =
      ∫ z, fderiv ℝ ψ z.1 (z.2 : Cover) ∂(μ : Measure NormalBundle) := by
  have hf := normalMeasure_local_flux hE hμ (gradient_contDiff hψ)
    (hc.of_isClosed_subset isClosed_closure (gradient_tsupport_subset ψ))
    ((gradient_tsupport_subset ψ).trans hs)
  simpa [inner_gradient_right] using hf.symm

theorem weakCMC_scalar_residual_identity {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {n : Cover} (hn : ‖n‖ = 1)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    (∫ x : Cover, characteristic E (quotientMap x) * divergence (gradient ψ) x) -
      (∫ z, fderiv ℝ ψ z.1 n ∂(μ : Measure NormalBundle)) +
      H * (∫ z, ψ z.1 * ⟪(z.2 : Cover), n⟫ ∂(μ : Measure NormalBundle)) =
      (1 / 2 : ℝ) * ∫ z, ‖(z.2 : Cover) - n‖ ^ 2 * fderiv ℝ ψ z.1 (z.2 : Cover)
        ∂(μ : Measure NormalBundle) := by
  have hx : Continuous (fun z : NormalBundle ↦ (z.1 : Cover)) :=
    continuous_subtype_val.comp continuous_fst
  have hν : Continuous (fun z : NormalBundle ↦ (z.2 : Cover)) :=
    continuous_subtype_val.comp continuous_snd
  have hd := (hψ.continuous_fderiv (by simp)).comp hx
  have hB : Integrable (fun z : NormalBundle ↦ fderiv ℝ ψ z.1 (z.2 : Cover)) (μ : Measure NormalBundle) :=
    (hd.clm_apply hν).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hD : Integrable (fun z : NormalBundle ↦ fderiv ℝ ψ z.1 n) (μ : Measure NormalBundle) :=
    (hd.clm_apply continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hA : Integrable (fun z : NormalBundle ↦ ⟪(z.2 : Cover), n⟫ * fderiv ℝ ψ z.1 (z.2 : Cover))
      (μ : Measure NormalBundle) :=
    ((hν.inner continuous_const).mul (hd.clm_apply hν)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hF := hψ.smul_const n
  have hFs := tsupport_smul_subset_left (f := ψ) (g := fun _ ↦ n)
  have hvar := weakCMC_local_identity hμ hH hF
    (hc.of_isClosed_subset isClosed_closure hFs) (hFs.trans hs)
  have he (z : NormalBundle) : tangentialDivergence (fun x ↦ ψ x • n) z.1 z.2 =
      fderiv ℝ ψ z.1 n - ⟪(z.2 : Cover), n⟫ * fderiv ℝ ψ z.1 (z.2 : Cover) := by
    rw [tangentialDivergence_smul_const ((hψ.differentiable (by simp)) _)]
    simp only [tangentPart, map_sub, map_smul, smul_eq_mul]
  simp_rw [he, inner_smul_right] at hvar
  rw [integral_sub hD hA] at hvar
  have herr (z : NormalBundle) :
      ‖(z.2 : Cover) - n‖ ^ 2 * fderiv ℝ ψ z.1 (z.2 : Cover) =
      2 * (fderiv ℝ ψ z.1 (z.2 : Cover) -
        ⟪(z.2 : Cover), n⟫ * fderiv ℝ ψ z.1 (z.2 : Cover)) := by
    rw [unit_normal_sq_distance z.2.property hn]
    ring
  simp_rw [herr]
  rw [integral_const_mul, integral_sub hB hA, normalMeasure_local_laplacian hE hμ hψ hc hs]
  linarith

theorem weakCMC_scalar_residual_bound {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {n : Cover} (hn : ‖n‖ = 1)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {w : NormalBundle → ℝ} (hw : Integrable w (μ : Measure NormalBundle))
    (hb : ∀ᵐ z ∂(μ : Measure NormalBundle), ‖fderiv ℝ ψ z.1‖ * ‖(z.2 : Cover) - n‖ ^ 2 ≤ w z) :
    |(∫ x : Cover, characteristic E (quotientMap x) * divergence (gradient ψ) x) -
      (∫ z, fderiv ℝ ψ z.1 n ∂(μ : Measure NormalBundle)) +
      H * (∫ z, ψ z.1 * ⟪(z.2 : Cover), n⟫ ∂(μ : Measure NormalBundle))| ≤
      (1 / 2 : ℝ) * ∫ z, w z ∂(μ : Measure NormalBundle) := by
  rw [weakCMC_scalar_residual_identity hE hμ hH hn hψ hc hs, abs_mul]
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le hw
  filter_upwards [hb] with z hz
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  have hd : |fderiv ℝ ψ z.1 (z.2 : Cover)| ≤ ‖fderiv ℝ ψ z.1‖ := by
    simpa only [Real.norm_eq_abs, z.2.property, mul_one] using
      (fderiv ℝ ψ z.1).le_opNorm (z.2 : Cover)
  exact (mul_le_mul_of_nonneg_left hd (sq_nonneg _)).trans (by simpa only [mul_comm] using hz)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalMeasure_frontier_ae {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∀ᵐ z ∂(μ : Measure NormalBundle), quotientMap z.1 ∈ frontier E := by
  have hh : ∀ᵐ c ∂(spatialNormalMeasure μ : Measure Torus), c ∈ frontier E := by
    filter_upwards [Measure.support_mem_ae (μ := (spatialNormalMeasure μ : Measure Torus))] with c hc
    have hc' := spatialNormalMeasure_support_subset_boundary hE hμ hc
    rw [frontier_eq_closure_inter_closure]
    exact ⟨Measure.support_restrict_subset.trans inter_subset_left hc'.1,
      Measure.support_restrict_subset.trans inter_subset_left hc'.2⟩
  change ∀ᵐ c ∂Measure.map normalProjection (μ : Measure NormalBundle), c ∈ frontier E at hh
  exact (ae_map_iff normalProjection_continuous.measurable.aemeasurable
    (show MeasurableSet {c : Torus | c ∈ frontier E} from isClosed_frontier.measurableSet)).mp hh

lemma trapped_frontier_height {E : Set Torus} (hE : IsOpen E)
    {a n x : Cover} {r ε : ℝ} (hrsmall : r < 1 / 2)
    (htrap : normalCap (quotientMap a) n r (ε * r) ⊆ (closure E)ᶜ ∧
      normalCap (quotientMap a) (-n) r (ε * r) ⊆ E)
    (hx : x ∈ Metric.ball a r) (hb : quotientMap x ∈ frontier E) :
    |⟪n, x - a⟫| ≤ ε * r := by
  have hl : shortestLift (quotientMap x - quotientMap a) = x - a := by
    rw [← quotientMap_sub]
    exact shortestLift_quotientMap ((show ‖x - a‖ < r by simpa only [Metric.mem_ball, dist_eq_norm] using hx).trans hrsmall)
  have hd : dist (quotientMap x) (quotientMap a) < r := by
    rw [dist_eq_norm, ← norm_shortestLift, hl]
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  apply abs_le.mpr
  constructor
  · by_contra! hh
    have hmem := htrap.2 (show quotientMap x ∈ normalCap (quotientMap a) (-n) r (ε * r) from
      ⟨hd, by rw [hl, inner_neg_left]; linarith⟩)
    rw [frontier, hE.interior_eq] at hb
    exact hb.2 hmem
  · by_contra! hh
    have hnot := htrap.1 (show quotientMap x ∈ normalCap (quotientMap a) n r (ε * r) from
      ⟨hd, by simpa only [hl] using hh⟩)
    exact hnot (frontier_subset_closure hb)

theorem normalMeasure_trapped_test_derivative_zero {E : Set Torus} (hE : IsOpen E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {a n : Cover} {r ε : ℝ} (hrsmall : r < 1 / 2)
    (htrap : normalCap (quotientMap a) n r (ε * r) ⊆ (closure E)ᶜ ∧
      normalCap (quotientMap a) (-n) r (ε * r) ⊆ E)
    {ψ : Cover → ℝ} (hs : tsupport ψ ⊆ Metric.ball a r)
    (hstrip : ∀ x, |⟪n, x - a⟫| ≤ ε * r → fderiv ℝ ψ x n = 0) :
    ∀ᵐ z ∂(μ : Measure NormalBundle), fderiv ℝ ψ z.1 n = 0 := by
  filter_upwards [normalMeasure_frontier_ae hE.measurableSet hμ] with z hz
  by_cases hsupp : (z.1 : Cover) ∈ tsupport ψ
  · exact hstrip _ (trapped_frontier_height hE hrsmall htrap (hs hsupp) hz)
  · rw [fderiv_of_notMem_tsupport ℝ hsupp]
    rfl

theorem weakCMC_trapped_scalar_identity {E : Set Torus} (hE : IsOpen E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {a n : Cover} (hn : ‖n‖ = 1) {r ε : ℝ} (hrsmall : r < 1 / 2)
    (htrap : normalCap (quotientMap a) n r (ε * r) ⊆ (closure E)ᶜ ∧
      normalCap (quotientMap a) (-n) r (ε * r) ⊆ E)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ ⊆ Metric.ball a r)
    (hcell : Metric.closedBall a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    (hstrip : ∀ x, |⟪n, x - a⟫| ≤ ε * r → fderiv ℝ ψ x n = 0) :
    (∫ x : Cover, characteristic E (quotientMap x) * divergence (gradient ψ) x) +
      H * (∫ z, ψ z.1 * ⟪(z.2 : Cover), n⟫ ∂(μ : Measure NormalBundle)) =
      (1 / 2 : ℝ) * ∫ z, ‖(z.2 : Cover) - n‖ ^ 2 * fderiv ℝ ψ z.1 (z.2 : Cover)
        ∂(μ : Measure NormalBundle) := by
  have hc : HasCompactSupport ψ := (isCompact_closedBall a r).of_isClosed_subset isClosed_closure
    (hs.trans Metric.ball_subset_closedBall)
  have hi := weakCMC_scalar_residual_identity hE.measurableSet hμ hH hn hψ hc
    (hs.trans (Metric.ball_subset_closedBall.trans hcell))
  have hz : (∫ z, fderiv ℝ ψ z.1 n ∂(μ : Measure NormalBundle)) = 0 :=
    integral_eq_zero_of_ae (normalMeasure_trapped_test_derivative_zero hE hμ hrsmall htrap hs hstrip)
  simpa only [hz, sub_zero] using hi

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma good_scales_boundary_cone {E B : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {D δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ a ∈ B, ∀ t : ℝ, 0 < t → t ≤ D →
      δ * t ^ 3 ≤ torusVolume.real (E ∩ Metric.ball a t) ∧
      δ * t ^ 3 ≤ torusVolume.real (Eᶜ ∩ Metric.ball a t))
    {c : Torus} (hc : c ∈ B) {n : Cover} (hnorm : ‖n‖ = 1)
    {R ε : ℝ} (hRsmall : R ≤ 1 / 32) (hRD : 2 * R ≤ D) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hgood : ∀ s : ℝ, 0 < s → s ≤ 16 * R →
      131072 * normalOscillation (spatialNormalMeasure μ) N c n s < δ ^ 2 * (ε / 8) ^ 6) :
    ∀ y ∈ B, dist y c ≤ R → |⟪n, shortestLift (y - c)⟫| ≤ ε * dist y c := by
  intro y hy hyr
  by_cases hyc : y = c
  · subst y
    have hz : shortestLift (0 : Torus) = 0 := shortestLift_eq_of_lift rfl (by norm_num)
    simp only [sub_self, hz, inner_zero_right, abs_zero, dist_self, mul_zero, le_refl]
  have hdpos : 0 < dist y c := dist_pos.mpr hyc
  let r := 2 * dist y c
  let t := ε * dist y c / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrsmall : r ≤ 1 / 16 := by dsimp [r]; linarith
  have ht : 0 < t := by dsimp [t]; positivity
  have htr : t ≤ r := by dsimp [t, r]; nlinarith
  have htD : t ≤ D := htr.trans (by dsimp [r]; linarith)
  have har : dist c c < r := by simpa only [dist_self] using hr
  have hbr : dist y c < r := by dsimp [r]; linarith
  have hquot : t / r = ε / 8 := by dsimp [t, r]; field_simp; norm_num
  have hos := hgood (8 * r) (by positivity) (by dsimp [r]; linarith)
  have hforbid : ∀ a ∈ B, dist a c < r → ∀ b ∈ B, dist b c < r →
      ¬ 2 * t ≤ ⟪n, shortestLift (b - a)⟫ := by
    intro a ha har b hb hbr hh
    have hp := ordered_density_normal_oscillation hE hμ hN hpolar hn hnorm hr hrsmall ht htr hδ
      har hbr (hd a ha t ht htD).2 (hd b hb t ht htD).1 hh
    rw [hquot] at hp
    exact (not_lt_of_ge hp) hos
  have hupper := lt_of_not_ge (hforbid c hc har y hy hbr)
  have hlower := lt_of_not_ge (hforbid y hy hbr c hc har)
  have he : shortestLift (c - y) = -shortestLift (y - c) := by
    apply shortestLift_eq_of_lift
    · rw [quotientMap_neg, quotientMap_shortestLift]; abel
    · rw [norm_neg, norm_shortestLift, ← dist_eq_norm]; linarith
  rw [he, inner_neg_right] at hlower
  have habs : |⟪n, shortestLift (y - c)⟫| < 2 * t := abs_lt.mpr ⟨by linarith, hupper⟩
  exact habs.le.trans (by dsimp [t]; nlinarith)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalPlaneProjection (n v : Cover) : Cover := v - ⟪n, v⟫ • n

lemma normalPlaneProjection_sub (n v w : Cover) :
    normalPlaneProjection n (v - w) = normalPlaneProjection n v - normalPlaneProjection n w := by
  simp only [normalPlaneProjection, inner_sub_right, sub_smul]
  abel

lemma normalPlaneProjection_inner {n : Cover} (hn : ‖n‖ = 1) (v : Cover) :
    ⟪n, normalPlaneProjection n v⟫ = 0 := by
  simp only [normalPlaneProjection, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hn]
  ring

lemma norm_le_two_normalPlaneProjection {n v : Cover} (hn : ‖n‖ = 1)
    {ε : ℝ} (hε : ε ≤ 1 / 2) (hc : |⟪n, v⟫| ≤ ε * ‖v‖) :
    ‖v‖ ≤ 2 * ‖normalPlaneProjection n v‖ := by
  have hh := norm_add_le (normalPlaneProjection n v) (⟪n, v⟫ • n)
  rw [show normalPlaneProjection n v + ⟪n, v⟫ • n = v by simp [normalPlaneProjection],
    norm_smul, hn, mul_one, Real.norm_eq_abs] at hh
  nlinarith [norm_nonneg v]

lemma exists_lipschitz_height_of_cone (S : Set Cover) {n : Cover} (hn : ‖n‖ = 1)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hc : ∀ x ∈ S, ∀ y ∈ S, |⟪n, x - y⟫| ≤ ε * ‖x - y‖) :
    ∃ g : Cover → ℝ, LipschitzWith ⟨2 * ε, by positivity⟩ g ∧
      ∀ x ∈ S, g (normalPlaneProjection n x) = ⟪n, x⟫ := by
  classical
  by_cases hnon : S.Nonempty
  swap
  · refine ⟨fun _ ↦ 0, ?_, ?_⟩
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [dist_self]
      change (0 : ℝ) ≤ 2 * ε * dist x y
      positivity
    simp only [not_nonempty_iff_eq_empty.mp hnon, mem_empty_iff_false, false_implies, implies_true]
  let : Nonempty S := hnon.to_subtype
  let F : S → Cover := fun x ↦ normalPlaneProjection n x.1
  have hF : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    have hh := norm_le_two_normalPlaneProjection hn hε (hc x x.property y y.property)
    rw [normalPlaneProjection_sub, show normalPlaneProjection n x.1 = normalPlaneProjection n y.1 from hxy,
      sub_self, norm_zero, mul_zero] at hh
    exact hh
  let height : Cover → ℝ := fun z ↦ ⟪n, ((Function.invFun F z).1 : Cover)⟫
  have hheight : LipschitzOnWith ⟨2 * ε, by positivity⟩ height (range F) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have hx := Function.leftInverse_invFun hF x
    have hy := Function.leftInverse_invFun hF y
    dsimp only [height]
    rw [hx, hy]
    change |⟪n, (x : Cover)⟫ - ⟪n, (y : Cover)⟫| ≤ (2 * ε) * ‖normalPlaneProjection n x - normalPlaneProjection n y‖
    rw [← inner_sub_right]
    have hnorm := norm_le_two_normalPlaneProjection hn hε (hc x x.property y y.property)
    have hm := mul_le_mul_of_nonneg_left hnorm hε0
    rw [normalPlaneProjection_sub] at hm
    exact (hc x x.property y y.property).trans (by nlinarith [hm])
  obtain ⟨g, hg, hgeq⟩ := hheight.extend_real
  refine ⟨g, hg, ?_⟩
  intro x hx
  have hh := hgeq (show F ⟨x, hx⟩ ∈ range F from mem_range_self _)
  simpa only [F, height, Function.leftInverse_invFun hF ⟨x, hx⟩] using hh.symm

lemma lifted_cone_of_torus_cone {S : Set Torus} {a : Torus} {n : Cover} {ε : ℝ}
    (hS : S ⊆ Metric.ball a (1 / 4))
    (hc : ∀ x ∈ S, ∀ y ∈ S, |⟪n, shortestLift (x - y)⟫| ≤ ε * dist x y) :
    ∀ x ∈ (fun z ↦ shortestLift (z - a)) '' S,
      ∀ y ∈ (fun z ↦ shortestLift (z - a)) '' S, |⟪n, x - y⟫| ≤ ε * ‖x - y‖ := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  have hr : dist x a + dist y a < 1 / 2 := by
    have hxl : dist x a < 1 / 4 := hS hx
    have hyl : dist y a < 1 / 4 := hS hy
    linarith
  rw [← shortestLift_sub_local hr, norm_shortestLift, ← dist_eq_norm]
  exact hc x hx y hy

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma ediam_metricBall_le (a : Torus) {r : ℝ} (_hr : 0 ≤ r) :
    ediam (Metric.ball a r) ≤ ENNReal.ofReal (2 * r) := by
  apply Metric.ediam_le_of_forall_dist_le
  intro x hx y hy
  have hh := dist_triangle_right x y a
  exact hh.trans (by linarith [Metric.mem_ball.mp hx, Metric.mem_ball.mp hy])

lemma hausdorff_two_le_of_lower_density (σ : FiniteMeasure Torus) (S : Set Torus)
    {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hl : ∀ a ∈ S, ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 2 ≤ (σ : Measure Torus).real (Metric.ball a r)) :
    Measure.hausdorffMeasure 2 S ≤ ENNReal.ofReal (64 / c) * (σ : Measure Torus) univ := by
  let r : ℕ → ℝ := fun n ↦ R / ((n : ℝ) + 1)
  have hr (n) : 0 < r n := by dsimp [r]; positivity
  have hrR (n) : r n ≤ R := by
    dsimp [r]
    exact div_le_self hR.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hr0 : Tendsto r atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := R)).mul tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [mul_zero, mul_one_div] using hh
  have hex (n : ℕ) := Vitali.exists_disjoint_subfamily_covering_enlargement_ball S id
    (fun _ ↦ r n) (r n) (fun _ _ ↦ le_rfl) 4 (by norm_num)
  choose u hu hdis hcov using hex
  have hcount (n) : (u n).Countable :=
    (hdis n).countable_of_isOpen (fun _ _ ↦ Metric.isOpen_ball)
      (fun a _ ↦ ⟨a, Metric.mem_ball_self (hr n)⟩)
  let : ∀ n, Countable (u n) := fun n ↦ (hcount n).to_subtype
  let t (n : ℕ) (a : u n) : Set Torus := Metric.ball (a : Torus) (4 * r n)
  have hdiam (n : ℕ) (a : u n) : ediam (t n a) ≤ ENNReal.ofReal (8 * r n) := by
    simpa only [t, show (2 : ℝ) * (4 * r n) = 8 * r n by ring] using
      ediam_metricBall_le (a : Torus) (show 0 ≤ 4 * r n by positivity)
  have hcover (n) : S ⊆ ⋃ a : u n, t n a := by
    intro a ha
    obtain ⟨b, hb, hsub⟩ := hcov n a ha
    exact mem_iUnion.mpr ⟨⟨b, hb⟩, hsub (Metric.mem_ball_self (hr n))⟩
  have hstep (n : ℕ) (a : u n) : ediam (t n a) ^ (2 : ℝ) ≤
      ENNReal.ofReal (64 / c) * (σ : Measure Torus) (Metric.ball (a : Torus) (r n)) := by
    have hlow := hl a (hu n a.property) (r n) (hr n) (hrR n)
    have hb : ENNReal.ofReal (c * r n ^ 2) ≤
        (σ : Measure Torus) (Metric.ball (a : Torus) (r n)) :=
      (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 hlow
    calc
      _ = ediam (t n a) ^ (2 : ℕ) := ENNReal.rpow_two _
      _ ≤ (ENNReal.ofReal (8 * r n)) ^ (2 : ℕ) := pow_le_pow_left' (hdiam n a) _
      _ = ENNReal.ofReal (64 / c) * ENNReal.ofReal (c * r n ^ 2) := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring
      _ ≤ _ := mul_le_mul_right hb _
  have hsum (n : ℕ) : (∑' a : u n, ediam (t n a) ^ (2 : ℝ)) ≤
      ENNReal.ofReal (64 / c) * (σ : Measure Torus) univ := by
    calc
      _ ≤ ∑' a : u n, ENNReal.ofReal (64 / c) *
          (σ : Measure Torus) (Metric.ball (a : Torus) (r n)) := ENNReal.tsum_le_tsum (hstep n)
      _ = ENNReal.ofReal (64 / c) *
          (∑' a : u n, (σ : Measure Torus) (Metric.ball (a : Torus) (r n))) := by
        rw [ENNReal.tsum_mul_left]
      _ = ENNReal.ofReal (64 / c) *
          (σ : Measure Torus) (⋃ a ∈ u n, Metric.ball a (r n)) := by
        congr 1
        exact (measure_biUnion (hcount n) (hdis n)
          (fun _ _ ↦ Metric.isOpen_ball.measurableSet)).symm
      _ ≤ _ := mul_le_mul_right (measure_mono (subset_univ _)) _
  have hlim : Tendsto (fun n ↦ ENNReal.ofReal (8 * r n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hr0.const_mul 8)
  have hh := Measure.hausdorffMeasure_le_liminf_tsum 2 S
    (fun n ↦ ENNReal.ofReal (8 * r n)) hlim t
    (Eventually.of_forall hdiam) (Eventually.of_forall hcover)
  exact hh.trans (liminf_le_of_frequently_le' (Eventually.of_forall hsum).frequently)

theorem isMinimizerAt_finite_boundary_area {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    Measure.hausdorffMeasure 2 (frontier (openRepresentative E)) < ⊤ := by
  obtain ⟨μ, hmass, hflux⟩ := exists_normalMeasure hE hmin.1.2.ne
  have hμ : IsNormalMeasure E μ := ⟨hmass, hflux⟩
  obtain ⟨R, c, hR, hc, hl⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  have hh := hausdorff_two_le_of_lower_density (spatialNormalMeasure μ)
    (volumeSupport E ∩ volumeSupport Eᶜ) hR hc (hl μ hμ)
  rw [isMinimizerAt_frontier_openRepresentative hV hE hmin]
  exact hh.trans_lt (by finiteness)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma hausdorff_two_le_open_of_lower_density (σ : FiniteMeasure Torus) (S U : Set Torus)
    (hU : IsOpen U) (hSU : S ⊆ U) {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hl : ∀ a ∈ S, ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 2 ≤ (σ : Measure Torus).real (Metric.ball a r)) :
    Measure.hausdorffMeasure 2 S ≤ ENNReal.ofReal (64 / c) * (σ : Measure Torus) U := by
  classical
  let r : ℕ → ℝ := fun n ↦ R / ((n : ℝ) + 1)
  have hr (n) : 0 < r n := by dsimp [r]; positivity
  have hrR (n) : r n ≤ R := by
    dsimp [r]
    exact div_le_self hR.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hr0 : Tendsto r atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := R)).mul tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [mul_zero, mul_one_div] using hh
  have heps : ∀ a ∈ S, ∃ e : ℝ, 0 < e ∧ Metric.ball a e ⊆ U := by
    intro a ha
    exact Metric.isOpen_iff.mp hU a (hSU ha)
  choose e he heU using heps
  let rad (n : ℕ) (a : Torus) : ℝ := if ha : a ∈ S then min (r n) (e a ha) else r n
  have hrad (n : ℕ) (a : Torus) (ha : a ∈ S) : 0 < rad n a := by
    simp only [rad, dite_eq_left ha]
    exact lt_min (hr n) (he a ha)
  have hradle (n : ℕ) (a : Torus) : rad n a ≤ r n := by
    by_cases ha : a ∈ S
    · simp only [rad, dite_eq_left ha]; exact min_le_left _ _
    · simp only [rad, dite_eq_right ha]; exact le_rfl
  have hradU (n : ℕ) (a : Torus) (ha : a ∈ S) : Metric.ball a (rad n a) ⊆ U := by
    apply (Metric.ball_subset_ball ?_).trans (heU a ha)
    simp only [rad, dite_eq_left ha]
    exact min_le_right _ _
  have hex (n : ℕ) := Vitali.exists_disjoint_subfamily_covering_enlargement_ball S id
    (rad n) (r n) (fun a _ ↦ hradle n a) 4 (by norm_num)
  choose u hu hdis hcov using hex
  have hcount (n) : (u n).Countable :=
    (hdis n).countable_of_isOpen (fun _ _ ↦ Metric.isOpen_ball)
      (fun a ha ↦ ⟨a, Metric.mem_ball_self (hrad n a (hu n ha))⟩)
  let : ∀ n, Countable (u n) := fun n ↦ (hcount n).to_subtype
  let t (n : ℕ) (a : u n) : Set Torus := Metric.ball (a : Torus) (4 * rad n a)
  have hdiam' (n : ℕ) (a : u n) : ediam (t n a) ≤ ENNReal.ofReal (8 * rad n a) := by
    simpa only [t, show (2 : ℝ) * (4 * rad n a) = 8 * rad n a by ring] using
      ediam_metricBall_le (a : Torus) (show 0 ≤ 4 * rad n a from by
        have hh := hrad n a (hu n a.property); positivity)
  have hdiam (n : ℕ) (a : u n) : ediam (t n a) ≤ ENNReal.ofReal (8 * r n) :=
    (hdiam' n a).trans (ENNReal.ofReal_le_ofReal (by nlinarith [hradle n a]))
  have hcover (n) : S ⊆ ⋃ a : u n, t n a := by
    intro a ha
    obtain ⟨b, hb, hsub⟩ := hcov n a ha
    exact mem_iUnion.mpr ⟨⟨b, hb⟩, hsub (Metric.mem_ball_self (hrad n a ha))⟩
  have hstep (n : ℕ) (a : u n) : ediam (t n a) ^ (2 : ℝ) ≤
      ENNReal.ofReal (64 / c) * (σ : Measure Torus) (Metric.ball (a : Torus) (rad n a)) := by
    have hrpos := hrad n a (hu n a.property)
    have hlow := hl a (hu n a.property) (rad n a) hrpos ((hradle n a).trans (hrR n))
    have hb : ENNReal.ofReal (c * rad n a ^ 2) ≤
        (σ : Measure Torus) (Metric.ball (a : Torus) (rad n a)) :=
      (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 hlow
    calc
      _ = ediam (t n a) ^ (2 : ℕ) := ENNReal.rpow_two _
      _ ≤ (ENNReal.ofReal (8 * rad n a)) ^ (2 : ℕ) := pow_le_pow_left' (hdiam' n a) _
      _ = ENNReal.ofReal (64 / c) * ENNReal.ofReal (c * rad n a ^ 2) := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring
      _ ≤ _ := mul_le_mul_right hb _
  have hsum (n : ℕ) : (∑' a : u n, ediam (t n a) ^ (2 : ℝ)) ≤
      ENNReal.ofReal (64 / c) * (σ : Measure Torus) U := by
    calc
      _ ≤ ∑' a : u n, ENNReal.ofReal (64 / c) *
          (σ : Measure Torus) (Metric.ball (a : Torus) (rad n a)) := ENNReal.tsum_le_tsum (hstep n)
      _ = ENNReal.ofReal (64 / c) *
          (∑' a : u n, (σ : Measure Torus) (Metric.ball (a : Torus) (rad n a))) := by
        rw [ENNReal.tsum_mul_left]
      _ = ENNReal.ofReal (64 / c) *
          (σ : Measure Torus) (⋃ a ∈ u n, Metric.ball a (rad n a)) := by
        congr 1
        exact (measure_biUnion (hcount n) (hdis n)
          (fun _ _ ↦ Metric.isOpen_ball.measurableSet)).symm
      _ ≤ _ := mul_le_mul_right (measure_mono (by
        intro x hx
        obtain ⟨a, ha, hx⟩ := mem_iUnion₂.mp hx
        exact hradU n a (hu n ha) hx)) _
  have hlim : Tendsto (fun n ↦ ENNReal.ofReal (8 * r n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hr0.const_mul 8)
  have hh := Measure.hausdorffMeasure_le_liminf_tsum 2 S
    (fun n ↦ ENNReal.ofReal (8 * r n)) hlim t
    (Eventually.of_forall hdiam) (Eventually.of_forall hcover)
  exact hh.trans (liminf_le_of_frequently_le' (Eventually.of_forall hsum).frequently)

lemma hausdorff_two_le_measure_of_lower_density (σ : FiniteMeasure Torus) (S : Set Torus)
    {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hl : ∀ a ∈ S, ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 2 ≤ (σ : Measure Torus).real (Metric.ball a r)) :
    Measure.hausdorffMeasure 2 S ≤ ENNReal.ofReal (64 / c) * (σ : Measure Torus) S := by
  have h0 : ENNReal.ofReal (64 / c) ≠ 0 := by positivity
  rw [S.measure_eq_iInf_isOpen (σ : Measure Torus),
    ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  apply le_iInf
  intro U
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  apply le_iInf
  intro hSU
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  exact le_iInf fun hU ↦ hausdorff_two_le_open_of_lower_density σ S U hU hSU hR hc hl

lemma hausdorff_two_null_of_lower_density (σ : FiniteMeasure Torus) (B : Set Torus)
    {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hl : ∀ a ∈ B, ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 2 ≤ (σ : Measure Torus).real (Metric.ball a r))
    {S : Set Torus} (hSB : S ⊆ B) (hS : (σ : Measure Torus) S = 0) :
    Measure.hausdorffMeasure 2 S = 0 := by
  have hh := hausdorff_two_le_measure_of_lower_density σ S hR hc
    (fun a ha ↦ hl a (hSB ha))
  rw [hS, mul_zero] at hh
  exact le_zero_iff.mp hh

theorem isMinimizerAt_boundary_area_absolutelyContinuous {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    (Measure.hausdorffMeasure 2).restrict (frontier (openRepresentative E)) ≪
      (spatialNormalMeasure μ : Measure Torus) := by
  obtain ⟨R, c, hR, hc, hl⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  intro S hS
  rw [Measure.restrict_apply₀' isClosed_frontier.measurableSet.nullMeasurableSet]
  apply hausdorff_two_null_of_lower_density (spatialNormalMeasure μ)
    (volumeSupport E ∩ volumeSupport Eᶜ) hR hc (hl μ hμ)
  · rw [← isMinimizerAt_frontier_openRepresentative hV hE hmin]
    exact inter_subset_right
  · exact measure_mono_null inter_subset_left hS

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma singleton_null_of_quadratic_upper_density (σ : FiniteMeasure Torus)
    {R A : ℝ} (hR : 0 < R)
    (hu : ∀ a : Torus, ∀ r : ℝ, 0 < r → r ≤ R →
      (σ : Measure Torus).real (Metric.ball a r) ≤ A * r ^ 2) (a : Torus) :
    (σ : Measure Torus) {a} = 0 := by
  have hh : ∀ᶠ r : ℝ in 𝓝[>] 0,
      (σ : Measure Torus).real {a} ≤ A * r ^ 2 := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hR)] with r hr hrR
    exact (measureReal_mono (singleton_subset_iff.mpr (Metric.mem_ball_self hr))).trans
      (hu a r hr hrR.le)
  have hl : Tendsto (fun r : ℝ ↦ A * r ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using (((tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0)).pow 2).const_mul A).mono_left nhdsWithin_le_nhds
  have hzero := ge_of_tendsto hl hh
  exact (ENNReal.toReal_eq_zero_iff _).mp (le_antisymm hzero ENNReal.toReal_nonneg) |>.resolve_right
    (measure_ne_top _ _)

lemma measure_le_hausdorff_two_of_upper_density (σ : FiniteMeasure Torus)
    {R A : ℝ} (hR : 0 < R) (hA : 0 < A)
    (hu : ∀ a : Torus, ∀ r : ℝ, 0 < r → r ≤ R →
      (σ : Measure Torus).real (Metric.ball a r) ≤ A * r ^ 2) :
    (σ : Measure Torus) ≤ ENNReal.ofReal (4 * A) • Measure.hausdorffMeasure 2 := by
  have hk : ENNReal.ofReal (4 * A) ≠ 0 := by positivity
  have hsmall : (ENNReal.ofReal (4 * A))⁻¹ • (σ : Measure Torus) ≤ Measure.hausdorffMeasure 2 := by
    apply Measure.le_hausdorffMeasure 2 _ (ENNReal.ofReal (R / 2)) (by positivity)
    intro s hs
    rw [Measure.smul_apply, smul_eq_mul]
    apply (ENNReal.inv_mul_le_iff hk ENNReal.ofReal_ne_top).2
    by_cases he : s.Nonempty
    swap
    · simp [not_nonempty_iff_eq_empty.mp he]
    obtain ⟨a, ha⟩ := he
    have hfin : ediam s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
    by_cases hz : ediam s = 0
    · have hsub : s ⊆ {a} := fun x hx ↦ (ediam_eq_zero_iff.mp hz hx ha)
      rw [measure_mono_null hsub (singleton_null_of_quadratic_upper_density σ hR hu a)]
      exact zero_le
    have hd : 0 < diam s := ENNReal.toReal_pos hz hfin
    have hdR : 2 * diam s ≤ R := by
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hs
      rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ R / 2)] at hh
      change diam s ≤ R / 2 at hh
      linarith
    have hsub : s ⊆ Metric.ball a (2 * diam s) := by
      intro x hx
      exact (Metric.dist_le_diam_of_mem' hfin hx ha).trans_lt (by linarith)
    have hb := (measureReal_mono hsub).trans (hu a (2 * diam s) (by positivity) hdR)
    have hh : (σ : Measure Torus) s ≤ ENNReal.ofReal (A * (2 * diam s) ^ 2) :=
      (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).2 hb
    calc
      _ ≤ ENNReal.ofReal (A * (2 * diam s) ^ 2) := hh
      _ = ENNReal.ofReal (4 * A) * ediam s ^ (2 : ℝ) := by
        rw [ENNReal.rpow_two, ← ENNReal.ofReal_toReal hfin]
        change ENNReal.ofReal (A * (2 * diam s) ^ 2) =
          ENNReal.ofReal (4 * A) * ENNReal.ofReal (diam s) ^ (2 : ℕ)
        rw [← ENNReal.ofReal_pow hd.le, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  intro s
  have hh := hsmall s
  rw [Measure.smul_apply, smul_eq_mul] at hh ⊢
  exact (ENNReal.inv_mul_le_iff hk ENNReal.ofReal_ne_top).1 hh

theorem isMinimizerAt_perimeter_absolutelyContinuous_area {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    (spatialNormalMeasure μ : Measure Torus) ≪
      (Measure.hausdorffMeasure 2).restrict (frontier (openRepresentative E)) := by
  obtain ⟨R, A, hR, hA, hu⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  have hbound := measure_le_hausdorff_two_of_upper_density (spatialNormalMeasure μ) hR hA (hu μ hμ)
  have habs : (spatialNormalMeasure μ : Measure Torus) ≪ Measure.hausdorffMeasure 2 := by
    intro s hs
    have hh := hbound s
    simpa only [Measure.smul_apply, smul_eq_mul, hs, mul_zero, nonpos_iff_eq_zero] using hh
  have hsupport : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus),
      x ∈ frontier (openRepresentative E) := by
    filter_upwards [Measure.support_mem_ae (μ := (spatialNormalMeasure μ : Measure Torus))] with x hx
    rw [isMinimizerAt_frontier_openRepresentative hV hE hmin]
    exact spatialNormalMeasure_support_subset_boundary hE hμ hx
  intro s hs
  have hh : Measure.hausdorffMeasure 2 (s ∩ frontier (openRepresentative E)) = 0 := by
    simpa only [Measure.restrict_apply₀' isClosed_frontier.measurableSet.nullMeasurableSet] using hs
  have hnull := habs hh
  have hae : s =ᵐ[(spatialNormalMeasure μ : Measure Torus)] (s ∩ frontier (openRepresentative E) : Set Torus) := by
    filter_upwards [hsupport] with x hx
    exact propext ⟨fun hs ↦ ⟨hs, hx⟩, And.left⟩
  rw [measure_congr hae]
  exact hnull

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measure_bad_scales_le (σ : FiniteMeasure Torus) (τ : Measure Torus)
    (B : Set Torus) {R A δ : ℝ} (hA : 0 < A) (hδ : 0 < δ)
    (hu : ∀ a : Torus, ∀ r : ℝ, 0 < r → r ≤ R →
      (σ : Measure Torus).real (Metric.ball a r) ≤ A * r ^ 2)
    (hbad : ∀ a ∈ B, ∃ r : ℝ, 0 < r ∧ 5 * r ≤ R ∧
      ENNReal.ofReal (δ * r ^ 2) ≤ τ (Metric.closedBall a r)) :
    (σ : Measure Torus) B ≤ ENNReal.ofReal (25 * A / δ) * τ univ := by
  classical
  choose r hr hrR he using hbad
  let rad (a : Torus) : ℝ := if ha : a ∈ B then r a ha else 0
  have hrad (a : Torus) (ha : a ∈ B) : 0 < rad a := by simpa only [rad, dite_eq_left ha] using hr a ha
  have hradR (a : Torus) (ha : a ∈ B) : 5 * rad a ≤ R := by
    simpa only [rad, dite_eq_left ha] using hrR a ha
  have henergy (a : Torus) (ha : a ∈ B) :
      ENNReal.ofReal (δ * rad a ^ 2) ≤ τ (Metric.closedBall a (rad a)) := by
    simpa only [rad, dite_eq_left ha] using he a ha
  obtain ⟨u, huB, hdis, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
    B id rad (R / 5) (fun a ha ↦ by linarith [hradR a ha]) 4 (by norm_num)
  have hdisopen : u.PairwiseDisjoint (fun a ↦ Metric.ball a (rad a)) :=
    hdis.mono (fun _ ↦ Metric.ball_subset_closedBall)
  have hcount : u.Countable := hdisopen.countable_of_isOpen (fun _ _ ↦ Metric.isOpen_ball)
    (fun a ha ↦ ⟨a, Metric.mem_ball_self (hrad a (huB ha))⟩)
  let : Countable u := hcount.to_subtype
  have hcover : B ⊆ ⋃ a : u, Metric.closedBall (a : Torus) (4 * rad a) := by
    intro a ha
    obtain ⟨b, hb, hsub⟩ := hcov a ha
    exact mem_iUnion.mpr ⟨⟨b, hb⟩, hsub (Metric.mem_closedBall_self (hrad a ha).le)⟩
  have hstep (a : u) : (σ : Measure Torus) (Metric.closedBall (a : Torus) (4 * rad a)) ≤
      ENNReal.ofReal (25 * A / δ) * τ (Metric.closedBall (a : Torus) (rad a)) := by
    have hrpos := hrad a (huB a.property)
    have hh := (measureReal_mono (Metric.closedBall_subset_ball (by linarith : 4 * rad a < 5 * rad a))).trans
      (hu a (5 * rad a) (by positivity) (hradR a (huB a.property)))
    calc
      _ ≤ ENNReal.ofReal (A * (5 * rad a) ^ 2) :=
        (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).2 hh
      _ = ENNReal.ofReal (25 * A / δ) * ENNReal.ofReal (δ * rad a ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring
      _ ≤ _ := mul_le_mul_right (henergy a (huB a.property)) _
  calc
    _ ≤ (σ : Measure Torus) (⋃ a : u, Metric.closedBall (a : Torus) (4 * rad a)) := measure_mono hcover
    _ ≤ ∑' a : u, (σ : Measure Torus) (Metric.closedBall (a : Torus) (4 * rad a)) := measure_iUnion_le _
    _ ≤ ∑' a : u, ENNReal.ofReal (25 * A / δ) * τ (Metric.closedBall (a : Torus) (rad a)) :=
      ENNReal.tsum_le_tsum hstep
    _ = ENNReal.ofReal (25 * A / δ) *
        (∑' a : u, τ (Metric.closedBall (a : Torus) (rad a))) := by rw [ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal (25 * A / δ) * τ (⋃ a ∈ u, Metric.closedBall a (rad a)) := by
      congr 1
      exact (measure_biUnion hcount hdis (fun _ _ ↦ Metric.isClosed_closedBall.measurableSet)).symm
    _ ≤ _ := mul_le_mul_right (measure_mono (subset_univ _)) _

end CubicTorus

end
end

end

end OAI
